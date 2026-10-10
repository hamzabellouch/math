import OAI.MeasureTheory.Falconer.Fourier.InverseMaskJets
import OAI.MeasureTheory.Falconer.Fourier.DescriptorJetProduct

namespace OAI

/-! # Individual radius normalization in the actual inverse expansion

Every mask retains its own radius and derivative order. The extracted
coefficient costs only the largest inverse radius to the total order.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace MaskJetIndex
variable {d : ℕ}

noncomputable def normalizedValue (j : MaskJetIndex d) (r : ℝ)
    (f : Space d → ℝ) (z : Space d) : ℂ :=
  (r^j.order * (iteratedFDeriv ℝ j.order f z) j.vectors : ℝ)

theorem value_ofReal (j : MaskJetIndex d) (f : Space d → ℝ)
    (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.value (fun w => (f w : ℂ)) z =
      ((iteratedFDeriv ℝ j.order f z) j.vectors : ℝ) := by
  change (iteratedFDeriv ℝ j.order (Complex.ofRealCLM ∘ f) z) j.vectors = _
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hf.contDiffAt (by simp)]
  rfl

theorem value_eq_inv_radius_normalized (j : MaskJetIndex d) (r : ℝ) (hr : r ≠ 0)
    (f : Space d → ℝ) (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.value (fun w => (f w : ℂ)) z =
      (((r⁻¹)^j.order : ℝ) : ℂ) * j.normalizedValue r f z := by
  rw [value_ofReal j f hf z,normalizedValue,Complex.ofReal_mul,← mul_assoc,
    ← Complex.ofReal_mul,← mul_pow,inv_mul_cancel₀ hr,one_pow,Complex.ofReal_one,one_mul]

theorem normalizedValue_descriptor (j : MaskJetIndex d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PlanarFalconer.PolicyDescriptor) (S : Finset (Sphere d))
    (x : Space d) (w : Sphere d) :
    j.normalizedValue (descriptorMaskRadius N σ b)
      (descriptorAmbientMask Q ρ m N σ J i b S x) w =
    normalizedDescriptorJet Q ρ m N σ J i b S j.order j.vectors x w := rfl

end MaskJetIndex

namespace MaskJetTerm
variable {ι X E : Type*} {d : ℕ} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def radiusCoefficient (T : MaskJetTerm ι d E) (r : ι → ℝ) (z : E) : ℂ :=
  T.coefficient z * ((∏ i, (r i)⁻¹^(T.jet i).order : ℝ) : ℂ)

theorem value_radius_normalized (T : MaskJetTerm ι d E)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space d → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (z : E) (p : Space d)
    (hp : T.point z = p) :
    T.value (fun i x w => (B i x w : ℂ)) x z =
      T.radiusCoefficient r z * ∏ i, (T.jet i).normalizedValue (r i) (B i x) p := by
  unfold value
  rw [hp]
  have hi (i : ι) := (T.jet i).value_eq_inv_radius_normalized
    (r i) (hr i) (B i x) (hB i x) p
  simp_rw [hi]
  rw [Finset.prod_mul_distrib,← Complex.ofReal_prod]
  exact (mul_assoc _ _ _).symm

theorem radiusCoefficient_norm_le (T : MaskJetTerm ι d E) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) {D : ℝ} (hD : 1 ≤ D) (hscale : ∀ i, (r i)⁻¹ ≤ D)
    {K : ℕ} (hK : T.order ≤ K) (z : E) :
    ‖T.radiusCoefficient r z‖ ≤ ‖T.coefficient z‖*D^K := by
  have hprod : 0 ≤ ∏ i, (r i)⁻¹^(T.jet i).order :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hr i).le) _)
  rw [radiusCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hprod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∏ i, D^(T.jet i).order := by
      apply Finset.prod_le_prod₀ (fun i _ => pow_nonneg (inv_nonneg.mpr (hr i).le) _)
      intro i _
      exact pow_le_pow_left₀ (inv_nonneg.mpr (hr i).le) (hscale i) _
    _ = D^T.order := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ D^K := pow_le_pow_right₀ hD hK

theorem value_radius_endpoint_split {τ Y : Type*} [Fintype τ]
    (T : MaskJetTerm (ι ⊕ τ) d E) (r : ι ⊕ τ → ℝ) (hr : ∀ i, r i ≠ 0)
    (B : ι → X → Space d → ℝ) (C : τ → Y → Space d → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (x : X) (y : Y) (z : E) (p : Space d) (hp : T.point z = p) :
    T.value (fun i (xy : X × Y) w => Sum.elim (fun a => (B a xy.1 w : ℂ))
      (fun b => (C b xy.2 w : ℂ)) i) (x,y) z =
      T.radiusCoefficient r z *
        (∏ i, (T.jet (.inl i)).normalizedValue (r (.inl i)) (B i x) p) *
        (∏ i, (T.jet (.inr i)).normalizedValue (r (.inr i)) (C i y) p) := by
  have hfun : (fun i (xy : X × Y) w => Sum.elim (fun a => (B a xy.1 w : ℂ))
      (fun b => (C b xy.2 w : ℂ)) i) =
      (fun i (xy : X × Y) w =>
        ((Sum.elim (fun a => B a xy.1 w) (fun b => C b xy.2 w) i : ℝ) : ℂ)) := by
    funext i xy w
    cases i <;> rfl
  rw [hfun]
  rw [value_radius_normalized T r hr
    (fun i (xy : X × Y) w => Sum.elim (fun a => B a xy.1 w) (fun b => C b xy.2 w) i)
    (by intro i xy; cases i with
        | inl i => exact hB i xy.1
        | inr i => exact hC i xy.2) (x,y) z p hp]
  rw [Fintype.prod_sum_type,mul_assoc]
  rfl

end MaskJetTerm

namespace MaskJetExpansion
variable {ι : Type} {X E : Type*} {d : ℕ} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem value_radius_normalized (S : MaskJetExpansion ι d E)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space d → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (z : E) (p : Space d)
    (hp : S.HasPointAt z p) :
    S.value (fun i x w => (B i x w : ℂ)) x z =
      ∑ a : S.index, (S.term a).radiusCoefficient r z *
        ∏ i, ((S.term a).jet i).normalizedValue (r i) (B i x) p := by
  apply Finset.sum_congr rfl
  intro a _
  exact (S.term a).value_radius_normalized r hr B hB x z p (hp a)

theorem localInverseAmplitude_product_radius_jets [DecidableEq ι] (m j : ℕ)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) :
    ∃ S : MaskJetExpansion ι (m+3) (Space (m+3)), S.HasOrder (2*j) ∧
      ∀ (B : ι → X → Space (m+3) → ℝ),
        (∀ i x, ContDiff ℝ ∞ (B i x)) → ∀ (x : X) (e : Sphere (m+3)),
        ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 →
        localInverseAmplitude m (fun z => ∏ i, (B i x z : ℂ)) j e =
          ∑ a : S.index, (S.term a).radiusCoefficient r e *
            ∏ i, ((S.term a).jet i).normalizedValue (r i) (B i x) e := by
  obtain ⟨S,horder,hvalue,hpoint⟩ :=
    localInverseAmplitude_product_jets (ι := ι) (X := X) m j
  refine ⟨S,horder,?_⟩
  intro B hB x e he
  rw [← hvalue (fun i x z => (B i x z : ℂ))
    (fun i x => Complex.ofRealCLM.contDiff.comp (hB i x)) x e]
  exact S.value_radius_normalized r hr B hB x e e (hpoint e he)

end MaskJetExpansion
end Falconer

end OAI
