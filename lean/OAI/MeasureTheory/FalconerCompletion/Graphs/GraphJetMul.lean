import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.CoordNormBound
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphSourceFourSpatialDecay
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasureAeNorm

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set
open scoped ContDiff ComplexConjugate
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma graphJetMul {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : ℕ) {C D A : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A) (w : V)
    (hfb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f w‖ ≤ C*A^j)
    (hgb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j g w‖ ≤ D*A^j) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun w => f w*g w) w‖ ≤ (C*D*2^m)*A^j := by
  intro j hj
  calc
    _ ≤ ∑ k ∈ Finset.range (j+1), (j.choose k:ℝ)*‖iteratedFDeriv ℝ k f w‖*
        ‖iteratedFDeriv ℝ (j-k) g w‖ :=
      norm_iteratedFDeriv_mul_le hf hg w (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))
    _ ≤ ∑ k ∈ Finset.range (j+1), (j.choose k:ℝ)*(C*A^k)*(D*A^(j-k)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      gcongr
      · exact hfb k (hkj.trans hj)
      · exact hgb (j-k) ((Nat.sub_le _ _).trans hj)
    _ = C*D*(A+A)^j := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (C*D*2^j)*A^j := by rw [show A+A=2*A by ring,mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj)
        (mul_nonneg hC hD)) (pow_nonneg hA _)

lemma graphJetConj {f : V → ℂ} {m : ℕ} {C A : ℝ} {w : V}
    (h : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f w‖ ≤ C*A^j) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun w => conj (f w)) w‖ ≤ C*A^j := by
  intro j hj
  change ‖iteratedFDeriv ℝ j (Complex.conjLIE ∘ f) w‖ ≤ _
  rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left f w j]
  exact h j hj

lemma graphJetPair {θ b c : V → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c)
    (m : ℕ) {P B C A : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (w : V)
    (hdθ : ∀ j ≤ m, ‖iteratedFDeriv ℝ j θ w‖ ≤ P*A^j)
    (hdb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j b w‖ ≤ B*A^j)
    (hdc : ∀ j ≤ m, ‖iteratedFDeriv ℝ j c w‖ ≤ C*A^j) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun w => θ w*b w*conj (c w)) w‖ ≤
      (P*B*2^m*C*2^m)*A^j := by
  exact graphJetMul (hθ.mul hb) (Complex.conjCLE.contDiff.comp hc) m
    (by positivity) hC hA w (graphJetMul hθ hb m hP hB hA w hdθ hdb)
      (graphJetConj hdc)

lemma graphJet_enlarge {f : V → ℂ} {m : ℕ} {C a A : ℝ} {w : V}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (haA : a ≤ A)
    (h : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f w‖ ≤ C*a^j) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j f w‖ ≤ C*A^j := by
  intro j hj
  exact (h j hj).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha haA j) hC)

lemma graphCapJet (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ A : ℝ) (a : Fin d → ℤ), 0 < δ → δ⁻¹ ≤ A →
    ∀ w, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun w => (tensorCapND δ a w:ℂ)) w‖ ≤ C*A^j := by
  obtain ⟨C,hC,hb⟩ := tensorCapND_derivative_bound d m
  refine ⟨C,hC,?_⟩
  intro δ A a hδ hA w j hj
  change ‖iteratedFDeriv ℝ j (Complex.ofRealLI ∘ tensorCapND δ a) w‖ ≤ _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    (tensorCapND_contDiff δ a).contDiffAt (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))]
  exact (hb δ a hδ j hj w).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hA j) hC)

end CurrentFalconer
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma graph_four_moment_bridge
    (μ₁ μ₂ μ₃ μ₄ : Measure V)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (Ψ : ℝ → ℂ) {Q : ℝ} (hQ : 0 < Q)
    (θ₁ θ₂ : V → ℂ) (b₁ b₂ b₃ b₄ : V → V → ℂ)
    (hi : Integrable (fun p : ℝ×(V×V) => Ψ (p.1/Q)*
      (θ₁ p.2.1*sourceAngularTransformND μ₁ univ 1 b₁ p.1 p.2.1*
        conj (sourceAngularTransformND μ₂ univ 1 b₂ p.1 p.2.1))*
      (θ₂ p.2.2*sourceAngularTransformND μ₃ univ 1 b₃ p.1 p.2.2*
        conj (sourceAngularTransformND μ₄ univ 1 b₄ p.1 p.2.2)))
      (volume.prod ((canonicalSphereMeasureND V).prod (canonicalSphereMeasureND V)))) :
    (Q⁻¹:ℝ) • (∫ p : ℝ×(V×V), Ψ (p.1/Q)*
      (θ₁ p.2.1*sourceAngularTransformND μ₁ univ 1 b₁ p.1 p.2.1*
        conj (sourceAngularTransformND μ₂ univ 1 b₂ p.1 p.2.1))*
      (θ₂ p.2.2*sourceAngularTransformND μ₃ univ 1 b₃ p.1 p.2.2*
        conj (sourceAngularTransformND μ₄ univ 1 b₄ p.1 p.2.2))
      ∂volume.prod ((canonicalSphereMeasureND V).prod (canonicalSphereMeasureND V))) =
    ∫ u, Ψ u * graphPairMoment μ₁ μ₂ b₁ b₂ θ₁ (Q*u) *
      graphPairMoment μ₃ μ₄ b₃ b₄ θ₂ (Q*u) := by
  rw [integral_prod _ hi]
  have he (r : ℝ) :
      (∫ w : V×V, Ψ (r/Q)*
        (θ₁ w.1*sourceAngularTransformND μ₁ univ 1 b₁ r w.1*
          conj (sourceAngularTransformND μ₂ univ 1 b₂ r w.1))*
        (θ₂ w.2*sourceAngularTransformND μ₃ univ 1 b₃ r w.2*
          conj (sourceAngularTransformND μ₄ univ 1 b₄ r w.2))
        ∂(canonicalSphereMeasureND V).prod (canonicalSphereMeasureND V)) =
      Ψ (r/Q)*graphPairMoment μ₁ μ₂ b₁ b₂ θ₁ r * graphPairMoment μ₃ μ₄ b₃ b₄ θ₂ r := by
    let F := fun w => θ₁ w*sourceAngularTransformND μ₁ univ 1 b₁ r w*
      conj (sourceAngularTransformND μ₂ univ 1 b₂ r w)
    let G := fun w => θ₂ w*sourceAngularTransformND μ₃ univ 1 b₃ r w*
      conj (sourceAngularTransformND μ₄ univ 1 b₄ r w)
    change (∫ w : V×V, Ψ (r/Q)*F w.1*G w.2
      ∂(canonicalSphereMeasureND V).prod (canonicalSphereMeasureND V)) = _
    rw [show (fun w : V×V => Ψ (r/Q)*F w.1*G w.2) =
      (fun w : V×V => Ψ (r/Q)*(F w.1*G w.2)) by funext w; ring,
      integral_const_mul,integral_prod_mul]
    change Ψ (r/Q)*(graphPairMoment μ₁ μ₂ b₁ b₂ θ₁ r * graphPairMoment μ₃ μ₄ b₃ b₄ θ₂ r) = _
    ring
  simp_rw [he]
  have h := Measure.integral_comp_mul_left (fun r => Ψ (r/Q)*
    graphPairMoment μ₁ μ₂ b₁ b₂ θ₁ r*graphPairMoment μ₃ μ₄ b₃ b₄ θ₂ r) Q
  rw [abs_of_pos (inv_pos.mpr hQ)] at h
  rw [←h]
  apply integral_congr_ae
  filter_upwards with u
  rw [mul_div_cancel_left₀ u hQ.ne']

omit [BorelSpace V] in
lemma graph_angular_four_integrable [BorelSpace V] (σ : Measure V) [IsFiniteMeasure σ]
    {Ψ : ℝ → ℂ} (hiΨ : Integrable Ψ)
    (θ₁ θ₂ : V → ℂ) (hθ₁ : Measurable θ₁) (hθ₂ : Measurable θ₂)
    (U₁ U₂ U₃ U₄ : ℝ×V → ℂ)
    (hm₁ : Measurable U₁) (hm₂ : Measurable U₂) (hm₃ : Measurable U₃) (hm₄ : Measurable U₄)
    {P₁ P₂ B₁ B₂ B₃ B₄ : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hB₃ : 0 ≤ B₃) (_hB₄ : 0 ≤ B₄)
    (hb : ∀ᵐ w ∂σ, ‖θ₁ w‖ ≤ P₁ ∧ ‖θ₂ w‖ ≤ P₂ ∧
      ∀ r, ‖U₁ (r,w)‖ ≤ B₁ ∧ ‖U₂ (r,w)‖ ≤ B₂ ∧ ‖U₃ (r,w)‖ ≤ B₃ ∧ ‖U₄ (r,w)‖ ≤ B₄) :
    Integrable (fun p : ℝ×(V×V) => Ψ p.1*
      (θ₁ p.2.1*U₁ (p.1,p.2.1)*conj (U₂ (p.1,p.2.1)))*
      (θ₂ p.2.2*U₃ (p.1,p.2.2)*conj (U₄ (p.1,p.2.2))))
      (volume.prod (σ.prod σ)) := by
  let H := fun w => ‖θ₁ w‖ ≤ P₁ ∧ ‖θ₂ w‖ ≤ P₂ ∧
    ∀ r, ‖U₁ (r,w)‖ ≤ B₁ ∧ ‖U₂ (r,w)‖ ≤ B₂ ∧ ‖U₃ (r,w)‖ ≤ B₃ ∧ ‖U₄ (r,w)‖ ≤ B₄
  change ∀ᵐ w ∂σ, H w at hb
  have hprod : ∀ᵐ z : V×V ∂σ.prod σ, H z.1 ∧ H z.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb,
      Measure.quasiMeasurePreserving_snd.ae hb] with z h₁ h₂
    exact ⟨h₁,h₂⟩
  have hpt : ∀ᵐ p : ℝ×(V×V) ∂volume.prod (σ.prod σ), H p.2.1 ∧ H p.2.2 :=
    Measure.quasiMeasurePreserving_snd.ae hprod
  let K := (P₁*B₁*B₂)*(P₂*B₃*B₄)
  have hm : AEStronglyMeasurable (fun p : ℝ×(V×V) => Ψ p.1*
      (θ₁ p.2.1*U₁ (p.1,p.2.1)*conj (U₂ (p.1,p.2.1)))*
      (θ₂ p.2.2*U₃ (p.1,p.2.2)*conj (U₄ (p.1,p.2.2)))) (volume.prod (σ.prod σ)) := by
    apply (hiΨ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (Measurable.aestronglyMeasurable ?_) |>.mul (Measurable.aestronglyMeasurable ?_)
    · exact ((hθ₁.comp measurable_snd.fst).mul
        (hm₁.comp (measurable_fst.prodMk measurable_snd.fst))).mul
          (Complex.continuous_conj.measurable.comp (hm₂.comp (measurable_fst.prodMk measurable_snd.fst)))
    · exact ((hθ₂.comp measurable_snd.snd).mul
        (hm₃.comp (measurable_fst.prodMk measurable_snd.snd))).mul
          (Complex.continuous_conj.measurable.comp (hm₄.comp (measurable_fst.prodMk measurable_snd.snd)))
  apply ((hiΨ.norm.comp_fst (σ.prod σ)).mul_const K).mono' hm
  filter_upwards [hpt] with p hp
  change ‖Ψ p.1 * _ * _‖ ≤ ‖Ψ p.1‖*K
  simp only [norm_mul,Complex.norm_conj]
  simp only [K]
  have hh₁ := (hp.1.2.2 p.1)
  have hh₂ := (hp.2.2.2 p.1)
  calc
    _ ≤ (‖Ψ p.1‖*(P₁*B₁*B₂))*(P₂*B₃*B₄) := by gcongr <;> first | exact hp.1.1 | exact hp.2.2.1 | exact hh₁.1 | exact hh₁.2.1 | exact hh₂.2.2.1 | exact hh₂.2.2.2
    _ = _ := by ring

end CurrentFalconer
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def graphCellLaw (ρ : Measure V) (P : Set V) (M : ℝ) : Measure V :=
  ENNReal.ofReal M⁻¹ • ρ.restrict P

instance graphCellLaw_finite (ρ : Measure V) [IsFiniteMeasure ρ] (P : Set V) (M : ℝ) :
    IsFiniteMeasure (graphCellLaw ρ P M) := by
  refine ⟨?_⟩
  simp only [graphCellLaw,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
lemma graphCellLaw_ae [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [BorelSpace V]
    (ρ : Measure V) {P : Set V} (hP : MeasurableSet P) (M : ℝ) :
    ∀ᵐ x ∂graphCellLaw ρ P M, x ∈ P := by
  exact Measure.ae_smul_measure (ae_restrict_mem hP) _

omit [FiniteDimensional ℝ V] [BorelSpace V] in
lemma graphCellLaw_transform [FiniteDimensional ℝ V] [BorelSpace V]
    (ρ : Measure V) (P : Set V) {M : ℝ} (hM : 0 ≤ M)
    (b : V → V → ℂ) (r : ℝ) (w : V) :
    sourceAngularTransformND (graphCellLaw ρ P M) univ 1 b r w =
      sourceAngularTransformND ρ P M b r w := by
  simp only [sourceAngularTransformND,graphCellLaw,Measure.restrict_univ,inv_one,one_smul]
  rw [integral_smul_measure,ENNReal.toReal_ofReal (inv_nonneg.mpr hM)]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
lemma graphCellLaw_mass [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [BorelSpace V]
    (ρ : Measure V) [IsFiniteMeasure ρ] (P : Set V) {M : ℝ} (hM : 0 ≤ M) :
    (graphCellLaw ρ P M).real univ = M⁻¹*ρ.real P := by
  simp [graphCellLaw,Measure.real,ENNReal.toReal_ofReal (inv_nonneg.mpr hM)]

lemma graph_four_integrable
    (μ₁ μ₂ μ₃ μ₄ : Measure V)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    {Ψ : ℝ → ℂ} (hiΨ : Integrable Ψ)
    (θ₁ θ₂ : V → ℂ) (b₁ b₂ b₃ b₄ : V → V → ℂ)
    (hθ₁ : Measurable θ₁) (hθ₂ : Measurable θ₂)
    (hb₁ : Measurable (Function.uncurry b₁)) (hb₂ : Measurable (Function.uncurry b₂))
    (hb₃ : Measurable (Function.uncurry b₃)) (hb₄ : Measurable (Function.uncurry b₄))
    {P₁ P₂ B₁ B₂ B₃ B₄ : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃) (hB₄ : 0 ≤ B₄)
    (hdθ₁ : ∀ w, ‖w‖=1 → ‖θ₁ w‖ ≤ P₁) (hdθ₂ : ∀ w, ‖w‖=1 → ‖θ₂ w‖ ≤ P₂)
    (hbd₁ : ∀ x w, ‖w‖=1 → ‖b₁ x w‖ ≤ B₁) (hbd₂ : ∀ x w, ‖w‖=1 → ‖b₂ x w‖ ≤ B₂)
    (hbd₃ : ∀ x w, ‖w‖=1 → ‖b₃ x w‖ ≤ B₃) (hbd₄ : ∀ x w, ‖w‖=1 → ‖b₄ x w‖ ≤ B₄) :
    Integrable (fun p : ℝ×(V×V) => Ψ p.1*
      (θ₁ p.2.1*sourceAngularTransformND μ₁ univ 1 b₁ p.1 p.2.1*
        conj (sourceAngularTransformND μ₂ univ 1 b₂ p.1 p.2.1))*
      (θ₂ p.2.2*sourceAngularTransformND μ₃ univ 1 b₃ p.1 p.2.2*
        conj (sourceAngularTransformND μ₄ univ 1 b₄ p.1 p.2.2)))
      (volume.prod ((canonicalSphereMeasureND V).prod (canonicalSphereMeasureND V))) := by
  apply graph_angular_four_integrable (canonicalSphereMeasureND V) hiΨ θ₁ θ₂ hθ₁ hθ₂
    _ _ _ _ (sourceAngularTransformND_measurable μ₁ univ 1 hb₁)
    (sourceAngularTransformND_measurable μ₂ univ 1 hb₂)
    (sourceAngularTransformND_measurable μ₃ univ 1 hb₃)
    (sourceAngularTransformND_measurable μ₄ univ 1 hb₄)
    hP₁ hP₂ (mul_nonneg measureReal_nonneg hB₁)
    (mul_nonneg measureReal_nonneg hB₂)
    (mul_nonneg measureReal_nonneg hB₃)
    (mul_nonneg measureReal_nonneg hB₄)
  filter_upwards [canonicalSphereMeasureND_ae_norm (V:=V)] with w hw
  refine ⟨hdθ₁ w hw,hdθ₂ w hw,fun r => ?_⟩
  constructor
  · simpa [Measure.real] using sourceAngularTransformND_norm_le μ₁ univ 1 b₁ r w (fun x => hbd₁ x w hw)
  constructor
  · simpa [Measure.real] using sourceAngularTransformND_norm_le μ₂ univ 1 b₂ r w (fun x => hbd₂ x w hw)
  constructor
  · simpa [Measure.real] using sourceAngularTransformND_norm_le μ₃ univ 1 b₃ r w (fun x => hbd₃ x w hw)
  · simpa [Measure.real] using sourceAngularTransformND_norm_le μ₄ univ 1 b₄ r w (fun x => hbd₄ x w hw)

end CurrentFalconer
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem graph_source_raw_four_decay
    {sig c₀ Ccap G : ℝ} (hsig : 0 < sig) (hc₀ : 0 < c₀)
    (hCcap : 0 ≤ Ccap) (hG : 0 ≤ G) (T : ℝ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (a p v L : ℝ), p-a ≤ v-p+2*sig*N → L ≤ v-p+2*sig*N → 0 ≤ v-p →
    let R := (2:ℝ)^N
    let δ := min c₀ (((2:ℝ)^(p-a))⁻¹*R^(10*sig))
    let τ := (2:ℝ)^(-p)*R^(30*sig)
    let A := 1+R^sig*max 1 ((2:ℝ)^L*R^(-50*sig))+δ⁻¹
    ∀ (μ₁ μ₂ μ₃ μ₄ : Measure V),
    ∀ [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄],
    ∀ (Ψ : ℝ → ℂ) (w₁ w₂ d₁ d₂ : V) (K J₁ J₂ : ℝ)
      (θ₁ θ₂ : V → ℂ) (b₁ b₂ b₃ b₄ : V → V → ℂ)
      (P₁ P₂ B₁ B₂ B₃ B₄ : ℝ),
    ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Icc (1/4:ℝ) 4 →
    (∫ u : ℝ, ‖Ψ u‖) ≤ K → (∀ u, ‖iteratedDeriv m Ψ u‖ ≤ K) →
    ‖w₁‖=1 → ‖w₂‖=1 → 0 ≤ K → 0 ≤ J₁ → 0 ≤ J₂ →
    Measurable θ₁ → Measurable θ₂ →
    Measurable (Function.uncurry b₁) → Measurable (Function.uncurry b₂) →
    Measurable (Function.uncurry b₃) → Measurable (Function.uncurry b₄) →
    0 ≤ P₁ → 0 ≤ P₂ → 0 ≤ B₁ → 0 ≤ B₂ → 0 ≤ B₃ → 0 ≤ B₄ →
    (∀ w, ‖w‖=1 → ‖θ₁ w‖ ≤ P₁) → (∀ w, ‖w‖=1 → ‖θ₂ w‖ ≤ P₂) →
    (∀ x w, ‖w‖=1 → ‖b₁ x w‖ ≤ B₁) → (∀ x w, ‖w‖=1 → ‖b₂ x w‖ ≤ B₂) →
    (∀ x w, ‖w‖=1 → ‖b₃ x w‖ ≤ B₃) → (∀ x w, ‖w‖=1 → ‖b₄ x w‖ ≤ B₄) →
    (∀ᵐ z ∂(μ₁.prod μ₂).prod (μ₃.prod μ₄),
      ‖z.1.1-z.1.2‖ ≤ G*(2:ℝ)^(-a) ∧ ‖z.2.1-z.2.2‖ ≤ G*(2:ℝ)^(-a) ∧
      ‖(z.1.1-z.1.2)-d₁‖ ≤ G*(2:ℝ)^(-p) ∧ ‖(z.2.1-z.2.2)-d₂‖ ≤ G*(2:ℝ)^(-p)) →
    ¬(‖d₁-inner ℝ d₁ w₁ • w₁‖ ≤ τ ∧
      ‖d₂-inner ℝ d₂ w₂ • w₂‖ ≤ τ ∧ |inner ℝ w₁ d₁+inner ℝ w₂ d₂| ≤ τ) →
    (∀ z, ContDiff ℝ ∞ (graphPairAmplitude θ₁ b₁ b₂ z)) →
    (∀ z, ContDiff ℝ ∞ (graphPairAmplitude θ₂ b₃ b₄ z)) →
    (∀ z j, j ≤ m → ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (graphPairAmplitude θ₁ b₁ b₂ z) w‖ ≤ J₁*A^j) →
    (∀ z j, j ≤ m → ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (graphPairAmplitude θ₂ b₃ b₄ z) w‖ ≤ J₂*A^j) →
    (∀ w, ‖w‖=1 → θ₁ w ≠ 0 → ‖w-w₁‖ ≤ Ccap*δ) →
    (∀ w, ‖w‖=1 → θ₂ w ≠ 0 → ‖w-w₂‖ ≤ Ccap*δ) →
    ‖∫ p : ℝ×(V×V), Ψ (p.1/(2:ℝ)^v)*
      (θ₁ p.2.1*sourceAngularTransformND μ₁ univ 1 b₁ p.1 p.2.1*
        conj (sourceAngularTransformND μ₂ univ 1 b₂ p.1 p.2.1))*
      (θ₂ p.2.2*sourceAngularTransformND μ₃ univ 1 b₃ p.1 p.2.2*
        conj (sourceAngularTransformND μ₄ univ 1 b₄ p.1 p.2.2))
      ∂volume.prod ((canonicalSphereMeasureND V).prod (canonicalSphereMeasureND V))‖ ≤
      C*K*J₁*J₂*R^(-T)*(2:ℝ)^v*((μ₁.prod μ₂).prod (μ₃.prod μ₄)).real univ := by
  obtain ⟨m,C,hC,N₀,hN₀⟩ := graph_source_four_spatial_decay (V:=V) hsig hc₀ hCcap hG T
  refine ⟨m,C,hC,N₀,?_⟩
  intro N hN a p v L hh hL hq R δ τ A μ₁ μ₂ μ₃ μ₄ _ _ _ _
    Ψ w₁ w₂ d₁ d₂ K J₁ J₂ θ₁ θ₂ b₁ b₂ b₃ b₄ P₁ P₂ B₁ B₂ B₃ B₄
    hΨ hsΨ hK hdΨ hw₁ hw₂ hK0 hJ₁ hJ₂ hθ₁ hθ₂ hb₁ hb₂ hb₃ hb₄
    hP₁ hP₂ hB₁ hB₂ hB₃ hB₄ hdθ₁ hdθ₂ hbd₁ hbd₂ hbd₃ hbd₄ hgeo hne
    ha₁ ha₂ hd₁ hd₂ hs₁ hs₂
  have hiΨ : Integrable Ψ := hΨ.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport Ψ) hsΨ)
  have hQ : (0:ℝ)<(2:ℝ)^v := by positivity
  have hi := graph_four_integrable μ₁ μ₂ μ₃ μ₄ (hiΨ.comp_div hQ.ne') θ₁ θ₂
    b₁ b₂ b₃ b₄ hθ₁ hθ₂ hb₁ hb₂ hb₃ hb₄ hP₁ hP₂ hB₁ hB₂ hB₃ hB₄
    hdθ₁ hdθ₂ hbd₁ hbd₂ hbd₃ hbd₄
  have he := graph_four_moment_bridge μ₁ μ₂ μ₃ μ₄ Ψ hQ θ₁ θ₂ b₁ b₂ b₃ b₄ hi
  have hd := hN₀ N hN a p v L hh hL hq μ₁ μ₂ μ₃ μ₄ Ψ w₁ w₂ d₁ d₂
    K J₁ J₂ θ₁ θ₂ b₁ b₂ b₃ b₄ P₁ P₂ B₁ B₂ B₃ B₄
    hΨ hsΨ hK hdΨ hw₁ hw₂ hK0 hJ₁ hJ₂ hθ₁ hθ₂ hb₁ hb₂ hb₃ hb₄
    hP₁ hP₂ hB₁ hB₂ hB₃ hB₄ hdθ₁ hdθ₂ hbd₁ hbd₂ hbd₃ hbd₄ hgeo hne
    ha₁ ha₂ hd₁ hd₂ hs₁ hs₂
  rw [←he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hQ)] at hd
  have hz := mul_le_mul_of_nonneg_left hd hQ.le
  rw [←mul_assoc,mul_inv_cancel₀ hQ.ne',one_mul] at hz
  exact hz.trans_eq (by ring)

end CurrentFalconer
end
end

end OAI
