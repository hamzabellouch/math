import OAI.MeasureTheory.Falconer.Fourier.MaskJetAlgebra
import OAI.MeasureTheory.Falconer.Estimates.SeparatedInverse

namespace OAI

/-! # The actual inverse as finite products of individual mask jets

The construction follows the already proved safe-chart inverse recursion.
All mask occurrences survive in every term, and the total order charged to
them is at most twice the inverse index.
-/

namespace Falconer
open scoped ContDiff

structure MaskJetExpansion (ι : Type) (d : ℕ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  index : Type
  finite : Fintype index
  term : index → MaskJetTerm ι d E

attribute [instance] MaskJetExpansion.finite

namespace MaskJetExpansion
variable {ι : Type} {X E H : Type*} {d : ℕ}
  [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def value (S : MaskJetExpansion ι d E)
    (B : ι → X → Space d → ℂ) (x : X) (z : E) : ℂ :=
  ∑ a : S.index, (S.term a).value B x z

def HasOrder (S : MaskJetExpansion ι d E) (K : ℕ) : Prop :=
  ∀ a, (S.term a).order ≤ K

theorem value_contDiff (S : MaskJetExpansion ι d E) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) :
    ContDiff ℝ ∞ (S.value B x) :=
  ContDiff.sum (fun a _ => (S.term a).value_contDiff B hB x)

noncomputable def product : MaskJetExpansion ι d (Space d) where
  index := Unit
  finite := inferInstance
  term := fun _ => ⟨fun _ => 1,id,fun _ => MaskJetIndex.zero d,contDiff_const,contDiff_id⟩

@[simp] theorem product_value (B : ι → X → Space d → ℂ) (x : X) (z : Space d) :
    (product : MaskJetExpansion ι d (Space d)).value B x z = ∏ i, B i x z := by
  change (∑ _a : Unit, (1:ℂ)*∏ i, (MaskJetIndex.zero d).value (B i x) z) = _
  simp

theorem product_hasOrder : (product : MaskJetExpansion ι d (Space d)).HasOrder 0 := by
  intro a
  simp [product,MaskJetTerm.order,MaskJetIndex.zero]

noncomputable def mulFixed (S : MaskJetExpansion ι d E) (c : E → ℂ)
    (hc : ContDiff ℝ ∞ c) : MaskJetExpansion ι d E :=
  ⟨S.index,S.finite,fun a => (S.term a).mulFixed c hc⟩

@[simp] theorem mulFixed_value (S : MaskJetExpansion ι d E) (c : E → ℂ)
    (hc : ContDiff ℝ ∞ c) (B : ι → X → Space d → ℂ) (x : X) (z : E) :
    (S.mulFixed c hc).value B x z = c z*S.value B x z := by
  change (∑ a : S.index, ((S.term a).mulFixed c hc).value B x z) = _
  simp only [MaskJetTerm.mulFixed_value,← Finset.mul_sum]
  rfl

noncomputable def pullback (S : MaskJetExpansion ι d E) (g : H → E)
    (hg : ContDiff ℝ ∞ g) : MaskJetExpansion ι d H :=
  ⟨S.index,S.finite,fun a => (S.term a).pullback g hg⟩

@[simp] theorem pullback_value (S : MaskJetExpansion ι d E) (g : H → E)
    (hg : ContDiff ℝ ∞ g) (B : ι → X → Space d → ℂ) (x : X) (z : H) :
    (S.pullback g hg).value B x z = S.value B x (g z) := rfl

noncomputable def sum {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E) :
    MaskJetExpansion ι d E :=
  ⟨(j : J) × (S j).index,inferInstance,fun a => (S a.1).term a.2⟩

@[simp] theorem sum_value {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E)
    (B : ι → X → Space d → ℂ) (x : X) (z : E) :
    (sum S).value B x z = ∑ j, (S j).value B x z :=
  Fintype.sum_sigma _

noncomputable def derivative [DecidableEq ι] (S : MaskJetExpansion ι d E)
    (v : E) : MaskJetExpansion ι d E :=
  ⟨S.index × (Unit ⊕ (ι × Fin d)),inferInstance,
    fun a => (S.term a.1).derivativeTerm v a.2⟩

theorem derivative_value [DecidableEq ι] (S : MaskJetExpansion ι d E)
    (B : ι → X → Space d → ℂ) (hB : ∀ i x, ContDiff ℝ ∞ (B i x))
    (v : E) (x : X) (z : E) :
    (S.derivative v).value B x z = fderiv ℝ (S.value B x) z v := by
  change (∑ a : S.index × (Unit ⊕ (ι × Fin d)),
    ((S.term a.1).derivativeTerm v a.2).value B x z) = _
  rw [Fintype.sum_prod_type]
  simp_rw [MaskJetTerm.derivative_value _ _ hB]
  change _ = fderiv ℝ (fun z => ∑ a : S.index, (S.term a).value B x z) z v
  rw [fderiv_fun_sum (fun a _ =>
    ((S.term a).value_contDiff B hB x).differentiable (by simp) |>.differentiableAt)]
  simp only [sum_apply]

theorem HasOrder.mulFixed {S : MaskJetExpansion ι d E} {K : ℕ}
    (h : S.HasOrder K) (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    (S.mulFixed c hc).HasOrder K := h

theorem HasOrder.pullback {S : MaskJetExpansion ι d E} {K : ℕ}
    (h : S.HasOrder K) (g : H → E) (hg : ContDiff ℝ ∞ g) :
    (S.pullback g hg).HasOrder K := h

theorem sum_hasOrder {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E)
    {K : ℕ} (h : ∀ j, (S j).HasOrder K) : (sum S).HasOrder K :=
  fun a => h a.1 a.2

theorem HasOrder.derivative [DecidableEq ι] {S : MaskJetExpansion ι d E} {K : ℕ}
    (h : S.HasOrder K) (v : E) : (S.derivative v).HasOrder (K+1) :=
  fun a => ((S.term a.1).derivativeTerm_order v a.2).trans (Nat.add_le_add_right (h a.1) 1)

noncomputable def laplacian [DecidableEq ι] {n : ℕ} (S : MaskJetExpansion ι d E)
    (v : Fin n → E) : MaskJetExpansion ι d E :=
  sum (fun j => (S.derivative (v j)).derivative (v j))

theorem laplacian_value [DecidableEq ι] {n : ℕ} (S : MaskJetExpansion ι d E)
    (v : Fin n → E) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (z : E) :
    (S.laplacian v).value B x z = directionalLaplacian v (S.value B x) z := by
  rw [laplacian,sum_value,directionalLaplacian,directionalLaplacianTrace_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [derivative_value _ _ hB]
  have he : (S.derivative (v j)).value B x = fun z => fderiv ℝ (S.value B x) z (v j) :=
    funext (derivative_value S B hB (v j) x)
  rw [he]
  have hdf : Differentiable ℝ (fderiv ℝ (S.value B x)) :=
    ((S.value_contDiff B hB x).fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hc := ((ContinuousLinearMap.apply ℝ ℂ (v j)).hasFDerivAt.comp z
    hdf.differentiableAt.hasFDerivAt).fderiv
  have hv := congrArg (fun T : E →L[ℝ] ℂ => T (v j)) hc
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using hv

theorem HasOrder.laplacian [DecidableEq ι] {n : ℕ} {S : MaskJetExpansion ι d E}
    {K : ℕ} (h : S.HasOrder K) (v : Fin n → E) : (S.laplacian v).HasOrder (K+2) :=
  sum_hasOrder _ (fun j => (h.derivative (v j)).derivative (v j))

noncomputable def iteratedLaplacian [DecidableEq ι] {n : ℕ} (S : MaskJetExpansion ι d E)
    (v : Fin n → E) (j : ℕ) : MaskJetExpansion ι d E :=
  (fun T : MaskJetExpansion ι d E => T.laplacian v)^[j] S

theorem iteratedLaplacian_value [DecidableEq ι] {n : ℕ} (S : MaskJetExpansion ι d E)
    (v : Fin n → E) (j : ℕ) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) :
    (S.iteratedLaplacian v j).value B x = (directionalLaplacian v)^[j] (S.value B x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [MaskJetExpansion.iteratedLaplacian,Function.iterate_succ_apply']
    funext z
    rw [laplacian_value _ _ _ hB]
    change directionalLaplacian v ((S.iteratedLaplacian v j).value B x) z = _
    rw [ih]

theorem HasOrder.iteratedLaplacian [DecidableEq ι] {n : ℕ} {S : MaskJetExpansion ι d E}
    {K : ℕ} (h : S.HasOrder K) (v : Fin n → E) (j : ℕ) :
    (S.iteratedLaplacian v j).HasOrder (K+2*j) := by
  induction j with
  | zero => simpa only [MaskJetExpansion.iteratedLaplacian,Function.iterate_zero_apply,mul_zero,Nat.add_zero] using h
  | succ j ih =>
    have hh := ih.laplacian v
    rw [show K+2*j+2 = K+2*(j+1) by omega] at hh
    simpa only [MaskJetExpansion.iteratedLaplacian,Function.iterate_succ_apply'] using hh

noncomputable def stationaryJet [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) : MaskJetExpansion ι d (Space (m+3)) :=
  let T := (S.pullback (safeStationaryChart m) (safeStationaryChart_contDiff m)).mulFixed
    (SmoothSeparation.stationaryJointDensity m) (SmoothSeparation.stationaryJointDensity_contDiff m)
  let U := (T.iteratedLaplacian (verticalDirections (m+2)) j).pullback
    (fun e => (e,(0 : Space (m+2)))) (contDiff_id.prodMk contDiff_const)
  U.mulFixed (SmoothSeparation.stationaryJetMultiplier m j)
    (SmoothSeparation.stationaryJetMultiplier_contDiff m j)

theorem stationaryJet_value [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Space (m+3)) :
    (S.stationaryJet m j).value B x e = maskedStationaryCoefficient m j (S.value B x) e := by
  rw [maskedStationaryCoefficient_safe]
  rw [stationaryJet,mulFixed_value,pullback_value,iteratedLaplacian_value _ _ _ _ hB]
  rw [iteratedDirectionalLaplacian_vertical]
  · simp only [mulFixed_value,pullback_value,quadraticJetCoefficient,
      SmoothSeparation.stationaryJetMultiplier,SmoothSeparation.stationaryJointDensity]
    ring
  · exact value_contDiff _ B hB x

theorem HasOrder.stationaryJet [DecidableEq ι] {m j K : ℕ}
    {S : MaskJetExpansion ι d (Space (m+3))} (h : S.HasOrder K) :
    (S.stationaryJet m j).HasOrder (K+2*j) := by
  unfold MaskJetExpansion.stationaryJet
  exact (((h.pullback _ (safeStationaryChart_contDiff m)).mulFixed _
    (SmoothSeparation.stationaryJointDensity_contDiff m)).iteratedLaplacian _ j).pullback _
      (contDiff_id.prodMk contDiff_const) |>.mulFixed _
        (SmoothSeparation.stationaryJetMultiplier_contDiff m j)

noncomputable def inverse [DecidableEq ι] (m : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) : ℕ → MaskJetExpansion ι d (Space (m+3))
  | 0 => S.mulFixed (fun e => (sphereStationaryConstant (m+2))⁻¹*(stationaryPatchMask m e : ℂ))
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m)))
  | j+1 => (sum (fun h : Fin (j+1) => (inverse m S (j-h)).stationaryJet m (h+1))).mulFixed
      (fun _ => -(sphereStationaryConstant (m+2))⁻¹) contDiff_const
termination_by j => j
decreasing_by omega

theorem inverse_value [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Space (m+3)) :
    (S.inverse m j).value B x e = localInverseAmplitude m (S.value B x) j e := by
  induction j using Nat.strong_induction_on generalizing e with
  | h j ih =>
    cases j with
    | zero => rw [inverse,mulFixed_value,localInverseAmplitude]
    | succ j =>
      rw [inverse,mulFixed_value,sum_value,localInverseAmplitude]
      congr 1
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro h _
      rw [stationaryJet_value _ _ _ _ hB]
      have he : (S.inverse m (j-h)).value B x = localInverseAmplitude m (S.value B x) (j-h) := by
        funext z
        exact ih (j-h) (by have hh := h.isLt; omega) z
      rw [he]

theorem HasOrder.inverse [DecidableEq ι] {m K : ℕ}
    {S : MaskJetExpansion ι d (Space (m+3))} (h : S.HasOrder K) (j : ℕ) :
    (S.inverse m j).HasOrder (K+2*j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [MaskJetExpansion.inverse]
      exact h.mulFixed _ _
    | succ j =>
      rw [MaskJetExpansion.inverse]
      apply HasOrder.mulFixed
      apply sum_hasOrder
      intro k
      have hk := (ih (j-k) (by have hi := k.isLt; omega)).stationaryJet (j := (k:ℕ)+1)
      rwa [show K+2*(j-k)+2*((k:ℕ)+1) = K+2*(j+1) by have hi := k.isLt; omega] at hk

/-- Every individual mask jet in the expansion is evaluated at the same point. -/
def HasPointAt (S : MaskJetExpansion ι d E) (z : E) (p : Space d) : Prop :=
  ∀ a, (S.term a).point z = p

omit [Fintype ι] in
theorem product_hasPointAt (z : Space d) :
    (product : MaskJetExpansion ι d (Space d)).HasPointAt z z := fun _ => rfl

omit [Fintype ι] in
theorem HasPointAt.mulFixed {S : MaskJetExpansion ι d E} {z : E} {p : Space d}
    (h : S.HasPointAt z p) (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    (S.mulFixed c hc).HasPointAt z p := h

omit [Fintype ι] in
theorem HasPointAt.pullback {S : MaskJetExpansion ι d E} {g : H → E}
    {z : H} {p : Space d} (h : S.HasPointAt (g z) p) (hg : ContDiff ℝ ∞ g) :
    (S.pullback g hg).HasPointAt z p := h

omit [Fintype ι] in
theorem sum_hasPointAt {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E)
    {z : E} {p : Space d} (h : ∀ j, (S j).HasPointAt z p) :
    (sum S).HasPointAt z p := fun a => h a.1 a.2

theorem HasPointAt.derivative [DecidableEq ι] {S : MaskJetExpansion ι d E}
    {z : E} {p : Space d} (h : S.HasPointAt z p) (v : E) :
    (S.derivative v).HasPointAt z p := by
  intro a
  rcases a with ⟨a,b⟩
  rcases b with b | ⟨i,j⟩ <;> exact h a

theorem HasPointAt.laplacian [DecidableEq ι] {n : ℕ}
    {S : MaskJetExpansion ι d E} {z : E} {p : Space d}
    (h : S.HasPointAt z p) (v : Fin n → E) : (S.laplacian v).HasPointAt z p :=
  sum_hasPointAt _ (fun j => (h.derivative (v j)).derivative (v j))

theorem HasPointAt.iteratedLaplacian [DecidableEq ι] {n : ℕ}
    {S : MaskJetExpansion ι d E} {z : E} {p : Space d}
    (h : S.HasPointAt z p) (v : Fin n → E) (j : ℕ) :
    (S.iteratedLaplacian v j).HasPointAt z p := by
  induction j with
  | zero => exact h
  | succ j ih =>
    simpa only [MaskJetExpansion.iteratedLaplacian,Function.iterate_succ_apply'] using
      ih.laplacian v

theorem HasPointAt.stationaryJet [DecidableEq ι] {m j : ℕ}
    {S : MaskJetExpansion ι d (Space (m+3))} {p : Space d}
    {e : Sphere (m+3)} (h : S.HasPointAt e p)
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2) :
    (S.stationaryJet m j).HasPointAt e p := by
  have hchart : S.HasPointAt (safeStationaryChart m (e,0)) p := by
    simpa only [safeStationaryChart_zero m e he] using h
  unfold MaskJetExpansion.stationaryJet
  have hT := (hchart.pullback (g := safeStationaryChart m) (z := (e,0))
    (safeStationaryChart_contDiff m)).mulFixed
      (SmoothSeparation.stationaryJointDensity m)
      (SmoothSeparation.stationaryJointDensity_contDiff m)
  have hU := (hT.iteratedLaplacian (verticalDirections (m+2)) j).pullback
    (g := fun z : Space (m+3) => (z,(0 : Space (m+2)))) (z := (e : Space (m+3)))
    (contDiff_id.prodMk contDiff_const)
  exact hU.mulFixed (SmoothSeparation.stationaryJetMultiplier m j)
    (SmoothSeparation.stationaryJetMultiplier_contDiff m j)

theorem HasPointAt.inverse [DecidableEq ι] {m : ℕ}
    {S : MaskJetExpansion ι d (Space (m+3))} {p : Space d} {e : Sphere (m+3)}
    (h : S.HasPointAt e p)
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2)
    (j : ℕ) : (S.inverse m j).HasPointAt e p := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [MaskJetExpansion.inverse]
      exact h.mulFixed _ _
    | succ j =>
      rw [MaskJetExpansion.inverse]
      apply HasPointAt.mulFixed
      apply sum_hasPointAt
      intro k
      exact (ih (j-k) (by have hk := k.isLt; omega)).stationaryJet he

/-- The actual inverse coefficient has a finite expansion into individual mask
jets, with at most `2*j` derivatives in total. On the fixed patch all those
jets are evaluated at the original sphere point. -/
theorem localInverseAmplitude_product_jets [DecidableEq ι] (m j : ℕ) :
    ∃ S : MaskJetExpansion ι (m+3) (Space (m+3)), S.HasOrder (2*j) ∧
      (∀ (B : ι → X → Space (m+3) → ℂ),
        (∀ i x, ContDiff ℝ ∞ (B i x)) → ∀ x e,
        S.value B x e = localInverseAmplitude m (fun z => ∏ i, B i x z) j e) ∧
      (∀ e : Sphere (m+3),
        ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 →
        S.HasPointAt e e) := by
  refine ⟨product.inverse m j, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add] using (product_hasOrder (ι := ι) (d := m+3)).inverse j
  · intro B hB x e
    rw [inverse_value _ _ _ _ hB]
    have hp : (product : MaskJetExpansion ι (m+3) (Space (m+3))).value B x =
        fun z => ∏ i, B i x z := funext (product_value B x)
    rw [hp]
  · intro e he
    exact (product_hasPointAt (ι := ι) (e : Space (m+3))).inverse he j

end MaskJetExpansion
end Falconer

end OAI
