import OAI.Analysis.TracialSplitting.Model
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

namespace OAI

/-! Bounded operator families have weak operator ultralimits. The construction
uses bounded scalar ultralimits and the Hilbert-space representation of each
limiting linear functional. This is the compactness step for extending finite
matrix cpc maps to Hilbert-space operator targets. -/

noncomputable section
open Filter Topology
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def ultraOperatorForm (U : Ultrafilter ι) (T : ι → H →L[ℂ] H) (x y : H) : ℂ :=
  limUnder (U : Filter ι) (fun i => inner ℂ (T i x) y)

omit [CompleteSpace H] in
private lemma ultraOperatorForm_tendsto (U : Ultrafilter ι) (T : ι → H →L[ℂ] H)
    {C : ℝ} (hT : ∀ i, ‖T i‖ ≤ C) (x y : H) :
    Tendsto (fun i => inner ℂ (T i x) y) (U : Filter ι)
      (𝓝 (ultraOperatorForm U T x y)) := by
  apply CurrentMain.bounded_ultrafilter_tendsto U _ (C * ‖x‖ * ‖y‖)
  intro i
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    ((T i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x)))
    (norm_nonneg y))

omit [CompleteSpace H] in
private lemma ultraOperatorForm_bound (U : Ultrafilter ι) (T : ι → H →L[ℂ] H)
    {C : ℝ} (hT : ∀ i, ‖T i‖ ≤ C) (x y : H) :
    ‖ultraOperatorForm U T x y‖ ≤ (C * ‖x‖) * ‖y‖ := by
  apply le_of_tendsto (ultraOperatorForm_tendsto U T hT x y).norm
  exact Eventually.of_forall fun i => (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right ((T i).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x))) (norm_nonneg y))

private def ultraOperatorFunctional (U : Ultrafilter ι) (T : ι → H →L[ℂ] H)
    {C : ℝ} (hT : ∀ i, ‖T i‖ ≤ C) (x : H) : H →L[ℂ] ℂ :=
  ({ toFun := ultraOperatorForm U T x
     map_add' := by
       intro y z
       apply tendsto_nhds_unique (ultraOperatorForm_tendsto U T hT x (y + z))
       simpa only [inner_add_right] using
         (ultraOperatorForm_tendsto U T hT x y).add (ultraOperatorForm_tendsto U T hT x z)
     map_smul' := by
       intro c y
       apply tendsto_nhds_unique (ultraOperatorForm_tendsto U T hT x (c • y))
       simpa only [inner_smul_right, RingHom.id_apply, smul_eq_mul] using
         (ultraOperatorForm_tendsto U T hT x y).const_mul c } : H →ₗ[ℂ] ℂ).mkContinuous
    (C * ‖x‖) (ultraOperatorForm_bound U T hT x)

omit [CompleteSpace H] in
private lemma ultraOperatorForm_add_left (U : Ultrafilter ι) (T : ι → H →L[ℂ] H)
    {C : ℝ} (hT : ∀ i, ‖T i‖ ≤ C) (x z y : H) :
    ultraOperatorForm U T (x + z) y = ultraOperatorForm U T x y + ultraOperatorForm U T z y := by
  apply tendsto_nhds_unique (ultraOperatorForm_tendsto U T hT (x + z) y)
  simpa only [map_add, inner_add_left] using
    (ultraOperatorForm_tendsto U T hT x y).add (ultraOperatorForm_tendsto U T hT z y)

omit [CompleteSpace H] in
private lemma ultraOperatorForm_smul_left (U : Ultrafilter ι) (T : ι → H →L[ℂ] H)
    {C : ℝ} (hT : ∀ i, ‖T i‖ ≤ C) (c : ℂ) (x y : H) :
    ultraOperatorForm U T (c • x) y = star c * ultraOperatorForm U T x y := by
  apply tendsto_nhds_unique (ultraOperatorForm_tendsto U T hT (c • x) y)
  simpa only [map_smul, inner_smul_left, RingHom.id_apply, starRingEnd_apply] using
    (ultraOperatorForm_tendsto U T hT x y).const_mul (star c)

private def operatorUltraLinear (U : Ultrafilter ι) (T : ι → H →L[ℂ] H)
    {C : ℝ} (hT : ∀ i, ‖T i‖ ≤ C) : H →ₗ[ℂ] H where
  toFun x := (InnerProductSpace.toDual ℂ H).symm (ultraOperatorFunctional U T hT x)
  map_add' x z := by
    apply ext_inner_right ℂ
    intro y
    simp only [InnerProductSpace.toDual_symm_apply, inner_add_left]
    exact ultraOperatorForm_add_left U T hT x z y
  map_smul' c x := by
    apply ext_inner_right ℂ
    intro y
    simp only [InnerProductSpace.toDual_symm_apply, inner_smul_left, RingHom.id_apply]
    exact ultraOperatorForm_smul_left U T hT c x y

def operatorUltraLimit (U : Ultrafilter ι) (T : ι → H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) : H →L[ℂ] H :=
  (operatorUltraLinear U T hT).mkContinuous C (fun x => by
    change ‖(InnerProductSpace.toDual ℂ H).symm (ultraOperatorFunctional U T hT x)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (mul_nonneg hC (norm_nonneg x)) _)

lemma operatorUltraLimit_inner (U : Ultrafilter ι) (T : ι → H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) (x y : H) :
    inner ℂ (operatorUltraLimit U T hC hT x) y = ultraOperatorForm U T x y := by
  exact InnerProductSpace.toDual_symm_apply

lemma operatorUltraLimit_norm_le (U : Ultrafilter ι) (T : ι → H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) :
    ‖operatorUltraLimit U T hC hT‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

lemma operatorUltraLimit_inner_tendsto (U : Ultrafilter ι) (T : ι → H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) (x y : H) :
    Tendsto (fun i => inner ℂ (T i x) y) (U : Filter ι)
      (𝓝 (inner ℂ (operatorUltraLimit U T hC hT x) y)) := by
  rw [operatorUltraLimit_inner]
  exact ultraOperatorForm_tendsto U T hT x y

end WeakPureInfiniteness

end

end OAI
