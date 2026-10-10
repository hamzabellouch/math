import OAI.Analysis.OperatorAlgebra.WeakOperatorUltralimit
import OAI.Analysis.OperatorAlgebra.FiniteHilbertCompression

namespace OAI

/-! A uniformly contractive family of cpc maps into Hilbert-space operators
has a cpc weak operator ultralimit. Complete positivity is checked on each
finite matrix and finite vector family, by passing the positive quadratic
forms to their scalar limits. -/

noncomputable section
open Filter Topology
open scoped InnerProductSpace CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {ι A H : Type*} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
private lemma cpcOperatorFamily_bound (F : ι → A →L[ℂ] (H →L[ℂ] H))
    (hF : ∀ i, ‖F i‖ ≤ 1) (a : A) (i : ι) : ‖F i a‖ ≤ ‖a‖ := by
  exact ((F i).le_opNorm a).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hF i) (norm_nonneg a))

private def cpOperatorUltraLinear (U : Ultrafilter ι) (F : ι → A →L[ℂ] (H →L[ℂ] H))
    (hF : ∀ i, ‖F i‖ ≤ 1) : A →ₗ[ℂ] (H →L[ℂ] H) where
  toFun a := operatorUltraLimit U (fun i => F i a) (norm_nonneg a) (cpcOperatorFamily_bound F hF a)
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    apply tendsto_nhds_unique (operatorUltraLimit_inner_tendsto U _
      (norm_nonneg (a + b)) (cpcOperatorFamily_bound F hF (a + b)) x y)
    simpa only [map_add, add_apply, inner_add_left] using
      (operatorUltraLimit_inner_tendsto U _ (norm_nonneg a) (cpcOperatorFamily_bound F hF a) x y).add
        (operatorUltraLimit_inner_tendsto U _ (norm_nonneg b) (cpcOperatorFamily_bound F hF b) x y)
  map_smul' c a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    apply tendsto_nhds_unique (operatorUltraLimit_inner_tendsto U _
      (norm_nonneg (c • a)) (cpcOperatorFamily_bound F hF (c • a)) x y)
    simpa only [map_smul, smul_apply, inner_smul_left,
      RingHom.id_apply, starRingEnd_apply] using
      (operatorUltraLimit_inner_tendsto U _ (norm_nonneg a)
        (cpcOperatorFamily_bound F hF a) x y).const_mul (star c)

def cpOperatorUltraLimit (U : Ultrafilter ι) (F : ι → A →L[ℂ] (H →L[ℂ] H))
    (hF : ∀ i, ‖F i‖ ≤ 1) : A →L[ℂ] (H →L[ℂ] H) :=
  (cpOperatorUltraLinear U F hF).mkContinuous 1 (fun a => by
    change ‖operatorUltraLimit U (fun i => F i a) (norm_nonneg a)
      (cpcOperatorFamily_bound F hF a)‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using operatorUltraLimit_norm_le U _
      (norm_nonneg a) (cpcOperatorFamily_bound F hF a))

omit [PartialOrder A] [StarOrderedRing A] in
lemma cpOperatorUltraLimit_norm_le (U : Ultrafilter ι) (F : ι → A →L[ℂ] (H →L[ℂ] H))
    (hF : ∀ i, ‖F i‖ ≤ 1) : ‖cpOperatorUltraLimit U F hF‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

omit [PartialOrder A] [StarOrderedRing A] in
lemma cpOperatorUltraLimit_inner_tendsto (U : Ultrafilter ι)
    (F : ι → A →L[ℂ] (H →L[ℂ] H)) (hF : ∀ i, ‖F i‖ ≤ 1) (a : A) (x y : H) :
    Tendsto (fun i => inner ℂ (F i a x) y) (U : Filter ι)
      (𝓝 (inner ℂ (cpOperatorUltraLimit U F hF a x) y)) :=
  operatorUltraLimit_inner_tendsto U _ (norm_nonneg a) (cpcOperatorFamily_bound F hF a) x y

omit [CompleteSpace H] in
private lemma matrixOperator_inner_formula {n : ℕ}
    (M : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : Fin n => H)) :
    inner ℂ (matrixOperator M x) x = ∑ j, ∑ k, inner ℂ (M j k (x k)) (x j) := by
  simp only [PiLp.inner_apply, matrixOperator_apply, sum_inner]

lemma cpOperatorUltraLimit_completelyPositive (U : Ultrafilter ι)
    (F : ι → A →L[ℂ] (H →L[ℂ] H)) (hF : ∀ i, ‖F i‖ ≤ 1)
    (hCP : ∀ i, CompletelyPositive (F i)) :
    CompletelyPositive (cpOperatorUltraLimit U F hF) := by
  intro n M hM
  let X := matrixLinearMap (cpOperatorUltraLimit U F hF) M
  apply (NonUnitalStarAlgHom.map_le_map_iff
    (matrixOperatorHom (n := Fin n) (H := H)) matrixOperator_injective).mp
  rw [map_zero]
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have ht : Tendsto (fun i => inner ℂ (matrixOperator (matrixLinearMap (F i) M) x) x)
      (U : Filter ι) (𝓝 (inner ℂ (matrixOperator X x) x)) := by
    simp only [matrixOperator_inner_formula, matrixLinearMap_apply, X]
    exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ =>
      cpOperatorUltraLimit_inner_tendsto U F hF (M j k) (x k) (x j)
  have hn : 0 ≤ inner ℂ (matrixOperator X x) x := by
    apply ge_of_tendsto' ht
    intro i
    exact
      (ContinuousLinearMap.nonneg_iff_isPositive.mp
        (map_nonneg (matrixOperatorHom (n := Fin n) (H := H)) (hCP i n M hM))).inner_nonneg_left x
  exact ⟨Complex.ext rfl hn.2, hn.1⟩

end WeakPureInfiniteness

end

end OAI
