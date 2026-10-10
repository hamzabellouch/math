import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Multiplier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
namespace CoulombAtom

lemma graph_value_components_ext {N : ℕ} {F G : fermionGraph N}
    (h : ∀ s, graphComponent s none F = graphComponent s none G) : F = G := by
  apply fermionGraphValue_injective N
  apply Subtype.ext
  apply PiLp.ext
  intro s
  exact h s

lemma complex_square_partition (p q : ℝ) (h : p ^ 2 + q ^ 2 = 1) (z : ℂ) :
    (p : ℂ) * ((p : ℂ) * z) + (q : ℂ) * ((q : ℂ) * z) = z := by
  calc
    _ = ((p ^ 2 + q ^ 2 : ℝ) : ℂ) * z := by push_cast; ring
    _ = z := by rw [h]; simp

attribute [local irreducible] FermionMultiplier.apply graphComponent
  fermionGraphValue coulombFormOperator graphFormVector formEnergy

lemma FermionMultiplier.partition_apply {N : ℕ} (p q : FermionMultiplier N)
    (h : ∀ x, p.value x ^ 2 + q.value x ^ 2 = 1) (F : fermionGraph N) :
    p.apply (p.apply F) + q.apply (q.apply F) = F := by
  apply graph_value_components_ext
  intro s
  rw [map_add]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (graphComponent s none (p.apply (p.apply F)))
      (graphComponent s none (q.apply (q.apply F))),
    p.apply_value (p.apply F) s, p.apply_value F s,
    q.apply_value (q.apply F) s, q.apply_value F s] with x ha hb hc hd he
  exact ha.trans ((congrArg₂ (fun a b : ℂ => a + b)
    (hb.trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hc))
    (hd.trans (congrArg (fun z : ℂ => (q.value x : ℂ) * z) he))).trans
      (complex_square_partition (p.value x) (q.value x) (h x) _))

lemma FermionMultiplier.partition_mass {N : ℕ} (p q : FermionMultiplier N)
    (h : ∀ x, p.value x ^ 2 + q.value x ^ 2 = 1) (F : fermionGraph N) :
    ‖fermionGraphValue N (p.apply F)‖ ^ 2 +
      ‖fermionGraphValue N (q.apply F)‖ ^ 2 = ‖fermionGraphValue N F‖ ^ 2 := by
  have he := congrArg (fermionGraphValue N) (p.partition_apply q h F)
  have hi := congrArg (fun U => (⟪U, fermionGraphValue N F⟫_ℂ).re) he
  simp only [map_add, inner_add_left, Complex.add_re] at hi
  calc
    _ = _ := congrArg₂ (fun a b : ℝ => a + b)
      (p.value_pairing F).symm (q.value_pairing F).symm
    _ = _ := hi
    _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) (fermionGraphValue N F)).symm

def multiplierError {N : ℕ} (p : FermionMultiplier N) (F : fermionGraph N) : ℝ :=
  (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
    ∫ x, (lineDeriv ℝ p.value x (direction i a)) ^ 2 *
      ‖graphComponent s none F x‖ ^ 2)

lemma multiplierError_nonneg {N : ℕ} (p : FermionMultiplier N) (F : fermionGraph N) :
    0 ≤ multiplierError p F := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro s _
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro a _
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem quantum_partition_ims {N : ℕ} (Z : ℝ) (p q : FermionMultiplier N)
    (h : ∀ x, p.value x ^ 2 + q.value x ^ 2 = 1) (F : fermionGraph N) :
    formEnergy Z (graphFormVector (p.apply F)) +
      formEnergy Z (graphFormVector (q.apply F)) =
      formEnergy Z (graphFormVector F) + multiplierError p F + multiplierError q F := by
  have hp := p.form_ims Z F
  have hq := q.form_ims Z F
  have hi : (⟪p.apply (p.apply F), coulombFormOperator Z N F⟫_ℂ).re +
      (⟪q.apply (q.apply F), coulombFormOperator Z N F⟫_ℂ).re =
      formEnergy Z (graphFormVector F) := by
    rw [← Complex.add_re, ← inner_add_left, p.partition_apply q h F,
      coulombFormOperator_inner]
  change _ = multiplierError p F at hp
  change _ = multiplierError q F at hq
  linarith

lemma quantum_form_above_sector {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ} (F : fermionGraph N) :
    energy Z N * ‖fermionGraphValue N F‖ ^ 2 ≤ formEnergy Z (graphFormVector F) := by
  rw [← coulombFormOperator_inner]
  exact form_lower_of_unit (fermionGraphValue N) (fermionGraphValue_injective N)
    (coulombFormOperator Z N) (fun U hU => energy_le_graphForm hZ U hU) F

theorem quantum_partition_excess {Z b : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (hb : b ≤ energy Z N) (p q : FermionMultiplier N)
    (h : ∀ x, p.value x ^ 2 + q.value x ^ 2 = 1) (F : fermionGraph N) :
    formEnergy Z (graphFormVector (p.apply F)) -
      b * ‖fermionGraphValue N (p.apply F)‖ ^ 2 ≤
    formEnergy Z (graphFormVector F) - b * ‖fermionGraphValue N F‖ ^ 2 +
      multiplierError p F + multiplierError q F := by
  have hl := quantum_form_above_sector hZ (q.apply F)
  have hbq := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖fermionGraphValue N (q.apply F)‖)
  have hmass := p.partition_mass q h F
  have henergy := quantum_partition_ims Z p q h F
  have hm := congrArg (fun x : ℝ => b * x) hmass
  simp only [mul_add] at hm
  linarith

end CoulombAtom

open MeasureTheory Filter Set
open scoped Topology BigOperators

end

end OAI
