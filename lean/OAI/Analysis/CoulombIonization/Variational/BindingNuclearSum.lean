import Mathlib
import OAI.Analysis.CoulombIonization.Variational.WeightedMass

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue bindingTotalMultiplier
  bindingApprox bindingPairApprox

lemma bindingPairApprox_ite_integral_le {N : ℕ} (n : ℕ) (i j : Fin N)
    {f : Configuration N → ℂ} (hf : MemLp f 2)
    (hij : i ≠ j → Integrable (fun x => ‖f x‖ ^ 2 / ‖x i-x j‖)) :
    (if i ≠ j then (∫ x, bindingPairApprox n i j x * ‖f x‖ ^ 2) else 0) ≤
      (if i ≠ j then (∫ x, bindingApprox n (x i) * (‖f x‖ ^ 2 / ‖x i-x j‖)) else 0) +
      (if j ≠ i then (∫ x, bindingApprox n (x j) * (‖f x‖ ^ 2 / ‖x j-x i‖)) else 0) := by
  by_cases h : i ≠ j
  · simp only [ite_eq_left h, ite_eq_left h.symm]
    exact bindingPairApprox_integral_le_rev n i j hf (hij h)
  · obtain rfl := not_ne_iff.mp h
    simp only [ne_eq, not_true_eq_false, ite_false, add_zero, le_refl]

lemma graph_nuclear_integrable {N : ℕ} (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    Integrable (fun x => ‖graphComponent s none F x‖ ^ 2 / ‖x i‖) := by
  have h := graphFormVector_sobolev F
  simpa only [graphFormVector_value_eq] using nuclear_integrable i (h.1 s)
    (h.2.1 s i) (h.2.2.1 s i)

lemma graph_pair_integrable {N : ℕ} (F : fermionGraph N) (s : Spins N)
    (i j : Fin N) (hij : i ≠ j) :
    Integrable (fun x => ‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖) := by
  have h := graphFormVector_sobolev F
  simpa only [graphFormVector_value_eq] using pair_integrable i j hij (h.1 s)
    (h.2.1 s i) (h.2.2.1 s i)

def bindingNuclearSum {N : ℕ} (F : fermionGraph N) (n : ℕ) : ℝ :=
  ∑ i, weightedNuclear F i (fun x => bindingApprox n (x i))

def bindingPairSum {N : ℕ} (F : fermionGraph N) (n : ℕ) : ℝ :=
  ∑ i, weightedPairs F i (fun x => bindingApprox n (x i))

def bindingCappedSum {N : ℕ} (F : fermionGraph N) (n : ℕ) : ℝ :=
  ∑ s, ∑ i, ∑ j, if i ≠ j then
    (∫ x, bindingPairApprox n i j x * ‖graphComponent s none F x‖ ^ 2) else 0

lemma graph_mass_integral {N : ℕ} (F : fermionGraph N) :
    (∑ s, ∫ x, ‖graphComponent s none F x‖ ^ 2) = ‖fermionGraphValue N F‖ ^ 2 := by
  rw [graphValue_norm_sq]
  simp only [lp_norm_sq]

lemma bindingNuclearSum_tendsto {N : ℕ} (F : fermionGraph N) :
    Tendsto (bindingNuclearSum F) atTop (𝓝 ((N:ℝ)*‖fermionGraphValue N F‖ ^ 2)) := by
  have hs (i : Fin N) : Tendsto
      (fun n => ∑ s, ∫ x, bindingApprox n (x i) * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖))
      atTop (𝓝 (∑ s, ∫ x, ‖graphComponent s none F x‖ ^ 2)) :=
    tendsto_finsetSum _ (fun s _ => bindingApprox_nuclear_tendsto i (Lp.memLp _) (graph_nuclear_integrable F s i))
  have hh := tendsto_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) => hs i)
  unfold bindingNuclearSum weightedNuclear
  simpa only [graph_mass_integral,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh

lemma bindingCappedSum_tendsto {N : ℕ} (F : fermionGraph (N+1)) :
    Tendsto (bindingCappedSum F) atTop
      (𝓝 (((N+1:ℕ):ℝ)*(N:ℝ)*‖fermionGraphValue (N+1) F‖ ^ 2)) := by
  classical
  have hs (s : Spins (N+1)) (i j : Fin (N+1)) : Tendsto
      (fun n => if i ≠ j then (∫ x, bindingPairApprox n i j x * ‖graphComponent s none F x‖ ^ 2) else 0)
      atTop (𝓝 (if i ≠ j then (∫ x, ‖graphComponent s none F x‖ ^ 2) else 0)) := by
    by_cases hij : i ≠ j
    · simpa only [ite_eq_left hij] using bindingPairApprox_integral_tendsto i j hij (Lp.memLp (graphComponent s none F))
    · simpa only [ite_eq_right hij] using (tendsto_const_nhds (x := (0:ℝ)) (f := (atTop : Filter ℕ)))
  have hh := tendsto_finsetSum Finset.univ (fun s (_ : s ∈ Finset.univ) =>
    tendsto_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) =>
      tendsto_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) => hs s i j)))
  have he : (∑ s, ∑ i : Fin (N+1), ∑ j : Fin (N+1),
      if i ≠ j then (∫ x, ‖graphComponent s none F x‖ ^ 2) else 0) =
      ((N+1:ℕ):ℝ)*(N:ℝ)*‖fermionGraphValue (N+1) F‖ ^ 2 := by
    simp only [sum_excluding_const, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, graph_mass_integral]
    ring
  change Tendsto (bindingCappedSum F) atTop (𝓝 _) at hh
  rwa [he] at hh

lemma bindingCappedSum_le {N : ℕ} (F : fermionGraph N) (n : ℕ) :
    bindingCappedSum F n ≤ 2 * bindingPairSum F n := by
  classical
  let A (s : Spins N) (i j : Fin N) :=
    if i ≠ j then (∫ x, bindingApprox n (x i) * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖)) else 0
  let B (s : Spins N) (i j : Fin N) :=
    if i ≠ j then (∫ x, bindingPairApprox n i j x * ‖graphComponent s none F x‖ ^ 2) else 0
  have h (s : Spins N) (i j : Fin N) : B s i j ≤ A s i j + A s j i :=
    bindingPairApprox_ite_integral_le n i j (Lp.memLp (graphComponent s none F))
      (fun hij => graph_pair_integrable F s i j hij)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ => sum_pair_bound (A s) (B s) (h s))
  rw [← Finset.mul_sum] at hh
  have he : (∑ s, ∑ i, ∑ j, A s i j) = bindingPairSum F n := by
    unfold bindingPairSum weightedPairs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro j _
    dsimp only [A]
    split_ifs <;> simp
  rw [he] at hh
  exact hh

attribute [local irreducible] bindingNuclearSum bindingPairSum bindingCappedSum

lemma quantum_ground_binding_approx {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph (N+1)) (hn : ‖fermionGraphValue (N+1) F‖ ^ 2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z (N+1))
    (hstep : energy Z (N+1) ≤ energy Z N) (n : ℕ) :
    bindingCappedSum F n ≤ 2*Z*bindingNuclearSum F n := by
  have h := quantum_ground_binding_regularized hZ F hn hF hstep
    (R := (n:ℝ)+1) (ε := ((n:ℝ)+1)⁻¹) (by positivity) (by positivity)
  have hp : bindingPairSum F n ≤ Z*bindingNuclearSum F n := by
    unfold bindingPairSum bindingNuclearSum bindingApprox
    exact h
  have hc := bindingCappedSum_le F n
  linarith

theorem quantum_ground_particle_bound {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph (N+1)) (hn : ‖fermionGraphValue (N+1) F‖ ^ 2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z (N+1))
    (hstep : energy Z (N+1) ≤ energy Z N) : ((N+1:ℕ):ℝ) ≤ 2*Z+1 := by
  have hl := bindingCappedSum_tendsto F
  have hr := (bindingNuclearSum_tendsto F).const_mul (2*Z)
  have hh := le_of_tendsto_of_tendsto hl hr
    (Eventually.of_forall fun n => quantum_ground_binding_approx hZ F hn hF hstep n)
  simp only [hn, mul_one, Nat.cast_add, Nat.cast_one] at hh ⊢
  have hp : 0 < (N:ℝ)+1 := by positivity
  nlinarith

end CoulombAtom

end

end OAI
