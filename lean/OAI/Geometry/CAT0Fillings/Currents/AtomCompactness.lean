import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.FiniteAtoms
import OAI.Geometry.CAT0Fillings.Charts.Atoms

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
theorem exists_integer_configuration_subsequence {X : Type*} [MetricSpace X] [CompactSpace X]
    {N : ℕ} (a : ℕ → Fin N → ℤ) (x : ℕ → Fin N → X)
    (M : ℝ) (hM : ∀ j i, |(a j i : ℝ)| ≤ M) :
    ∃ (b : Fin N → ℤ) (y : Fin N → X) (ψ : ℕ → ℕ), StrictMono ψ ∧
      (∀ i, Tendsto (fun j => (a (ψ j) i : ℝ)) atTop (𝓝 ((b i : ℤ) : ℝ))) ∧
      (∀ i, Tendsto (fun j => x (ψ j) i) atTop (𝓝 (y i))) := by
  classical
  let K : Set ((Fin N → ℝ) × (Fin N → X)) :=
    {v | ∀ i, v i ∈ Icc (-M) M} ×ˢ univ
  have hK : IsCompact K := (isCompact_pi_infinite (fun _ : Fin N => isCompact_Icc)).prod isCompact_univ
  let seq j : (Fin N → ℝ) × (Fin N → X) := (fun i => (a j i : ℝ),x j)
  have hseq j : seq j ∈ K := ⟨fun i => abs_le.mp (hM j i),mem_univ _⟩
  obtain ⟨v,_,ψ,hψ,hlim⟩ := hK.isSeqCompact hseq
  have ha i : Tendsto (fun j => (a (ψ j) i : ℝ)) atTop (𝓝 (v.1 i)) :=
    (continuous_apply i).tendsto _ |>.comp (continuous_fst.tendsto _ |>.comp hlim)
  have hx i : Tendsto (fun j => x (ψ j) i) atTop (𝓝 (v.2 i)) :=
    (continuous_apply i).tendsto _ |>.comp (continuous_snd.tendsto _ |>.comp hlim)
  have hInt i : ∃ b : ℤ, (b : ℝ) = v.1 i :=
    Real.isClosed_range_intCast.mem_of_tendsto (ha i) (Eventually.of_forall fun j => ⟨a (ψ j) i,rfl⟩)
  choose b hb using hInt
  exact ⟨b,v.2,ψ,hψ,fun i => (hb i) ▸ ha i,hx⟩


open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

lemma integral_finite_atoms {N : ℕ} (a : Fin N → ℤ) (x : Fin N → X) :
    IsIntegral 0 (fun b π => ∑ i, atomCurrent (a i) (x i) b π) := by
  classical
  let U (j : ℕ) : Functional X 0 := if h : j < N then atomCurrent (a ⟨j,h⟩) (x ⟨j,h⟩) else 0
  have hUI j : IsIntegral 0 (U j) := by
    dsimp [U]
    split_ifs
    · exact atomCurrent_integral _ _
    · exact isIntegral_zero 0
  have hUS : Summable (fun j => mass (U j)) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro j hj
    have hj' : ¬ j < N := by simpa only [Finset.mem_range] using hj
    dsimp [U]
    rw [dite_eq_right hj']
    exact mass_zero 0
  have hEq : (fun b π => ∑ i, atomCurrent (a i) (x i) b π) = (fun b π => ∑' j, U j b π) := by
    funext b π
    rw [tsum_eq_sum (s := Finset.range N) (fun j hj => by
      dsimp [U]
      rw [dite_eq_right (show ¬j < N by simpa only [Finset.mem_range] using hj)]
      rfl),←Fin.sum_univ_eq_sum_range (fun j => U j b π) N]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [U]
    rw [ite_eq_left i.isLt]
  rw [hEq]
  exact ⟨isMetricCurrent_tsum (fun j => (hUI j).1) hUS,
    integerRectifiable_tsum (fun j => (hUI j).1) (fun j => (hUI j).2) hUS⟩

lemma integral_zero_uniform_representation {T : Functional X 0} (hT : IsIntegral 0 T)
    (M : ℝ) (hM : mass T ≤ M) :
    ∃ (a : Fin (Nat.ceil M) → ℤ) (x : Fin (Nat.ceil M) → X),
      (∀ i, |(a i : ℝ)| ≤ M) ∧
      ∀ b π, T b π = ∑ i, atomCurrent (a i) (x i) b π := by
  classical
  obtain ⟨m,a,x,hm,ha,heq⟩ := integerRectifiable_zero_finite_representation hT.1 hT.2
  have hmN : m ≤ Nat.ceil M := by exact_mod_cast (hm.trans hM).trans (Nat.le_ceil M)
  let p := padFinite hmN (fun i => (a i,x i)) (0,Classical.arbitrary X)
  refine ⟨fun i => (p i).1,fun i => (p i).2,?_,?_⟩
  · exact padFinite_property hmN (fun i => (a i,x i)) (0,Classical.arbitrary X)
      (fun z : ℤ × X => |(z.1 : ℝ)| ≤ M) (fun i => (ha i).trans hM)
      (by simpa only [Int.cast_zero,abs_zero] using (mass_nonneg T).trans hM)
  · intro b π
    rw [heq]
    exact (sum_padFinite hmN (fun i => (a i,x i)) (0,Classical.arbitrary X)
      (fun z : ℤ × X => atomCurrent z.1 z.2 b π)
      (by simp only [atomCurrent,Int.cast_zero,zero_mul,ite_self])).symm

theorem integral_zero_weak_closed {Ts : ℕ → Functional X 0} {T : Functional X 0}
    (hTs : ∀ j, IsIntegral 0 (Ts j)) (M : ℝ) (hM : ∀ j, mass (Ts j) ≤ M)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    IsIntegral 0 T := by
  classical
  choose a x ha heq using fun j => integral_zero_uniform_representation (hTs j) M (hM j)
  obtain ⟨c,y,ψ,hψ,hc,hy⟩ := exists_integer_configuration_subsequence a x M ha
  let S : Functional X 0 := fun b π => ∑ i, atomCurrent (c i) (y i) b π
  have hSLim b π : Tendsto (fun j => Ts (ψ j) b π) atTop (𝓝 (S b π)) := by
    simp_rw [heq]
    apply tendsto_finsetSum
    intro i _
    by_cases hab : Admissible b π
    · simp only [atomCurrent,ite_eq_left hab]
      exact (hc i).mul ((hab.1.1.choose_spec.continuous.tendsto (y i)).comp (hy i))
    · simp only [atomCurrent,ite_eq_right hab]
      exact tendsto_const_nhds
  have hTS : T = S := by
    funext b π
    exact tendsto_nhds_unique ((hlim b π).comp hψ.tendsto_atTop) (hSLim b π)
  rw [hTS]
  exact integral_finite_atoms c y

end CAT0Fillings
end

end OAI
