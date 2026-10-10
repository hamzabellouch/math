import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphDescendants

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}
abbrev blockDepth (N B i : ℕ) : ℕ := N-i*B

structure RegularizedProfileData (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (N B : ℕ) (s lam : ℝ) (m : ℝ → ℝ) : Prop where
  probability : IsProbabilityMeasure ν
  continuous : Continuous m
  zero : m 0 = 0
  slope : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ N →
    0 ≤ m v-m u ∧ m v-m u ≤ d*(v-u)/(N:ℝ)
  affine : ∀ i < N/B+1, ∃ a b : ℝ, ∀ u : ℝ,
    (blockDepth N B (i+1):ℝ) ≤ u → u ≤ (blockDepth N B i:ℝ) → m u = a*u+b
  cells : ∀ n ≤ N, ∀ P : CellPath d, P.length = n → 0 < ν (treeCell P) →
    ((2:ℝ)^N)^(-(d+1:ℝ)*lam)*((2:ℝ)^N)^(-m n) ≤ (ν (treeCell P)).toReal ∧
    (ν (treeCell P)).toReal ≤ ((2:ℝ)^N)^((d+1:ℝ)*lam)*((2:ℝ)^N)^(-m n)
  envelope : ∀ n ≤ N, s*(n:ℝ)/(N:ℝ)-(d+3:ℝ)*lam ≤ m n ∧ m n ≤ d*(n:ℝ)/(N:ℝ)
  adjusted : ∀ u v : ℝ, 0 ≤ u → u ≤ N → 0 ≤ v → v ≤ N →
    |(m v-(d:ℝ)/2*v/(N:ℝ))-(m u-(d:ℝ)/2*u/(N:ℝ))| ≤ (d:ℝ)/2*|v-u|/(N:ℝ)
  packing : ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ x : EuclideanSpace ℝ (Fin d), ∀ C₀ : ℝ, 0 ≤ C₀ →
    ((occupiedCenterCells ν p x (C₀/(2:ℝ)^g)).card:ℝ) ≤
      (2*C₀+2*(d:ℝ)+7)^d*((2:ℝ)^N)^(m p-m g+2*(d+1:ℝ)*lam)

lemma RegularizedProfileData.profile_nonneg
    {ρ : Measure (EuclideanSpace ℝ (Fin d))} {N B : ℕ} {s sig : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData ρ N B s sig m) {n : ℕ} (hn : n ≤ N) : 0 ≤ m n := by
  have hh := (h.slope 0 n le_rfl (by positivity) (by exact_mod_cast hn)).1
  simpa only [h.zero,sub_zero] using hh

lemma RegularizedProfileData.profile_le_dim
    {ρ : Measure (EuclideanSpace ℝ (Fin d))} {N B : ℕ} {s sig : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData ρ N B s sig m) (hN : 0 < N) {n : ℕ} (hn : n ≤ N) : m n ≤ d := by
  apply (h.envelope n hn).2.trans
  rw [div_le_iff₀ (by positivity : (0:ℝ) < N)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (by positivity)

lemma RegularizedProfileData.graph_child_lower
    {ρ : Measure (EuclideanSpace ℝ (Fin d))} {N B : ℕ} {s sig : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData ρ N B s sig m) {a p : ℕ} (hp : p ≤ N)
    {X P : CellPath d} (hP : P ∈ graphChildren ρ a p X) :
    ((2:ℝ)^N)^(-m p-(d+1:ℝ)*sig) ≤ ρ.real (treeCell P) := by
  have hm := (h.cells p hp P (graphChildren_length hP) (Finset.mem_filter.mp hP).2).1
  rw [←Real.rpow_add (by positivity : (0:ℝ) < 2^N)] at hm
  convert hm using 1 <;> congr 1
  ring

lemma RegularizedProfileData.graph_parent_upper
    {ρ : Measure (EuclideanSpace ℝ (Fin d))} {N B : ℕ} {s sig : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData ρ N B s sig m) {a : ℕ} (ha : a ≤ N)
    {X : CellPath d} (hX : X ∈ dyadicPaths a) (hocc : 0 < ρ (treeCell X)) :
    ρ.real (treeCell X) ≤ ((2:ℝ)^N)^(-m a+(d+1:ℝ)*sig) := by
  have hm := (h.cells a ha X ((mem_dyadicPaths _ _).mp hX) hocc).2
  rw [←Real.rpow_add (by positivity : (0:ℝ) < 2^N)] at hm
  convert hm using 1 <;> congr 1
  ring
end CurrentFalconer.TreeND
end
end

end OAI
