import OAI.Combinatorics.BooleanFunctions.Grouping

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Amplification
open Observations Switching GaussianGain MomentTransfer
attribute [local instance] Classical.propDecidable

structure Observation where
  Coord : Type
  [coordFintype : Fintype Coord]
  [coordDecidableEq : DecidableEq Coord]
  Label : Type
  [labelFintype : Fintype Label]
  map : Cube Coord → Label
  cost : ℕ
  cost_pos : 0 < cost
  cell_le : ∀ b, fourierDegree (cell map b) ≤ cost
  variance_pos : 0 < variance map

attribute [instance] Observation.coordFintype Observation.coordDecidableEq Observation.labelFintype

def ratio (F : Observation) : ℝ := variance F.map/F.cost

def costFactor : ℕ := 2*gridN+2

def factor : ℝ := 1+eta/costFactor

theorem costFactor_eq : Fintype.card Leaves+1 = costFactor := by
  simp only [Leaves,Fintype.card_fin,costFactor]

theorem costFactor_pos : 0 < costFactor := by
  unfold costFactor
  omega

theorem factor_gt_one : 1 < factor := by
  unfold factor
  have : 0 < eta/(costFactor:ℝ) := div_pos eta_pos (Nat.cast_pos.mpr costFactor_pos)
  linarith

theorem ratio_improvement {q n D : ℕ} (hq : 0 < q) (hn : 0 < n) (hD : 0 < D)
    {v v' η : ℝ} (hv : (n:ℝ)*v*((q:ℝ)+η) < v') :
    (1+η/q)*(v/D) < v'/(q*(n*D):ℕ) := by
  rw [lt_div_iff₀ (Nat.cast_pos.mpr (Nat.mul_pos hq (Nat.mul_pos hn hD)))]
  calc (1+η/q)*(v/D)*(q*(n*D):ℕ) = (n:ℝ)*v*((q:ℝ)+η) := by
        have hD' : (D:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
        have hq' : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
        simp only [Nat.cast_mul]
        field_simp
    _ < _ := hv

theorem exists_step (F : Observation) : ∃ G : Observation, factor*ratio F < ratio G := by
  obtain ⟨n,hn,S,L,hv⟩ := exists_amplification F.map F.variance_pos
  have he : (Fintype.card Leaves:ℝ)+1 = (costFactor:ℝ) := by
    rw [← costFactor_eq,Nat.cast_add,Nat.cast_one]
  rw [he] at hv
  let G : Observation := {
    Coord := Slots Leaves × (Fin n × F.Coord)
    Label := EventSpace (Fin n → F.Label) Leaves ⊕ (Fin n → F.Label)
    map := switched (grouped (κ := Fin n) F.map) S L
    cost := costFactor*(n*F.cost)
    cost_pos := Nat.mul_pos costFactor_pos (Nat.mul_pos hn F.cost_pos)
    cell_le := fun b => by
      rw [← costFactor_eq]
      exact switched_degree _ _ _ _
        (fun a => by simpa only [Fintype.card_fin] using grouped_degree F.map F.cost F.cell_le a) b
    variance_pos := lt_trans (mul_pos (mul_pos (Nat.cast_pos.mpr hn) F.variance_pos)
      (add_pos (Nat.cast_pos.mpr costFactor_pos) eta_pos)) hv }
  refine ⟨G,?_⟩
  exact ratio_improvement costFactor_pos hn F.cost_pos hv

theorem identity_variance : variance (id : Cube (Fin 1) → Cube (Fin 1)) = 1 := by
  have hs : score (id : Cube (Fin 1) → Cube (Fin 1)) = cubeSum :=
    Projection.conditional_comp id cubeSum
  unfold Observations.variance
  rw [hs]
  simp only [cubeSum,Fin.sum_univ_one,sign_sq]
  exact average_const 1

def base : Observation where
  Coord := Fin 1
  Label := Cube (Fin 1)
  map := id
  cost := 1
  cost_pos := Nat.zero_lt_one
  cell_le := fun b => by
    have hd : fourierDegree (cell id b) ≤ (Finset.univ : Finset (Fin 1)).card := by
      apply fourierDegree_le_card_of_dependsOn
      intro x y h
      have he : x = y := funext fun i => h i (Finset.mem_univ i)
      rw [he]
    simpa using hd
  variance_pos := by rw [identity_variance]; exact zero_lt_one

theorem base_ratio : ratio base = 1 := by
  unfold ratio base
  rw [identity_variance]
  norm_num

theorem exists_iterate (k : ℕ) : ∃ F : Observation, factor^k ≤ ratio F := by
  induction k with
  | zero => exact ⟨base,by simp [base_ratio]⟩
  | succ k ih =>
    obtain ⟨F,hF⟩ := ih
    obtain ⟨G,hG⟩ := exists_step F
    refine ⟨G,?_⟩
    calc factor^(k+1) = factor*factor^k := pow_succ' factor k
      _ ≤ factor*ratio F := mul_le_mul_of_nonneg_left hF (le_trans zero_le_one factor_gt_one.le)
      _ ≤ ratio G := hG.le

theorem exists_large_ratio (R : ℝ) : ∃ F : Observation, R < ratio F := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt R factor_gt_one
  obtain ⟨F,hF⟩ := exists_iterate k
  exact ⟨F,hk.trans_le hF⟩

end Amplification
end SquareRootDegree

end

end OAI
