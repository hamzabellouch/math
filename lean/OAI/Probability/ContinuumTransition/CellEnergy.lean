import OAI.Probability.ContinuumTransition.ShellGeometry

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

def pairSum {ι : Type u_1} [Fintype ι] [LinearOrder ι] (f : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j

theorem two_mul_pairSum {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hsym : ∀ i j, f i j = f j i) :
    2 * pairSum f = ∑ i, ∑ j, if i = j then 0 else f i j := by
  classical
  have hsplit (i j : ι) : (if i = j then 0 else f i j) =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, hsym i j]
  simp_rw [hsplit]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : ι => if j < i then f j i else 0)]
  simp only [pairSum, Finset.sum_filter]
  ring

theorem sum_adjacency_indicator {ι : Type u_1} [Fintype ι] (G : SimpleGraph ι) :
    letI := Classical.decRel G.Adj
    (∑ i, ∑ j, if G.Adj i j then (1 : ℝ) else 0) = 2 * (G.edgeFinset.card : ℝ) := by
  classical
  have h := congrArg (fun n : ℕ => (n : ℝ)) G.two_mul_card_edgeFinset
  rw [Finset.card_filter] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_ite] at h
  rw [Fintype.sum_prod_type] at h
  simpa only [Nat.cast_one, Nat.cast_zero] using h.symm

theorem core_one_cell_bound {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (v : ι → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (hdiam : ∀ i j, ‖v i - v j‖ < 1) :
    t ^ 2 / 8 * (Fintype.card ι : ℝ) ^ 2 - t ^ 2 / 2 * Fintype.card ι ≤
      pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
  classical
  let G := shellGraph v (Real.exp (-t))
  have hpoint (i j : ι) :
      t ^ 2 * (1 - (if G.Adj i j then 1 else 0) - (if i = j then 1 else 0)) ≤
        if i = j then 0 else coreProfile t ‖v i - v j‖ := by
    by_cases hij : i = j
    · subst j
      simp
    · simp only [ite_eq_right hij, sub_zero]
      by_cases hadj : G.Adj i j
      · simp only [ite_eq_left hadj, sub_self, mul_zero]
        exact coreProfile_nonneg _ _
      · simp only [ite_eq_right hadj, sub_zero, mul_one]
        apply coreProfile_ge_of_not_shell _ _ (hdiam i j)
        intro hshell
        exact hadj ⟨hij, hshell⟩
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpoint i j))
  have horient := two_mul_pairSum (fun i j => coreProfile t ‖v i - v j‖)
    (fun i j => by rw [norm_sub_rev])
  have hadj := sum_adjacency_indicator G
  have hdiag : (∑ i : ι, ∑ j : ι, if i = j then (1 : ℝ) else 0) = Fintype.card ι := by simp
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at htotal
  rw [hadj, hdiag, ← horient] at htotal
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htotal
  have hedge := shellGraph_edge_bound v (Real.exp_pos (-t))
  have hedger : 8 * (G.edgeFinset.card : ℝ) ≤ 3 * (Fintype.card ι : ℝ) ^ 2 := by exact_mod_cast hedge
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hedger)]

theorem row_sum_quadratic_bound {ι : Type u_1} [Fintype ι]
    (J : ι → ι → ℝ) (n : ι → ℝ) (M : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    ∑ i, ∑ j, J i j * n i * n j ≤ M * ∑ i, n i ^ 2 := by
  have hYoung (i j : ι) : 2 * (J i j * n i * n j) ≤
      J i j * n i ^ 2 + J i j * n j ^ 2 := by
    nlinarith [mul_nonneg (hJ i j) (sq_nonneg (n i - n j))]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hYoung i j))
  simp_rw [Finset.sum_add_distrib] at hs
  simp only [← Finset.mul_sum] at hs
  have hswap : (∑ i, ∑ j, J i j * n j ^ 2) = ∑ i, ∑ j, J i j * n i ^ 2 := by
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    rw [hsym j i]
  rw [hswap] at hs
  have hr : (∑ i, ∑ j, J i j * n i ^ 2) ≤ M * ∑ i, n i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  linarith

theorem superstable_algebra {ι : Type u_1} [Fintype ι]
    (J : ι → ι → ℝ) (n : ι → ℝ) (M t N Ucore Uattr : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M)
    (hcore : t ^ 2 / 8 * (∑ i, n i ^ 2) - t ^ 2 / 2 * N ≤ Ucore)
    (hattr : Uattr ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, J i j * n i * n j) :
    (t ^ 2 / 8 - M / 2) * (∑ i, n i ^ 2) - t ^ 2 / 2 * N ≤ Ucore - Uattr := by
  have hq := row_sum_quadratic_bound J n M hJ hsym hrow
  nlinarith

theorem sum_subtype_le_of_nonneg {ι : Type u_1} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i : {i // p i}, f i ≤ ∑ i, f i := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hp : 0 ≤ ∑ i : {i // ¬ p i}, f i := Finset.sum_nonneg (fun i _ => hf i)
  linarith

theorem core_partition_bound {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] (c : ι → κ) (v : ι → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (hdiam : ∀ i j, c i = c j → ‖v i - v j‖ < 1) :
    t ^ 2 / 8 * (∑ k, (Fintype.card {i // c i = k} : ℝ) ^ 2) -
      t ^ 2 / 2 * Fintype.card ι ≤ pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
  classical
  let f (i j : ι) : ℝ := if i = j then 0 else coreProfile t ‖v i - v j‖
  have hf (i j : ι) : 0 ≤ f i j := by
    dsimp [f]
    split_ifs
    · rfl
    · exact coreProfile_nonneg _ _
  let U (k : κ) : ℝ := pairSum (fun i j : {i // c i = k} => coreProfile t ‖v i - v j‖)
  have htwocell (k : κ) : 2 * U k = ∑ i : {i // c i = k}, ∑ j : {j // c j = k}, f i j := by
    dsimp [U]
    rw [two_mul_pairSum _ (fun i j => by rw [norm_sub_rev])]
    simp only [f, Subtype.ext_iff]
  have htwototal : 2 * pairSum (fun i j => coreProfile t ‖v i - v j‖) = ∑ i, ∑ j, f i j :=
    two_mul_pairSum _ (fun i j => by rw [norm_sub_rev])
  have hu : 2 * (∑ k, U k) ≤ 2 * pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
    rw [Finset.mul_sum, htwototal]
    simp_rw [htwocell]
    calc
      _ ≤ ∑ k : κ, ∑ i : {i // c i = k}, ∑ j : ι, f i j := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro i _
        exact sum_subtype_le_of_nonneg (fun j => c j = k) (f i) (hf i)
      _ = _ := Fintype.sum_fiberwise c (fun i => ∑ j, f i j)
  have hs (k : κ) : t ^ 2 / 8 * (Fintype.card {i // c i = k} : ℝ) ^ 2 -
      t ^ 2 / 2 * Fintype.card {i // c i = k} ≤ U k := by
    apply core_one_cell_bound
    intro i j
    exact hdiam i j (i.property.trans j.property.symm)
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset κ)) => hs k)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hcard : (∑ k, (Fintype.card {i // c i = k} : ℝ)) = Fintype.card ι := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      Fintype.sum_fiberwise c (fun _ => (1 : ℝ))
  rw [hcard] at hsum
  linarith

end
end ContinuumTemperature
end

end OAI
