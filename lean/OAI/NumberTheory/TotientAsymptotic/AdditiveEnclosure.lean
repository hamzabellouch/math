import OAI.NumberTheory.TotientAsymptotic.JoinedSimplex
import OAI.NumberTheory.TotientAsymptotic.PerturbationCost
import OAI.NumberTheory.TotientAsymptotic.CubeBoundary

namespace OAI

/-! Banded perturbed witness regions and their unit boxes have an additive
full-dimensional enclosure with explicit coordinate errors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def boxSlackError (x : ℝ) (k : ℕ) : ℝ :=
  (xi x k-1)*((11/10 : ℝ)*bandScale x k)+4*((m x-k : ℕ) : ℝ)^2

def boxTopError (x : ℝ) : ℝ := topPerturbation x+4*(m x : ℝ)^2

lemma boxSlackError_nonneg (x : ℝ) (k : ℕ) : 0 ≤ boxSlackError x k := by
  exact add_nonneg (mul_nonneg (xi_sub_one_pos _ _).le
    (mul_nonneg (by norm_num) (bandScale_nonneg _ _))) (by positivity)

lemma boxTopError_nonneg {x : ℝ} (hB : 0 ≤ B x) : 0 ≤ boxTopError x :=
  add_nonneg (topPerturbation_nonneg hB) (by positivity)

lemma join_witness_perturbed_enlarged {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hη : IsWitness H (theta x) η) (hPH : P H < H) (hHm : H ≤ m x)
    {u : Fin (R x H) → ℝ} (hu : u ∈ perturbedTailPrefixRegion x H η)
    (hb : u ∈ prefixBandRegion x H) :
    joinCoordinates (R x H) (H-P H) (u,tailVector η) ∈
      enlargedSimplex (R x H+(H-P H)) (B x) (xi x 0) (fun i => xi x (i.val+1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [joinCoordinates_left] using
        (mul_nonneg (by norm_num) (bandScale_nonneg _ _)).trans (hb j).1
    · simpa only [joinCoordinates_right] using tailVector_nonneg hη j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.val_castAdd]
      rw [joined_prefix_row, joinCoordinates_left, ← prefix_D_tailVector η hPH.le hHm j]
      have hh := hu.1 j
      rw [prefixLinear_apply] at hh
      change D (m x-(j.val+1)) η ≤ u j-_+(xi x (j.val+1)-1)*u j at hh
      linarith
    · simp only [Fin.val_natAdd]
      rw [joined_tail_row, joinCoordinates_right]
      have hj := j.isLt
      have he : m x-(R x H+j.val+1) = H-1-j.val := by unfold R; omega
      simpa only [xi, he] using tailVector_simplex hη j
  · rw [joined_budget, ← top_D_tailVector η hPH.le hHm]
    have hh := hu.2
    change (∑ j, a (j.val+1)*u j) ≤ xi x 0*B x-D (m x) η at hh
    linarith

lemma join_witness_band_upper {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hη : IsWitness H (theta x) η) (hPH : P H ≤ H) (hHm : H ≤ m x)
    {u : Fin (R x H) → ℝ} (hb : u ∈ prefixBandRegion x H) :
    ∀ i, joinCoordinates (R x H) (H-P H) (u,tailVector η) i ≤
      (11/10 : ℝ)*bandScale x (i.val+1) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [joinCoordinates_left, Fin.val_castAdd] using (hb j).2
  · simp only [joinCoordinates_right, Fin.val_natAdd]
    have hj := j.isLt
    have he : m x-(R x H+j.val+1) = H-1-j.val := by unfold R; omega
    have hm : H-1-j.val ∈ Finset.Ico (P H) H := Finset.mem_Ico.mpr (by omega)
    simpa only [tailVector, bandScale, he, mul_assoc] using (hη.2.2.1 _ hm).2.2.1

lemma banded_simplex_cube_additive {x : ℝ} {N : ℕ} (hN : N < m x)
    {u v : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hb : ∀ i, u i ≤ (11/10 : ℝ)*bandScale x (i.val+1))
    (hdist : ∀ i, |u i-v i| ≤ 1) :
    v ∈ prefixRegion N (B x+boxTopError x) 0 (fun i => -boxSlackError x (i.val+1)) := by
  constructor
  · intro i
    have hs := hu.2.1 i
    have hd := (le_abs_self _).trans (prefixLinear_cube_error u v hdist i)
    have hp := mul_le_mul_of_nonneg_left (hb i) (xi_sub_one_pos x (i.val+1)).le
    have hi := i.isLt
    have hh : ((N-i.val : ℕ) : ℝ)^2 ≤ 4*((m x-(i.val+1) : ℕ) : ℝ)^2 := by
      have ht' : ((N-i.val : ℕ) : ℝ) ≤ (m x-(i.val+1) : ℕ) := by exact_mod_cast (show N-i.val ≤ m x-(i.val+1) by omega)
      have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (N-i.val) (α := ℝ)) ht' 2
      nlinarith [sq_nonneg (((m x-(i.val+1) : ℕ) : ℝ))]
    simp only [prefixLinear_apply] at hd ⊢
    dsimp [boxSlackError]
    nlinarith
  · have hd := (neg_le_abs _).trans (prefixBudget_cube_error u v hdist)
    have hs : (N : ℝ)^2 ≤ (m x : ℝ)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hN.le) 2
    dsimp [boxTopError, topPerturbation]
    have hb := hu.2.2
    linarith [sq_nonneg (m x : ℝ)]

end TotientAsymptotic

end

end OAI
