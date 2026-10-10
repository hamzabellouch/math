import OAI.Probability.ContinuumTransition.ProfileBounds

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

open scoped InnerProductSpace

theorem affineIndependent_of_sq_dist_close {E : Type u_1} {ι : Type u_2}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (v : ι → E) {a ε : ℝ} (hε : 0 ≤ ε)
    (hgap : ε * Fintype.card ι < a)
    (hdist : ∀ i j, i ≠ j → |‖v i - v j‖ ^ 2 - a| ≤ ε) :
    AffineIndependent ℝ v := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv
  rw [Finset.univ.weightedVSub_eq_linear_combination hw] at hv
  have hid := inner_sum_smul_sum_smul_of_sum_eq_zero v hw v hw
  rw [hv, inner_zero_left] at hid
  have hzero : (∑ i, ∑ j, w i * w j * ‖v i - v j‖ ^ 2) = 0 := by
    simp only [← sq] at hid
    linarith
  have hpair (i j : ι) :
      w i * w j * ‖v i - v j‖ ^ 2 ≤
        a * w i * w j - (if i = j then a * w i ^ 2 else 0) +
          ε / 2 * (w i ^ 2 + w j ^ 2) := by
    by_cases hij : i = j
    · subst j
      simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, ↓reduceIte]
      nlinarith [mul_nonneg hε (sq_nonneg (w i))]
    · rw [ite_eq_right hij]
      have habs : w i * w j * (‖v i - v j‖ ^ 2 - a) ≤ |w i * w j| * ε := by
        calc
          _ ≤ |w i * w j * (‖v i - v j‖ ^ 2 - a)| := le_abs_self _
          _ = |w i * w j| * |‖v i - v j‖ ^ 2 - a| := abs_mul _ _
          _ ≤ |w i * w j| * ε := mul_le_mul_of_nonneg_left (hdist i j hij) (abs_nonneg _)
      have htwo : 2 * |w i * w j| ≤ w i ^ 2 + w j ^ 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|w i| - |w j|), sq_abs (w i), sq_abs (w j)]
      have := mul_le_mul_of_nonneg_left htwo hε
      nlinarith
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpair i j))
  have hdiag : (∑ i, ∑ j, if i = j then a * w i ^ 2 else 0) = a * ∑ i, w i ^ 2 := by
    simp [← Finset.mul_sum]
  have hmain : (∑ i, ∑ j, a * w i * w j) = 0 := by
    simp only [← Finset.mul_sum, hw, mul_zero, Finset.sum_const_zero]
  have herror : (∑ i, ∑ j, ε / 2 * (w i ^ 2 + w j ^ 2)) =
      ε * (Fintype.card ι : ℝ) * ∑ i, w i ^ 2 := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.card_univ]
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at htotal
  rw [hzero, hmain, hdiag, herror] at htotal
  have hsnonneg : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs0 : (∑ i, w i ^ 2) = 0 := by nlinarith
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    sq_nonneg (w j))).mp hs0 i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

theorem no_five_in_shell (v : Fin 5 → EuclideanSpace ℝ (Fin 3)) {r : ℝ}
    (hr : 0 < r)
    (hlow : ∀ i j, i ≠ j → r ≤ ‖v i - v j‖)
    (hupp : ∀ i j, i ≠ j → ‖v i - v j‖ ≤ (1 + shellDelta) * r) : False := by
  have hai : AffineIndependent ℝ v := by
    apply affineIndependent_of_sq_dist_close v
      (a := r ^ 2) (ε := (2 * shellDelta + shellDelta ^ 2) * r ^ 2)
    · dsimp [shellDelta]
      positivity
    · simp only [Fintype.card_fin]
      dsimp [shellDelta]
      nlinarith [sq_pos_of_pos hr]
    · intro i j hij
      have hlo := hlow i j hij
      have hup := hupp i j hij
      rw [abs_le]
      constructor
      · have hnorm := norm_nonneg (v i - v j)
        have hsq := sq_le_sq₀ hr.le hnorm |>.mpr hlo
        dsimp [shellDelta]
        nlinarith [sq_nonneg r]
      · have hnorm := norm_nonneg (v i - v j)
        have hsq := sq_le_sq₀ hnorm (by dsimp [shellDelta]; positivity) |>.mpr hup
        dsimp [shellDelta] at hsq ⊢
        nlinarith
  have hdim := hai.card_le_finrank_succ
  have hle := Submodule.finrank_le (vectorSpan ℝ (range v))
  have hthree : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hthree] at hle
  simp only [Fintype.card_fin] at hdim
  omega

def shellGraph {ι : Type u_1} (v : ι → EuclideanSpace ℝ (Fin 3)) (r : ℝ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ r ≤ ‖v i - v j‖ ∧ ‖v i - v j‖ ≤ (1 + shellDelta) * r
  symm := ⟨by
    intro i j h
    simpa only [norm_sub_rev] using And.intro h.1.symm h.2⟩
  loopless := ⟨by intro i; simp⟩

theorem shellGraph_cliqueFree {ι : Type u_1} (v : ι → EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) : (shellGraph v r).CliqueFree 5 := by
  classical
  intro s hs
  let e : ↥s ≃ Fin 5 := Finset.equivFinOfCardEq hs.card_eq
  let q : Fin 5 → EuclideanSpace ℝ (Fin 3) := fun i => v (e.symm i)
  apply no_five_in_shell q hr
  · intro i j hij
    have hne : (e.symm i : ι) ≠ e.symm j := by
      intro he
      apply hij
      exact e.symm.injective (Subtype.ext he)
    exact (hs.isClique (e.symm i).property (e.symm j).property hne).2.1
  · intro i j hij
    have hne : (e.symm i : ι) ≠ e.symm j := by
      intro he
      apply hij
      exact e.symm.injective (Subtype.ext he)
    exact (hs.isClique (e.symm i).property (e.symm j).property hne).2.2

theorem shellGraph_edge_bound {ι : Type u_1} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r) :
    letI := Classical.decRel (shellGraph v r).Adj
    8 * (shellGraph v r).edgeFinset.card ≤ 3 * (Fintype.card ι) ^ 2 := by
  classical
  have h := (shellGraph_cliqueFree v hr).card_edgeFinset_le (r := 4)
  have hT := SimpleGraph.mul_turanNumber_le
    (n := Fintype.card ι) (r := 4)
  omega

theorem coreProfile_ge_of_not_shell (t r : ℝ) (hr : r < 1)
    (hnot : ¬ (Real.exp (-t) ≤ r ∧ r ≤ (1 + shellDelta) * Real.exp (-t))) :
    t ^ 2 ≤ coreProfile t r := by
  unfold coreProfile
  split_ifs with hlow hhigh
  · have hp : 0 ≤ (Real.exp (-t) / r) ^ 12 := by positivity
    linarith
  · exact False.elim (hnot ⟨le_of_not_gt hlow, hhigh⟩)
  · rfl

end
end ContinuumTemperature
end

end OAI
