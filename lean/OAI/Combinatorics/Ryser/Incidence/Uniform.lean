import OAI.Combinatorics.Ryser.Incidence.Pruning
import OAI.Combinatorics.Ryser.Incidence.PrunedContradiction

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section

def SmallProperSubfields (F : Type*) [Field F] [Fintype F] : Prop :=
  ∀ M : Subfield F, M ≠ ⊤ → Nat.card M ^ 3 ≤ Fintype.card F

theorem cardinality_scale_eq {q : ℝ} (hq : 0 < q) :
    q ^ (1 + savingExponent) = densityScale q * q := by
  rw [Real.rpow_add hq, Real.rpow_one]
  exact mul_comm _ _

theorem incidence_scale_eq {q : ℝ} (hq : 0 < q) :
    q ^ ((3 : ℝ) / 2 - savingExponent) = q * Real.sqrt q / densityScale q := by
  rw [Real.rpow_sub hq]
  congr 1
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq,
    Real.rpow_one, Real.sqrt_eq_rpow]

theorem uniform_incidence_bound (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hq : incidenceThreshold ≤ Fintype.card F) (hsub : SmallProperSubfields F)
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (hP : (P.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 + savingExponent))
    (hL : (L.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 + savingExponent)) :
    (incidenceCount ProjectiveIncidence P L : ℝ) ≤
      (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - savingExponent) := by
  classical
  let q : ℝ := Fintype.card F
  let U := densityScale q
  let r := Real.sqrt q
  obtain ⟨hqpos, hU, hdegree, hlarge, hremove, hfirst, hsecond, hthird⟩ :=
    largeEnough_of_threshold hq
  have hr : 0 < r := Real.sqrt_pos.2 hqpos
  have hrq : r ^ 2 = q := Real.sq_sqrt hqpos.le
  have hP' : (P.card : ℝ) ≤ U * q := by
    simpa only [cardinality_scale_eq hqpos] using hP
  have hL' : (L.card : ℝ) ≤ U * q := by
    simpa only [cardinality_scale_eq hqpos] using hL
  by_contra hnot
  have hI : q * r / U ≤ (incidenceCount ProjectiveIncidence P L : ℝ) := by
    have hstrict := lt_of_not_ge hnot
    rw [incidence_scale_eq hqpos] at hstrict
    exact hstrict.le
  obtain ⟨P', _, L', _, _, hPlo, _, hPup, hLup, hmin, hmax, _, hcap⟩ :=
    exists_projective_pruning P L hU hqpos hrq hdegree hP' hL' hI
  have hproper : ∀ M : Subfield F, M ≠ ⊤ →
      (Nat.card M : ℝ) ^ 3 ≤ (Fintype.card F : ℝ) := by
    intro M hM
    exact_mod_cast hsub M hM
  have hleft (p : ProjectivePoint F) : leftDegree ProjectiveIncidence L' p =
      (L'.filter fun l => ProjectiveIncidence p l).card := by
    unfold leftDegree
    apply congrArg Finset.card
    ext l
    simp only [Finset.mem_filter]
  have hright (l : ProjectiveLine F) : rightDegree ProjectiveIncidence P' l =
      (P'.filter fun p => ProjectiveIncidence p l).card := by
    unfold rightDegree leftDegree
    apply congrArg Finset.card
    ext p
    simp only [Finset.mem_filter]
  apply pruned_incidence_impossible P' L' r U hr hrq hU hlarge hremove
    hfirst hsecond hthird hproper
  · simpa only [hrq] using hPlo
  · simpa only [hrq] using hPup
  · simpa only [hrq] using hLup
  · intro p hp
    simpa only [hleft] using hmin.1 p hp
  · intro l hl
    simpa only [hright] using hmin.2 l hl
  · intro p hp
    simpa only [hleft] using hmax p hp
  · intro l
    simpa only [hright] using hcap l

end
end RyserCoveringCounterexample.Incidence

end OAI
