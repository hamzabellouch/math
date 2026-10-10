import OAI.NumberTheory.JointDickman.Amplification.LatentSquareSymmetry

namespace OAI

/-! # The integrated row-square estimate for the actual latent kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- Manuscript equation (24), before rewriting the finite expectations in
sampling notation. The short-lag cutoff supplies the separation needed by
the multiplicity sieve, and the singular factors sum uniformly over a row. -/
theorem candidateSquareMoment_row_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ K : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧ 0 < K ∧
      ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        T ≤ auxiliaryCutoff B → (T : ℝ) ≤ (B : ℝ)^2 →
        η*(B : ℝ)^(32/100 : ℝ) ≤ H →
        ∀ (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
        ∀ i : Fin M, (∑ t : Fin M, candidateSquareMoment B L T H τ C χ i t) ≤
          K*(B : ℝ)^(-(21/100 : ℝ)) := by
  obtain ⟨τ,K,hτ,hτcap,hτsampling,hK,hbound⟩ := candidateSquareMoment_bound hFord hM hL hη hcap
  refine ⟨τ,2*Real.exp 24*K,hτ,hτcap,hτsampling,by positivity,?_⟩
  filter_upwards [hbound] with B hB
  intro T H M C hT hTs hcut hT2 hH χ hχ i
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  let c := K/(T : ℝ)*(B : ℝ)^(-(21/100 : ℝ))
  have hc : 0 ≤ c := mul_nonneg (div_nonneg hK.le hTr.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpoint (t : Fin M) : candidateSquareMoment B L T H τ C χ i t ≤
      c*(if i ≠ t ∧ Nat.dist i.val t.val < T then singularFactor 24 (Nat.dist i.val t.val) else 0) := by
    by_cases heq : i = t
    · subst t
      simp only [candidateSquareMoment_diag,ne_eq,not_true_eq_false,false_and,ite_false,mul_zero,le_refl]
    by_cases hfar : T ≤ Nat.dist i.val t.val
    · rw [candidateSquareMoment_zero_of_far χ i t hfar,ite_eq_right (by omega),mul_zero]
    have hdist : Nat.dist i.val t.val < T := Nat.lt_of_not_ge hfar
    rw [ite_eq_left ⟨heq,hdist⟩]
    by_cases hshort : Nat.dist i.val t.val ≤ H
    · rw [candidateSquareMoment_zero_of_short χ i t hshort]
      exact mul_nonneg hc (zero_le_one.trans (singularFactor_one_le (by norm_num) _))
    have hjcut : Nat.dist i.val t.val ≤ auxiliaryCutoff B := hdist.le.trans hcut
    have hjB : (Nat.dist i.val t.val : ℝ) ≤ (B : ℝ)^2 :=
      (show (Nat.dist i.val t.val : ℝ) ≤ T by exact_mod_cast hdist.le).trans hT2
    have hjlow : η*(B : ℝ)^(32/100 : ℝ) ≤ (Nat.dist i.val t.val : ℝ) :=
      hH.trans (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hshort)))
    rcases lt_or_gt_of_ne heq with hit | hti
    · have hh := hB T H M C hT hTs χ hχ i t hit
      simpa only [Nat.dist_eq_sub_of_le hit.le] using hh
        (by simpa only [Nat.dist_eq_sub_of_le hit.le] using hjcut)
        (by simpa only [Nat.dist_eq_sub_of_le hit.le] using hjB)
        (by simpa only [Nat.dist_eq_sub_of_le hit.le] using hjlow)
    · rw [candidateSquareMoment_symm B L T H τ C χ i t]
      have hh := hB T H M C hT hTs χ hχ t i hti
      simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hh
        (by simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hjcut)
        (by simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hjB)
        (by simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hjlow)
  calc
    _ ≤ ∑ t : Fin M, c*(if i ≠ t ∧ Nat.dist i.val t.val < T then
        singularFactor 24 (Nat.dist i.val t.val) else 0) := sum_le_sum (fun t _ => hpoint t)
    _ = c*∑ t : Fin M, if i ≠ t ∧ Nat.dist i.val t.val < T then
        singularFactor 24 (Nat.dist i.val t.val) else 0 := (mul_sum _ _ _).symm
    _ ≤ c*(2*Real.exp 24*T) := mul_le_mul_of_nonneg_left (distance_lag_singular_sum i T) hc
    _ = _ := by
      dsimp only [c]
      field_simp

end JointDickman

end OAI
