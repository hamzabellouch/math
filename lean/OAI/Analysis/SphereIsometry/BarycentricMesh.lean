import OAI.Analysis.SphereIsometry.BarycentricBasic
import OAI.Analysis.SphereIsometry.ConvexDiameter
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The mesh estimate for barycentric subdivision

The larger face is split into the smaller face and its complement. Its
barycenter is the corresponding weighted average, giving the exact factor
`1 - S.card / T.card`. A dimension bound gives the uniform contraction.
-/

noncomputable section

open scoped BigOperators

namespace Tingley

variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq V] in
theorem norm_finiteBarycenter_sub_le_of_subsets {p : V → E}
    {S R T : Finset V} {D : ℝ} (hs : S.Nonempty) (hr : R.Nonempty)
    (hst : S ⊆ T) (hrt : R ⊆ T)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p R‖ ≤ D := by
  have hdiam : DiameterLE (p '' (↑T : Set V)) D := by
    rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
    simpa only [dist_eq_norm] using hpair u hu v hv
  have h := hdiam.convexHull
    (finiteBarycenter p S) (finiteBarycenter_mem_convexHull hs hst)
    (finiteBarycenter p R) (finiteBarycenter_mem_convexHull hr hrt)
  simpa only [dist_eq_norm] using h

theorem finiteBarycenter_partition {p : V → E} {S T : Finset V}
    (hs : S.Nonempty) (hst : S ⊆ T) (hr : (T \ S).Nonempty) :
    finiteBarycenter p T =
      ((S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S +
      (((T \ S).card : ℝ) / (T.card : ℝ)) • finiteBarycenter p (T \ S) := by
  classical
  have hs0 : (S.card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
  have hr0 : ((T \ S).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hr))
  have ht0 : (T.card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr (hs.mono hst)))
  have hS : ((S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S =
      (T.card : ℝ)⁻¹ • ∑ v ∈ S, p v := by
    rw [finiteBarycenter, smul_smul]
    congr 1
    field_simp [hs0, ht0]
  have hR : (((T \ S).card : ℝ) / (T.card : ℝ)) •
      finiteBarycenter p (T \ S) =
      (T.card : ℝ)⁻¹ • ∑ v ∈ T \ S, p v := by
    rw [finiteBarycenter, smul_smul]
    congr 1
    field_simp [hr0, ht0]
  rw [hS, hR, ← smul_add]
  unfold finiteBarycenter
  congr 1
  simpa only [add_comm] using (Finset.sum_sdiff (f := p) hst).symm

theorem norm_finiteBarycenter_sub_le_card {p : V → E}
    {S T : Finset V} {D : ℝ} (hs : S.Nonempty) (hst : S ⊆ T)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p T‖ ≤
      (1 - (S.card : ℝ) / (T.card : ℝ)) * D := by
  classical
  have ht : T.Nonempty := hs.mono hst
  have htpos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ht)
  by_cases heq : S = T
  · subst S
    simp [ne_of_gt htpos]
  have hr : (T \ S).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hts
    exact heq (Finset.Subset.antisymm hst hts))
  have hcard : ((T \ S).card : ℝ) + (S.card : ℝ) = (T.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hst
  have hfrac : ((T \ S).card : ℝ) / (T.card : ℝ) =
      1 - (S.card : ℝ) / (T.card : ℝ) := by
    apply (div_eq_iff (ne_of_gt htpos)).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt htpos)]
    linarith
  have hnonneg : 0 ≤ ((T \ S).card : ℝ) / (T.card : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) htpos.le
  have hid : finiteBarycenter p S - finiteBarycenter p T =
      (((T \ S).card : ℝ) / (T.card : ℝ)) •
        (finiteBarycenter p S - finiteBarycenter p (T \ S)) := by
    calc
      finiteBarycenter p S - finiteBarycenter p T =
          (1 - (S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S -
            (((T \ S).card : ℝ) / (T.card : ℝ)) •
              finiteBarycenter p (T \ S) := by
        rw [finiteBarycenter_partition hs hst hr, sub_smul, one_smul]
        abel
      _ = _ := by rw [← hfrac, smul_sub]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    ((T \ S).card : ℝ) / (T.card : ℝ) *
        ‖finiteBarycenter p S - finiteBarycenter p (T \ S)‖ ≤
        ((T \ S).card : ℝ) / (T.card : ℝ) * D :=
      mul_le_mul_of_nonneg_left
        (norm_finiteBarycenter_sub_le_of_subsets hs hr hst Finset.sdiff_subset hpair)
        hnonneg
    _ = _ := by rw [hfrac]

theorem norm_finiteBarycenter_sub_le_mesh {p : V → E}
    {S T : Finset V} {D : ℝ} (m : ℕ) (hD : 0 ≤ D)
    (hs : S.Nonempty) (hst : S ⊆ T) (hcard : T.card ≤ m + 1)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p T‖ ≤
      ((m : ℝ) / (m + 1 : ℝ)) * D := by
  have ht : T.Nonempty := hs.mono hst
  have htpos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ht)
  have hmpos : 0 < (m + 1 : ℝ) := by positivity
  have hsone : (1 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hs))
  have htcard : (T.card : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast hcard
  have hlow : 1 / (m + 1 : ℝ) ≤ (S.card : ℝ) / (T.card : ℝ) := by
    calc
      1 / (m + 1 : ℝ) ≤ 1 / (T.card : ℝ) :=
        one_div_le_one_div_of_le htpos htcard
      _ ≤ (S.card : ℝ) / (T.card : ℝ) :=
        (div_le_div_iff_of_pos_right htpos).2 hsone
  have hfactor : 1 - (S.card : ℝ) / (T.card : ℝ) ≤
      (m : ℝ) / (m + 1 : ℝ) := by
    have heq : (m : ℝ) / (m + 1 : ℝ) = 1 - 1 / (m + 1 : ℝ) := by
      apply (div_eq_iff (ne_of_gt hmpos)).2
      rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hmpos)]
      ring
    rw [heq]
    linarith
  exact (norm_finiteBarycenter_sub_le_card hs hst hpair).trans
    (mul_le_mul_of_nonneg_right hfactor hD)

theorem norm_finiteBarycenter_sub_le_of_comparable {p : V → E}
    {S T U : Finset V} {D : ℝ} (m : ℕ) (hD : 0 ≤ D)
    (hs : S.Nonempty) (ht : T.Nonempty) (hsu : S ⊆ U) (htu : T ⊆ U)
    (hcmp : S ⊆ T ∨ T ⊆ S) (hcard : U.card ≤ m + 1)
    (hpair : ∀ u ∈ U, ∀ v ∈ U, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p T‖ ≤
      ((m : ℝ) / (m + 1 : ℝ)) * D := by
  rcases hcmp with hst | hts
  · exact norm_finiteBarycenter_sub_le_mesh m hD hs hst
      ((Finset.card_le_card htu).trans hcard)
      (fun u hu v hv => hpair u (htu hu) v (htu hv))
  · simpa only [norm_sub_rev] using
      norm_finiteBarycenter_sub_le_mesh m hD ht hts
        ((Finset.card_le_card hsu).trans hcard)
        (fun u hu v hv => hpair u (hsu hu) v (hsu hv))

end Tingley

end

end OAI
