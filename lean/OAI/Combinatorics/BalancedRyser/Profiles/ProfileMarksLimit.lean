import OAI.Combinatorics.BalancedRyser.Profiles.ProfileGridFiniteIdentity
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileScheduledApproximation
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileScheduledMargin

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators

namespace Balanced.ProfileMarksLimit

universe u

open ProfileScheduledMarks ProfileScheduledApproximation ProfileFiniteMarks
  ProfileGridDetection ProfileScheduledMargin

theorem uniform_finite_detection_bound (k : ℕ) (η ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)),
      N ≤ Fintype.card F → N ≤ D.card → (C = ∅ ∨ N ≤ C.card) →
      IsProfilePair k D C →
      dFinite D C η ε + cFinite D C η ε ≤ normalizedMean D C η ε +
        32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card F : ℝ) * ε^2) := by
  obtain ⟨ND, _hND, hD⟩ := uniform_scheduled_D_means.{u} k (half_pos hε)
  obtain ⟨NC, _hNC, hC⟩ := uniform_scheduled_C_means.{u} k (half_pos hε)
  obtain ⟨NE, _hNE, hE⟩ := uniform_scheduled_empty_means.{u} k (half_pos hε)
  refine ⟨max ND (max NC NE), ?_⟩
  intro F _ _ _ D C hq hDc hCc hp
  rcases hCc with rfl | hCc
  · apply finiteDetection_le_normalizedMean_add_bound k D ∅ hp η ε hε
    · intro i x _
      exact (hE F D i x (by omega) (by omega) hp.1).1.le
    · intro i x _
      exact (hE F D i x (by omega) (by omega) hp.1).2.le
    · intro i
      exact (Finset.notMem_empty i.val i.property).elim
    · intro i
      exact (Finset.notMem_empty i.val i.property).elim
  · apply finiteDetection_le_normalizedMean_add_bound k D C hp η ε hε
    · intro i x _
      exact (hD F D C i x (by omega) (by omega) (by omega) hp).1.le
    · intro i x _
      exact (hD F D C i x (by omega) (by omega) (by omega) hp).2.le
    · intro i x _
      exact (hC F D C i x (by omega) (by omega) (by omega) hp).1.le
    · intro i x _
      exact (hC F D C i x (by omega) (by omega) (by omega) hp).2.le

theorem eventually_finite_detection_bound
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (hk : 1 ≤ k) (D C : ∀ n, Finset (Line (F n)))
    (hp : ∀ n, IsProfilePair k (D n) (C n))
    (a : ℝ) (ha : 0 < a)
    (hgap : ∀ n, (C n).card = 0 ∨
      a * (Fintype.card (F n) : ℝ) ≤ ((C n).card : ℝ))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (η ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      dFinite (D n) (C n) η ε + cFinite (D n) (C n) η ε ≤
        normalizedMean (D n) (C n) η ε +
          32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card (F n) : ℝ) * ε^2) := by
  obtain ⟨N, hN⟩ := uniform_finite_detection_bound.{u} k η ε hε
  have hDc (n : ℕ) : Fintype.card (F n) ≤ (D n).card := by
    rw [profile_deletionSet_card k (D n) (hp n).1]
    have hmul := Nat.mul_le_mul_right (Fintype.card (F n) + 1) hk
    simp only [Nat.one_mul] at hmul
    exact (Nat.le_succ _).trans hmul
  have hqR : Tendsto (fun n => (Fintype.card (F n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hq
  have haN : ∀ᶠ n in atTop, (N : ℝ) ≤ a * (Fintype.card (F n) : ℝ) :=
    (hqR.const_mul_atTop ha).eventually_ge_atTop (N : ℝ)
  filter_upwards [hq.eventually_ge_atTop N, haN] with n hn han
  apply hN (F n) (D n) (C n) hn (hn.trans (hDc n)) _ (hp n)
  rcases hgap n with hempty | hpositive
  · exact Or.inl (Finset.card_eq_zero.mp hempty)
  · right
    exact_mod_cast han.trans hpositive

theorem eventually_grid_le_sourceMean_add_error
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (hk : 1 ≤ k) (D C : ∀ n, Finset (Line (F n)))
    (hp : ∀ n, IsProfilePair k (D n) (C n))
    (a : ℝ) (ha : 0 < a)
    (hgap : ∀ n, (C n).card = 0 ∨
      a * (Fintype.card (F n) : ℝ) ≤ ((C n).card : ℝ))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) (t : ℕ) :
    ∀ᶠ n in atTop,
      dGridCutoffMass (D n) (C n) t + cGridCutoffMass (D n) (C n) t ≤
        sourceTest t (F n) (D n) (C n) +
          32 * (2 * (k : ℝ) + 1)^2 /
            ((Fintype.card (F n) : ℝ) * (threshold t)^2) := by
  have h := eventually_finite_detection_bound k hk D C hp a ha hgap hq
    (threshold t) (threshold t) (threshold_pos t)
  simpa only [dGridCutoffMass_eq_dFinite, cGridCutoffMass_eq_cFinite,
    sourceTest, threshold] using h

theorem source_limit_lower_bound
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A) :
    ProfileClassMargin.LimitLowerBound A sourceTest := by
  obtain ⟨a, ha, hsize⟩ := hgap
  intro F _ _ _ D C hA hq c P νD νC hlim t r hr
  have hp : ∀ n, IsProfilePair k (D n) (C n) :=
    fun n => hvalid (F n) (D n) (C n) (hA n)
  let S : ℝ := ProfileClassMargin.cutoffMass P νD νC t
  let s : ℝ := (r + S) / 2
  have hrs : r < s := by dsimp [s, S]; linarith
  have hsS : s < S := by dsimp [s, S]; linarith
  have hliminf := cutoff_sum_le_liminf_actual_grid k hk D C hp hq hlim t
  have hslim : s < atTop.liminf (fun n =>
      dGridCutoffMass (D n) (C n) t + cGridCutoffMass (D n) (C n) t) :=
    hsS.trans_le hliminf
  have hb : atTop.IsBoundedUnder (· ≥ ·) (fun n =>
      dGridCutoffMass (D n) (C n) t + cGridCutoffMass (D n) (C n) t) :=
    isBoundedUnder_of ⟨0, fun n => add_nonneg
      (dGridCutoffMass_nonneg (D n) (C n) t)
      (cGridCutoffMass_nonneg (D n) (C n) t)⟩
  have hgrid := eventually_lt_of_lt_liminf hslim hb
  have hbound := eventually_grid_le_sourceMean_add_error k hk D C hp a ha
    (fun n => hsize (F n) (D n) (C n) (hA n)) hq t
  have herror := (ProfileMarkedError.bound_tendsto_zero k (threshold t)
    (threshold_pos t) (fun n => Fintype.card (F n)) hq).eventually_lt_const
      (sub_pos.mpr hrs)
  filter_upwards [hgrid, hbound, herror] with n hg hn he
  linarith

end Balanced.ProfileMarksLimit

end

end OAI
