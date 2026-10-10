import OAI.Combinatorics.BalancedRyser.Profiles.ProfileFiniteMarks
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileScheduledApproximation

namespace OAI

section

noncomputable section
open Filter
open scoped Topology

namespace Balanced.ProfileFiniteScheduled

universe u
open ProfileFiniteMarks ProfileScheduledMarks ProfileScheduledApproximation

theorem uniform_finiteDetection_le_mean_add_bound
    (k : ℕ) (hk : 1 ≤ k) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)),
      N ≤ Fintype.card F → IsProfilePair k D C →
      (C.card = 0 ∨ a * (Fintype.card F : ℝ) ≤ (C.card : ℝ)) →
      ∀ η : ℝ,
        dFinite D C η ε + cFinite D C η ε ≤ normalizedMean D C η ε +
          32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card F : ℝ) * ε^2) := by
  obtain ⟨ND, _, hDapp⟩ := uniform_scheduled_D_means k (half_pos hε)
  obtain ⟨NC, _, hCapp⟩ := uniform_scheduled_C_means k (half_pos hε)
  obtain ⟨NE, _, hEapp⟩ := uniform_scheduled_empty_means k (half_pos hε)
  let M := max ND (max NC NE)
  obtain ⟨Q, hQ⟩ := exists_nat_ge ((M : ℝ) / a)
  refine ⟨max M Q, ?_⟩
  intro F hField hFin hDec D C hq hp hgap η
  have hMq : M ≤ Fintype.card F := (Nat.le_max_left M Q).trans hq
  have hQq : Q ≤ Fintype.card F := (Nat.le_max_right M Q).trans hq
  have hqD : Fintype.card F ≤ D.card := by
    have hmul := Nat.mul_le_mul_right (Fintype.card F + 1) hk
    rw [profile_deletionSet_card k D hp.1]
    exact (Nat.le_succ _).trans (by simpa only [one_mul] using hmul)
  have hMD : M ≤ D.card := hMq.trans hqD
  have hND : ND ≤ M := Nat.le_max_left _ _
  have hNC : NC ≤ M := (Nat.le_max_left NC NE).trans (Nat.le_max_right ND _)
  have hNE : NE ≤ M := (Nat.le_max_right NC NE).trans (Nat.le_max_right ND _)
  rcases hgap with hzero | hsize
  · have hC : C = ∅ := Finset.card_eq_zero.mp hzero
    subst C
    apply finiteDetection_le_normalizedMean_add_bound k D ∅ hp η ε hε
    · intro i x _
      exact (hEapp F D i x (hNE.trans hMq) (hNE.trans hMD) hp.1).1.le
    · intro i x _
      exact (hEapp F D i x (hNE.trans hMq) (hNE.trans hMD) hp.1).2.le
    · intro i
      exact (Finset.notMem_empty i.val i.property).elim
    · intro i
      exact (Finset.notMem_empty i.val i.property).elim
  · have hMC : M ≤ C.card := by
      have hQq' : (Q : ℝ) ≤ Fintype.card F := by exact_mod_cast hQq
      have hratio : (M : ℝ) / a ≤ Fintype.card F := hQ.trans hQq'
      have hscaled : (M : ℝ) ≤ a * Fintype.card F := by
        simpa only [mul_comm] using (div_le_iff₀ ha).mp hratio
      exact_mod_cast hscaled.trans hsize
    apply finiteDetection_le_normalizedMean_add_bound k D C hp η ε hε
    · intro i x _
      exact (hDapp F D C i x (hND.trans hMq) (hND.trans hMD)
        (hND.trans hMC) hp).1.le
    · intro i x _
      exact (hDapp F D C i x (hND.trans hMq) (hND.trans hMD)
        (hND.trans hMC) hp).2.le
    · intro i x _
      exact (hCapp F D C i x (hNC.trans hMq) (hNC.trans hMD)
        (hNC.trans hMC) hp).1.le
    · intro i x _
      exact (hCapp F D C i x (hNC.trans hMq) (hNC.trans hMD)
        (hNC.trans hMC) hp).2.le

theorem eventually_finiteDetection_le_mean_add_bound
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (k : ℕ) (hk : 1 ≤ k)
    (D C : ∀ n, Finset (Line (F n)))
    (hp : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hgap : ∀ n, (C n).card = 0 ∨
      a * (Fintype.card (F n) : ℝ) ≤ ((C n).card : ℝ)) (η : ℝ) :
    ∀ᶠ n in atTop,
      dFinite (D n) (C n) η ε + cFinite (D n) (C n) η ε ≤
        normalizedMean (D n) (C n) η ε +
          32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card (F n) : ℝ) * ε^2) := by
  obtain ⟨N, hN⟩ := uniform_finiteDetection_le_mean_add_bound k hk ha hε
  filter_upwards [hq.eventually (eventually_ge_atTop N)] with n hn
  exact hN (F n) (D n) (C n) hn (hp n) (hgap n) η

end Balanced.ProfileFiniteScheduled

end

section

noncomputable section
open Filter
open scoped Topology

namespace Balanced.ProfileScheduledFiniteComparison

universe u

open ProfileScheduledApproximation ProfileScheduledMarks ProfileFiniteMarks

theorem uniform_finiteDetection_le_normalizedMean_add_bound
    (k : ℕ) (η ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)),
      N ≤ Fintype.card F → N ≤ D.card → (C = ∅ ∨ N ≤ C.card) →
      IsProfilePair k D C →
      dFinite D C η ε + cFinite D C η ε ≤ normalizedMean D C η ε +
        32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card F : ℝ) * ε^2) := by
  obtain ⟨ND, hND, hD⟩ := uniform_scheduled_D_means k (half_pos hε)
  obtain ⟨NC, hNC, hC⟩ := uniform_scheduled_C_means k (half_pos hε)
  obtain ⟨NE, hNE, hE⟩ := uniform_scheduled_empty_means k (half_pos hε)
  refine ⟨max (max ND NC) NE, by omega, ?_⟩
  intro F _ _ _ D C hq hd hc hp
  rcases hc with rfl | hc
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

theorem eventually_finiteDetection_le_normalizedMean_add_bound
    {F : ℕ → Type u} [∀ t, Field (F t)] [∀ t, Fintype (F t)]
    [∀ t, DecidableEq (F t)]
    (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 0 < a)
    (D C : ∀ t, Finset (Line (F t)))
    (hp : ∀ t, IsProfilePair k (D t) (C t))
    (hgap : ∀ t, (C t).card = 0 ∨
      a * (Fintype.card (F t) : ℝ) ≤ (C t).card)
    (hq : Tendsto (fun t => Fintype.card (F t)) atTop atTop)
    (η ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      dFinite (D t) (C t) η ε + cFinite (D t) (C t) η ε ≤
        normalizedMean (D t) (C t) η ε +
          32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card (F t) : ℝ) * ε^2) := by
  obtain ⟨N, _hN, hfinite⟩ :=
    uniform_finiteDetection_le_normalizedMean_add_bound k η ε hε
  have hqR : Tendsto (fun t => (Fintype.card (F t) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hlarge : ∀ᶠ t in atTop, (N : ℝ) ≤ a * (Fintype.card (F t) : ℝ) :=
    (hqR.const_mul_atTop ha).eventually_ge_atTop N
  filter_upwards [hq.eventually_ge_atTop N, hlarge] with t ht hta
  have hd : N ≤ (D t).card := by
    rw [profile_deletionSet_card k (D t) (hp t).1]
    have hm := Nat.mul_le_mul_right (Fintype.card (F t) + 1) hk
    simp only [Nat.one_mul] at hm
    exact ht.trans ((Nat.le_succ _).trans hm)
  have hc : C t = ∅ ∨ N ≤ (C t).card := by
    rcases hgap t with hz | hbig
    · exact Or.inl (Finset.card_eq_zero.mp hz)
    · exact Or.inr (by exact_mod_cast hta.trans hbig)
  exact hfinite (F t) (D t) (C t) ht hd hc (hp t)

theorem eventually_finiteDetection_of_profileClass
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    {F : ℕ → Type u} [∀ t, Field (F t)] [∀ t, Fintype (F t)]
    [∀ t, DecidableEq (F t)]
    (D C : ∀ t, Finset (Line (F t)))
    (hA : ∀ t, A (F t) (D t) (C t))
    (hq : Tendsto (fun t => Fintype.card (F t)) atTop atTop)
    (η ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      dFinite (D t) (C t) η ε + cFinite (D t) (C t) η ε ≤
        normalizedMean (D t) (C t) η ε +
          32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card (F t) : ℝ) * ε^2) := by
  obtain ⟨a, ha, hsize⟩ := hgap
  exact eventually_finiteDetection_le_normalizedMean_add_bound k hk a ha D C
    (fun t => hvalid (F t) (D t) (C t) (hA t))
    (fun t => hsize (F t) (D t) (C t) (hA t)) hq η ε hε

end Balanced.ProfileScheduledFiniteComparison

end

end
end

end OAI
