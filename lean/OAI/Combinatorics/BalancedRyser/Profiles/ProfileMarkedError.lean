import OAI.Combinatorics.BalancedRyser.Profiles.ProfileEmpirical
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMarkedOrders

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Balanced.ProfileMarkedError

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem population_size_le (k : ℕ) (D C : Finset (Line F))
    (hp : IsProfilePair k D C) :
    (D.card : ℝ) + C.card ≤ (2 * (k : ℝ) + 1) * Fintype.card F := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hD : (D.card : ℝ) = (k : ℝ) * ((Fintype.card F : ℝ) + 1) := by
    exact_mod_cast profile_deletionSet_card k D hp.1
  have hC : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hp.2.2
  rw [hD]
  nlinarith [mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hq)]

def loss (U V : Finset (Line F)) (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (η ε : ℝ) : ℝ :=
  ∑ i : U, if η < z i then
    32 * (((I i).card : ℝ) + (J i).card) /
      ((Fintype.card F : ℝ)^2 * ε^2) else 0

omit [Field F] [Fintype F] [DecidableEq F] in

theorem prefix_size_le (U V : Finset (Line F))
    (I : Finset U) (J : Finset V) :
    (I.card : ℝ) + J.card ≤ (U.card : ℝ) + V.card := by
  have hI : I.card ≤ U.card := by simpa using Finset.card_le_univ I
  have hJ : J.card ≤ V.card := by simpa using Finset.card_le_univ J
  exact_mod_cast Nat.add_le_add hI hJ

theorem total_loss_div_le (k : ℕ) (D C : Finset (Line F))
    (hp : IsProfilePair k D C)
    (ID : D → Finset D) (JD : D → Finset C) (zD : D → ℝ)
    (IC : C → Finset C) (JC : C → Finset D) (zC : C → ℝ)
    (η ε : ℝ) :
    (loss D C ID JD zD η ε + loss C D IC JC zC η ε) / Fintype.card F ≤
      32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card F : ℝ) * ε^2) := by
  let B : ℝ := 2 * (k : ℝ) + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsize := population_size_le k D C hp
  have hD := ProfileMarkedOrders.normalized_variance_error_le D C ID JD zD η ε B hB
    (fun i => (prefix_size_le D C (ID i) (JD i)).trans hsize)
  have hC := ProfileMarkedOrders.normalized_variance_error_le C D IC JC zC η ε B hB
    (fun i => (prefix_size_le C D (IC i) (JC i)).trans (by simpa [B, add_comm] using hsize))
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  calc
    _ ≤ 32 * B * D.card / ((Fintype.card F : ℝ)^2 * ε^2) +
        32 * B * C.card / ((Fintype.card F : ℝ)^2 * ε^2) := by
      rw [add_div]
      exact add_le_add hD hC
    _ = 32 * B * ((D.card : ℝ) + C.card) /
        ((Fintype.card F : ℝ)^2 * ε^2) := by ring
    _ ≤ 32 * B * (B * Fintype.card F) /
        ((Fintype.card F : ℝ)^2 * ε^2) := by
      gcongr
    _ = _ := by
      dsimp [B]
      field_simp

theorem bound_tendsto_zero (k : ℕ) (ε : ℝ) (_hε : 0 < ε)
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) :
    Tendsto (fun n => 32 * (2 * (k : ℝ) + 1)^2 / ((q n : ℝ) * ε^2))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (q n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hq)
  have ht := hi.const_mul (32 * (2 * (k : ℝ) + 1)^2 / ε^2)
  convert ht using 1
  · ext n
    ring
  · simp

theorem total_loss_tendsto_zero
    {K : ℕ → Type*} [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)] (k : ℕ)
    (D C : ∀ n, Finset (Line (K n)))
    (hp : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
    (ID : ∀ n, D n → Finset (D n)) (JD : ∀ n, D n → Finset (C n))
    (zD : ∀ n, D n → ℝ) (IC : ∀ n, C n → Finset (C n))
    (JC : ∀ n, C n → Finset (D n)) (zC : ∀ n, C n → ℝ)
    (η ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n =>
      (loss (D n) (C n) (ID n) (JD n) (zD n) η ε +
        loss (C n) (D n) (IC n) (JC n) (zC n) η ε) / Fintype.card (K n))
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => div_nonneg (add_nonneg ?_ ?_) (Nat.cast_nonneg _))
    (fun n => total_loss_div_le k (D n) (C n) (hp n)
      (ID n) (JD n) (zD n) (IC n) (JC n) (zC n) η ε)
    (bound_tendsto_zero k ε hε _ hq)
  all_goals
    unfold loss
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity

end Balanced.ProfileMarkedError

end

end OAI
