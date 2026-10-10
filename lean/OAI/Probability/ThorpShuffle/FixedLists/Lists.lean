import OAI.Probability.ThorpShuffle.FixedLists.Objects
import OAI.Probability.ThorpShuffle.FixedLists.Asymptotics

namespace OAI


noncomputable section
open scoped BigOperators
open Filter
namespace Thorp
namespace FixedLists
open Conditional

theorem list_test_bound_raw (d C m k : ℕ)
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * m)
    (hk : k + m ≤ Fintype.card (Position (d + 2)))
    (e : LabelList (d + 2) k) (r : State (d + 2))
    (f : LabelList (d + 2) k → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    |mean (fun ω : History (d + 2) ((C + 2) * (d + 2)) =>
        f (e.trans ((r * run (d + 2) ((C + 2) * (d + 2)) ω).toEmbedding))) -
      mean (fun g : State (d + 2) => f (e.trans ((r * g).toEmbedding)))| ≤
      (k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
        ((63 / 64 : ℝ) ^ (C * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)) := by
  let F : (Fin k → Position (d + 2)) → ℝ := fun z =>
    if hz : Function.Injective z then f ((⟨z, hz⟩ : LabelList (d + 2) k).trans r.toEmbedding)
    else 0
  have hF : ∀ z, |F z| ≤ 1 := by
    intro z
    dsimp only [F]
    split_ifs
    · exact hf _
    · norm_num
  have hmap (g : State (d + 2)) :
      F (g ∘ e) = f (e.trans ((r * g).toEmbedding)) := by
    dsimp only [F]
    rw [dite_eq_left (g.injective.comp e.injective)]
    rfl
  have hb := prefix_test_bound_sixteen d C m hm k hk e e.injective F hF
  simpa only [hmap] using hb

theorem list_tv_bound_raw (d C m k : ℕ)
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * m)
    (hk : k + m ≤ Fintype.card (Position (d + 2)))
    (e : LabelList (d + 2) k) (r : State (d + 2)) :
    tv (fairMass (fun ω : History (d + 2) ((C + 2) * (d + 2)) =>
        e.trans ((r * run (d + 2) ((C + 2) * (d + 2)) ω).toEmbedding)))
      (fun _ => (1 : ℝ) / Fintype.card (LabelList (d + 2) k)) ≤
      (k : ℝ) / 2 * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
        ((63 / 64 : ℝ) ^ (C * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)) := by
  rw [← uniform_list_mass_frame e r]
  have hh := fairMass_tv_le_of_test
    (fun ω : History (d + 2) ((C + 2) * (d + 2)) =>
      e.trans ((r * run (d + 2) ((C + 2) * (d + 2)) ω).toEmbedding))
    (fun g : State (d + 2) => e.trans ((r * g).toEmbedding))
    ((k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((63 / 64 : ℝ) ^ (C * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)))
    (list_test_bound_raw d C m k hm hk e r)
  calc
    _ ≤ (↑k * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((63 / 64 : ℝ) ^ (C * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m))) / 2 := hh
    _ = _ := by ring

lemma images_factor {d k : ℕ} (t : ℕ) (start : State d) (labels : LabelList d k)
    (ω : History d t) :
    images t start labels ω =
      (labels.trans start.toEmbedding).trans
        (((rotate d)⁻¹ ^ t * run d t ω).toEmbedding) := by
  ext i
  rfl

theorem listTV_bound_raw (d C m k : ℕ)
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * m)
    (hk : k + m ≤ Fintype.card (Position (d + 2)))
    (start : State (d + 2)) (labels : LabelList (d + 2) k) :
    listTV ((C + 2) * (d + 2)) start labels ≤
      (k : ℝ) / 2 * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
        ((63 / 64 : ℝ) ^ (C * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)) := by
  simp only [listTV]
  exact list_tv_bound_raw d C m k hm hk (labels.trans start.toEmbedding)
    ((rotate (d + 2))⁻¹ ^ ((C + 2) * (d + 2)))

theorem listTV_bound (d C k : ℕ) (hk : 16 * k ≤ 15 * 2 ^ (d + 4))
    (start : State (d + 4)) (labels : LabelList (d + 4) k) :
    listTV ((C + 2) * (d + 4)) start labels ≤
      (k : ℝ) / 2 * Real.sqrt ((2 : ℝ) ^ (d + 4) * energyEnvelope C d) := by
  have hn : Fintype.card (Position (d + 2 + 2)) = 16 * 2 ^ d := by
    rw [card_position]
    simp only [pow_add]
    norm_num
    omega
  have hk' : k + 2 ^ d ≤ Fintype.card (Position (d + 2 + 2)) := by
    have hn' : 2 ^ (d + 4) = 16 * 2 ^ d := by simp [pow_add, Nat.mul_comm]
    rw [hn' ] at hk
    rw [hn]
    omega
  have hh := listTV_bound_raw (d + 2) C (2 ^ d) k (by rw [hn]) hk' start labels
  simpa only [Nat.add_assoc, card_position, Nat.cast_pow, Nat.cast_ofNat, energyEnvelope] using hh

lemma k_le_size (d k : ℕ) (hk : 16 * k ≤ 15 * 2 ^ d) : (k : ℝ) ≤ (2 : ℝ) ^ d := by
  have h : k ≤ 2 ^ d := by omega
  exact_mod_cast h

theorem listTV_256 (d k : ℕ) (hk : 16 * k ≤ 15 * 2 ^ (d + 4))
    (start : State (d + 4)) (labels : LabelList (d + 4) k) :
    listTV (256 * (d + 4)) start labels ≤ listRate d := by
  have h := listTV_bound d 254 k hk start labels
  have hk' := k_le_size (d + 4) k hk
  have ha := energyEnvelope_nonneg 254 d
  have hb : (k : ℝ) / 2 * Real.sqrt ((2 : ℝ) ^ (d + 4) * energyEnvelope 254 d) ≤ listRate d := by
    calc
      _ ≤ ((2 : ℝ) ^ (d + 4)) / 2 * Real.sqrt ((2 : ℝ) ^ (d + 4) * energyEnvelope 254 d) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hk' (by norm_num)) (Real.sqrt_nonneg _)
      _ ≤ listRate d := by
        unfold listRate
        apply Real.le_sqrt_of_sq_le
        rw [mul_pow, div_pow, Real.sq_sqrt (mul_nonneg (by positivity) ha)]
        have hp : 0 ≤ ((2 : ℝ) ^ (d + 4)) ^ 3 * energyEnvelope 254 d := mul_nonneg (by positivity) ha
        nlinarith
  exact h.trans hb

theorem listTV_1024_eventually :
    ∀ᶠ d : ℕ in atTop, ∀ k, 16 * k ≤ 15 * 2 ^ (d + 4) →
      ∀ (start : State (d + 4)) (labels : LabelList (d + 4) k),
      listTV (1024 * (d + 4)) start labels ≤ Real.rpow ((2 : ℝ) ^ (d + 4)) (-(3 : ℝ) / 2) := by
  have he : ∀ᶠ d : ℕ in atTop,
      ((2 : ℝ) ^ (d + 4)) ^ 6 * energyEnvelope 1022 d ≤ 2 :=
    (scaledEnergy_tendsto 1022 6 geometric_base_1024).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [he] with d hd
  intro k hk start labels
  have h := listTV_bound d 1022 k hk start labels
  have hk' := k_le_size (d + 4) k hk
  exact h.trans ((mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hk' (by norm_num)) (Real.sqrt_nonneg _)).trans
      (scalar_tv_finish _ _ (by positivity) (energyEnvelope_nonneg _ _) hd))

end FixedLists
end Thorp

end

end OAI
