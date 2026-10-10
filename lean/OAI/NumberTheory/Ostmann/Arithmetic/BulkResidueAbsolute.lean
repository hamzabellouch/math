import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorAbsolute
import OAI.NumberTheory.Ostmann.Arithmetic.BulkResiduePageBound

namespace OAI

/-! # Nonnegative norm comparison after bulk CRT separation -/

namespace Ostmann
open scoped Classical BigOperators

theorem uniform_equiv_product_average_real {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B × C) (f : B → ℝ) (g : C → ℝ) :
    (Fintype.card A : ℝ)⁻¹ * (∑ a, f (e a).1 * g (e a).2) =
      ((Fintype.card B : ℝ)⁻¹ * ∑ b, f b) *
        ((Fintype.card C : ℝ)⁻¹ * ∑ c, g c) := by
  rw [e.sum_comp (fun z => f z.1 * g z.2), Fintype.card_congr e,
    Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

/-- Page factors at every original bulk slot cost at most two. The frequency
and spectator averages still retain their independent CRT coordinates. -/
theorem bulk_residue_absolute_mean_le {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ) (Y : J → ℝ) (hY : ∀ j, 0 ≤ Y j)
    (F : (J → (ZMod r)ˣ) → ℂ) (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (C : I → ℝ)
    (hF : (Fintype.card (J → (ZMod r)ˣ) : ℝ)⁻¹ * ∑ a, ‖F a‖ ≤ B)
    (hG : ∀ i, (Fintype.card (J → (ZMod (p i))ˣ) : ℝ)⁻¹ * ∑ a, ‖G i a‖ ≤ C i) :
    (Fintype.card (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) : ℝ)⁻¹ *
      (∑ x : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ,
        ‖(F (bulkResidueEquiv r p hc x).1 *
          ∏ j, pageGiantWeight P Q (∏ i, bulkResidueModuli r p i) (x j).val.val (Y j)) *
          ∏ i, G i ((bulkResidueEquiv r p hc x).2 i)‖) ≤
      (2 : ℝ) ^ Fintype.card J * (B * ∏ i, C i) := by
  let e := bulkResidueEquiv (J := J) r p hc
  have hpage (x : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) :
      ‖∏ j, pageGiantWeight P Q (∏ i, bulkResidueModuli r p i) (x j).val.val (Y j)‖ ≤
        (2 : ℝ) ^ Fintype.card J := by
    rw [norm_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ =>
      pageGiantWeight_norm_le_two P Q _ _ _ (hY j))).trans_eq (by simp)
  have hspec := product_uniform_mean_le (fun i a => ‖G i a‖) (fun _ _ => norm_nonneg _)
    C hG
  have hspec0 : 0 ≤ (Fintype.card (∀ i, J → (ZMod (p i))ˣ) : ℝ)⁻¹ *
      ∑ a : ∀ i, J → (ZMod (p i))ˣ, ∏ i, ‖G i (a i)‖ := by positivity
  calc
    _ ≤ (Fintype.card (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) : ℝ)⁻¹ *
        ∑ x : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ,
          (2 : ℝ) ^ Fintype.card J * (‖F (e x).1‖ * ∏ i, ‖G i ((e x).2 i)‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_le_sum
      intro x _
      have hgn : 0 ≤ ∏ i, ‖G i ((e x).2 i)‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
      have hp := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hpage x) (norm_nonneg (F (e x).1))) hgn
      simpa only [norm_mul, norm_prod, mul_assoc, mul_comm, mul_left_comm] using hp
    _ = (2 : ℝ) ^ Fintype.card J *
        (((Fintype.card (J → (ZMod r)ˣ) : ℝ)⁻¹ * ∑ a, ‖F a‖) *
          ((Fintype.card (∀ i, J → (ZMod (p i))ˣ) : ℝ)⁻¹ *
            ∑ a : ∀ i, J → (ZMod (p i))ˣ, ∏ i, ‖G i (a i)‖)) := by
      rw [← Finset.mul_sum, ← mul_assoc, mul_comm _ ((2 : ℝ) ^ Fintype.card J), mul_assoc]
      rw [uniform_equiv_product_average_real e (fun a => ‖F a‖) (fun a => ∏ i, ‖G i (a i)‖)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hF hspec hspec0 hB) (by positivity)

end Ostmann

end OAI
