import OAI.NumberTheory.CubicMoment.Decomposition.StoppedAbsoluteMass

namespace OAI

/-! The complementary pair mass after a selected-bin prime is removed.
The rough distinguished factor has only a bounded number of choices for
each squarefree product, so the total mass is linear in its norm range. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopped_complement_mass (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d)
    (v : Eisenstein → ℂ) {M Y w : ℝ} (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hv : ∀ r ∈ R, ‖v r‖ ≤ M) (hw : 1 ≤ w)
    (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : Y < w^k) :
    (∑ t ∈ (R ×ˢ D).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y),
      ‖v t.1‖) ≤ 18*Y*((2^k:ℕ)*M) := by
  let U := (R ×ˢ D).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y)
  let B := (primaryElementBall Y).filter Squarefree
  have hmap (t : Eisenstein × Eisenstein) (ht : t ∈ U) : t.1*t.2 ∈ B := by
    obtain ⟨ht,hpred⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
      ⟨primary_mul (hR _ hr) (hD _ hd),hpred.2⟩,hpred.1⟩
  have hfiber (b : Eisenstein) (hb : b ∈ B) :
      (∑ t ∈ U with t.1*t.2 = b, ‖v t.1‖) ≤ (2^k:ℕ)*M := by
    obtain ⟨hb,hs⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb,hbY⟩ := mem_primaryElementBall.mp hb
    have hsub : U.filter (fun t => t.1*t.2 = b) ⊆ primaryPairFiber R D b := by
      intro t ht
      obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,he⟩
    calc
      _ ≤ ∑ t ∈ primaryPairFiber R D b, ‖v t.1‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => _root_.norm_nonneg _)
      _ = pairAbsolute R D v (fun _ => 1) b := by
        simp only [pairAbsolute,norm_one,mul_one]
      _ ≤ _ := rough_pairAbsolute_bound R D hR v (fun _ => 1) hM hv
        (fun _ _ => by simp) hb hs hw hrough (hbY.trans_lt hsize)
  calc
    _ = ∑ b ∈ B, ∑ t ∈ U with t.1*t.2 = b, ‖v t.1‖ :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ _b ∈ B, (2^k:ℕ)*M := Finset.sum_le_sum hfiber
    _ = (B.card:ℝ)*((2^k:ℕ)*M) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (primaryElementBall_card_le hY))
      (mul_nonneg (Nat.cast_nonneg _) hM)

end CubicFirstMoment

end

end OAI
