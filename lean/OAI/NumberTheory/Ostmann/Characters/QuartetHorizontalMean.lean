import OAI.NumberTheory.Ostmann.Characters.TreeTupleProfiles
import OAI.NumberTheory.Ostmann.Characters.HeldCycleAverage

namespace OAI

/-! # Summing the surviving characters after horizontal density domination -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance horizontalCharFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def rationalCutCharacterSum {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2))
    (B : TreeLeafIndex n → MulChar (ZMod p) ℂ → ZMod p → ℝ)
    (sign : TreeLeafIndex n → ℤ) (P : TreeLeafTuple (ZMod p)ˣ n) : ℝ := by
  classical
  exact ∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
    if (∏ i : TreeLeafIndex n, (ρ i) ^ sign i) = 1 then
      quartetCutValue (fun S (wp : (ZMod p → ℝ) × (ZMod p)ˣ) =>
        wp.1 (rationalQuartetStateArgument D S wp.2)) n
        (rationalQuartetStates n T XL XR c P)
        (treeLeafZip n ((treeLeafTupleEquiv _ n).symm (fun i => B i (ρ i))) P)
    else 0

/-- Apply horizontal density first, then eliminate one surviving character.
The majorants may vary with the quartet label but not with ancestor data. -/
theorem rationalCutCharacterSum_mean_le {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2))
    (B : TreeLeafIndex n → MulChar (ZMod p) ℂ → ZMod p → ℝ)
    (sign : TreeLeafIndex n → ℤ) (i : TreeLeafIndex n)
    (hi : sign i = 1 ∨ sign i = -1) (M H : ℝ) (hM : 0 ≤ M)
    (hB : ∀ j χ y, 0 ≤ B j χ y)
    (hsmall : ∀ χ, (∑ y : (ZMod p)ˣ, B i χ y) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ M)
    (hmass : ∀ j, (∑ χ : MulChar (ZMod p) ℂ,
      (∑ y : (ZMod p)ˣ, B j χ y) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤ H) :
    (∑ P : TreeLeafTuple (ZMod p)ˣ n, rationalCutCharacterSum D n T XL XR c B sign P) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤
      (2 : ℝ) ^ (2 ^ n - 1) * (M * H ^ (2 ^ n - 1)) := by
  classical
  let w (ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ) : TreeLeafTuple (ZMod p → ℝ) n :=
    (treeLeafTupleEquiv _ n).symm (fun i => B i (ρ i))
  let F (ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ) (P : TreeLeafTuple (ZMod p)ˣ n) :=
    quartetCutValue (fun S (wp : (ZMod p → ℝ) × (ZMod p)ˣ) =>
      wp.1 (rationalQuartetStateArgument D S wp.2)) n
      (rationalQuartetStates n T XL XR c P) (treeLeafZip n (w ρ) P)
  have hp (ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ) :
      (∑ P : TreeLeafTuple (ZMod p)ˣ n, F ρ P) /
        (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤
        (2 : ℝ) ^ (2 ^ n - 1) * ∏ j : TreeLeafIndex n,
          (∑ y : (ZMod p)ˣ, B j (ρ j) y) / (Fintype.card (ZMod p)ˣ : ℝ) := by
    have hw : treeWeightsNonneg n (w ρ) := by
      rw [treeWeightsNonneg_iff]
      intro j y
      simpa only [w, Equiv.apply_symm_apply] using hB j (ρ j) y
    have h := rationalQuartetStates_profile_mean_le D n T XL XR c (w ρ) hw
    rw [treeProfileMean_eq_prod] at h
    simpa only [w, Equiv.apply_symm_apply] using h
  have hc := cycle_majorant_average_le (fun j χ (y : (ZMod p)ˣ) => B j χ y)
    sign i hi M (fun _ => H) hM (fun j χ y => hB j χ y)
    (fun χ => by simpa only [div_eq_mul_inv, mul_comm] using hsmall χ)
    (fun j => by simpa only [div_eq_mul_inv, mul_comm] using hmass j)
  rw [cycle_majorant_average (fun j χ (y : (ZMod p)ˣ) => B j χ y) sign] at hc
  have hcard : Fintype.card {j : TreeLeafIndex n // j ≠ i} = 2 ^ n - 1 := by
    simpa only [Fintype.card_subtype_eq, card_treeLeafIndex] using
      Fintype.card_subtype_compl (fun j : TreeLeafIndex n => j = i)
  have hchars : (∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
      if (∏ j : TreeLeafIndex n, (ρ j) ^ sign j) = 1 then
        ∏ j : TreeLeafIndex n,
          (∑ y : (ZMod p)ˣ, B j (ρ j) y) / (Fintype.card (ZMod p)ˣ : ℝ) else 0) ≤
      M * H ^ (2 ^ n - 1) := by
    simpa only [Finset.prod_const, Finset.card_univ, hcard, div_eq_mul_inv, mul_comm] using hc
  calc
    _ = ∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
        if (∏ j : TreeLeafIndex n, (ρ j) ^ sign j) = 1 then
          (∑ P : TreeLeafTuple (ZMod p)ˣ n, F ρ P) /
            (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) else 0 := by
      unfold rationalCutCharacterSum
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ρ _
      split_ifs
      · rfl
      · simp
    _ ≤ (2 : ℝ) ^ (2 ^ n - 1) *
        ∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
          if (∏ j : TreeLeafIndex n, (ρ j) ^ sign j) = 1 then
            ∏ j : TreeLeafIndex n,
              (∑ y : (ZMod p)ˣ, B j (ρ j) y) / (Fintype.card (ZMod p)ˣ : ℝ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ρ _
      split_ifs
      · exact hp ρ
      · simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hchars (by positivity)

end Ostmann

end OAI
