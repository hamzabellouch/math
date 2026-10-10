import Mathlib

namespace OAI


noncomputable section

namespace Problem355.PrimitiveLine

theorem integral_scalar_of_bezout {ι : Type*} [Fintype ι]
    (x z w : ι → ℤ) (hx : (∑ i, x i * z i) = 1)
    (r : ℝ) (hw : ∀ i, (w i : ℝ) = r * (x i : ℝ)) :
    ∃ a : ℤ, (a : ℝ) = r ∧ ∀ i, w i = a * x i := by
  let a : ℤ := ∑ i, w i * z i
  have ha : (a : ℝ) = r := by
    dsimp [a]
    push_cast
    simp_rw [hw, mul_assoc]
    rw [← Finset.mul_sum]
    have hxR : (∑ i, (x i : ℝ) * (z i : ℝ)) = 1 := by exact_mod_cast hx
    rw [hxR, mul_one]
  refine ⟨a, ha, fun i => ?_⟩
  have hwi : (w i : ℝ) = ((a * x i : ℤ) : ℝ) := by
    push_cast
    rw [ha]
    exact hw i
  exact_mod_cast hwi

theorem card_integral_multiples_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (hv : v ≠ 0) (R : ℝ) (hR : 0 ≤ R) (S : Finset E)
    (hline : ∀ p ∈ S, ∃ z : ℤ, p = (z : ℝ) • v)
    (hball : ∀ p ∈ S, ‖p‖ ≤ R) :
    (S.card : ℝ) ≤ 1 + 2 * R / ‖v‖ := by
  classical
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let T : ℝ := R / ‖v‖
  let Q : Finset ℤ := Finset.Icc (-⌊T⌋) ⌊T⌋
  have hT : 0 ≤ T := div_nonneg hR hvnorm.le
  have hf : (0 : ℤ) ≤ ⌊T⌋ := Int.le_floor.mpr (by simpa using hT)
  have hsubset : S ⊆ Q.image (fun z : ℤ => (z : ℝ) • v) := by
    intro p hp
    obtain ⟨z, hz⟩ := hline p hp
    have hzabs : |(z : ℝ)| ≤ T := by
      apply (le_div_iff₀ hvnorm).mpr
      simpa only [hz, norm_smul, Real.norm_eq_abs] using hball p hp
    have hzu : z ≤ ⌊T⌋ := Int.le_floor.mpr ((le_abs_self _).trans hzabs)
    have hzl : -z ≤ ⌊T⌋ := Int.le_floor.mpr (by
      simpa only [Int.cast_neg] using (neg_le_abs (z : ℝ)).trans hzabs)
    apply Finset.mem_image.mpr
    refine ⟨z, ?_, hz.symm⟩
    change z ∈ Finset.Icc (-⌊T⌋) ⌊T⌋
    simp only [Finset.mem_Icc]
    omega
  have hcard : S.card ≤ Q.card :=
    (Finset.card_le_card hsubset).trans Finset.card_image_le
  have hnat : 0 ≤ ⌊T⌋ + 1 - (-⌊T⌋) := by omega
  calc
    (S.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcard
    _ = 2 * (⌊T⌋ : ℝ) + 1 := by
      dsimp [Q]
      rw [Int.card_Icc]
      have heq := Int.toNat_of_nonneg hnat
      have heqR : (((⌊T⌋ + 1 - (-⌊T⌋)).toNat : ℕ) : ℝ) =
          ((⌊T⌋ + 1 - (-⌊T⌋) : ℤ) : ℝ) := by exact_mod_cast heq
      rw [heqR]
      push_cast
      ring
    _ ≤ 1 + 2 * T := by linarith [Int.floor_le T]
    _ = 1 + 2 * R / ‖v‖ := by dsimp [T]; ring

theorem integer_multiple_of_shortest {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : AddSubgroup E) {v w : E} (hv : v ≠ 0) (hvL : v ∈ L)
    (hshort : ∀ u ∈ L, u ≠ 0 → ‖v‖ ≤ ‖u‖)
    (hwL : w ∈ L) (hline : ∃ r : ℝ, w = r • v) :
    ∃ z : ℤ, w = (z : ℝ) • v := by
  obtain ⟨r, hr⟩ := hline
  let u : E := (r - (⌊r⌋ : ℝ)) • v
  have humem : u ∈ L := by
    change (r - (⌊r⌋ : ℝ)) • v ∈ L
    rw [sub_smul, ← hr, Int.cast_smul_eq_zsmul]
    exact L.sub_mem hwL (L.zsmul_mem hvL _)
  have hnonneg : 0 ≤ r - (⌊r⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le r)
  have hlt : r - (⌊r⌋ : ℝ) < 1 := by linarith [Int.lt_floor_add_one r]
  have hunorm : ‖u‖ < ‖v‖ := by
    change ‖(r - (⌊r⌋ : ℝ)) • v‖ < ‖v‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    nlinarith [norm_pos_iff.mpr hv]
  have hu : u = 0 := by
    by_contra hne
    exact (not_lt_of_ge (hshort u humem hne)) hunorm
  refine ⟨⌊r⌋, sub_eq_zero.mp ?_⟩
  calc
    w - (⌊r⌋ : ℝ) • v = u := by rw [hr, ← sub_smul]
    _ = 0 := hu

theorem card_lattice_line_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : AddSubgroup E) (v : E) (hv : v ≠ 0) (hvL : v ∈ L)
    (hshort : ∀ u ∈ L, u ≠ 0 → ‖v‖ ≤ ‖u‖)
    (R : ℝ) (hR : 0 ≤ R) (S : Finset E)
    (hmem : ∀ p ∈ S, p ∈ L)
    (hline : ∀ p ∈ S, ∃ r : ℝ, p = r • v)
    (hball : ∀ p ∈ S, ‖p‖ ≤ R) :
    (S.card : ℝ) ≤ 1 + 2 * R / ‖v‖ := by
  apply card_integral_multiples_le v hv R hR S _ hball
  intro p hp
  exact integer_multiple_of_shortest L hv hvL hshort (hmem p hp) (hline p hp)

theorem card_short_lattice_vectors_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : AddSubgroup E) (v : E) (hv : v ≠ 0) (hvL : v ∈ L)
    (hshort : ∀ u ∈ L, u ≠ 0 → ‖v‖ ≤ ‖u‖)
    (lambda₂ : ℝ)
    (hsecond : ∀ p ∈ L, ‖p‖ < lambda₂ → ∃ r : ℝ, p = r • v)
    (R : ℝ) (hR : 0 ≤ R) (hRsecond : R < lambda₂) (S : Finset E)
    (hmem : ∀ p ∈ S, p ∈ L) (hball : ∀ p ∈ S, ‖p‖ ≤ R) :
    (S.card : ℝ) ≤ 1 + 2 * R / ‖v‖ := by
  apply card_lattice_line_le L v hv hvL hshort R hR S hmem _ hball
  intro p hp
  exact hsecond p (hmem p hp) ((hball p hp).trans_lt hRsecond)

end Problem355.PrimitiveLine

end

end OAI
