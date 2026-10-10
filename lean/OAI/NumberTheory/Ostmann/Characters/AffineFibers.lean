import OAI.NumberTheory.Ostmann.Characters.SquarePullback

namespace OAI

/-!
# Nonidentity affine-map fibers

The finite-field representation count used immediately before equation
`tree-affine-coefficient-norm`: every nonidentity affine map arising from
`U_r^* U_s` has at most two representations.
-/

namespace Ostmann

/-- Slope and translation of the affine map underlying `U_r^* U_s`.
The translation is written in ratio coordinates. -/
def affineParameters {p : ℕ} (r s : (ZMod p)ˣ) : (ZMod p)ˣ × ZMod p :=
  ((s / r) ^ 2, (r : ZMod p) *
    (((s / r : (ZMod p)ˣ) : ZMod p) - ((s / r : (ZMod p)ˣ) : ZMod p) ^ 2))

/-- The ratio-coordinate translation equals the manuscript's `s - s²/r`. -/
theorem affineParameters_translation {p : ℕ} [Fact p.Prime] (r s : (ZMod p)ˣ) :
    (affineParameters r s).2 = (s : ZMod p) - (s : ZMod p) ^ 2 / (r : ZMod p) := by
  simp only [affineParameters, Units.val_div_eq_div_val]
  field_simp

private theorem sub_sq_ne_zero {p : ℕ} [Fact p.Prime]
    (z : (ZMod p)ˣ) (hz : z ≠ 1) : (z : ZMod p) - (z : ZMod p) ^ 2 ≠ 0 := by
  intro h
  have hprod : (z : ZMod p) * (1 - (z : ZMod p)) = 0 := by
    calc
      (z : ZMod p) * (1 - (z : ZMod p)) = (z : ZMod p) - (z : ZMod p) ^ 2 := by ring
      _ = 0 := h
  rcases mul_eq_zero.mp hprod with hzero | hone
  · exact Units.ne_zero z hzero
  · exact hz (Units.ext (sub_eq_zero.mp hone).symm)

private theorem ratio_ne_one_of_nonidentity {p : ℕ} (r s : (ZMod p)ˣ)
    (h : affineParameters r s ≠ (1, 0)) : s / r ≠ 1 := by
  intro heq
  apply h
  simp only [affineParameters, heq, one_pow, Units.val_one, sub_self, mul_zero]

/-- The ratio determines both unit parameters once a nonidentity affine map
has been fixed. -/
theorem affineParameters_ratio_injective {p : ℕ} [Fact p.Prime]
    {r s r' s' : (ZMod p)ˣ}
    (hnon : affineParameters r s ≠ (1, 0))
    (hmap : affineParameters r s = affineParameters r' s')
    (hratio : s / r = s' / r') : r = r' ∧ s = s' := by
  have hz := ratio_ne_one_of_nonidentity r s hnon
  have hfactor := sub_sq_ne_zero (s / r) hz
  have htrans := congrArg Prod.snd hmap
  change (r : ZMod p) * (((s / r : (ZMod p)ˣ) : ZMod p) -
      ((s / r : (ZMod p)ˣ) : ZMod p) ^ 2) =
    (r' : ZMod p) * (((s' / r' : (ZMod p)ˣ) : ZMod p) -
      ((s' / r' : (ZMod p)ˣ) : ZMod p) ^ 2) at htrans
  rw [← hratio] at htrans
  have hr : r = r' := Units.ext (mul_right_cancel₀ hfactor htrans)
  refine ⟨hr, ?_⟩
  subst r'
  have := congrArg (fun u : (ZMod p)ˣ => u * r) hratio
  simpa only [div_mul_cancel] using this

/-- Every nonidentity affine map has at most two ordered unit representations. -/
theorem affineParameters_fiber_card_le_two {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (b : ZMod p) (hnon : (a, b) ≠ (1, 0)) :
    ((Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
      (fun rs => affineParameters rs.1 rs.2 = (a, b))).card ≤ 2 := by
  classical
  let S := (Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
    (fun rs => affineParameters rs.1 rs.2 = (a, b))
  let T := (Finset.univ : Finset (ZMod p)ˣ).filter (fun z => z ^ 2 = a)
  have hmaps : Set.MapsTo (fun rs : (ZMod p)ˣ × (ZMod p)ˣ => rs.2 / rs.1) S T := by
    intro rs hrs
    have hmap := (Finset.mem_filter.mp hrs).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact congrArg Prod.fst hmap
  have hinj : (S : Set ((ZMod p)ˣ × (ZMod p)ˣ)).InjOn
      (fun rs => rs.2 / rs.1) := by
    intro rs hrs uv huv hratio
    have hrs' := (Finset.mem_filter.mp hrs).2
    have huv' := (Finset.mem_filter.mp huv).2
    have hn : affineParameters rs.1 rs.2 ≠ (1, 0) := by simpa only [hrs'] using hnon
    have h := affineParameters_ratio_injective hn (hrs'.trans huv'.symm) hratio
    exact Prod.ext h.1 h.2
  exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans
    (unit_square_fiber_card_le_two Finset.univ a)

end Ostmann

end OAI
