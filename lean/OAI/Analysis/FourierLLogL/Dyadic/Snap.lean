import OAI.Analysis.FourierLLogL.Dyadic.Node

/-! # Subgrids, snapping and projecting -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate Real
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic
open Law Node Period Real

variable {M l : ℕ}

private def times_step (l M : ℕ) : ℤ →+ Grid M where
  toFun x := ↑((2^(M-l):ℕ)*(x:ℤ))
  map_zero' := by simp
  map_add' x y := by push_cast; ring

/-- Mesh 2^(M-l) in multiples. -/
def raise (h : l ≤ M) : Grid l →+ Grid M :=
  ZMod.lift (2^l) ⟨times_step l M,by
    change (((↑(2^(M-l):ℕ):ℤ) * ↑(2^l:ℕ) : ℤ):Grid M)=0
    rw [← Nat.cast_mul,← pow_add,show M-l+l=M by omega]
    rw [Int.cast_natCast,ZMod.natCast_self]
    ⟩

def cut (h : l ≤ M) : Grid M →+* Grid l :=
  ZMod.castHom (pow_dvd_pow _ h) _

lemma cut_natCast (h : l ≤ M) (k : ℕ) :
    cut h (k:Grid M) = (k:Grid l) := map_natCast _ _

lemma cut_val (h : l ≤ M) (x : Grid M) :
    cut h x = (x.val:Grid l) := by rw [← cut_natCast h,ZMod.natCast_zmod_val]

lemma cut_mod (h : l ≤ M) (x : Grid M) :
    (cut h x).val = x.val % 2^l := by rw [cut_val,ZMod.val_natCast]

lemma raise_cast (h : l ≤ M) (x : ℕ) :
    raise h (x : Grid l) = (↑(2^(M-l)*x:ℕ):Grid M) := by
  have H : ∀ k : ℤ, raise h (k:Grid l) = times_step l M k := fun k => ZMod.lift_coe _ _ _
  convert H x using 1 <;> simp [times_step]

lemma raise_eq (h : l ≤ M) (x : Grid l) :
    raise h x = ↑(2^(M-l)*x.val:ℕ) := by rw [← raise_cast h,ZMod.natCast_zmod_val]

lemma raise_val (h : l ≤ M) (x : Grid l) :
    (raise h x).val = 2^(M-l)*x.val := by
  rw [raise_eq,ZMod.val_natCast_of_lt]
  calc
    _ < 2^(M-l)*2^l := Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

lemma raise_inj (h : l ≤ M) : Injective (raise h) := by
  intro x y he
  apply ZMod.val_injective _
  have H := congrArg ZMod.val he
  simp only [raise_val] at H
  exact mul_left_cancel₀ (by positivity) H

lemma raised_pos (h : l ≤ M) (i : Grid l) : pos (raise h i) = pos i := by
  simp only [pos,raise_val]
  have heq : side l = side M*(2:ℝ)^(M-l) := descale (p:=⟨l,0⟩) h
  rw [heq]; push_cast; ring

lemma cut_chi (h : l ≤ M) (i : Grid l) (x : Grid M) :
    chi (raise h i) x = chi i (cut h x) := by
  rw [cut_val,chi_comm i _,chi_comm (raise h i) x]
  have heq (x : ℕ) : chi (x:Grid M) (raise h i) = chi (x:Grid l) i := by
    have H := chi_cast (x:ℤ) (raise h i)
    have hh := chi_cast (x:ℤ) i
    rw [raised_pos] at H
    simpa only [Int.cast_natCast] using H.trans hh.symm
  rw [← heq, ZMod.natCast_zmod_val x]

lemma annihilator (h : l ≤ M) (u : Grid M) :
    cut (show M-l ≤ M by omega) u = 0 ↔ ∃ i, raise h i = u := by
  let p := cut (show M-l ≤ M by omega)
  have he (u : Grid M) : p u = 0 ↔ 2^(M-l) ∣ u.val := by
    rw [← (ZMod.val_injective (2^(M-l))).eq_iff]
    simp only [p,cut_mod,ZMod.val_zero,Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro hu
    obtain ⟨i,hi⟩ := (he _).mp hu
    refine ⟨(i:Grid l),?_⟩
    rw [raise_cast,← hi,ZMod.natCast_zmod_val]
  rintro ⟨i,rfl⟩
  exact (he _).mpr (by rw [raise_val]; simp)

/-- A snap (rounding down). -/
def down (_h : l ≤ M) (u : Grid M) : Grid l :=
  ↑(u.val / 2^(M-l))

lemma raise_down (h : l ≤ M) (u : Grid M) :
    u - raise h (down h u) = (↑(u.val % 2^(M-l)):Grid M) := by
  have hh := Nat.mod_add_div u.val (2^(M-l))
  unfold down; rw [raise_cast]
  apply sub_eq_iff_eq_add.mpr; rw [← Nat.cast_add,hh,ZMod.natCast_zmod_val]

lemma snap_dist (h : l ≤ M) (u : Grid M) :
    rad (u-raise h (down h u)) ≤ 2^(M-l)-1 := by
  rw [raise_down]
  apply le_trans (rad_le_nat _)
  have H : u.val % 2^(M-l) +1 ≤ 2^(M-l) := Nat.mod_lt _ (by positivity)
  apply le_sub_iff_add_le.mpr
  exact_mod_cast H

lemma cut_injOn {p : Node} (h : l ≤ M) (hp : p.lev ≤ M) (hh : M-l ≤ p.lev) :
    InjOn (cut h) (p.block M) := by
  intro x hx y hy hxy
  apply ZMod.val_injective _
  have HE := congrArg ZMod.val hxy
  simp only [cut_mod] at HE
  rw [mem_block_iff hp x] at hx; rw [mem_block_iff hp y] at hy
  let a := 2^(M-p.lev)
  let b := 2^l
  let i := p.ix
  change i*a ≤ _ ∧ _ < (i+1)*a at hx hy
  rw [add_mul,one_mul] at hx hy
  have h1 := Nat.mod_add_div x.val b
  have h2 := Nat.mod_add_div y.val b
  have hi : a ≤ b := Nat.pow_le_pow_right (by omega) (by omega)
  change _ % b = _ % b at HE
  have h3 : x.val/b=y.val/b := by
    by_contra! he
    rcases lt_or_gt_of_ne he with H|H
    · have Hx : b*(x.val/b +1) ≤ b*(y.val/b) := Nat.mul_le_mul_left b H
      rw [mul_add,mul_one] at Hx; omega
    · have Hx : b*(y.val/b +1) ≤ b*(x.val/b) := Nat.mul_le_mul_left b H
      rw [mul_add,mul_one] at Hx; omega
  rw [HE,h3,h2] at h1; exact h1.symm

/-- Projection density bound for any input sublaw on p. -/
lemma cut_send {p : Node} (h : l ≤ M) (hp : p.ok M) (hh : M-l ≤ p.lev)
    (P : Law (Grid M)) (a : ℝ) (ha : 0 ≤ a)
    (H : ∀ x, P x ≤ a*p.dice M x) (i : Grid l) :
    P.send (cut h) i ≤ a*p.invlen*side M := by
  classical
  rcases eq_or_lt_of_le ((P.send (cut h)).nonneg i) with H0|H0
  · rw [← H0]
    have := p.invlen_pos; have := side_pos M; positivity
  obtain ⟨x,hx,hx'⟩ := (P.send_pos_iff _ _).mp H0
  have he {x : Grid M} (hh : 0 < P x) : x∈p.block M := by
    have H := lt_of_lt_of_le hh (H x)
    rw [dice_apply hp] at H
    by_contra h'
    rw [ite_eq_right h',mul_zero] at H
    exact lt_irrefl _ H
  rw [send_apply, prob_eq]
  have HX := H x
  rw [dice_apply hp,ite_eq_left (he hx'), p.rinv] at *
  rw [Finset.sum_eq_single x,ite_eq_left hx,mul_right_comm]
  · nlinarith
  · intro j _ hj; split_ifs with hi
    · by_contra hh'
      have h2 : j∈p.block M := he ((P.nonneg j).lt_of_ne (Ne.symm hh'))
      exact hj (cut_injOn h hp.2 hh h2 (he hx') (hi.trans hx.symm))
    rfl
  simp

end FourierLLogL.Dyadic

end OAI
