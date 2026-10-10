import OAI.Probability.ClassicalON.TorusFourier

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

abbrev DyadicFreq (k : ℕ) := Σ j : Fin k, Fin (2^j.val) × Fin (2*2^j.val+1)

def dyadicRadius {k : ℕ} (p : DyadicFreq k) : ℕ := 2^p.1.val

def dyadicPoint {k : ℕ} (p : DyadicFreq k) : ℤ × ℤ :=
  ((dyadicRadius p : ℤ)+p.2.1.val, (p.2.2.val:ℤ)-dyadicRadius p)

theorem dyadicRadius_pos {k : ℕ} (p : DyadicFreq k) : 0 < dyadicRadius p := by
  unfold dyadicRadius
  positivity

theorem dyadicRadius_le {k : ℕ} (p : DyadicFreq k) : dyadicRadius p ≤ 2^k := by
  exact Nat.pow_le_pow_right (by decide) p.1.isLt.le

theorem dyadicPoint_bounds {k : ℕ} (p : DyadicFreq k) :
    (dyadicRadius p:ℤ) ≤ (dyadicPoint p).1 ∧ (dyadicPoint p).1 < 2*dyadicRadius p ∧
      -(dyadicRadius p:ℤ) ≤ (dyadicPoint p).2 ∧ (dyadicPoint p).2 ≤ dyadicRadius p := by
  have h1 := p.2.1.isLt
  have h2 := p.2.2.isLt
  simp only [dyadicPoint, dyadicRadius]
  omega

theorem dyadicPoint_injective {k : ℕ} : Function.Injective (dyadicPoint (k := k)) := by
  intro p q he
  have hf := congrArg Prod.fst he
  have hs := congrArg Prod.snd he
  have hp := dyadicPoint_bounds p
  have hq := dyadicPoint_bounds q
  have hj : p.1 = q.1 := by
    apply Fin.ext
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hr : 2*dyadicRadius p ≤ dyadicRadius q := by
        have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) (Nat.succ_le_of_lt hlt)
        simpa only [dyadicRadius, pow_succ, Nat.mul_comm] using hh
      have hr' : (2*dyadicRadius p:ℤ) ≤ dyadicRadius q := by exact_mod_cast hr
      omega
    · have hr : 2*dyadicRadius q ≤ dyadicRadius p := by
        have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) (Nat.succ_le_of_lt hgt)
        simpa only [dyadicRadius, pow_succ, Nat.mul_comm] using hh
      have hr' : (2*dyadicRadius q:ℤ) ≤ dyadicRadius p := by exact_mod_cast hr
      omega
  rcases p with ⟨j,a,b⟩
  rcases q with ⟨j',a',b'⟩
  dsimp only at hj
  subst j'
  have ha : a = a' := by apply Fin.ext; simp only [dyadicPoint, dyadicRadius] at hf; omega
  have hb : b = b' := by apply Fin.ext; simp only [dyadicPoint, dyadicRadius] at hs; omega
  subst a'; subst b'; rfl

theorem zmod_cast_inj_interval (L : ℕ) (c a b : ℤ)
    (ha : c ≤ a ∧ a < c+L) (hb : c ≤ b ∧ b < c+L)
    (he : (a:ZMod L) = (b:ZMod L)) : a=b := by
  have hh : ((a-c:ℤ):ZMod L) = ((b-c:ℤ):ZMod L) := by simpa only [Int.cast_sub] using congrArg (fun z : ZMod L => z-(c:ZMod L)) he
  have ha' : a-c ∈ Set.Ico (0:ℤ) L := by constructor <;> omega
  have hb' : b-c ∈ Set.Ico (0:ℤ) L := by constructor <;> omega
  have hz := CharP.intCast_injOn_Ico (R := ZMod L) L ha' hb' hh
  omega

def dyadicTorusPoint {k : ℕ} (p : DyadicFreq k) : DiscreteTorus (16*2^k) :=
  (((dyadicPoint p).1:ZMod (16*2^k)), ((dyadicPoint p).2:ZMod (16*2^k)))

theorem dyadicTorusPoint_injective {k : ℕ} : Function.Injective (dyadicTorusPoint (k := k)) := by
  intro p q he
  apply dyadicPoint_injective
  apply Prod.ext
  · apply zmod_cast_inj_interval (16*2^k) 0 _ _
    · have hp := dyadicPoint_bounds p; have hr := dyadicRadius_le p; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · have hq := dyadicPoint_bounds q; have hr := dyadicRadius_le q; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.fst he
  · apply zmod_cast_inj_interval (16*2^k) (-(2^k:ℕ):ℤ) _ _
    · have hp := dyadicPoint_bounds p; have hr := dyadicRadius_le p; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · have hq := dyadicPoint_bounds q; have hr := dyadicRadius_le q; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.snd he

theorem dyadic_shell_card_bounds (j : ℕ) :
    2*(2^j)^2 ≤ Fintype.card (Fin (2^j) × Fin (2*2^j+1)) ∧
      Fintype.card (Fin (2^j) × Fin (2*2^j+1)) ≤ 3*(2^j)^2 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  have h : 1 ≤ 2^j := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  constructor <;> nlinarith

end ClassicalON

end

end OAI
