import Mathlib
import OAI.MathematicalPhysics.SheetFlows.RationalBalls

namespace OAI

/-! SheetFlows computing. -/

section
open Encodable
namespace Solenoidal.Computing

theorem gcd_findGreatest (a b : ℕ) :
    Nat.findGreatest (fun d => d ∣ a ∧ d ∣ b) (a+b) = Nat.gcd a b := by
  by_cases h : a+b=0
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    simp [ha,hb]
  have hg : 0 < Nat.gcd a b := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simpa using (show 0 < b by omega)
    · exact Nat.gcd_pos_of_pos_left b ha
  apply le_antisymm
  · have hh := Nat.findGreatest_spec (P := fun d => d ∣ a ∧ d ∣ b)
      (show 1 ≤ a+b by omega) (show 1 ∣ a ∧ 1 ∣ b from ⟨one_dvd _,one_dvd _⟩)
    exact Nat.le_of_dvd hg (Nat.dvd_gcd hh.1 hh.2)
  · apply Nat.le_findGreatest
    · rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · exact (Nat.gcd_le_left b ha).trans (Nat.le_add_right a b)
    · exact ⟨Nat.gcd_dvd_left _ _,Nat.gcd_dvd_right _ _⟩

theorem nat_dvd : PrimrecRel ((· ∣ ·) : ℕ → ℕ → Prop) :=
  (Primrec.eq.comp (Primrec.nat_mod.comp .snd .fst) (.const 0)).of_eq
    (fun _ => Nat.dvd_iff_mod_eq_zero.symm)

theorem nat_gcd : Primrec₂ Nat.gcd := by
  refine (Primrec.nat_findGreatest Primrec.nat_add
    (((nat_dvd.comp .snd (Primrec.fst.comp .fst)).and
      (nat_dvd.comp .snd (Primrec.snd.comp .fst))).primrecRel)).of_eq ?_
  intro p
  exact gcd_findGreatest p.1 p.2

@[simp] theorem encode_int_ofNat (n : ℕ) : encode (Int.ofNat n) = 2*n := rfl
@[simp] theorem encode_int_negSucc (n : ℕ) : encode (Int.negSucc n) = 2*n+1 := rfl

theorem int_ofNat : Primrec Int.ofNat :=
  Primrec.encode_iff.mp (Primrec.nat_mul.comp (.const 2) .id)

theorem int_negSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 2) .id) (.const 1))

def intToSum : ℤ → ℕ ⊕ ℕ := fun z => Int.casesOn z Sum.inl Sum.inr

theorem intToSum_pr : Primrec intToSum :=
  Primrec.encode_iff.mp (Primrec.encode.of_eq (by intro z; cases z <;> rfl))

theorem int_cases {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℤ} {g h : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec (fun a => Int.casesOn (motive := fun _ => β) (f a) (g a) (h a)) :=
  (Primrec.sumCasesOn (intToSum_pr.comp hf) hg hh).of_eq
    (fun a => by cases f a <;> rfl)

theorem int_natAbs : Primrec Int.natAbs :=
  (int_cases .id .right (Primrec.succ.comp₂ .right)).of_eq
    (fun z => by cases z <;> rfl)

theorem int_neg : Primrec ((- ·) : ℤ → ℤ) := by
  have h : Primrec (fun z : ℤ => Int.casesOn (motive := fun _ => ℤ) z
      (fun n => Nat.casesOn n (0 : ℤ) Int.negSucc) (fun n => Int.ofNat (n+1))) := by
    exact int_cases .id
      (Primrec.nat_casesOn .snd (.const 0) (int_negSucc.comp .snd).to₂)
      (int_ofNat.comp (Primrec.succ.comp .snd))
  exact h.of_eq (fun z => by cases z with
    | ofNat n => cases n <;> rfl
    | negSucc n => rfl)

theorem int_subNatNat : Primrec₂ Int.subNatNat := by
  refine (Primrec.ite Primrec.nat_le
    (Primrec.nat_casesOn (Primrec.nat_sub.comp .snd .fst) (.const 0)
      (int_negSucc.comp .snd).to₂)
    (int_ofNat.comp (Primrec.nat_sub.comp .fst .snd))).of_eq ?_
  intro p
  simp only [Int.subNatNat]
  split <;> rename_i h
  · split <;> simp_all
  · split <;> simp_all; omega

theorem int_add : Primrec₂ ((·+·) : ℤ → ℤ → ℤ) := by
  let f : ℤ×ℤ → ℤ := fun p => Int.casesOn p.1
    (fun n => Int.casesOn p.2 (fun m => Int.ofNat (n+m))
      (fun m => Int.subNatNat n (m+1)))
    (fun n => Int.casesOn p.2 (fun m => Int.subNatNat m (n+1))
      (fun m => Int.negSucc (n+m+1)))
  have h : Primrec f := by
    apply int_cases .fst
    · apply int_cases (Primrec.snd.comp .fst)
      · exact int_ofNat.comp (Primrec.nat_add.comp (Primrec.snd.comp .fst) .snd)
      · exact int_subNatNat.comp (Primrec.snd.comp .fst) (Primrec.succ.comp .snd)
    · apply int_cases (Primrec.snd.comp .fst)
      · exact int_subNatNat.comp .snd (Primrec.succ.comp (Primrec.snd.comp .fst))
      · exact int_negSucc.comp (Primrec.succ.comp
          (Primrec.nat_add.comp (Primrec.snd.comp .fst) .snd))
  exact h.of_eq (fun ⟨a,b⟩ => by cases a <;> cases b <;> rfl)

theorem int_mul : Primrec₂ ((·*·) : ℤ → ℤ → ℤ) := by
  let f : ℤ×ℤ → ℤ := fun p => Int.casesOn p.1
    (fun n => Int.casesOn p.2 (fun m => Int.ofNat (n*m))
      (fun m => -(Int.ofNat (n*(m+1)))))
    (fun n => Int.casesOn p.2 (fun m => -(Int.ofNat ((n+1)*m)))
      (fun m => Int.ofNat ((n+1)*(m+1))))
  have h : Primrec f := by
    apply int_cases .fst
    · apply int_cases (Primrec.snd.comp .fst)
      · exact int_ofNat.comp (Primrec.nat_mul.comp (Primrec.snd.comp .fst) .snd)
      · exact int_neg.comp (int_ofNat.comp (Primrec.nat_mul.comp
          (Primrec.snd.comp .fst) (Primrec.succ.comp .snd)))
    · apply int_cases (Primrec.snd.comp .fst)
      · exact int_neg.comp (int_ofNat.comp (Primrec.nat_mul.comp
          (Primrec.succ.comp (Primrec.snd.comp .fst)) .snd))
      · exact int_ofNat.comp (Primrec.nat_mul.comp
          (Primrec.succ.comp (Primrec.snd.comp .fst)) (Primrec.succ.comp .snd))
  exact h.of_eq (fun ⟨a,b⟩ => by cases a <;> cases b <;> rfl)

theorem int_edivNat : Primrec₂ (fun (z : ℤ) (n : ℕ) => z / (n:ℤ)) := by
  let f : ℤ×ℕ → ℤ := fun p => Int.casesOn p.1
    (fun m => Int.ofNat (m / p.2))
    (fun m => Nat.casesOn p.2 0 (fun n => Int.negSucc (m / (n+1))))
  have h : Primrec f := by
    apply int_cases .fst
    · exact int_ofNat.comp (Primrec.nat_div.comp .snd (Primrec.snd.comp .fst))
    · exact Primrec.nat_casesOn (Primrec.snd.comp .fst) (.const 0)
        (int_negSucc.comp (Primrec.nat_div.comp (Primrec.snd.comp .fst)
          (Primrec.succ.comp .snd))).to₂
  exact h.of_eq (fun ⟨a,b⟩ => by cases a <;> cases b <;> rfl)

theorem int_nonneg : PrimrecPred (fun z : ℤ => 0 ≤ z) := by
  refine ⟨inferInstance, ?_⟩
  refine (int_cases .id (Primrec₂.const true) (Primrec₂.const false)).of_eq ?_
  intro z
  cases z with
  | ofNat n => change true = decide (0 ≤ (n:ℤ)); simp
  | negSucc n => rfl

theorem int_le : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) :=
  (int_nonneg.comp (int_add.comp .snd (int_neg.comp .fst))).of_eq
    (fun p => by simp [← sub_eq_add_neg])

theorem int_lt : PrimrecRel ((· < ·) : ℤ → ℤ → Prop) :=
  ((int_le.comp .snd .fst).not).of_eq (fun _ => not_le)

def ratValid (p : ℤ×ℕ) : Prop := 0 < p.2 ∧ p.1.natAbs.Coprime p.2

instance : DecidablePred ratValid := fun p => inferInstanceAs
  (Decidable (0 < p.2 ∧ p.1.natAbs.Coprime p.2))

theorem ratValid_pr : PrimrecPred ratValid :=
  (Primrec.nat_lt.comp (.const 0) .snd).and
    ((Primrec.eq.comp (nat_gcd.comp (int_natAbs.comp .fst) .snd) (.const 1)).of_eq
      (fun _ => Iff.rfl))

instance ratPairPrimcodable : Primcodable {p : ℤ×ℕ // ratValid p} :=
  Primcodable.subtype ratValid_pr

def ratEquiv : ℚ ≃ {p : ℤ×ℕ // ratValid p} where
  toFun q := ⟨(q.num,q.den),q.den_pos,q.reduced⟩
  invFun p := ⟨p.1.1,p.1.2,ne_of_gt p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance ratPrimcodable : Primcodable ℚ := Primcodable.ofEquiv _ ratEquiv

theorem rat_encoding (q : ℚ) :
    @encode ℚ ratPrimcodable.toEncodable q = @encode ℚ Rat.instEncodable q := rfl

theorem rat_num : Primrec Rat.num :=
  Primrec.fst.comp (Primrec.subtype_val.comp (Primrec.of_equiv (e := ratEquiv)))

theorem rat_den : Primrec Rat.den :=
  Primrec.snd.comp (Primrec.subtype_val.comp (Primrec.of_equiv (e := ratEquiv)))

theorem rat_mk_iff {α : Type*} [Primcodable α] {f : α → ℚ} :
    Primrec f ↔ Primrec (fun a => (f a).num) ∧ Primrec (fun a => (f a).den) := by
  refine ⟨fun h => ⟨rat_num.comp h,rat_den.comp h⟩, fun h => ?_⟩
  exact (Primrec.of_equiv_iff ratEquiv).mp
    ((Primrec.subtype_val_iff).mp (h.1.pair h.2))

theorem rat_mk : Primrec₂ mkRat := by
  apply rat_mk_iff.mpr
  constructor
  · exact (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 0)
      (int_edivNat.comp .fst (nat_gcd.comp .snd (int_natAbs.comp .fst)))).of_eq
        (fun p => (Rat.num_mkRat p.1 p.2).symm)
  · exact (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 1)
      (Primrec.nat_div.comp .snd (nat_gcd.comp .snd (int_natAbs.comp .fst)))).of_eq
        (fun p => (Rat.den_mkRat p.1 p.2).symm)

theorem rat_int : Primrec (fun z : ℤ => (z:ℚ)) :=
  rat_mk_iff.mpr ⟨.id,.const 1⟩

theorem rat_nat : Primrec (fun n : ℕ => (n:ℚ)) := rat_int.comp int_ofNat

theorem rat_neg : Primrec (fun q : ℚ => -q) :=
  rat_mk_iff.mpr ⟨int_neg.comp rat_num,rat_den⟩

theorem rat_add : Primrec₂ ((·+·) : ℚ → ℚ → ℚ) :=
  (rat_mk.comp (int_add.comp
    (int_mul.comp (rat_num.comp .fst) (int_ofNat.comp (rat_den.comp .snd)))
    (int_mul.comp (rat_num.comp .snd) (int_ofNat.comp (rat_den.comp .fst))))
    (Primrec.nat_mul.comp (rat_den.comp .fst) (rat_den.comp .snd))).of_eq
      (fun p => (Rat.add_def' p.1 p.2).symm)

theorem rat_sub : Primrec₂ ((·-·) : ℚ → ℚ → ℚ) :=
  (rat_add.comp .fst (rat_neg.comp .snd)).of_eq (fun _ => (sub_eq_add_neg ..).symm)

theorem rat_mul : Primrec₂ ((·*·) : ℚ → ℚ → ℚ) :=
  (rat_mk.comp (int_mul.comp (rat_num.comp .fst) (rat_num.comp .snd))
    (Primrec.nat_mul.comp (rat_den.comp .fst) (rat_den.comp .snd))).of_eq
      (fun p => by conv_rhs => rw [← Rat.mkRat_self p.1, ← Rat.mkRat_self p.2]
                   exact (Rat.mkRat_mul_mkRat ..).symm)

theorem rat_le : PrimrecRel ((·≤·) : ℚ → ℚ → Prop) :=
  (int_le.comp
    (int_mul.comp (rat_num.comp .fst) (int_ofNat.comp (rat_den.comp .snd)))
    (int_mul.comp (rat_num.comp .snd) (int_ofNat.comp (rat_den.comp .fst)))).of_eq
      (fun p => (Rat.le_iff (a := p.1) (b := p.2)).symm)

theorem rat_lt : PrimrecRel ((·<·) : ℚ → ℚ → Prop) :=
  ((rat_le.comp .snd .fst).not).of_eq (fun _ => not_le)

theorem rat_abs : Primrec (fun q : ℚ => |q|) :=
  (Primrec.ite (rat_le.comp (.const 0) .id) .id rat_neg).of_eq
    (fun q => by by_cases h : 0 ≤ q
                 · simp [h,abs_of_nonneg h]
                 · simp [h,abs_of_neg (lt_of_not_ge h)])

theorem rat_inv : Primrec (fun q : ℚ => q⁻¹) := by
  have h : Primrec (fun q : ℚ =>
      if q.num < 0 then mkRat (-(q.den:ℤ)) q.num.natAbs
      else mkRat (q.den:ℤ) q.num.natAbs) :=
    Primrec.ite (int_lt.comp rat_num (.const 0))
      (rat_mk.comp (int_neg.comp (int_ofNat.comp rat_den)) (int_natAbs.comp rat_num))
      (rat_mk.comp (int_ofNat.comp rat_den) (int_natAbs.comp rat_num))
  refine h.of_eq ?_
  intro q
  rw [Rat.inv_def]
  cases q.num with
  | ofNat numerator => simp [Rat.divInt]
  | negSucc numerator => simp [Rat.divInt,Rat.normalize_eq_mkRat]

theorem rat_div : Primrec₂ ((·/·) : ℚ → ℚ → ℚ) :=
  (rat_mul.comp .fst (rat_inv.comp .snd)).of_eq (fun _ => (div_eq_mul_inv ..).symm)

theorem rat_max : Primrec₂ ((max) : ℚ → ℚ → ℚ) :=
  (Primrec.ite rat_le .snd .fst).of_eq (fun _ => rfl)

theorem rat_pow : Primrec₂ ((·^·) : ℚ → ℕ → ℚ) := by
  exact (Primrec.nat_rec (.const 1)
    (rat_mul.comp (Primrec.snd.comp .snd) .fst).to₂).of_eq
      (fun q n => by induction n with
        | zero => simp
        | succ n ih => simp_all [pow_succ])

theorem nat_factorial : Primrec Nat.factorial := by
  have h : Primrec (fun n : ℕ => Nat.rec (motive := fun _ => ℕ) 1 (fun m r => (m+1)*r) n) :=
    Primrec.nat_rec₁ 1
      (Primrec.nat_mul.comp (Primrec.succ.comp .fst) .snd)
  exact h.of_eq (fun n => by induction n with
    | zero => rfl
    | succ n ih => simp [Nat.factorial_succ,ih])

theorem rat_floor : Primrec (fun q : ℚ => ⌊q⌋) :=
  (int_edivNat.comp rat_num rat_den).of_eq (fun q => by
    change q.num / (q.den:ℤ) = q.floor
    exact (Rat.floor_def q).symm)

end Solenoidal.Computing
end

section
open Encodable
open scoped BigOperators
namespace Solenoidal.Computing

theorem ball_point : Primrec QBall.point := Primrec.id.pair (.const 0)
theorem ball_add : Primrec₂ QBall.add :=
  (rat_add.comp (Primrec.fst.comp .fst) (Primrec.fst.comp .snd)).pair
    (rat_add.comp (Primrec.snd.comp .fst) (Primrec.snd.comp .snd))
theorem ball_neg : Primrec QBall.neg := (rat_neg.comp .fst).pair .snd

theorem ball_mul : Primrec₂ QBall.mul :=
  (rat_mul.comp (Primrec.fst.comp .fst) (Primrec.fst.comp .snd)).pair
    (rat_add.comp (rat_add.comp
      (rat_mul.comp (rat_abs.comp (Primrec.fst.comp .fst)) (Primrec.snd.comp .snd))
      (rat_mul.comp (rat_abs.comp (Primrec.fst.comp .snd)) (Primrec.snd.comp .fst)))
      (rat_mul.comp (Primrec.snd.comp .fst) (Primrec.snd.comp .snd)))

theorem ball_pow : Primrec₂ QBall.pow :=
  (Primrec.nat_rec (.const (QBall.point 1))
    (ball_mul.comp (Primrec.snd.comp .snd) .fst).to₂).of_eq
      (fun a n => by induction n with
        | zero => rfl
        | succ n ih => simp [QBall.pow,ih])

theorem rat_sum_range {α : Type*} [Primcodable α] {g : α → ℕ → ℚ}
    (hg : Primrec₂ g) : Primrec₂ (fun a n => ∑ i ∈ Finset.range n, g a i) :=
  (Primrec.nat_rec (.const 0)
    (rat_add.comp (Primrec.snd.comp .snd)
      (hg.comp .fst (Primrec.fst.comp .snd))).to₂).of_eq
      (fun a n => by induction n with
        | zero => simp
        | succ n ih => simp [Finset.sum_range_succ,ih])

theorem ball_taylor : Primrec₂ QBall.taylor :=
  rat_sum_range (rat_div.comp rat_pow (rat_nat.comp (nat_factorial.comp .snd)))

theorem ball_smallExp : Primrec₂ QBall.smallExp :=
  (ball_taylor.comp .fst (Primrec.succ.comp .snd)).pair
    (rat_mul.comp (.const 2) (rat_pow.comp (.const (1/2)) (Primrec.succ.comp .snd)))

theorem ball_expScale : Primrec QBall.expScale :=
  Primrec.nat_mul.comp (.const 2) (Primrec.succ.comp (int_natAbs.comp rat_num))

theorem ball_expApprox : Primrec₂ QBall.expApprox :=
  ball_pow.comp (ball_smallExp.comp
    (rat_div.comp .fst (rat_nat.comp (ball_expScale.comp .fst))) .snd)
    (ball_expScale.comp .fst)

theorem ball_clampInv : Primrec QBall.clampInv :=
  (rat_inv.comp (rat_max.comp (.const (1/32)) .fst)).pair
    (rat_mul.comp (.const 512) .snd)

theorem ball_flatApprox : Primrec (fun p : ℕ × ℚ × ℕ => QBall.flatApprox p.1 p.2.1 p.2.2) :=
  Primrec.ite (rat_le.comp (Primrec.fst.comp .snd) (.const 0)) (.const (QBall.point 0))
    (ball_mul.comp (ball_point.comp (rat_pow.comp (rat_inv.comp (Primrec.fst.comp .snd)) .fst))
      (ball_expApprox.comp (rat_neg.comp (rat_inv.comp (Primrec.fst.comp .snd)))
        (Primrec.snd.comp .snd)))

theorem ball_reciprocalApprox : Primrec₂ QBall.reciprocalApprox :=
  ball_clampInv.comp (ball_add.comp
    (ball_flatApprox.comp ((Primrec.const 0).pair (Primrec.fst.pair .snd)))
    (ball_flatApprox.comp ((Primrec.const 0).pair
      ((rat_sub.comp (.const 1) .fst).pair .snd))))

end Solenoidal.Computing
end

end OAI
