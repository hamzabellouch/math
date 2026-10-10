import OAI.MathematicalPhysics.AlternatingFlow.Model

namespace OAI

section ArithmeticDevelopment

namespace AlternatingNS
namespace Arithmetic

lemma int_natCast : Primrec (fun n : ℕ => (n : ℤ)) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq (fun n => rfl)

lemma int_negSucc : Primrec Int.negSucc := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).of_eq (fun n => rfl)

lemma int_cases {A B : Type*} [Primcodable A] [Primcodable B]
    {f g : A → ℕ → B} (hf : Primrec₂ f) (hg : Primrec₂ g) :
    Primrec (fun z : A × ℤ => (Int.casesOn z.2 (f z.1) (g z.1) : B)) := by
  have hi : Primrec (fun z : A × ℤ => Encodable.encode z.2) := Primrec.encode.comp Primrec.snd
  refine (Primrec.cond (Primrec.nat_bodd.comp hi)
    (hg.comp Primrec.fst (Primrec.nat_div2.comp hi))
    (hf.comp Primrec.fst (Primrec.nat_div2.comp hi))).of_eq ?_
  rintro ⟨a,z⟩
  cases z with
  | ofNat n =>
    change (bif (Nat.bit false n).bodd then g a (Nat.bit false n).div2
      else f a (Nat.bit false n).div2) = f a n
    simp
  | negSucc n =>
    change (bif (Nat.bit true n).bodd then g a (Nat.bit true n).div2
      else f a (Nat.bit true n).div2) = g a n
    simp

lemma int_toNat : Primrec Int.toNat := by
  have h := int_cases (f := fun _ : ℕ => fun n : ℕ => n) (g := fun _ _ => (0 : ℕ))
    Primrec.snd (Primrec.const (0 : ℕ))
  exact (h.comp ((Primrec.const (0 : ℕ)).pair Primrec.id)).of_eq (fun z => by cases z <;> rfl)

lemma int_abs : Primrec Int.natAbs := by
  have h := int_cases (f := fun _ : ℕ => fun n : ℕ => n) (g := fun _ n => n + 1)
    Primrec.snd (Primrec.succ.comp Primrec.snd)
  exact (h.comp ((Primrec.const (0 : ℕ)).pair Primrec.id)).of_eq (fun z => by cases z <;> rfl)

lemma int_diff : Primrec₂ (fun a b : ℕ => (a : ℤ) - b) := by
  refine (Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (int_natCast.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (int_negSucc.comp (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
      (Primrec.const 1)))).of_eq ?_
  rintro ⟨a,b⟩
  dsimp only
  split_ifs <;> omega

lemma int_neg : Primrec (fun z : ℤ => -z) := by
  have h := int_cases (f := fun _ : ℕ => fun n : ℕ => (0 : ℤ) - n)
    (g := fun _ n => (n + 1 : ℕ))
    (int_diff.comp (Primrec.const 0 : Primrec (fun _ : ℕ × ℕ => (0 : ℕ))) Primrec.snd)
    (int_natCast.comp (Primrec.succ.comp Primrec.snd))
  refine (h.comp ((Primrec.const (0 : ℕ)).pair Primrec.id)).of_eq ?_
  intro z
  cases z with
  | ofNat n => change (0 : ℤ) - n = -(n : ℤ); simp
  | negSucc n => change ((n + 1 : ℕ) : ℤ) = -Int.negSucc n; simp

lemma int_add : Primrec₂ (fun a b : ℤ => a + b) := by
  have h := int_diff.comp
    (Primrec.nat_add.comp (int_toNat.comp Primrec.fst) (int_toNat.comp Primrec.snd))
    (Primrec.nat_add.comp (int_toNat.comp (int_neg.comp Primrec.fst))
      (int_toNat.comp (int_neg.comp Primrec.snd)))
  exact h.of_eq (fun z => by push_cast; omega)

lemma int_sub : Primrec₂ (fun a b : ℤ => a - b) :=
  (int_add.comp Primrec.fst (int_neg.comp Primrec.snd)).of_eq (fun _ => (sub_eq_add_neg _ _).symm)

lemma int_mul : Primrec₂ (fun a b : ℤ => a * b) := by
  have hn : Primrec (fun z : ℤ × ℤ => (Int.natAbs z.1 * Int.natAbs z.2 : ℕ)) :=
    Primrec.nat_mul.comp (int_abs.comp Primrec.fst) (int_abs.comp Primrec.snd)
  have hh := Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.fst))
    (Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.snd))
      (int_natCast.comp hn) (int_neg.comp (int_natCast.comp hn)))
    (Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.snd))
      (int_neg.comp (int_natCast.comp hn)) (int_natCast.comp hn))
  refine hh.of_eq ?_
  rintro ⟨a,b⟩
  change (bif (Encodable.encode a).bodd then
    (bif (Encodable.encode b).bodd then ((a.natAbs * b.natAbs : ℕ) : ℤ) else
      -((a.natAbs * b.natAbs : ℕ) : ℤ)) else
    (bif (Encodable.encode b).bodd then -((a.natAbs * b.natAbs : ℕ) : ℤ) else
      ((a.natAbs * b.natAbs : ℕ) : ℤ))) = a * b
  have hsign (z : ℤ) : (Encodable.encode z).bodd = decide (z < 0) := by
    cases z with
    | ofNat n =>
      change (Nat.bit false n).bodd = decide ((n : ℤ) < 0)
      simp
    | negSucc n =>
      change (Nat.bit true n).bodd = decide (Int.negSucc n < 0)
      simp

  rw [hsign a, hsign b]
  simp only [Bool.cond_decide, Nat.cast_mul, Int.natCast_natAbs]
  split_ifs with ha hb hb <;> simp_all [abs_of_neg, abs_of_nonneg, not_lt]

end Arithmetic
end AlternatingNS

namespace AlternatingNS.Arithmetic
lemma nat_dvd : PrimrecRel (fun a b : ℕ => a ∣ b) :=
  (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
    (fun _ => Nat.dvd_iff_mod_eq_zero.symm)

lemma nat_gcd : Primrec₂ Nat.gcd := by
  have h := Primrec.nat_findGreatest (p := fun z : ℕ × ℕ => fun d => d ∣ z.1 ∧ d ∣ z.2)
    (Primrec.nat_add.comp Primrec.fst Primrec.snd)
    ((nat_dvd.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
      (nat_dvd.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
  refine h.of_eq ?_
  rintro ⟨a,b⟩
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨?_, fun _ => ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩, ?_⟩
  · by_cases ha : a = 0
    · simp [ha]
    · exact (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a b)).trans (Nat.le_add_right a b)
  · intro d hd _ hab
    have hpos : 0 < a.gcd b := by
      by_contra hn
      have hz := Nat.gcd_eq_zero_iff.mp (by omega : a.gcd b = 0)
      omega
    exact (not_lt_of_ge (Nat.le_of_dvd hpos (Nat.dvd_gcd hab.1 hab.2))) hd

lemma rat_valid : PrimrecPred (fun z : ℤ × ℕ => 0 < z.2 ∧ z.1.natAbs.Coprime z.2) :=
  (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
    (Primrec.eq.comp (nat_gcd.comp (int_abs.comp Primrec.fst) Primrec.snd) (Primrec.const 1))

def ratEquiv : ℚ ≃ {z : ℤ × ℕ // 0 < z.2 ∧ z.1.natAbs.Coprime z.2} where
  toFun q := ⟨(q.num,q.den), q.den_pos, q.reduced⟩
  invFun q := ⟨q.1.1,q.1.2, Nat.ne_of_gt q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible] def rationalCoding : Primcodable ℚ := by
  letI := Primcodable.subtype rat_valid
  exact Primcodable.ofEquiv _ ratEquiv

lemma rationalCoding_encode (q : ℚ) :
    @Encodable.encode ℚ rationalCoding.toEncodable q = Encodable.encode q := rfl

attribute [local instance] rationalCoding

lemma rat_num : Primrec Rat.num := by
  let := Primcodable.subtype rat_valid
  have := Primrec.fst.comp (Primrec.subtype_val (hp := rat_valid))
  exact this.comp (Primrec.of_equiv (e := ratEquiv))

lemma rat_den : Primrec Rat.den := by
  let := Primcodable.subtype rat_valid
  exact (Primrec.snd.comp (Primrec.subtype_val (hp := rat_valid))).comp
    (Primrec.of_equiv (e := ratEquiv))

lemma int_ediv_nat : Primrec₂ (fun z : ℤ => fun d : ℕ => z / (d : ℤ)) := by
  have h := int_cases
    (f := fun d n : ℕ => ((n / d : ℕ) : ℤ))
    (g := fun d n => if d = 0 then 0 else Int.negSucc (n / d))
    (int_natCast.comp (Primrec.nat_div.comp Primrec.snd Primrec.fst))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
      (int_negSucc.comp (Primrec.nat_div.comp Primrec.snd Primrec.fst)))
  refine (h.comp (Primrec.snd.pair Primrec.fst)).of_eq ?_
  rintro ⟨z,d⟩
  cases z with
  | ofNat n => exact Int.natCast_ediv n d
  | negSucc n => cases d <;> rfl

lemma rat_mk : Primrec₂ mkRat := by
  have hz : PrimrecPred (fun z : ℤ × ℕ => z.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hg : Primrec (fun z : ℤ × ℕ => z.2.gcd z.1.natAbs) :=
    nat_gcd.comp Primrec.snd (int_abs.comp Primrec.fst)
  have hn := Primrec.ite hz (Primrec.const (0 : ℤ)) (int_ediv_nat.comp Primrec.fst hg)
  have hd := Primrec.ite hz (Primrec.const (1 : ℕ)) (Primrec.nat_div.comp Primrec.snd hg)
  apply Primrec.encode_iff.mp
  refine (Primrec₂.natPair.comp (Primrec.encode.comp hn) hd).of_eq ?_
  rintro ⟨n,d⟩
  change Nat.pair (Encodable.encode (if d = 0 then (0 : ℤ) else n / ↑(d.gcd n.natAbs)))
    (if d = 0 then 1 else d / d.gcd n.natAbs) =
    Nat.pair (Encodable.encode (mkRat n d).num) (mkRat n d).den
  rw [Rat.num_mkRat, Rat.den_mkRat]

lemma rat_intCast : Primrec (fun n : ℤ => (n : ℚ)) := by
  exact (rat_mk.comp Primrec.id (Primrec.const 1)).of_eq (fun n => by simp [Rat.mkRat_eq_div])

lemma rat_natCast : Primrec (fun n : ℕ => (n : ℚ)) :=
  (rat_intCast.comp int_natCast).of_eq (fun n => by simp)

lemma rat_add : Primrec₂ (fun a b : ℚ => a + b) := by
  have hn := int_add.comp
    (int_mul.comp (rat_num.comp Primrec.fst) (int_natCast.comp (rat_den.comp Primrec.snd)))
    (int_mul.comp (rat_num.comp Primrec.snd) (int_natCast.comp (rat_den.comp Primrec.fst)))
  have hd := Primrec.nat_mul.comp (rat_den.comp Primrec.fst) (rat_den.comp Primrec.snd)
  exact (rat_mk.comp hn hd).of_eq (fun z => by
    dsimp only
    rw [Rat.add_def, Rat.normalize_eq_mkRat])

lemma rat_mul : Primrec₂ (fun a b : ℚ => a * b) := by
  exact (rat_mk.comp (int_mul.comp (rat_num.comp Primrec.fst) (rat_num.comp Primrec.snd))
    (Primrec.nat_mul.comp (rat_den.comp Primrec.fst) (rat_den.comp Primrec.snd))).of_eq
    (fun z => (Rat.mul_eq_mkRat z.1 z.2).symm)

lemma rat_neg : Primrec (fun a : ℚ => -a) := by
  refine (rat_mk.comp (int_neg.comp rat_num) rat_den).of_eq ?_
  intro q
  rw [Rat.mkRat_eq_div, Int.cast_neg, neg_div, Rat.num_div_den]

lemma rat_sub : Primrec₂ (fun a b : ℚ => a - b) :=
  (rat_add.comp Primrec.fst (rat_neg.comp Primrec.snd)).of_eq (fun _ => (sub_eq_add_neg _ _).symm)

lemma int_le : PrimrecRel (fun a b : ℤ => a ≤ b) :=
  (Primrec.eq.comp (int_toNat.comp int_sub) (Primrec.const 0)).of_eq (fun z => by
    dsimp only; omega)

lemma int_lt : PrimrecRel (fun a b : ℤ => a < b) :=
  (int_le.comp Primrec.snd Primrec.fst).not.of_eq (fun z => by simp)

lemma rat_divInt : Primrec₂ Rat.divInt := by
  have h := int_cases (f := fun a : ℤ => fun d : ℕ => mkRat a d)
    (g := fun a d => mkRat (-a) (d + 1)) rat_mk
    (rat_mk.comp (int_neg.comp Primrec.fst) (Primrec.succ.comp Primrec.snd))
  refine h.of_eq ?_
  rintro ⟨n,d⟩
  cases d with
  | ofNat d => rfl
  | negSucc d => exact (Rat.normalize_eq_mkRat (Nat.succ_ne_zero d)).symm

lemma rat_inv : Primrec (fun q : ℚ => q⁻¹) :=
  (rat_divInt.comp (int_natCast.comp rat_den) rat_num).of_eq (fun q => (Rat.inv_def q).symm)

lemma rat_div : Primrec₂ (fun a b : ℚ => a / b) :=
  (rat_mul.comp Primrec.fst (rat_inv.comp Primrec.snd)).of_eq
    (fun _ => (div_eq_mul_inv _ _).symm)

lemma rat_le : PrimrecRel (fun a b : ℚ => a ≤ b) :=
  (int_le.comp
    (int_mul.comp (rat_num.comp Primrec.fst) (int_natCast.comp (rat_den.comp Primrec.snd)))
    (int_mul.comp (rat_num.comp Primrec.snd) (int_natCast.comp (rat_den.comp Primrec.fst)))).of_eq
    (fun z => (Rat.le_iff z.1 z.2).symm)

lemma rat_lt : PrimrecRel (fun a b : ℚ => a < b) :=
  (rat_le.comp Primrec.snd Primrec.fst).not.of_eq (fun _ => by simp)

lemma rat_abs : Primrec (fun a : ℚ => |a|) :=
  (Primrec.ite (rat_le.comp (Primrec.const 0) Primrec.id) Primrec.id rat_neg).of_eq
    (fun a => by
      change (if 0 ≤ a then a else -a) = |a|
      split_ifs with h
      · exact (abs_of_nonneg h).symm
      · exact (abs_of_neg (lt_of_not_ge h)).symm)

lemma rat_floor : Primrec (fun q : ℚ => ⌊q⌋) := by
  change Primrec Rat.floor
  exact (int_ediv_nat.comp rat_num rat_den).of_eq (fun q => (Rat.floor_def q).symm)

lemma rat_pow : Primrec₂ (fun q : ℚ => fun n : ℕ => q ^ n) := by
  have hs : Primrec₂ (fun q : ℚ => fun z : ℕ × ℚ => z.2 * q) :=
    rat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  refine (Primrec.nat_rec (Primrec.const (1 : ℚ)) hs).of_eq ?_
  intro q n
  induction n with
  | zero => simp
  | succ n ih => simpa only [ih] using (pow_succ q n).symm

end AlternatingNS.Arithmetic

end ArithmeticDevelopment

end OAI
