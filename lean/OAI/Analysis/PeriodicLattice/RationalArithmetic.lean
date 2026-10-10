import OAI.Analysis.PeriodicLattice.FieldCertificates

namespace OAI

/-! Uniform lattice constants and computable reduced rational arithmetic. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingRationalArithmetic {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace RecursiveArithmetic

theorem program_of_computable {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} (hf : Computable f) :
    ∃ P : Program, ∀ a, Encodable.encode (f a) ∈ P.eval (Encodable.encode a) := by
  obtain ⟨P,hP⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨P,fun a => ?_⟩
  rw [hP]
  simp
end RecursiveArithmetic

namespace Quantitative

noncomputable def latticeConstants (ν : ℝ) (N : ℕ) (hν : ‖ν‖ ≤ N)
    (d : Input) (r : ℕ) (α : MultiIndex) (J : ℕ) : ℕ :=
  velocityCertificate.mixedBudget d r α J + (forceCertificate ν N hν).mixedBudget d r α J +
    (solenoidalForceCertificate ν N hν).mixedBudget d r α J

theorem latticeConstants_effective (ν : ℝ) (N : ℕ) (hν : ‖ν‖ ≤ N) :
    EffectiveConstants (latticeConstants ν N hν) := by
  have hc : Primrec (fun p : Input × ℕ × MultiIndex × ℕ =>
      latticeConstants ν N hν p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp velocityCertificate.mixedBudget_recursive
      (forceCertificate ν N hν).mixedBudget_recursive) (solenoidalForceCertificate ν N hν).mixedBudget_recursive
  obtain ⟨P,hP⟩ := RecursiveArithmetic.program_of_computable hc.to_comp
  exact ⟨P,fun d _ r α J => hP (d,r,α,J)⟩

theorem latticeConstants_bounds (ν : ℝ) (N : ℕ) (hν : ‖ν‖ ≤ N) (d : Input) (hd : d.WellFormed) :
    RapidPair (FluidLift.velocity d) (FluidLift.force ν d) (latticeConstants ν N hν d) ∧
    RapidPair (FluidLift.velocity d) (FluidLift.solenoidalForce ν d) (latticeConstants ν N hν d) := by
  have hpair {F G : Input → VectorField} (hf : FieldCertificate F) (hg : FieldCertificate G)
      {C : ℕ → MultiIndex → ℕ → ℕ}
      (hc : ∀ r α J, hf.mixedBudget d r α J + hg.mixedBudget d r α J ≤ C r α J) : RapidPair (F d) (G d) C := by
    intro r J α t ht
    calc
      _ ≤ (hf.mixedBudget d r α J : ℝ) / (1+t)^J + (hg.mixedBudget d r α J : ℝ) / (1+t)^J :=
        add_le_add (hf.sup_estimate d hd r α J ht) (hg.sup_estimate d hd r α J ht)
      _ = ((hf.mixedBudget d r α J + hg.mixedBudget d r α J : ℕ) : ℝ) / (1+t)^J := by rw [Nat.cast_add, add_div]
      _ ≤ _ := div_le_div_of_nonneg_right (Nat.cast_le.mpr (hc r α J)) (by positivity)
  constructor
  · exact hpair velocityCertificate (forceCertificate ν N hν) (fun r α J => Nat.le_add_right _ _)
  · apply hpair velocityCertificate (solenoidalForceCertificate ν N hν)
    intro r α J
    exact Nat.add_le_add_right (Nat.le_add_right _ _) _
end Quantitative

namespace RecursiveArithmetic
open Encodable Primrec

theorem natDvd : PrimrecRel (fun a b : ℕ => a ∣ b) :=
  (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
    (fun _ => Nat.dvd_iff_mod_eq_zero.symm)

def gcdSearch (a b : ℕ) : ℕ :=
  Nat.findGreatest (fun k => k ∣ a ∧ k ∣ b) (a+b)

theorem gcdSearch_eq (a b : ℕ) : gcdSearch a b = Nat.gcd a b := by
  unfold gcdSearch
  by_cases hab : a + b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    simp [ha, hb]
  have hpos : 0 < Nat.gcd a b := Nat.gcd_pos_iff.mpr (by omega)
  have hle : Nat.gcd a b ≤ a + b := Nat.le_of_dvd (by omega)
    (dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b))
  have hs : (Nat.findGreatest (fun k => k ∣ a ∧ k ∣ b) (a+b)) ∣ a ∧
      (Nat.findGreatest (fun k => k ∣ a ∧ k ∣ b) (a+b)) ∣ b :=
    Nat.findGreatest_spec (P := fun k => k ∣ a ∧ k ∣ b) hle ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩
  apply le_antisymm
  · exact Nat.le_of_dvd hpos (Nat.dvd_gcd
      hs.1
      hs.2)
  · exact Nat.le_findGreatest hle ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩

@[fun_prop] theorem nat_gcd : Primrec (fun p : ℕ × ℕ => Nat.gcd p.1 p.2) := by
  have h := Primrec.nat_findGreatest (Primrec.nat_add.comp Primrec.fst Primrec.snd)
    ((natDvd.comp (Primrec.snd) (Primrec.fst.comp Primrec.fst)).and
      (natDvd.comp (Primrec.snd) (Primrec.snd.comp Primrec.fst))).primrecRel
  exact h.of_eq (fun p => gcdSearch_eq p.1 p.2)

theorem natCoprime : PrimrecRel Nat.Coprime :=
  (Primrec.eq.comp nat_gcd (Primrec.const 1)).of_eq (fun _ => Iff.rfl)

theorem reducedPred : PrimrecPred (fun p : ℤ × ℕ => 0 < p.2 ∧ p.1.natAbs.Coprime p.2) :=
  (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
    (natCoprime.comp (intNatAbs.comp Primrec.fst) Primrec.snd)

abbrev ReducedPair := {p : ℤ × ℕ // 0 < p.2 ∧ p.1.natAbs.Coprime p.2}
local instance rationalArithmeticLocal1 : Primcodable ReducedPair := Primcodable.subtype reducedPred

def ratEquiv : ℚ ≃ ReducedPair where
  toFun q := ⟨(q.num, q.den), Nat.pos_of_ne_zero q.den_nz, q.reduced⟩
  invFun p := ⟨p.1.1, p.1.2, Nat.ne_of_gt p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible] def rationalPrimcodable : Primcodable ℚ := Primcodable.ofEquiv _ ratEquiv

private theorem encodable_ext {α : Type*} {e f : Encodable α}
    (he : e.encode = f.encode) (hd : e.decode = f.decode) : e = f := by
  cases e
  cases f
  cases he
  cases hd
  rfl

theorem rational_encoding : rationalPrimcodable.toEncodable = Rat.instEncodable := by
  refine encodable_ext (e := rationalPrimcodable.toEncodable) (f := Rat.instEncodable) rfl ?_
  funext n
  dsimp +instances only [rationalPrimcodable, rationalArithmeticLocal1, Primcodable.ofEquiv, Primcodable.subtype, Primcodable.prod, Primcodable.ofDenumerable, Denumerable.int, Denumerable.nat, ratEquiv,
    Rat.instEncodable, Encodable.ofEquiv, Encodable.ofLeftInverse, Encodable.ofLeftInjection,
    Encodable.decodeSubtype, Encodable.decodeSigma, Encodable.Prod.encodable,
    Subtype.encodable, Sigma.encodable, Int.encodable, Nat.encodable,
    Option.bind_some, Option.map_some, Equiv.symm_symm, Equiv.sigmaEquivProd, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  simp only [Function.comp_apply, Option.bind_some]
  split_ifs with h
  · cases h with
    | intro hp hc => rfl
  · rfl

local instance ratPrimcodable : Primcodable ℚ :=
  { toEncodable := Rat.instEncodable
    prim := by
      rw [← rational_encoding]
      exact @Primcodable.prim ℚ rationalPrimcodable }

@[simp] theorem ratEncoding (q : ℚ) : encode q = Nat.pair (encode q.num) q.den := rfl

@[fun_prop] theorem ratNum : Primrec Rat.num := by
  exact Primrec.encode_iff.mp (((Primrec.fst.comp Primrec.unpair).comp
    (Primrec.encode : Primrec (encode : ℚ → ℕ))).of_eq (fun q => by simp))

@[fun_prop] theorem ratDen : Primrec Rat.den := by
  exact ((Primrec.snd.comp Primrec.unpair).comp
    (Primrec.encode : Primrec (encode : ℚ → ℕ))).of_eq (fun q => by simp)

@[fun_prop] theorem int_div : Primrec (fun p : ℤ × ℤ => p.1 / p.2) := by
  have hc : Primrec (fun p : ℤ × ℤ =>
      if p.2 = 0 then 0 else if p.1 < 0 then
        if p.2 < 0 then (((p.1.natAbs-1) / p.2.natAbs + 1 : ℕ) : ℤ)
        else Int.negSucc ((p.1.natAbs-1) / p.2.natAbs)
      else if p.2 < 0 then -((p.1.natAbs / p.2.natAbs : ℕ) : ℤ)
        else ((p.1.natAbs / p.2.natAbs : ℕ) : ℤ)) := by
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    apply Primrec.ite (intNegative.comp Primrec.fst)
    · apply Primrec.ite (intNegative.comp Primrec.snd)
      · fun_prop
      · exact intNegSucc.comp (by fun_prop)
    · apply Primrec.ite (intNegative.comp Primrec.snd) <;> fun_prop
  exact hc.of_eq (fun p => by
    rcases p with ⟨a,b⟩
    cases a with
    | ofNat a =>
      cases b with
      | ofNat b =>
        simp only [Int.ofNat_eq_natCast, Int.natAbs_natCast,
          not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte, Int.natCast_ediv]
        split_ifs with hb <;> simp_all
      | negSucc b =>
        rw [Int.ofNat_ediv_negSucc]
        simp only [Int.ofNat_eq_natCast, Int.negSucc_ne_zero, Int.negSucc_lt_zero,
          not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte,
          Int.natAbs_natCast, Int.natAbs_negSucc]
    | negSucc a =>
      cases b with
      | ofNat b =>
        cases b with
        | zero => simp
        | succ b => simp only [Int.ofNat_eq_natCast,
          Int.natCast_eq_zero, Nat.succ_ne_zero, Int.negSucc_lt_zero,
          not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte, Int.natAbs_natCast,
          Int.natAbs_negSucc,
          Int.negSucc_ediv_ofNat_succ, Nat.succ_sub_one]
      | negSucc b => simp [Int.negSucc_ediv_negSucc])

@[fun_prop] theorem ratMk : Primrec (fun p : ℤ × ℕ => mkRat p.1 p.2) := by
  apply Primrec.encode_iff.mp
  have hc : Primrec (fun p : ℤ × ℕ =>
      if p.2 = 0 then encode (0 : ℚ) else
      Nat.pair (encode (p.1 / (Nat.gcd p.2 p.1.natAbs : ℤ)))
        (p.2 / Nat.gcd p.2 p.1.natAbs)) := by
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const _)
    apply Primrec₂.natPair.comp
    · exact Primrec.encode.comp (by fun_prop)
    · fun_prop
  exact hc.of_eq (fun p => by
    simp only [ratEncoding, Rat.num_mkRat, Rat.den_mkRat]
    split_ifs <;> simp [*])

@[fun_prop] theorem ratInt : Primrec (fun z : ℤ => (z : ℚ)) := by
  apply Primrec.encode_iff.mp
  exact (Primrec₂.natPair.comp Primrec.encode (Primrec.const 1)).of_eq
    (fun z => by simp)

@[fun_prop] theorem ratNat : Primrec (fun n : ℕ => (n : ℚ)) :=
  (ratInt.comp intOfNat).of_eq (fun _ => by simp)

@[fun_prop] theorem rat_add : Primrec (fun p : ℚ × ℚ => p.1 + p.2) := by
  have hc : Primrec (fun p : ℚ × ℚ =>
      mkRat (p.1.num * p.2.den + p.2.num * p.1.den) (p.1.den * p.2.den)) := by
    exact ratMk.comp (show Primrec (fun p : ℚ × ℚ =>
      (p.1.num * p.2.den + p.2.num * p.1.den, p.1.den * p.2.den)) from by fun_prop)
  exact hc.of_eq (fun p => by simp [Rat.add_def, Rat.normalize_eq_mkRat])

@[fun_prop] theorem rat_mul : Primrec (fun p : ℚ × ℚ => p.1 * p.2) := by
  have hc : Primrec (fun p : ℚ × ℚ => mkRat (p.1.num * p.2.num) (p.1.den * p.2.den)) := by
    exact ratMk.comp (show Primrec (fun p : ℚ × ℚ =>
      (p.1.num * p.2.num, p.1.den * p.2.den)) from by fun_prop)
  exact hc.of_eq (fun p => by simp [Rat.mul_def, Rat.normalize_eq_mkRat])

@[fun_prop] theorem ratNeg : Primrec (fun q : ℚ => -q) := by
  have hc : Primrec (fun q : ℚ => mkRat (-q.num) q.den) := by
    exact ratMk.comp (show Primrec (fun q : ℚ => (-q.num, q.den)) from by fun_prop)
  exact hc.of_eq (fun q => by simp [Rat.neg_def, Rat.divInt_ofNat])

@[fun_prop] theorem ratDivInt : Primrec (fun p : ℤ × ℤ => Rat.divInt p.1 p.2) := by
  have hc : Primrec (fun p : ℤ × ℤ =>
      if p.2 < 0 then mkRat (-p.1) p.2.natAbs else mkRat p.1 p.2.natAbs) :=
    Primrec.ite (intNegative.comp Primrec.snd) (by fun_prop) (by fun_prop)
  exact hc.of_eq (fun p => by
    rcases p with ⟨a,b⟩
    cases b <;> simp [Rat.divInt, Rat.normalize_eq_mkRat])

@[fun_prop] theorem ratInv : Primrec (fun q : ℚ => q⁻¹) := by
  exact (ratDivInt.comp (show Primrec (fun q : ℚ => ((q.den : ℤ), q.num)) from by fun_prop)).of_eq (fun q => (Rat.inv_def q).symm)

@[fun_prop] theorem rat_sub : Primrec (fun p : ℚ × ℚ => p.1 - p.2) := by
  simpa only [sub_eq_add_neg] using rat_add.comp (Primrec.fst.pair (ratNeg.comp Primrec.snd))

@[fun_prop] theorem rat_div : Primrec (fun p : ℚ × ℚ => p.1 / p.2) := by
  simpa only [div_eq_mul_inv] using rat_mul.comp (Primrec.fst.pair (ratInv.comp Primrec.snd))

@[fun_prop] theorem rat_pow : Primrec (fun p : ℚ × ℕ => p.1 ^ p.2) := by
  exact (Primrec.nat_iterate Primrec.snd (Primrec.const (1 : ℚ))
    (rat_mul.comp (Primrec.snd.pair (Primrec.fst.comp Primrec.fst))).to₂).of_eq
    (fun p => by dsimp only; induction p.2 <;> simp_all [pow_succ'])

end RecursiveArithmetic

end
end PeriodicLattice

end OAI
