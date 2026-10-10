import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveArithmetic

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_ite {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : Computable (fun a => decide (p a))) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  exact (Computable.cond hp hf hg).of_eq (fun a => by
    by_cases h : p a <;> simp [h])

lemma primrec_int_nonneg : PrimrecPred (fun z : ℤ => 0 ≤ z) := by
  refine ⟨inferInstance, (primrec_int_cases Primrec.id (Primrec.const true).to₂
    (Primrec.const false).to₂).of_eq ?_⟩
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

lemma primrec_int_le : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) := by
  exact (primrec_int_nonneg.comp
    (primrec_int_add.comp Primrec.snd (primrec_int_neg.comp Primrec.fst))).of_eq
    (fun p => by simp only [← sub_eq_add_neg, sub_nonneg])

lemma computable_rat_le : Computable₂ (fun a b : ℚ => decide (a ≤ b)) := by
  have ha : Computable (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.fst)
      ((primrec_int_ofNat.to_comp.comp computable_rat_den).comp Computable.snd)
  have hb : Computable (fun p : ℚ × ℚ => p.2.num * (p.1.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.snd)
      ((primrec_int_ofNat.to_comp.comp computable_rat_den).comp Computable.fst)
  refine ((primrec_int_le.decide.to_comp).comp ha hb).of_eq ?_
  intro ⟨a,b⟩
  have he : a.num * (b.den : ℤ) ≤ b.num * (a.den : ℤ) ↔ a ≤ b := by
    simpa only [Rat.num_divInt_den] using
      (Rat.divInt_le_divInt (a := a.num) (c := b.num) (by exact_mod_cast a.pos : (0 : ℤ) < a.den)
        (by exact_mod_cast b.pos : (0 : ℤ) < b.den)).symm
  simp only [he]

lemma computable_rat_abs : Computable (fun q : ℚ => |q|) := by
  exact (computable_ite (computable_rat_le.comp (Computable.const 0) Computable.id)
    Computable.id computable_rat_neg).of_eq (fun q => by
      split_ifs with h
      · exact (abs_of_nonneg h).symm
      · exact (abs_of_neg (lt_of_not_ge h)).symm)

lemma computable_rat_sub : Computable₂ ((· - ·) : ℚ → ℚ → ℚ) := by
  exact (computable_rat_add.comp Computable.fst (computable_rat_neg.comp Computable.snd)).of_eq
    (fun _ => (sub_eq_add_neg _ _).symm)

lemma computable_rat_natCast : Computable (fun n : ℕ => (n : ℚ)) := by
  exact (computable_rat_of_parts primrec_int_ofNat.to_comp (Computable.const 1)
    (fun _ => by decide)).of_eq (fun n => by norm_cast; simp)

lemma computable_rat_intCast : Computable (fun n : ℤ => (n : ℚ)) := by
  exact (computable_rat_of_parts Computable.id (Computable.const 1)
    (fun _ => by decide)).of_eq (fun n => by norm_num)

lemma primrec_int_sign : Primrec Int.sign := by
  have h : Primrec (fun n : ℕ => if n = 0 then (0 : ℤ) else 1) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0) (Primrec.const 1)
  refine (primrec_int_cases Primrec.id (h.comp Primrec.snd).to₂
    (Primrec.const (-1 : ℤ)).to₂).of_eq ?_
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

lemma computable_rat_inv : Computable (fun q : ℚ => q⁻¹) := by
  have hn : Computable (fun q : ℚ => q.num.sign * (q.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (primrec_int_sign.to_comp.comp computable_rat_num)
      (primrec_int_ofNat.to_comp.comp computable_rat_den)
  have hnum : Computable (fun q : ℚ => q⁻¹.num) := hn.of_eq (fun q => (Rat.num_inv q).symm)
  have hd : Computable (fun q : ℚ => q⁻¹.den) := by
    refine (computable_ite (Primrec.eq.decide.to_comp.comp computable_rat_num (Computable.const 0))
      (Computable.const 1) (primrec_int_natAbs.to_comp.comp computable_rat_num)).of_eq ?_
    intro q
    exact (Rat.den_inv q).symm
  exact (computable_rat_of_parts hnum hd (fun q => q⁻¹.den_ne_zero)).of_eq
    (fun q => Rat.num_div_den q⁻¹)

lemma computable_rat_div : Computable₂ ((· / ·) : ℚ → ℚ → ℚ) := by
  exact (computable_rat_mul.comp Computable.fst (computable_rat_inv.comp Computable.snd)).of_eq
    (fun _ => (div_eq_mul_inv _ _).symm)

lemma primrec_nat_factorial : Primrec Nat.factorial := by
  have h : Primrec₂ (fun (_ : Unit) n => Nat.rec (motive := fun _ => ℕ) 1 (fun n r => (n + 1) * r) n) :=
    Primrec.nat_rec (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  refine (h.comp (Primrec.const ()) Primrec.id).of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa [Nat.factorial_succ] using congrArg (fun k => (n + 1) * k) ih

lemma computable_rat_pow : Computable₂ ((· ^ ·) : ℚ → ℕ → ℚ) := by
  have h : Computable (fun p : ℚ × ℕ =>
      Nat.rec (motive := fun _ => ℚ) (1 : ℚ) (fun _ r => r * p.1) p.2) :=
    Computable.nat_rec Computable.snd (Computable.const 1)
      (computable_rat_mul.comp (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.fst)).to₂
  refine h.of_eq ?_
  intro ⟨q,n⟩
  dsimp
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using congrArg (fun r => r * q) ih

lemma computable_sum_range {α : Type*} [Primcodable α]
    {f : α → ℕ → ℚ} (hf : Computable₂ f) :
    Computable₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hh : Computable (fun p : α × ℕ =>
      Nat.rec (motive := fun _ => ℚ) (0 : ℚ) (fun n r => r + f p.1 n) p.2) :=
    Computable.nat_rec Computable.snd (Computable.const 0)
      (computable_rat_add.comp (Computable.snd.comp Computable.snd)
        (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  refine hh.of_eq ?_
  intro ⟨a,n⟩
  dsimp
  induction n with
  | zero => simp
  | succ n ih => simpa [Finset.sum_range_succ] using congrArg (fun r => r + f a n) ih

end BalancedTransport.Effectivity
end

end OAI
