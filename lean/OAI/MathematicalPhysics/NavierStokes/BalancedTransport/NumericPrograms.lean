import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveLog

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_foldl {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    [Inhabited β] {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun s b => h a (s,b)) (g a)) := by
  have hc : Computable (fun a => Nat.rec (motive := fun _ => σ) (g a)
      (fun j v => h a (v, (f a).getD j default)) (f a).length) :=
    Computable.nat_rec (Computable.list_length.comp hf) hg
      (hh.comp Computable.fst ((Computable.snd.comp Computable.snd).pair
        ((Primrec.list_getD default).to_comp.comp (hf.comp Computable.fst)
          (Computable.fst.comp Computable.snd)))).to₂
  apply hc.of_eq
  intro a
  have he (n : ℕ) (hn : n ≤ (f a).length) : Nat.rec (motive := fun _ => σ) (g a)
      (fun j v => h a (v, (f a).getD j default)) n =
      ((f a).take n).foldl (fun s b => h a (s,b)) (g a) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hl : n < (f a).length := by omega
      change h a (Nat.rec (motive := fun _ => σ) (g a)
        (fun j v => h a (v, (f a).getD j default)) n, (f a).getD n default) = _
      rw [ih (by omega), List.take_succ_eq_append_getElem hl,
        List.foldl_concat]
      rw [List.getD_eq_getElem _ _ hl]
  simpa using he (f a).length le_rfl

lemma computable_fin_cases {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {n : ℕ} {i : α → Fin n} {f : Fin n → α → β}
    (hi : Computable i) (hf : ∀ j, Computable (f j)) :
    Computable (fun a => f (i a) a) := by
  have hl : Computable (fun a => List.ofFn (fun j => f j a)) :=
    Computable.list_ofFn hf
  exact ((Primrec.list_getD default).to_comp.comp hl (Primrec.fin_val.to_comp.comp hi)).of_eq
    (fun a => by simp)

abbrev NumericOp := Fin 9 × ℚ × ℕ × ℕ

abbrev NumericProgram := List NumericOp

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

def tag (o : NumericOp) : Fin 9 := o.1

def rat (o : NumericOp) : ℚ := o.2.1

def left (o : NumericOp) : ℕ := o.2.2.1

def right (o : NumericOp) : ℕ := o.2.2.2

noncomputable def real (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (s : List ℝ) : ℝ :=
  let a := o.left
  let b := o.right
  let q := o.rat
  match o.tag with
  | 0 => q
  | 1 => x (Fin.ofNat d a)
  | 2 => s.getD a 0 + s.getD b 0
  | 3 => s.getD a 0 * s.getD b 0
  | 4 => -s.getD a 0
  | 5 => (s.getD a 0)⁻¹
  | 6 => rhoJet a (s.getD b 0)
  | 7 => Real.exp (s.getD a 0)
  | 8 => if 0 < q then Real.log (q : ℝ) else 0

noncomputable def rationalCase (d : ℕ) [NeZero d] (j : Fin 9) (o : NumericOp) (x : Fin d → ℚ)
    (p : ℕ) (s : List ℚ) : ℚ :=
  let a := o.left
  let b := o.right
  let q := o.rat
  match j with
  | 0 => q
  | 1 => x (Fin.ofNat d a)
  | 2 => s.getD a 0 + s.getD b 0
  | 3 => s.getD a 0 * s.getD b 0
  | 4 => -s.getD a 0
  | 5 => (max ((b + 1 : ℕ) : ℚ)⁻¹ (s.getD a 0))⁻¹
  | 6 => rhoApprox a (s.getD b 0) p
  | 7 => expApprox (s.getD a 0) p
  | 8 => logApprox q p

noncomputable def rational (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℚ)
    (p : ℕ) (s : List ℚ) : ℚ := rationalCase d o.tag o x p s

def boundCase (j : Fin 9) (o : NumericOp) (C : ℕ) (s : List (ℕ × ℕ)) : ℕ × ℕ :=
  let a := o.left
  let b := o.right
  let q := o.rat
  let A := (s.getD a (0,0)).1
  let E := (s.getD a (0,0)).2
  let B := (s.getD b (0,0)).1
  let F := (s.getD b (0,0)).2
  match j with
  | 0 => (q.num.natAbs, 0)
  | 1 => (C, 0)
  | 2 => (A + B, E + F)
  | 3 => (A * B, (A + E) * F + B * E)
  | 4 => (A, E)
  | 5 => (b + 1, (b + 1)^2 * E)
  | 6 => (rhoBound a 0, 1 + rhoBound (a+1) 0 * F)
  | 7 => (3^A, 1 + 3^(A+E) * E)
  | 8 => (q.num.natAbs + q⁻¹.num.natAbs, 1)

def bound (o : NumericOp) (C : ℕ) (s : List (ℕ × ℕ)) : ℕ × ℕ :=
  boundCase o.tag o C s

def Valid (o : NumericOp) (s : List ℝ) : Prop :=
  o.tag = 5 → ((o.right + 1 : ℕ) : ℝ)⁻¹ ≤ s.getD o.left 0

lemma computable_rational (d : ℕ) [NeZero d] :
    Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ =>
      rational d z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have ha : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.1.left) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hb : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.1.right) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hq : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.1.rat) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hp : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hva := (Primrec.list_getD (0 : ℚ)).to_comp.comp hs ha
  have hvb := (Primrec.list_getD (0 : ℚ)).to_comp.comp hs hb
  have hi : Primrec (fun a : ℕ => Fin.ofNat d a) :=
    Primrec.fin_val_iff.mp (Primrec.nat_mod.comp Primrec.id (Primrec.const d))
  have hmax : Computable₂ (fun a b : ℚ => max a b) := by
    exact (computable_ite computable_rat_le Computable.snd Computable.fst).of_eq
      (fun p => by split_ifs with h <;> simp [max_def, h])
  have hc (j : Fin 9) : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ =>
      rationalCase d j z.1 z.2.1 z.2.2.1 z.2.2.2) := by
    fin_cases j <;> dsimp only [rationalCase, rat, left, right]
    · simpa only [left, right, rat] using hq
    · simpa only [left, right, rat, id_eq] using Computable.fin_app.comp (Computable.fst.comp Computable.snd) (hi.to_comp.comp ha)
    · simpa only [left, right, rat] using computable_rat_add.comp hva hvb
    · simpa only [left, right, rat] using computable_rat_mul.comp hva hvb
    · simpa only [left, right, rat] using computable_rat_neg.comp hva
    · simpa only [left, right, rat] using computable_rat_inv.comp (hmax.comp
        (computable_rat_inv.comp (computable_rat_natCast.comp (Computable.succ.comp hb))) hva)
    · simpa only [left, right, rat] using computable_rhoApprox.comp (ha.pair (hvb.pair hp))
    · simpa only [left, right, rat] using computable_expApprox.comp hva hp
    · simpa only [left, right, rat] using computable_logApprox.comp hq hp
  have H := computable_fin_cases (i := fun z => z.1.tag)
    (Computable.fst.comp Computable.fst) hc
  simpa only [rational] using H

lemma computable_bound : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) =>
    bound z.1 z.2.1 z.2.2) := by
  have ha : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.1.left) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hb : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.1.right) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hq : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.1.rat) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hva := (Primrec.list_getD (0,0)).to_comp.comp hs ha
  have hvb := (Primrec.list_getD (0,0)).to_comp.comp hs hb
  have hA := Computable.fst.comp hva
  have hE := Computable.snd.comp hva
  have hB := Computable.fst.comp hvb
  have hF := Computable.snd.comp hvb
  have hadd := Primrec.nat_add.to_comp
  have hmul := Primrec.nat_mul.to_comp
  have hpow : Computable₂ (fun a b : ℕ => a ^ b) := by
    exact (((Primrec.nat_iff.mpr Nat.Primrec.pow).comp Primrec.encode).of_eq
      (fun p => by rcases p with ⟨a,b⟩; change (Nat.unpair (Nat.pair a b)).1 ^ (Nat.unpair (Nat.pair a b)).2 = a ^ b; rw [Nat.unpair_pair])).to_comp
  have hn := primrec_int_natAbs.to_comp.comp (computable_rat_num.comp hq)
  have hc (j : Fin 9) : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) =>
      boundCase j z.1 z.2.1 z.2.2) := by
    fin_cases j <;> dsimp only [boundCase, rat, left, right]
    · simpa only [left, right, rat] using hn.pair (Computable.const 0)
    · simpa only [left, right, rat] using (Computable.fst.comp Computable.snd).pair (Computable.const 0)
    · simpa only [left, right, rat] using (hadd.comp hA hB).pair (hadd.comp hE hF)
    · simpa only [left, right, rat] using (hmul.comp hA hB).pair
        (hadd.comp (hmul.comp (hadd.comp hA hE) hF) (hmul.comp hB hE))
    · simpa only [left, right, rat] using hva
    · simpa only [left, right, rat] using (Computable.succ.comp hb).pair
        (hmul.comp (hpow.comp (Computable.succ.comp hb) (Computable.const 2)) hE)
    · simpa only [left, right, rat] using (primrec_rhoBound.to_comp.comp ha (Computable.const 0)).pair
        (hadd.comp (Computable.const 1) (hmul.comp
          (primrec_rhoBound.to_comp.comp (Computable.succ.comp ha) (Computable.const 0)) hF))
    · simpa only [left, right, rat] using (hpow.comp (Computable.const 3) hA).pair
        (hadd.comp (Computable.const 1) (hmul.comp
          (hpow.comp (Computable.const 3) (hadd.comp hA hE)) hE))
    · simpa only [left, right, rat] using (hadd.comp hn (primrec_int_natAbs.to_comp.comp
        (computable_rat_num.comp (computable_rat_inv.comp hq)))).pair (Computable.const 1)
  have H := computable_fin_cases (i := fun z => z.1.tag)
    (Computable.fst.comp Computable.fst) hc
  simpa only [bound] using H

end BalancedTransport.Effectivity.NumericOp
end

end OAI
