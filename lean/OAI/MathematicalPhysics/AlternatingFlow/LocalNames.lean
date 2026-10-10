import OAI.MathematicalPhysics.AlternatingFlow.FieldPrograms

namespace OAI

section LocalNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma Named.nat (f : A → ℕ) (hf : Computable f) : Named (fun a => (f a : ℝ)) :=
  (Named.rational (Arithmetic.rat_natCast.to_comp.comp hf)).congr (fun _ => Rat.cast_natCast _)

lemma Named.natPow (b n : A → ℕ) (hb : Computable b) (hn : Computable n) :
    Named (fun a => (b a : ℝ) ^ n a) :=
  (Named.rational (Arithmetic.rat_pow.to_comp.comp
    (Arithmetic.rat_natCast.to_comp.comp hb) hn)).congr (by intro a; simp)

lemma Named.invNatPow (b n : A → ℕ) (hb : Computable b) (hn : Computable n) :
    Named (fun a => ((b a : ℝ) ^ n a)⁻¹) :=
  (Named.rational (Arithmetic.rat_inv.to_comp.comp (Arithmetic.rat_pow.to_comp.comp
    (Arithmetic.rat_natCast.to_comp.comp hb) hn))).congr (by intro a; simp)

lemma Named.divNat {f : A → ℝ} (hf : Named f) (b : A → ℕ) (hb : Computable b) :
    Named (fun a => f a / b a) :=
  (hf.mul (Named.invNatPow b (fun _ => 1) hb (Computable.const 1))).congr
    (by intro a; simp [div_eq_mul_inv])

lemma Named.selector {f : A → ℝ} (hf : Named f) (b a : A → ℕ)
    (hb : Computable b) (ha : Computable a) :
    Named (fun z => Profiles.selector (b z) (a z) (f z)) := by
  have h1 := (((Named.const 8).mul (((Named.nat b hb).mul hf).sub
    ((Named.const 2).mul (Named.nat a ha)))).add (Named.const 2)).transition
  have h2 := (((Named.const 8).mul ((((Named.const 2).mul (Named.nat a ha)).add
    (Named.const 1)).sub ((Named.nat b hb).mul hf))).add (Named.const 2)).transition
  exact (h1.mul h2).congr (by intro; simp only [Profiles.selector, Rat.cast_ofNat, Rat.cast_one])

lemma read_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.readC (M z) (N z) (n z) (D z)) ∧
    Named (fun z => LocalRule.readB (M z) (N z) (n z) (D z)) ∧
    Named (fun z => LocalRule.readA (M z) (N z) (n z) (D z)) := by
  have hb := base.to_comp.comp hM
  have hs := exponent.to_comp.comp hN hn
  have hK := capacity.to_comp.comp hN hn
  have hbase (z : A) : 2 ≤ (M z).base := by have := (M z).base_ge_four; omega
  have hC := ((Named.natPow (fun z => (M z).base) _ hb hs).mul hD).decoder
    (fun z => (M z).base) hb hbase
  have hB := ((Named.natPow (fun z => (M z).base) _ hb
    (Primrec.nat_add.to_comp.comp (Computable.succ.comp hs) hK)).mul hD).decoder
    (fun z => (M z).base) hb hbase
  have hA := ((Named.natPow (fun z => (M z).base) _ hb (Computable.succ.comp hs)).mul hD).decoder
    (fun z => (M z).base) hb hbase
  exact ⟨hC,hB,hA.sub ((Named.invNatPow (fun z => (M z).base) _ hb hK).mul hB)⟩

lemma numerator_named (b K a l : A → ℕ) (r : A → Rule) (u v : A → ℝ)
    (hb : Computable b) (hK : Computable K) (ha : Computable a) (hl : Computable l)
    (hr : Computable r) (hu : Named u) (hv : Named v) :
    Named (fun z => LocalRule.branchNumerator (b z) (K z) (a z) (l z) (r z) (u z) (v z)) := by
  have h2a := Named.nat (fun z => 2 * a z) (Primrec.nat_mul.to_comp.comp (Computable.const 2) ha)
  have h2l := Named.nat (fun z => 2 * l z) (Primrec.nat_mul.to_comp.comp (Computable.const 2) hl)
  have h2w := Named.nat (fun z => 2 * (r z).2.1)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp (Computable.snd.comp hr)))
  have h2q := Named.nat (fun z => 2 * (r z).1)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp hr))
  have hi (i : Fin 3) : Computable (fun z => decide ((r z).2.2 = i)) :=
    Primrec.eq.decide.to_comp.comp (Computable.snd.comp (Computable.snd.comp hr)) (Computable.const i)
  have hL := Named.ite (fun z => (r z).2.2 = 0) (hi 0)
    (((Named.nat b hb).mul hu).sub h2l)
    (Named.ite (fun z => (r z).2.2 = 1) (hi 1) hu ((h2w.add hu).divNat b hb))
  have hR := ((Named.nat b hb).mul hv).sub h2a
  have hR' := Named.ite (fun z => (r z).2.2 = 0) (hi 0)
    ((h2l.add ((h2w.add hR).divNat b hb)).divNat b hb)
    (Named.ite (fun z => (r z).2.2 = 1) (hi 1) ((h2w.add hR).divNat b hb) hR)
  exact ((h2q.add hL).add ((Named.invNatPow b K hb hK).mul hR')).congr (by
    intro z; dsimp [LocalRule.branchNumerator, LocalRule.updateLeft, LocalRule.updateRight]
    push_cast; split_ifs <;> rfl)

lemma branch_named (M : A → Machine) (N n q a : A → ℕ) (u v : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hq : Computable q)
    (ha : Computable a) (hu : Named u) (hv : Named v) :
    Named (fun z => LocalRule.branch (M z) (N z) (n z) (q z) (a z) (u z) (v z)) := by
  let r := fun z => (M z).command (q z) (a z)
  have hr : Computable r := command.to_comp.comp (hM.pair (hq.pair ha))
  have hb := base.to_comp.comp hM
  have hK := capacity.to_comp.comp hN (Computable.succ.comp hn)
  have hsel := (hu.comp (g := (Prod.fst : A × ℕ → A)) Computable.fst).selector
    (fun z => (M z.1).base) Prod.snd (hb.comp Computable.fst) Computable.snd
  have hnum := numerator_named (fun z : A × ℕ => (M z.1).base)
    (fun z => Scales.K (N z.1) (n z.1+1)) (fun z => a z.1) Prod.snd (fun z => r z.1)
    (fun z => u z.1) (fun z => v z.1) (hb.comp Computable.fst) (hK.comp Computable.fst)
    (ha.comp Computable.fst) Computable.snd (hr.comp Computable.fst)
    (hu.comp Computable.fst) (hv.comp Computable.fst)
  have hsum := (hsel.mul hnum).sum_range (fun z => (M z).alphabet) (alphabet.to_comp.comp hM)
  have hother := numerator_named (fun z => (M z).base) (fun z => Scales.K (N z) (n z+1))
    a (fun _ => 0) r u v hb hK ha (Computable.const 0) hr hu hv
  have hi : Computable (fun z => decide ((r z).2.2 = 0)) :=
    Primrec.eq.decide.to_comp.comp (Computable.snd.comp (Computable.snd.comp hr)) (Computable.const (0 : Fin 3))
  exact (Named.ite (fun z => (r z).2.2 = 0) hi hsum hother).congr (by intro z; rfl)

lemma writeCore_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => Bounds.writeCore (M z) (N z) (n z) (D z)) := by
  let P := (A × ℕ) × ℕ
  let M' := fun z : P => M z.1.1
  let N' := fun z : P => N z.1.1
  let n' := fun z : P => n z.1.1
  let D' := fun z : P => D z.1.1
  have hp : Computable (fun z : P => z.1.1) := Computable.fst.comp Computable.fst
  have hm : Computable M' := hM.comp hp
  have hnn : Computable n' := hn.comp hp
  have hnd : Computable N' := hN.comp hp
  obtain ⟨hC,hB,hA⟩ := read_named M' N' n' D' hm hnd hnn (hD.comp hp)
  have hb := base.to_comp.comp hm
  have hQ : Computable (fun z : P => z.1.2) := Computable.snd.comp Computable.fst
  have hterm := ((hC.selector (fun z => (M' z).base) (fun z => z.1.2) hb hQ).mul
    (hB.selector (fun z => (M' z).base) Prod.snd hb Computable.snd)).mul
    (branch_named M' N' n' (fun z => z.1.2) Prod.snd _ _ hm hnd hnn hQ Computable.snd hA hB)
  have hsum := (hterm.sum_range (fun z : A × ℕ => (M z.1).alphabet)
    (alphabet.to_comp.comp (hM.comp Computable.fst))).sum_range
      (fun z => (M z).states+1) (Computable.succ.comp (states.to_comp.comp hM))
  exact (hsum.divNat (fun z => (M z).base) (base.to_comp.comp hM)).congr (by
    intro z; dsimp [P,M',N',n',D',Bounds.writeCore]; ring)

lemma haltWeight_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.haltWeight (M z) (N z) (n z) (D z)) := by
  have hC := (read_named M N n D hM hN hn hD).1
  have hsel := (hC.comp (g := (Prod.fst : A × ℕ → A)) Computable.fst).selector
    (fun z => (M z.1).base) Prod.snd (base.to_comp.comp (hM.comp Computable.fst)) Computable.snd
  have hp : Computable (fun z : A × ℕ =>
      decide (z.2 = (M z.1).states ∨ z.2 ∈ (M z.1).haltingStates)) :=
    (Computable.cond
      (Primrec.eq.decide.to_comp.comp Computable.snd (states.to_comp.comp (hM.comp Computable.fst)))
      (Computable.const true)
      (member.decide.to_comp.comp (haltingStates.to_comp.comp (hM.comp Computable.fst)) Computable.snd)).of_eq
        (by intro z; simp)
  exact ((Named.ite _ hp hsel (Named.const 0)).sum_range
    (fun z => (M z).states+1) (Computable.succ.comp (states.to_comp.comp hM))).congr
    (by intro z; simp only [LocalRule.haltWeight, Function.comp_apply, Rat.cast_zero])

lemma write_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.write (M z) (N z) (n z) (D z)) := by
  have he := epsilon_named.comp ((hM.pair hN).pair (Computable.succ.comp hn))
  exact (he.mul (writeCore_named M N n D hM hN hn hD)).congr
    (fun z => (Bounds.write_factor _ _ _ _).symm)

lemma signal_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.signal (M z) (N z) (n z) (D z)) := by
  have he := epsilon_named.comp ((hM.pair hN).pair hn)
  have he' := epsilon_named.comp ((hM.pair hN).pair (Computable.succ.comp hn))
  exact ((he.sub he').add (((Named.const 2).mul he').mul
    (haltWeight_named M N n D hM hN hn hD))).congr (by intro z; simp [LocalRule.signal])

end AlternatingNS.Effective

end LocalNamesDevelopment

end OAI
