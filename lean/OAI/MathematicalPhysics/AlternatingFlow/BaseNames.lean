import OAI.MathematicalPhysics.AlternatingFlow.LocalNames

namespace OAI

section BaseNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

def ratCoord (q : RationalVector) (i : Fin 3) : ℚ := ![q.1,q.2.1,q.2.2] i

lemma ratCoord_computable : Computable (fun z : RationalVector × Fin 3 => ratCoord z.1 z.2) := by
  have hi (i : Fin 3) : Computable (fun z : RationalVector × Fin 3 => decide (z.2 = i)) :=
    Primrec.eq.decide.to_comp.comp Computable.snd (Computable.const i)
  exact (Computable.cond (hi 0) (Computable.fst.comp Computable.fst)
    (Computable.cond (hi 1) (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))).of_eq
        (by rintro ⟨q,i⟩; fin_cases i <;> rfl)

lemma ratCoord_cast (q : RationalVector) (i : Fin 3) :
    (ratCoord q i : ℝ) = rationalVector q i := by
  fin_cases i <;> rfl

lemma coord_named (q : A → RationalPoint) (i : A → Fin 3)
    (hq : Computable q) (hi : Computable i) :
    Named (fun a => (rationalPoint (q a)).2 (i a)) :=
  (Named.rational (ratCoord_computable.comp ((Computable.snd.comp hq).pair hi))).congr
    (fun a => ratCoord_cast (q a).2 (i a))

lemma cutoff_named (q : A → RationalPoint) (hq : Computable q) :
    Named (fun a => Spatial.cutoff (rationalPoint (q a)).2) := by
  have h (i : Fin 3) := coord_named q (fun _ => i) hq (Computable.const i)
  have ht (i : Fin 3) := (((Named.const 3).sub (h i)).transition).mul
    (((Named.const 3).add (h i)).transition)
  exact (((ht 0).mul (ht 1)).mul (ht 2)).congr (by
    intro a; simp [Spatial.cutoff, Fin.prod_univ_succ]; ring)

lemma direction_succ (i : Fin 3) : direction i.succ = (0,e i) := by
  fin_cases i <;> rfl

lemma JetBound.spatial_d_named {f : A → Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2).2))
    (i : A → Fin 3) (hi : Computable i) :
    Named (fun z : A × RationalPoint => Spatial.d (i z.1) (f z.1) (rationalPoint z.2).2) := by
  have hf' := hf.comp_unit (fun _ => ContinuousLinearMap.snd ℝ ℝ Space) (fun _ => norm_snd)
  have hd := hf'.named_directional hn (fun a => (i a).succ) (Primrec.fin_succ.to_comp.comp hi)
  apply hd.congr
  intro z
  rw [direction_succ]
  dsimp [Spatial.d, Function.comp_def]
  rw [fderiv_fun_comp _ ((hf.1 z.1).differentiable (by simp) _) (differentiableAt_snd)]
  simp [fderiv_snd]

noncomputable def slotPotential (p : (Machine × ℕ) × ℕ) (x : Space) : ℝ :=
  Spatial.cutoff x * Spatial.shearPotential (Construction.donorIndex p.2)
    (Construction.receiverIndex p.2) 0 (LocalRule.write p.1.1 p.1.2 p.2)
      (LocalRule.signal p.1.1 p.1.2 p.2) x

noncomputable def loadPotential (p : Machine × List ℕ) (x : Space) : ℝ :=
  Spatial.cutoff x * Spatial.shearPotential 2 1 0
    (fun _ => Scales.ε p.1.base p.2.length 0 * p.1.recordedBlock p.2 0)
    (fun _ => 1 - Scales.ε p.1.base p.2.length 0) x

lemma loadPotential_bound : JetBound loadPotential := by
  obtain ⟨hs,B,hB,h⟩ := loadingPotential_scaled
  refine ⟨fun p => hs p 0, B, hB, fun p r x => ?_⟩
  change ‖iteratedFDeriv ℝ r (fun x : Space => Spatial.cutoff x *
    Spatial.shearPotential 2 1 0 (fun _ => Scales.ε p.1.base p.2.length 0 * p.1.recordedBlock p.2 0)
      (fun _ => 1 - Scales.ε p.1.base p.2.length 0) x) x‖ ≤ _
  simpa only [one_pow, mul_one] using h p r 0 x

lemma slotPotential_bound : JetBound slotPotential := by
  obtain ⟨C,hC,hc⟩ := potential_bound
  let S : (Machine × ℕ) × ℕ → ℕ := fun p => p.1.1.base ^
    (Scales.s p.1.2 p.2 + 1 + Scales.K p.1.2 p.2)
  have hS : Computable S := nat_pow.to_comp.comp
    (base.to_comp.comp (Computable.fst.comp Computable.fst))
    (Primrec.nat_add.to_comp.comp
      (Computable.succ.comp (exponent.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
      (capacity.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
  refine ⟨fun p => Spatial.cutoff_smooth.mul (Spatial.shearPotential_smooth _ _ _ _ _
    (LocalRule.write_smooth p.1.1 p.1.2 p.2) (LocalRule.signal_smooth p.1.1 p.1.2 p.2)),
    fun z => C (z.1.1,z.2) * (1 + S z.1 ^ z.2),
    Primrec.nat_mul.to_comp.comp
      (hC.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (Primrec.nat_add.to_comp.comp (Computable.const 1)
        (nat_pow.to_comp.comp (hS.comp Computable.fst) Computable.snd)), ?_⟩
  intro p r x
  have e₁ : Scales.ε p.1.1.base p.1.2 p.2 ≤ 1 :=
    (le_abs_self _).trans (Bounds.inverse_power_bound _ _)
  have e₂ : Scales.ε p.1.1.base p.1.2 (p.2+1) ≤ 1 :=
    (le_abs_self _).trans (Bounds.inverse_power_bound _ _)
  have hsc : Bounds.readScale p.1.1 p.1.2 p.2 = (S p : ℝ) := by
    simp [Bounds.readScale, S]
  apply (hc p.1.1 p.1.2 r p.2 x).trans
  push_cast
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [hsc]
  exact add_le_add e₁ (mul_le_of_le_one_left (by positivity) e₂)

lemma donor_computable : Computable Construction.donorIndex := by
  exact (Computable.cond
    (Primrec.eq.decide.to_comp.comp (Primrec.nat_mod.to_comp.comp Computable.id (Computable.const 2)) (Computable.const 0))
    (Computable.const (1 : Fin 3)) (Computable.const 2)).of_eq (by intros; simp [Construction.donorIndex])

lemma receiver_computable : Computable Construction.receiverIndex := by
  exact (Computable.cond
    (Primrec.eq.decide.to_comp.comp (Primrec.nat_mod.to_comp.comp Computable.id (Computable.const 2)) (Computable.const 0))
    (Computable.const (2 : Fin 3)) (Computable.const 1)).of_eq (by intros; simp [Construction.receiverIndex])

lemma loadPotential_named :
    Named (fun z : (Machine × List ℕ) × RationalPoint => loadPotential z.1 (rationalPoint z.2).2) := by
  let P := (Machine × List ℕ) × RationalPoint
  have hM : Computable (fun z : P => z.1.1) := Computable.fst.comp Computable.fst
  have hw : Computable (fun z : P => z.1.2) := Computable.snd.comp Computable.fst
  have he := epsilon_named.comp ((hM.pair (Computable.list_length.comp hw)).pair (Computable.const 0))
  have hblock := (Named.rational (initialBlock_primrec.to_comp.comp hM hw)).congr
    (fun z : P => initialBlock_cast z.1.1 z.1.2)
  have hcoord (i : Fin 3) := coord_named (Prod.snd : P → RationalPoint) (fun _ => i)
    Computable.snd (Computable.const i)
  exact ((cutoff_named (Prod.snd : P → RationalPoint) Computable.snd).mul
    (((hcoord 0).mul (he.mul hblock)).sub ((hcoord 1).mul ((Named.const 1).sub he)))).congr
      (by intro z; simp only [loadPotential, Spatial.shearPotential, Rat.cast_one, Function.comp_def])

lemma slotPotential_named :
    Named (fun z : ((Machine × ℕ) × ℕ) × RationalPoint => slotPotential z.1 (rationalPoint z.2).2) := by
  let P := ((Machine × ℕ) × ℕ) × RationalPoint
  let M := fun z : P => z.1.1.1
  let N := fun z : P => z.1.1.2
  let n := fun z : P => z.1.2
  have hM : Computable M := Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hN : Computable N := Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hn : Computable n := Computable.snd.comp Computable.fst
  have hd := coord_named (Prod.snd : P → RationalPoint) (fun z => Construction.donorIndex (n z))
    Computable.snd (donor_computable.comp hn)
  have hi := coord_named (Prod.snd : P → RationalPoint) (fun z => Construction.receiverIndex (n z))
    Computable.snd (receiver_computable.comp hn)
  have h0 := coord_named (Prod.snd : P → RationalPoint) (fun _ => 0) Computable.snd (Computable.const 0)
  have hw := write_named M N n _ hM hN hn hd
  have hs := signal_named M N n _ hM hN hn hd
  exact ((cutoff_named (Prod.snd : P → RationalPoint) Computable.snd).mul
    ((h0.mul hw).sub (hi.mul hs))).congr (by intro z; rfl)

end AlternatingNS.Effective

end BaseNamesDevelopment

end OAI
