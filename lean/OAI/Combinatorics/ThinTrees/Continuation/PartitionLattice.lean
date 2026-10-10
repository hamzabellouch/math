import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.CompactCharging

namespace OAI

/-! Partition lattice. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

variable {V E : Type*} [Fintype V]

instance partitionsFinite : Finite (Setoid V) :=
  Finite.of_injective (fun p : Setoid V => p.r) (fun p q h => by
    apply Setoid.ext
    intro a b
    exact iff_of_eq (congrFun (congrFun h a) b))

instance partitionsFintype : Fintype (Setoid V) := Fintype.ofFinite _

def partCount (p : Setoid V) : ℕ := Fintype.card (Quotient p)

def constants (p : Setoid V) : Submodule ℝ (V → ℝ) where
  carrier := {x | p ≤ Setoid.ker x}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro x y hx hy a b hab
    change x a+y a=x b+y b
    rw [hx hab,hy hab]
  smul_mem' := by
    intro c x hx a b hab
    change c*x a=c*x b
    rw [hx hab]

omit [Fintype V] in
lemma constants_antitone {p q : Setoid V} (hpq : p ≤ q) : constants q ≤ constants p :=
  fun _ hx => hpq.trans hx

omit [Fintype V] in
lemma constants_sup (p q : Setoid V) : constants (p ⊔ q)=constants p ⊓ constants q := by
  ext x
  change (p ⊔ q ≤ Setoid.ker x) ↔ (p ≤ Setoid.ker x) ∧ (q ≤ Setoid.ker x)
  exact sup_le_iff

def quotientConstants (p : Setoid V) : (Quotient p → ℝ) ≃ₗ[ℝ] constants p where
  toFun f := ⟨fun a => f (Quotient.mk p a),fun _ _ hab => congrArg f (Quotient.sound hab)⟩
  invFun x := Quotient.lift x (fun _ _ hab => x.property hab)
  left_inv f := by
    funext a
    exact Quotient.inductionOn a (fun _ => rfl)
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma constants_finrank (p : Setoid V) : Module.finrank ℝ (constants p)=partCount p := by
  rw [←(quotientConstants p).finrank_eq,Module.finrank_pi]
  rfl

theorem partCount_supermodular (p q : Setoid V) :
    partCount p+partCount q ≤ partCount (p ⊓ q)+partCount (p ⊔ q) := by
  have hi : constants p ⊔ constants q ≤ constants (p ⊓ q) :=
    sup_le (constants_antitone inf_le_left) (constants_antitone inf_le_right)
  have hr := Submodule.finrank_mono hi
  have he := Submodule.finrank_sup_add_finrank_inf_eq (constants p) (constants q)
  rw [←constants_sup,constants_finrank,constants_finrank,constants_finrank] at he
  rw [constants_finrank] at hr
  omega

theorem partCount_strictAnti : StrictAnti (partCount (V := V)) := by
  intro p q hpq
  let f : Quotient p → Quotient q := Quotient.map id hpq.le
  have hsur : Function.Surjective f := Quotient.map_surjective hpq.le Function.surjective_id
  have hninj : ¬Function.Injective f := by
    intro hinj
    have hqp : q ≤ p := by
      intro a b hab
      apply Quotient.exact
      apply hinj
      change (Quotient.mk q a)=(Quotient.mk q b)
      exact Quotient.sound hab
    exact (not_le_of_gt hpq) hqp
  exact Fintype.card_lt_of_surjective_not_injective f hsur hninj

lemma partCount_antitone : Antitone (partCount (V := V)) := partCount_strictAnti.antitone

def potential (p : Setoid V) : ℝ := (partCount p : ℝ)^2

theorem potential_uncross {p q : Setoid V} (hpq : ¬p ≤ q) (hqp : ¬q ≤ p) :
    potential p+potential q < potential (p ⊓ q)+potential (p ⊔ q) := by
  have hip : p ⊓ q < p := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hpq (he ▸ inf_le_right))
  have hiq : p ⊓ q < q := lt_of_le_of_ne inf_le_right (by
    intro he
    exact hqp (he ▸ inf_le_left))
  have hps : p < p ⊔ q := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hqp (he.symm ▸ le_sup_right))
  have hqs : q < p ⊔ q := lt_of_le_of_ne le_sup_right (by
    intro he
    exact hpq (he.symm ▸ le_sup_left))
  have hcp : (partCount p:ℝ) < partCount (p ⊓ q) := by exact_mod_cast partCount_strictAnti hip
  have hcq : (partCount q:ℝ) < partCount (p ⊓ q) := by exact_mod_cast partCount_strictAnti hiq
  have hdp : (partCount (p ⊔ q):ℝ) < partCount p := by exact_mod_cast partCount_strictAnti hps
  have hdq : (partCount (p ⊔ q):ℝ) < partCount q := by exact_mod_cast partCount_strictAnti hqs
  have hsum : (partCount p:ℝ)+partCount q ≤ partCount (p ⊓ q)+partCount (p ⊔ q) := by
    exact_mod_cast partCount_supermodular p q
  have hm1 := mul_pos (sub_pos.mpr hcp) (sub_pos.mpr hcq)
  have hm2 := mul_nonneg (sub_nonneg.mpr hdp.le) (sub_nonneg.mpr hdq.le)
  have hm3 := mul_nonneg (show (0:ℝ) ≤ partCount p+partCount q by positivity)
    (sub_nonneg.mpr hsum)
  dsimp [potential]
  nlinarith only [hm1,hm2,hm3]

def crossingIndicator (p : Setoid V) (a b : V) : ℝ := if p a b then 0 else 1

omit [Fintype V] in
lemma crossingIndicator_nonneg (p : Setoid V) (a b : V) : 0 ≤ crossingIndicator p a b := by
  unfold crossingIndicator
  split_ifs <;> norm_num

omit [Fintype V] in
theorem crossingIndicator_submodular (p q : Setoid V) (a b : V) :
    crossingIndicator (p ⊓ q) a b+crossingIndicator (p ⊔ q) a b ≤
      crossingIndicator p a b+crossingIndicator q a b := by
  have hp : p a b → (p ⊔ q) a b := fun h => (show p ≤ p ⊔ q from le_sup_left) h
  have hq : q a b → (p ⊔ q) a b := fun h => (show q ≤ p ⊔ q from le_sup_right) h
  have hinf : (p ⊓ q) a b ↔ p a b ∧ q a b := Iff.rfl
  unfold crossingIndicator
  by_cases habp : p a b <;> by_cases habq : q a b
  · simp [hinf,habp,habq,hp habp]
  · simp [hinf,habp,habq,hp habp]
  · simp [hinf,habp,habq,hq habq]
  · simp only [hinf,habp,habq,false_and,ite_false]
    split_ifs <;> norm_num

variable [Fintype E]

def capacity (left right : E → V) (w : E → ℝ) (p : Setoid V) : ℝ :=
  ∑e, w e*crossingIndicator p (left e) (right e)

omit [Fintype V] in
theorem capacity_submodular (left right : E → V) (w : E → ℝ) (hw : ∀e, 0 ≤ w e)
    (p q : Setoid V) :
    capacity left right w (p ⊓ q)+capacity left right w (p ⊔ q) ≤
      capacity left right w p+capacity left right w q := by
  simp only [capacity,←sum_add_distrib,←mul_add]
  exact sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left
    (crossingIndicator_submodular p q (left e) (right e)) (hw e))

def slack (left right : E → V) (w : E → ℝ) (r : ℝ) (p : Setoid V) : ℝ :=
  capacity left right w p-r*((partCount p:ℝ)-1)

theorem slack_submodular (left right : E → V) (w : E → ℝ) (hw : ∀e, 0 ≤ w e)
    {r : ℝ} (hr : 0 ≤ r) (p q : Setoid V) :
    slack left right w r (p ⊓ q)+slack left right w r (p ⊔ q) ≤
      slack left right w r p+slack left right w r q := by
  have hc := capacity_submodular left right w hw p q
  have hrank : (partCount p:ℝ)+partCount q ≤ partCount (p ⊓ q)+partCount (p ⊔ q) := by
    exact_mod_cast partCount_supermodular p q
  have hm := mul_le_mul_of_nonneg_left hrank hr
  dsimp [slack]
  linarith

end
end AlgorithmicThinTrees.Partitions
end

end OAI
