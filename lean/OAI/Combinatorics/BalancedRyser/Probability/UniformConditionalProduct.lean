import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformConditioning
import OAI.Combinatorics.BalancedRyser.Probability.UniformRestriction

namespace OAI

namespace Balanced.UniformConditionalProduct

open TupleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

def subtypeFirstEquiv {A B : Type*} (E : A → Prop) :
    {z : A × B // E z.1} ≃ {a : A // E a} × B where
  toFun z := (⟨z.1.1, z.2⟩, z.1.2)
  invFun z := ⟨(z.1.1, z.2), z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def conditionedSplitEquiv {X A B : Type*} (e : X ≃ A × B) (E : A → Prop) :
    {x : X // E (e x).1} ≃ {a : A // E a} × B :=
  (e.subtypeEquiv (fun _ => Iff.rfl)).trans (subtypeFirstEquiv E)

@[simp] theorem conditionedSplitEquiv_symm_val {X A B : Type*}
    (e : X ≃ A × B) (E : A → Prop) (z : {a : A // E a} × B) :
    ((conditionedSplitEquiv e E).symm z).1 = e.symm (z.1.1, z.2) := rfl

theorem uniform_filter_split {X A B : Type*}
    [Fintype X] [Fintype A] [Fintype B] [Nonempty X] [Nonempty B]
    (e : X ≃ A × B) (E : A → Prop) [Nonempty {a : A // E a}]
    (h : ∃ x ∈ {x : X | E (e x).1},
      x ∈ (PMF.uniformOfFintype X).support) :
    (PMF.uniformOfFintype X).filter {x | E (e x).1} h =
      (PMF.uniformOfFintype ({a : A // E a} × B)).map
        (fun z => e.symm (z.1.1, z.2)) := by
  let : Nonempty {x : X // E (e x).1} :=
    ⟨(conditionedSplitEquiv e E).symm (Classical.choice inferInstance)⟩
  let : Nonempty ({x : X | E (e x).1} : Set X) :=
    ⟨(conditionedSplitEquiv e E).symm (Classical.choice inferInstance)⟩
  rw [Balanced.uniform_filter_eq_subtype_map]
  change (PMF.uniformOfFintype {x : X // E (e x).1}).map Subtype.val = _
  have hlaw := uniform_map_equiv (conditionedSplitEquiv e E).symm
  rw [← hlaw, PMF.map_comp]
  rfl

theorem uniform_map_second {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype (A × B)).map Prod.snd = PMF.uniformOfFintype B := by
  have h := congrArg (fun law => law.map Prod.fst)
    (uniform_map_equiv (Equiv.prodComm A B))
  rw [PMF.map_comp, uniform_map_fst] at h
  exact h

theorem uniform_filter_split_second {X A B : Type*}
    [Fintype X] [Fintype A] [Fintype B] [Nonempty X] [Nonempty B]
    (e : X ≃ A × B) (E : A → Prop) [Nonempty {a : A // E a}]
    (h : ∃ x ∈ {x : X | E (e x).1},
      x ∈ (PMF.uniformOfFintype X).support) :
    ((PMF.uniformOfFintype X).filter {x | E (e x).1} h).map
      (fun x => (e x).2) = PMF.uniformOfFintype B := by
  rw [uniform_filter_split e E h, PMF.map_comp]
  have heq : ((fun x => (e x).2) ∘
      (fun z : {a : A // E a} × B => e.symm (z.1.1, z.2))) = Prod.snd := by
    funext z
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [heq]
  exact uniform_map_second

theorem uniform_product_eq_bind {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    PMF.uniformOfFintype (A × B) =
      (PMF.uniformOfFintype A).bind (fun a =>
        (PMF.uniformOfFintype B).map (fun b => (a, b))) := by
  classical
  ext z
  rcases z with ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    tsum_fintype, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv,
    ite_and]

def arraySplitEquiv {D V : Type*} (P : D → Prop) :
    (D → V) ≃ ({d : D // P d} → V) × ({d : D // ¬ P d} → V) :=
  Equiv.piEquivPiSubtypeProd P (fun _ => V)

@[simp] theorem arraySplitEquiv_first {D V : Type*} (P : D → Prop)
    (o : D → V) (d : {d : D // P d}) :
    (arraySplitEquiv P o).1 d = o d.1 := rfl

@[simp] theorem arraySplitEquiv_second {D V : Type*} (P : D → Prop)
    (o : D → V) (d : {d : D // ¬ P d}) :
    (arraySplitEquiv P o).2 d = o d.1 := rfl

theorem uniform_filter_array {D V : Type*} [Fintype D] [Fintype V] [Nonempty V]
    (P : D → Prop) (E : ({d : D // P d} → V) → Prop)
    [Nonempty {u : ({d : D // P d} → V) // E u}]
    (h : ∃ o ∈ {o : D → V | E (fun d => o d.1)},
      o ∈ (PMF.uniformOfFintype (D → V)).support) :
    (PMF.uniformOfFintype (D → V)).filter {o | E (fun d => o d.1)} h =
      (PMF.uniformOfFintype
        ({u : ({d : D // P d} → V) // E u} × ({d : D // ¬ P d} → V))).map
        (fun z => (arraySplitEquiv P).symm (z.1.1, z.2)) :=
  uniform_filter_split (arraySplitEquiv P) E h

theorem uniform_filter_array_unused {D V : Type*}
    [Fintype D] [Fintype V] [Nonempty V]
    (P : D → Prop) (E : ({d : D // P d} → V) → Prop)
    [Nonempty {u : ({d : D // P d} → V) // E u}]
    (h : ∃ o ∈ {o : D → V | E (fun d => o d.1)},
      o ∈ (PMF.uniformOfFintype (D → V)).support) :
    ((PMF.uniformOfFintype (D → V)).filter {o | E (fun d => o d.1)} h).map
      (fun o (d : {d : D // ¬ P d}) => o d.1) =
        PMF.uniformOfFintype ({d : D // ¬ P d} → V) :=
  uniform_filter_split_second (arraySplitEquiv P) E h

end
end Balanced.UniformConditionalProduct

end OAI
