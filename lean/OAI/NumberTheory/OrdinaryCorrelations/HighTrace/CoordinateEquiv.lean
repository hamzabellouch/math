import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Splice

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving
open Finset Classical OrdinaryCorrelations.PivotSummation
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k E : ℕ}

noncomputable def coordinateEquiv (e : Fin k ↪ ι) : Unselected e ⊕ Fin k ≃ ι :=
  Equiv.ofBijective (Sum.elim (fun a : Unselected e => a.val) e) (by
    constructor
    · intro a b hab
      cases a with
      | inl a => cases b with
        | inl b => exact congrArg Sum.inl (Subtype.ext hab)
        | inr b => exact (a.property ⟨b,hab.symm⟩).elim
      | inr a => cases b with
        | inl b => exact (b.property ⟨a,hab⟩).elim
        | inr b => exact congrArg Sum.inr (e.injective hab)
    · intro a
      by_cases ha : a ∈ Set.range e
      · obtain ⟨i,rfl⟩ := ha; exact ⟨Sum.inr i,rfl⟩
      · exact ⟨Sum.inl ⟨a,ha⟩,rfl⟩)

lemma prod_split (e : Fin k ↪ ι) (f : ι → ℝ) :
    ∏ a, f a = (∏ a : Unselected e, f a.val) * ∏ i, f (e i) := by
  have he := (coordinateEquiv e).prod_comp f
  rw [Fintype.prod_sum_type] at he
  exact he.symm

namespace TriangularExpressions
variable {e : Fin k ↪ ι} (d : TriangularExpressions e E)

def numericClause (i : Fin k) (x : ι → ℕ) : ArithmeticClause :=
  if d.linear i then
    .linear ((d.expression i).linearCoeff (e i) (fun a => (x a:ℤ)))
      ((d.expression i).constantTerm (e i) (fun a => (x a:ℤ))) (x (d.modulus i))
  else .divisor ((d.expression i).eval (fun a => (x a:ℤ)))

omit [Fintype ι] in
lemma clause_eq_numeric (u : Unselected e → ℕ) (v : Fin k → ℕ) (i : Fin k) :
    d.clause u i (earlierTuple v i) = d.numericClause i (splice e u v) :=
  d.clause_actual u v i

def Admissible (P K : ℝ) (x : ι → ℕ) : Prop :=
  ∀ i, (d.numericClause i x).Holds P K (x (e i))

noncomputable def fiberWeight (P K : ℝ) (x : ι → ℕ) : ℝ :=
  if d.Admissible P K x then ∏ a, (x a:ℝ)⁻¹ else 0

lemma fiberWeight_nonneg (P K : ℝ) (x : ι → ℕ) : 0 ≤ d.fiberWeight P K x := by
  unfold fiberWeight; split_ifs <;> positivity

lemma fiberWeight_split (P K : ℝ) (u : Unselected e → ℕ) (v : Fin k → ℕ) :
    d.fiberWeight P K (splice e u v) =
      (∏ a, (u a:ℝ)⁻¹) * ∏ i, (d.clause u i (earlierTuple v i)).weight P K (v i) := by
  unfold fiberWeight
  by_cases hx : d.Admissible P K (splice e u v)
  · rw [ite_eq_left hx, prod_split e]
    simp only [splice_unselected,splice_selected]
    congr 1
    apply prod_congr rfl
    intro i hi
    rw [clause_eq_numeric,ArithmeticClause.weight,ite_eq_left]
    simpa only [splice_selected] using hx i
  · rw [ite_eq_right hx]
    have hex : ∃ i, ¬ (d.numericClause i (splice e u v)).Holds P K (v i) := by
      simpa only [Admissible,splice_selected,not_forall] using hx
    obtain ⟨i,hi⟩ := hex
    have hz : (d.clause u i (earlierTuple v i)).weight P K (v i)=0 := by
      rw [clause_eq_numeric,ArithmeticClause.weight,ite_eq_right hi]
    rw [prod_eq_zero (mem_univ i) hz,mul_zero]

theorem fiber_sum_le (S : Finset ℕ) (P B K : ℝ)
    (hP : 0 < P) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B) :
    (∑ x : ι → S, d.fiberWeight P K (fun a => x a)) ≤
      (∑ p ∈ S, (p:ℝ)⁻¹)^(Fintype.card (Unselected e)) *
      (max (K/(P*Real.log 2)) ((2+B)/P))^k := by
  let δ := max (K/(P*Real.log 2)) ((2+B)/P)
  have he := (assignmentEquiv (β:=S) e).sum_comp
    (fun x : ι → S => d.fiberWeight P K (fun a => x a))
  rw [←he,Fintype.sum_prod_type]
  have hsplit (u : Unselected e → S) (v : Fin k → S) :
      (fun a => ((splice e u v a : S):ℕ)) = splice e (fun a => (u a:ℕ)) (fun i => (v i:ℕ)) := by
    funext a
    simp only [splice]
    split_ifs <;> rfl
  have hrow (u : Unselected e → S) :
      (∑ v : Fin k → S,
        d.fiberWeight P K (fun a => ((splice e u v a : S):ℕ))) ≤
      (∏ a, ((u a:ℕ):ℝ)⁻¹)*δ^k := by
    simp only [hsplit,fiberWeight_split]
    rw [←mul_sum]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun a ha => by positivity))
    exact triangular_arithmetic_saving S P B K hP hB hK hS k
      (fun i pre => d.clause (fun a => (u a:ℕ)) i (fun j => (pre j:ℕ)))
  calc
    _ ≤ ∑ u : Unselected e → S, (∏ a, ((u a:ℕ):ℝ)⁻¹)*δ^k := by
      apply sum_le_sum
      intro u hu
      exact hrow u
    _ = (∑ p ∈ S, (p:ℝ)⁻¹)^(Fintype.card (Unselected e))*δ^k := by
      rw [←sum_mul]
      congr 1
      have hh := Fintype.prod_sum (fun (_a : Unselected e) (p : S) => ((p:ℕ):ℝ)⁻¹)
      rw [←hh]
      simp only [prod_const]
      rw [sum_coe_sort S (fun p => (p:ℝ)⁻¹),card_univ]

end TriangularExpressions
end OrdinaryCorrelations.ArithmeticSaving

end

end OAI
