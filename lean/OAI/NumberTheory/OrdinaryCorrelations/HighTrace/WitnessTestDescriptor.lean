import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WitnessTestShape
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.OfRelabel

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical

abbrev WitnessTestDescriptor (ℓ L t m : ℕ) := WitnessTestShape ℓ L t × Fin m × Fin m × Bool
abbrev WitnessTemplateCode (ℓ L J t m : ℕ) :=
  WitnessMetadata ℓ L t × (WitnessCodeSlot ℓ L J t → Option (Fin m)) ×
    ((k : Fin (t+1)) × (Fin k.val → WitnessTestDescriptor ℓ L t m))

noncomputable instance (ℓ L J t m : ℕ) : Fintype (WitnessTemplateCode ℓ L J t m) := by
  haveI : Fintype (WitnessMetadata ℓ L t) := inferInstance
  haveI : Fintype (WitnessCodeSlot ℓ L J t → Option (Fin m)) := inferInstance
  haveI : Fintype (WitnessTestDescriptor ℓ L t m) := inferInstance
  haveI : ∀ k : Fin (t+1), Fintype (Fin k.val → WitnessTestDescriptor ℓ L t m) :=
    fun k => inferInstance
  haveI : Fintype ((k : Fin (t+1)) × (Fin k.val → WitnessTestDescriptor ℓ L t m)) := inferInstance
  unfold WitnessTemplateCode
  infer_instance

namespace WitnessTemplateCode
variable {ℓ L J t m : ℕ}
noncomputable def rank (d : WitnessTemplateCode ℓ L J t m) : ℕ := d.2.2.1.val
noncomputable def selected (d : WitnessTemplateCode ℓ L J t m) (i : Fin d.rank) : Fin m :=
  (d.2.2.2 i).2.1
noncomputable def modulus (d : WitnessTemplateCode ℓ L J t m) (i : Fin d.rank) : Fin m :=
  (d.2.2.2 i).2.2.1
noncomputable def linear (d : WitnessTemplateCode ℓ L J t m) (i : Fin d.rank) : Bool :=
  (d.2.2.2 i).2.2.2
noncomputable def expression (d : WitnessTemplateCode ℓ L J t m) (h : ℕ) (i : Fin d.rank) :
    SquarefreeExpression (Fin m) ((ℓ+L)+L) := (d.2.2.2 i).1.expression h d.1 d.2.1

def WellFormed (d : WitnessTemplateCode ℓ L J t m) (h : ℕ) : Prop :=
  Function.Injective d.selected ∧
  (∀ i, d.linear i=false → d.modulus i=d.selected i) ∧
  (∀ i, d.linear i=false → d.selected i ∉ (d.expression h i).support) ∧
  (∀ i, d.linear i=true → d.modulus i≠d.selected i) ∧
  (∀ i j, i<j → d.selected j ∉ insert (d.modulus i) (d.expression h i).support)

noncomputable def embedding (d : WitnessTemplateCode ℓ L J t m) (h : ℕ) (hd : d.WellFormed h) :
    Fin d.rank ↪ Fin m := ⟨d.selected,hd.1⟩
noncomputable def system (d : WitnessTemplateCode ℓ L J t m) (h : ℕ) (hd : d.WellFormed h) :
    TriangularExpressions (d.embedding h hd) ((ℓ+L)+L) where
  expression := d.expression h
  modulus := d.modulus
  linear := d.linear
  divisor_modulus := hd.2.1
  divisor_own_absent := hd.2.2.1
  linear_modulus_ne := hd.2.2.2.1
  future_absent := hd.2.2.2.2

lemma wellFormed_of_relabel (d : WitnessTemplateCode ℓ L J t m) (h : ℕ)
    {α : Type*} [DecidableEq α] (v : Fin m ↪ α) (e : Fin d.rank ↪ α)
    (q : TriangularExpressions e ((ℓ+L)+L))
    (hs : ∀ i, v (d.selected i)=e i)
    (he : ∀ i, (d.expression h i).relabel v=q.expression i)
    (hm : ∀ i, v (d.modulus i)=q.modulus i)
    (hl : ∀ i, d.linear i=q.linear i) : d.WellFormed h := by
  have hinj : Function.Injective d.selected := by
    intro i j hij
    apply e.injective
    rw [←hs i,←hs j,hij]
  let e' : Fin d.rank ↪ Fin m := ⟨d.selected,hinj⟩
  let c := q.ofRelabel v e' hs (d.expression h) d.modulus he hm
  refine ⟨hinj,?_,?_,?_,?_⟩
  · intro i hi
    exact c.divisor_modulus i (by simpa only [c,TriangularExpressions.ofRelabel,←hl] using hi)
  · intro i hi
    exact c.divisor_own_absent i (by simpa only [c,TriangularExpressions.ofRelabel,←hl] using hi)
  · intro i hi
    exact c.linear_modulus_ne i (by simpa only [c,TriangularExpressions.ofRelabel,←hl] using hi)
  · exact c.future_absent

lemma system_admissible_of_relabel (d : WitnessTemplateCode ℓ L J t m) (h : ℕ)
    (hd : d.WellFormed h) {α : Type*} [DecidableEq α]
    (v : Fin m ↪ α) (e : Fin d.rank ↪ α) (q : TriangularExpressions e ((ℓ+L)+L))
    (hs : ∀ i, v (d.selected i)=e i)
    (he : ∀ i, (d.expression h i).relabel v=q.expression i)
    (hm : ∀ i, v (d.modulus i)=q.modulus i)
    (hl : ∀ i, d.linear i=q.linear i)
    (P K : ℝ) (x : α → ℕ) (hx : q.Admissible P K x) :
    (d.system h hd).Admissible P K (fun a => x (v a)) := by
  intro i
  have hi := hx i
  change (if d.linear i then
    ArithmeticClause.linear ((d.expression h i).linearCoeff (d.selected i) (fun a => (x (v a):ℤ)))
      ((d.expression h i).constantTerm (d.selected i) (fun a => (x (v a):ℤ))) (x (v (d.modulus i)))
    else ArithmeticClause.divisor ((d.expression h i).eval (fun a => (x (v a):ℤ)))).Holds P K (x (v (d.selected i)))
  rw [←SquarefreeExpression.linearCoeff_relabel (d.expression h i) v (fun a => (x a:ℤ)) (d.selected i),
    ←SquarefreeExpression.constant_relabel (d.expression h i) v (fun a => (x a:ℤ)) (d.selected i),
    ←SquarefreeExpression.eval_relabel (d.expression h i) v (fun a => (x a:ℤ)),hs i,hm i,he i,hl i]
  exact hi

lemma descriptor_card (ℓ L t m : ℕ) :
    Fintype.card (WitnessTestDescriptor ℓ L t m)=
      (t^2*2*(L+1)^3*(ℓ+1)^2)*m^2*2 := by
  simp only [WitnessTestDescriptor,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,
    WitnessTestShape.card]
  ring

lemma card_le (ℓ L J t m : ℕ) :
    Fintype.card (WitnessTemplateCode ℓ L J t m) ≤
      Fintype.card (WitnessMetadata ℓ L t)*(m+1)^(Fintype.card (WitnessCodeSlot ℓ L J t)) *
      ((t+1)*(Fintype.card (WitnessTestDescriptor ℓ L t m)+1)^t) := by
  have hc : Fintype.card (WitnessTemplateCode ℓ L J t m) =
      Fintype.card (WitnessMetadata ℓ L t)*(m+1)^(Fintype.card (WitnessCodeSlot ℓ L J t)) *
        (∑ k : Fin (t+1), (Fintype.card (WitnessTestDescriptor ℓ L t m))^k.val) := by
    simp only [WitnessTemplateCode,Fintype.card_prod,Fintype.card_fun,Fintype.card_option,
      Fintype.card_fin,Fintype.card_sigma]
    ring
  rw [hc]
  apply Nat.mul_le_mul_left
  calc
    _ ≤ ∑ k : Fin (t+1), (Fintype.card (WitnessTestDescriptor ℓ L t m)+1)^t := by
      apply sum_le_sum
      intro k hk
      exact (Nat.pow_le_pow_left (Nat.le_succ _) k.val).trans
        (Nat.pow_le_pow_right (n:=Fintype.card (WitnessTestDescriptor ℓ L t m)+1)
          (Nat.succ_pos _) (Nat.lt_succ_iff.mp k.isLt))
    _ = _ := by simp

end WitnessTemplateCode
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
