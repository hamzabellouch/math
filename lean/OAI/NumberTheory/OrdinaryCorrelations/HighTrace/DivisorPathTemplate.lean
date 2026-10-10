import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GoodGapTemplate
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorPath
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeIndex

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.NumericalSubtrees OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical
noncomputable section
abbrev DivisorPathTemplate (ℓ K J t m : ℕ) :=
  (Fin ℓ → Bool) × (Fin ℓ × Fin J → Option (Fin m)) ×
    (Fin t → GapPathCode ℓ K) × (Fin t → Fin m)
namespace DivisorPathTemplate
variable {ℓ K J t m : ℕ}
def selected (d : DivisorPathTemplate ℓ K J t m) := d.2.2.2
def expression (d : DivisorPathTemplate ℓ K J t m) (h : ℕ) (i : Fin t) :=
  PatternExpression.gap h d.1 d.2.1 (d.2.2.1 i)
def WellFormed (d : DivisorPathTemplate ℓ K J t m) (h : ℕ) : Prop :=
  Function.Injective d.selected ∧ ∀ i j,d.selected j ∉ (d.expression h i).support

def embedding (d : DivisorPathTemplate ℓ K J t m) (h : ℕ) (hd : d.WellFormed h) : Fin t ↪ Fin m :=
  ⟨d.selected,hd.1⟩
def system (d : DivisorPathTemplate ℓ K J t m) (h : ℕ) (hd : d.WellFormed h) :
    TriangularExpressions (d.embedding h hd) K where
  expression := d.expression h
  modulus := d.selected
  linear _ := false
  divisor_modulus _ _ := rfl
  divisor_own_absent i _ := hd.2 i i
  linear_modulus_ne _ hi := Bool.noConfusion hi
  future_absent i j hij := by
    intro hj
    rcases mem_insert.mp hj with heq | hs
    · exact (ne_of_gt hij) (hd.1 heq)
    · exact hd.2 i j hs

lemma card_le (ℓ K J t m : ℕ) :
    Fintype.card (DivisorPathTemplate ℓ K J t m) ≤ Fintype.card (GapTemplate ℓ K J t m) := by
  apply Fintype.card_le_of_injective
    (fun d : DivisorPathTemplate ℓ K J t m => (⟨d.1,d.2.1,d.2.2.1,d.2.2.2,d.2.2.2⟩ : GapTemplate ℓ K J t m))
  intro a b hab
  have h1 : a.1=b.1 := congrArg (fun d : GapTemplate ℓ K J t m => d.1) hab
  have h2 : a.2.1=b.2.1 := congrArg (fun d : GapTemplate ℓ K J t m => d.2.1) hab
  have h3 : a.2.2.1=b.2.2.1 := congrArg (fun d : GapTemplate ℓ K J t m => d.2.2.1) hab
  have h4 : a.2.2.2=b.2.2.2 := congrArg (fun d : GapTemplate ℓ K J t m => d.2.2.2.1) hab
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
end DivisorPathTemplate

namespace NumericalLine.ShortCorruptSelection
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K t : ℕ}
variable {w : NumericalLine D h ℓ} (s : w.ShortCorruptSelection K t)
def tests : TriangularExpressions s.selected K where
  expression i := (s.path i).expression
  modulus := s.selected
  linear _ := false
  divisor_modulus _ _ := rfl
  divisor_own_absent i _ := s.independent i i
  linear_modulus_ne _ hi := Bool.noConfusion hi
  future_absent i j hij := by
    intro hj
    rcases mem_insert.mp hj with heq | hs
    · exact (ne_of_gt hij) (s.selected.injective heq)
    · exact s.independent i j hs
lemma admissible (P : ℝ) (hB : 0≤B) (hS : ∀ p : S.Index,(p:ℝ) ≤ Real.exp B) :
    s.tests.Admissible P (Specification.densitySize B C₀ h K) (fun p => (p:ℕ)) :=
  fun i => (s.path i).numeric_holds P hB hS

def selectedIndex (i : Fin t) : Fin (support w.linePrimeCode).card :=
  w.primeIndex (s.selected i) (w.used_mem_support _ (s.used i))
def template : DivisorPathTemplate ℓ K ⌈C₀*Real.log B⌉₊ t (support w.linePrimeCode).card :=
  ⟨signBit w.line,pattern w.linePrimeCode,fun i => (s.path i).path.code,s.selectedIndex⟩
lemma selected_relabel (i : Fin t) : values w.linePrimeCode (s.template.selected i)=s.selected i :=
  w.values_primeIndex _ _
lemma expression_relabel (i : Fin t) :
    (s.template.expression h i).relabel (values w.linePrimeCode)=(s.path i).expression := by
  change (PatternExpression.gap h (signBit w.line) (pattern w.linePrimeCode) (s.path i).path.code).relabel _=_
  rw [PatternExpression.gap_relabel]
  simp_rw [decode_pattern]
  exact (s.path i).path.code_source _ _ _
lemma formed : s.template.WellFormed h := by
  constructor
  · intro i j hij
    apply s.selected.injective
    rw [←s.selected_relabel i,←s.selected_relabel j,hij]
  · intro i j hj
    apply s.independent i j
    rw [←s.expression_relabel i,SquarefreeExpression.support_relabel]
    exact mem_image.mpr ⟨s.template.selected j,hj,s.selected_relabel j⟩
lemma template_admissible (P : ℝ) (hB : 0≤B) (hS : ∀ p : S.Index,(p:ℝ) ≤ Real.exp B) :
    (s.template.system h s.formed).Admissible P (Specification.densitySize B C₀ h K)
      (fun i => (values w.linePrimeCode i:ℕ)) := by
  intro i
  change (ArithmeticClause.divisor ((s.template.expression h i).eval
    (fun a => ((values w.linePrimeCode a:ℕ):ℤ)))).Holds P _ (values w.linePrimeCode (s.template.selected i):ℕ)
  rw [←SquarefreeExpression.eval_relabel _ (values w.linePrimeCode) (fun p => ((p:ℕ):ℤ)),s.expression_relabel,s.selected_relabel]
  exact (s.path i).numeric_holds P hB hS
end NumericalLine.ShortCorruptSelection

abbrev GoodDivisorPathTemplate (h ℓ K J t m : ℕ) := {d : DivisorPathTemplate ℓ K J t m // d.WellFormed h}
def divisorPathTemplateMass (S : PrimeSystem) (P Z : ℝ) (h ℓ K J t : ℕ) : ℝ :=
  ∑ m : Fin (ℓ*J+1),∑ d : GoodDivisorPathTemplate h ℓ K J t m.val,
    ∑ v : Fin m.val → S.Index,(d.val.system h d.property).fiberWeight P Z (fun a => (v a:ℕ))

lemma divisorPathTemplateMass_le (S : PrimeSystem) (P B Z : ℝ) (h ℓ K J t : ℕ)
    (hP : 0<P) (hB : 0≤B) (hZ : 0≤Z)
    (hS : ∀ p : S.Index,P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B) :
    divisorPathTemplateMass S P Z h ℓ K J t ≤ (gapTemplateBudget ℓ K J t:ℝ)*
      (max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹))^(ℓ*J)*(max (Z/(P*Real.log 2)) ((2+B)/P))^t := by
  let N := ℓ*J
  let H : ℝ := max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹)
  let δ : ℝ := max (Z/(P*Real.log 2)) ((2+B)/P)
  let C : ℕ := 2^ℓ*(N+1)^N*(2*ℓ+1)^(K*t)*(N+1)^(2*t)
  have hH : 1≤H := le_max_left _ _
  have h0H : 0≤H := zero_le_one.trans hH
  have hδ : 0≤δ := le_trans (by positivity : 0≤(2+B)/P) (le_max_right _ _)
  have hrow (m : Fin (N+1)) (d : GoodDivisorPathTemplate h ℓ K J t m.val) :
      (∑ v : Fin m.val → S.Index,(d.val.system h d.property).fiberWeight P Z (fun a => (v a:ℕ))) ≤ H^N*δ^t := by
    apply ((d.val.system h d.property).fiber_sum_le S.primes P B Z hP hB hZ
      (fun p hp => ⟨S.prime_mem p hp,(hS ⟨p,hp⟩).1,(hS ⟨p,hp⟩).2⟩)).trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hδ _)
    apply (pow_le_pow_left₀ (by positivity) (le_max_right (1:ℝ) _) _).trans
    apply pow_le_pow_right₀ hH
    rw [unselected_card,Fintype.card_fin]
    omega
  have hcodes (m : Fin (N+1)) :
      (∑ d : GoodDivisorPathTemplate h ℓ K J t m.val,
        ∑ v : Fin m.val → S.Index,(d.val.system h d.property).fiberWeight P Z (fun a => (v a:ℕ))) ≤
      (C:ℝ)*(H^N*δ^t) := by
    calc
      _ ≤ ∑ _d : GoodDivisorPathTemplate h ℓ K J t m.val,H^N*δ^t := sum_le_sum (fun d _ => hrow m d)
      _ = (Fintype.card (GoodDivisorPathTemplate h ℓ K J t m.val):ℝ)*(H^N*δ^t) := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Fintype.card_subtype_le _).trans ((DivisorPathTemplate.card_le ..).trans
          (gapTemplate_card_uniform ℓ K J t m.val (Nat.lt_succ_iff.mp m.isLt)))
  calc
    _ ≤ ∑ m : Fin (N+1),(C:ℝ)*(H^N*δ^t) := sum_le_sum (fun m _ => hcodes m)
    _ = ((N+1:ℕ):ℝ)*(C:ℝ)*(H^N*δ^t) := by simp [mul_assoc]
    _ = _ := by dsimp only [C,N,H,δ,gapTemplateBudget]; push_cast; ring

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
