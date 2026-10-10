import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GoodGapTemplate
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Constant
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ZeroExpression

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
noncomputable section

abbrev FarTemplate (ℓ K J t m R : ℕ) :=
  Fin (2*R+1) × (Fin ℓ → Bool) × (Fin ℓ × Fin J → Option (Fin m)) ×
    (Fin t → GapPathCode ℓ K) × (Fin t → GapPathCode ℓ K) × (Fin t → Fin m)
namespace FarTemplate
variable {ℓ K J t m R : ℕ}
def selected (d : FarTemplate ℓ K J t m R) := d.2.2.2.2.2
def root (d : FarTemplate ℓ K J t m R) : ℤ := (d.1.val:ℤ)-R
def first (d : FarTemplate ℓ K J t m R) (h : ℕ) (i : Fin t) :=
  PatternExpression.gap h d.2.1 d.2.2.1 (d.2.2.2.1 i)
def second (d : FarTemplate ℓ K J t m R) (h : ℕ) (i : Fin t) :=
  PatternExpression.gap h d.2.1 d.2.2.1 (d.2.2.2.2.1 i)
def expression (d : FarTemplate ℓ K J t m R) (h : ℕ) (i : Fin t) :=
  (((SquarefreeExpression.constant d.root).append (d.first h i).neg).append (d.second h i))
def WellFormed (d : FarTemplate ℓ K J t m R) (h : ℕ) : Prop :=
  Function.Injective d.selected ∧ (∀ i,d.selected i ∉ (d.expression h i).support) ∧
    ∀ i j,i<j → d.selected j ∉ (d.expression h i).support

def embedding (d : FarTemplate ℓ K J t m R) (h : ℕ) (hd : d.WellFormed h) : Fin t ↪ Fin m :=
  ⟨d.selected,hd.1⟩
def system (d : FarTemplate ℓ K J t m R) (h : ℕ) (hd : d.WellFormed h) :
    TriangularExpressions (d.embedding h hd) ((1+K)+K) where
  expression := d.expression h
  modulus := d.selected
  linear _ := false
  divisor_modulus _ _ := rfl
  divisor_own_absent i _ := hd.2.1 i
  linear_modulus_ne _ hi := Bool.noConfusion hi
  future_absent i j hij := by
    intro hj
    rcases mem_insert.mp hj with heq | hs
    · exact (ne_of_gt hij) (hd.1 heq)
    · exact hd.2.2 i j hij hs

lemma formed_of_relabel (d : FarTemplate ℓ K J t m R) (h : ℕ)
    {α : Type*} [DecidableEq α] (v : Fin m ↪ α) (e : Fin t ↪ α)
    (q : TriangularExpressions e ((1+K)+K)) (hdiv : ∀ i,q.linear i=false)
    (hs : ∀ i,v (d.selected i)=e i)
    (he : ∀ i,(d.expression h i).relabel v=q.expression i) : d.WellFormed h := by
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    apply e.injective
    rw [←hs i,←hs j,hij]
  · intro i hi
    apply q.divisor_own_absent i (hdiv i)
    rw [←he i,SquarefreeExpression.support_relabel]
    exact mem_image.mpr ⟨_,hi,hs i⟩
  · intro i j hij hj
    apply q.future_absent i j hij
    apply mem_insert_of_mem
    rw [←he i,SquarefreeExpression.support_relabel]
    exact mem_image.mpr ⟨_,hj,hs j⟩

lemma card_le (ℓ K J t m R : ℕ) :
    Fintype.card (FarTemplate ℓ K J t m R) ≤ (2*R+1)*Fintype.card (GapTemplate ℓ (K+K) J t m) := by
  let f : FarTemplate ℓ K J t m R → Fin (2*R+1) × GapTemplate ℓ (K+K) J t m := fun d =>
    (d.1,⟨d.2.1,d.2.2.1,fun i => Fin.addCases (d.2.2.2.1 i) (d.2.2.2.2.1 i),d.selected,d.selected⟩)
  have hf : Function.Injective f := by
    intro a b he
    have h0 := congrArg Prod.fst he
    have h1 := congrArg (fun z => z.2.1) he
    have h2 := congrArg (fun z => z.2.2.1) he
    have hp := congrArg (fun z => z.2.2.2.1) he
    have hs := congrArg (fun z => z.2.2.2.2.1) he
    have h3 : a.2.2.2.1=b.2.2.2.1 := by
      funext i j
      simpa only [f,Fin.addCases_left] using congrFun (congrFun hp i) (j.castAdd K)
    have h4 : a.2.2.2.2.1=b.2.2.2.2.1 := by
      funext i j
      simpa only [f,Fin.addCases_right] using congrFun (congrFun hp i) (j.natAdd K)
    exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 hs))))
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective f hf
end FarTemplate

abbrev GoodFarTemplate (h ℓ K J t m R : ℕ) := {d : FarTemplate ℓ K J t m R // d.WellFormed h}
def farTemplateMass (S : PrimeSystem) (P Z : ℝ) (h ℓ K J t R : ℕ) : ℝ :=
  ∑ m : Fin (ℓ*J+1),∑ d : GoodFarTemplate h ℓ K J t m.val R,
    ∑ v : Fin m.val → S.Index,(d.val.system h d.property).fiberWeight P Z (fun a => (v a:ℕ))

lemma farTemplateMass_le (S : PrimeSystem) (P B Z : ℝ) (h ℓ K J t R : ℕ)
    (hP : 0<P) (hB : 0≤B) (hZ : 0≤Z)
    (hS : ∀ p : S.Index,P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B) :
    farTemplateMass S P Z h ℓ K J t R ≤ ((2*R+1:ℕ):ℝ)*(gapTemplateBudget ℓ (K+K) J t:ℝ)*
      (max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹))^(ℓ*J)*(max (Z/(P*Real.log 2)) ((2+B)/P))^t := by
  let N := ℓ*J
  let H : ℝ := max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹)
  let δ : ℝ := max (Z/(P*Real.log 2)) ((2+B)/P)
  let C : ℕ := (2*R+1)*(2^ℓ*(N+1)^N*(2*ℓ+1)^((K+K)*t)*(N+1)^(2*t))
  have hH : 1≤H := le_max_left _ _
  have h0H : 0≤H := zero_le_one.trans hH
  have hδ : 0≤δ := le_trans (by positivity : 0≤(2+B)/P) (le_max_right _ _)
  have hrow (m : Fin (N+1)) (d : GoodFarTemplate h ℓ K J t m.val R) :
      (∑ v : Fin m.val → S.Index,(d.val.system h d.property).fiberWeight P Z (fun a => (v a:ℕ))) ≤ H^N*δ^t := by
    apply ((d.val.system h d.property).fiber_sum_le S.primes P B Z hP hB hZ
      (fun p hp => ⟨S.prime_mem p hp,(hS ⟨p,hp⟩).1,(hS ⟨p,hp⟩).2⟩)).trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hδ _)
    apply (pow_le_pow_left₀ (by positivity) (le_max_right (1:ℝ) _) _).trans
    apply pow_le_pow_right₀ hH
    rw [unselected_card,Fintype.card_fin]
    omega
  have hcodes (m : Fin (N+1)) :
      (∑ d : GoodFarTemplate h ℓ K J t m.val R,
        ∑ v : Fin m.val → S.Index,(d.val.system h d.property).fiberWeight P Z (fun a => (v a:ℕ))) ≤
      (C:ℝ)*(H^N*δ^t) := by
    calc
      _ ≤ ∑ _d : GoodFarTemplate h ℓ K J t m.val R,H^N*δ^t := sum_le_sum (fun d _ => hrow m d)
      _ = (Fintype.card (GoodFarTemplate h ℓ K J t m.val R):ℝ)*(H^N*δ^t) := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Fintype.card_subtype_le _).trans ((FarTemplate.card_le ..).trans
          (Nat.mul_le_mul_left _ (gapTemplate_card_uniform ℓ (K+K) J t m.val (Nat.lt_succ_iff.mp m.isLt))))
  calc
    _ ≤ ∑ m : Fin (N+1),(C:ℝ)*(H^N*δ^t) := sum_le_sum (fun m _ => hcodes m)
    _ = ((N+1:ℕ):ℝ)*(C:ℝ)*(H^N*δ^t) := by simp [mul_assoc]
    _ = _ := by dsimp only [C,N,H,δ,gapTemplateBudget]; push_cast; ring

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
