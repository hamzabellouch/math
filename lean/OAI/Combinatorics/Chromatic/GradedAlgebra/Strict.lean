import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.TruncatedChart
import OAI.Combinatorics.Chromatic.Walls.RootProducts

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
lemma predicate_nsmul (P : M→Prop) (hP : ∀a b,P a→P b→P (a+b))
    (m : M) (hm : P m) (n : ℕ) (hn : 0<n) : P (n • m) := by
  induction n with
  | zero=>omega
  | succ n ih=>
    by_cases h0 : n=0
    · subst n; simpa using hm
    · rw [succ_nsmul]
      exact hP _ _ (ih (by omega)) hm
lemma WallUnitDatum.strictSupport (P : M→Prop) (hP : ∀a b,P a→P b→P (a+b))
    (u : WallUnitDatum M) (hu : u.Allowed C P) (n : ℕ) :
    SupportedOn LaurentRay.vUnit Ω P (coeff (n+1) (u.value Ω)) := by
  intro m hm
  rw [WallUnitDatum.value,coeff_weightedRay]
  split_ifs with hd
  · change (Finsupp.single (((n+1)/u.degree) • u.root) _) m=0
    apply Finsupp.single_eq_of_ne
    intro he
    apply hm
    rw [he]
    exact predicate_nsmul P hP u.root hu.2.2 _
      (Nat.div_pos (Nat.le_of_dvd (by omega) hd) hu.1)
  · rfl
lemma literalRootProducts_strictSupport (P : M→Prop) (hP : ∀a b,P a→P b→P (a+b))
    {F : PowerSeries (Torus LaurentRay.vUnit Ω)} (hF : F∈literalRootProducts Ω C P) :
    ∀n,SupportedOn LaurentRay.vUnit Ω P (coeff (n+1) F) := by
  obtain ⟨l,hl,rfl⟩:=hF
  induction l with
  | nil=>
    intro n
    simp only [List.map_nil,List.prod_nil,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false]
    exact SupportedOn.zero _ _ P
  | cons u l ih=>
    intro n
    simp only [List.map_cons,List.prod_cons]
    apply strict_mul_through LaurentRay.vUnit Ω P hP _ _ (n+1)
      (u.constant Ω) (literalRootProducts_constant Ω C P ⟨l,fun w hw=>hl w (by simp [hw]),rfl⟩)
      (fun j hj=>u.strictSupport Ω C P hP (hl u (by simp)) j)
      (fun j hj=>ih (fun w hw=>hl w (by simp [hw])) j) n le_rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
