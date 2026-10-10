import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.RotationLocalPolynomials
import OAI.Combinatorics.Chromatic.QuantumTorus.IndependentSetElements

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M W : Type*} [Field K] [AddCommGroup M] [DecidableEq W]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (ell : M →+ ℤ) (p : M) (hp : ell p=1)

include hΩ in
lemma independent_rotation_slice (a c : M) (hpa : Ω p a=1) (hpc : Ω p c= -1)
    (hac : Ω a c=0) (w : W → M) (hw : ∀y,Ω p (w y)=0)
    (t : Finset W) (k : ℕ) :
    pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω)
      (embed v Ω hΩ ell p hp (∑ s : Finset (Fin 3),
        independentTerm v Ω (Sum.elim ![a,c+p,c] w) k (s.disjSum t))) =
      embed v Ω hΩ ell p hp (∑ s : Finset (Fin 3),
        independentTerm v Ω (Sum.elim ![a,a+p,c] w) k (s.disjSum t)) := by
  have hap : Ω a p= -1 := by rw [alternating_skew Ω hΩ a p,hpa]
  have oldab : Ω a (a+p)≠0 := by simp [map_add,hΩ,hap]
  have oldbc : Ω (a+p) c≠0 := by simp [map_add,hac,hpc]
  have newab : Ω a (c+p)≠0 := by simp [map_add,hac,hap]
  have newbc : Ω (c+p) c≠0 := by simp [map_add,hΩ,hpc]
  have hwp : Compatible Ω p w t := fun y _ => hw y
  have HA := compatible_add Ω a p w t hwp
  have HC := compatible_add Ω c p w t hwp
  rw [independent_triple_sum v Ω hΩ a (c+p) c newab newbc hac,
    independent_triple_sum v Ω hΩ a (a+p) c oldab oldbc hac]
  simp only [HA,HC]
  by_cases ht : IsIndependent Ω w t
  swap
  · simp only [ht,ite_false,map_zero]
  simp only [ht,ite_true]
  let z := ∑y∈t,w y
  have hpz : Ω p z=0 := by simp [z,map_sum,hw]
  have hpa' : Ω p (a+z)=1 := by rw [map_add,hpa,hpz,add_zero]
  have hpc' : Ω p (c+z)= -1 := by rw [map_add,hpc,hpz,add_zero]
  have hpac : Ω p (a+c+z)=0 := by rw [map_add,map_add,hpa,hpc,hpz]; norm_num
  have HA' := pureAction_pairing_one v Ω hΩ ell p hp (a+z) hpa'
  have HC' := pureAction_pairing_neg_one v Ω hΩ ell p hp (c+z) hpc'
  have H0 := pureAction_pairing_zero v Ω hΩ ell p hp z hpz
  have HAC := pureAction_pairing_zero v Ω hΩ ell p hp (a+c+z) hpac
  have hza : a+p+z=a+z+p := by abel
  have hzc : c+p+z=c+z+p := by abel
  change pureAction v _ _ (embed v Ω hΩ ell p hp
    ((if t.card=k then Torus.X v Ω z else 0)+
      (if t.card+1=k ∧ Compatible Ω a w t then Torus.X v Ω (a+z) else 0)+
      (if t.card+1=k ∧ Compatible Ω c w t then Torus.X v Ω (c+p+z) else 0)+
      (if t.card+1=k ∧ Compatible Ω c w t then Torus.X v Ω (c+z) else 0)+
      (if t.card+2=k ∧ Compatible Ω a w t ∧ Compatible Ω c w t then Torus.X v Ω (a+c+z) else 0))) = _
  rw [hza,hzc]
  have groupNew (A B C D E : Torus v Ω) : A+B+C+D+E=A+B+(D+C)+E := by abel
  rw [groupNew]
  simp only [ite_add_ite,zero_add]
  have groupOld (A B C D E : Torus v Ω) : A+B+C+D+E=A+(B+C)+D+E := by abel
  conv_rhs => rw [groupOld]
  simp only [ite_add_ite,zero_add]
  simp only [map_add]
  have embite (P : Prop) [Decidable P] (x : Torus v Ω) :
      embed v Ω hΩ ell p hp (if P then x else 0) =
        if P then embed v Ω hΩ ell p hp x else 0 := by
    split_ifs <;> simp
  have actite (P : Prop) [Decidable P] (x) :
      pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω)
        (if P then x else 0) =
        if P then pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω) x else 0 := by
    split_ifs <;> simp
  simp only [embite,actite]
  simp only [H0,HA',HC',HAC]
  rfl

include hΩ in
lemma independentElement_rotation [Fintype W] (a c : M)
    (hpa : Ω p a=1) (hpc : Ω p c= -1) (hac : Ω a c=0)
    (w : W → M) (hw : ∀y,Ω p (w y)=0) (k : ℕ) :
    pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω)
      (embed v Ω hΩ ell p hp (independentElement v Ω (Sum.elim ![a,c+p,c] w) k)) =
      embed v Ω hΩ ell p hp (independentElement v Ω (Sum.elim ![a,a+p,c] w) k) := by
  rw [independent_sum_decomposition,independent_sum_decomposition,map_sum,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact independent_rotation_slice v Ω hΩ ell p hp a c hpa hpc hac w hw t k
end
end ElementaryPositivity.RationalFiber

end

end OAI
