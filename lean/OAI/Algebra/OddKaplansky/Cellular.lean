import OAI.Algebra.OddKaplansky.Transfer

namespace OAI

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.Cellular
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G]
def rightShift (u : G) : Module.End K (G → K) where
  toFun x g := x (g*u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def shift : G →* Module.End K (G → K) where
  toFun := rightShift
  map_one' := by ext x g; simp [rightShift]
  map_mul' u v := by ext x g; simp [rightShift,mul_assoc]
def operator : MonoidAlgebra K G →ₐ[K] Module.End K (G → K) := MonoidAlgebra.lift K _ _ shift
lemma operator_single (u : G) (c : K) (x : G → K) (g : G) : operator (MonoidAlgebra.single u c) x g=c*x (g*u) := by
  rw [operator,MonoidAlgebra.lift_single]
  rfl
lemma operator_formula (a : MonoidAlgebra K G) (x : G → K) (g : G) : operator a x g=∑ u ∈ a.coeff.support, a.coeff u*x (g*u) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single a]
  simp only [Finsupp.sum,map_sum,LinearMap.sum_apply,Finset.sum_apply,operator_single]
lemma operator_mul (a b : MonoidAlgebra K G) (x : G → K) : operator (a*b) x=operator a (operator b x) := by rw [map_mul]; rfl
lemma operator_one (x : G → K) : operator (1 : MonoidAlgebra K G) x=x := by rw [map_one]; rfl
lemma indicator_eval (a : MonoidAlgebra K G) (h : G) : operator a (Pi.single h 1) 1=a.coeff h := by
  rw [operator_formula]
  simp only [one_mul,Pi.single_apply,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hh
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hh).symm
lemma operator_injective : Function.Injective (operator (K := K) (G := G)) := by
  intro a b he
  ext h
  simpa only [indicator_eval] using congrArg (fun T : Module.End K (G → K) => T (Pi.single h 1) 1) he

def IsCellular (F : (G → K) → (G → K)) : Prop :=
  ∃ S : Finset G, ∃ rule : (S → K) → K, ∀ x g, F x g=rule (fun u => x (g*u))
lemma operator_cellular (a : MonoidAlgebra K G) : IsCellular (operator a) := by
  refine ⟨a.coeff.support,fun z => ∑ u : a.coeff.support, a.coeff u*z u,?_⟩
  intro x g
  rw [operator_formula]
  exact (Finset.sum_attach a.coeff.support (fun u => a.coeff u*x (g*u))).symm
lemma left_inverse (a b : MonoidAlgebra K G) (hab : a*b=1) : Function.LeftInverse (operator a) (operator b) := by
  intro x
  rw [← operator_mul,hab,operator_one]
lemma range_eq (a b : MonoidAlgebra K G) (hab : a*b=1) : Set.range (operator b)={y | operator (b*a) y=y} := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    change operator (b*a) (operator b x)=operator b x
    rw [operator_mul,left_inverse a b hab x]
  · intro hy
    exact ⟨operator a y,by rw [← operator_mul]; exact hy⟩
lemma missing_indicator (a b : MonoidAlgebra K G) (hab : a*b=1) (h : G) (hh : (b*a-1).coeff h ≠ 0) :
    Pi.single h 1 ∉ Set.range (operator b) := by
  rw [range_eq a b hab]
  intro he
  have hv := congrFun he 1
  rw [indicator_eval] at hv
  apply hh
  change (b*a).coeff h-(1 : MonoidAlgebra K G).coeff h=0
  rw [← indicator_eval (1 : MonoidAlgebra K G),operator_one,hv,sub_self]
lemma theorem_all_configurations (a b : MonoidAlgebra K G) (hab : a*b=1) (hba : b*a≠1) :
    IsCellular (operator b) ∧ Function.Injective (operator b) ∧ ¬Function.Surjective (operator b) ∧
    Set.range (operator b)={y | operator (b*a) y=y} ∧
    ∃ h : G, (b*a-1).coeff h ≠ 0 ∧ Pi.single h 1 ∉ Set.range (operator b) := by
  have hex : ∃ h : G, (b*a-1).coeff h≠0 := by
    by_contra! hh
    apply hba
    apply sub_eq_zero.mp
    ext h
    exact hh h
  obtain ⟨h,hh⟩ := hex
  have hm := missing_indicator a b hab h hh
  exact ⟨operator_cellular b,(left_inverse a b hab).injective,
    fun hs => hm (hs (Pi.single h 1)),range_eq a b hab,h,hh,hm⟩
end
end OddKaplansky.Cellular

end

end OAI
