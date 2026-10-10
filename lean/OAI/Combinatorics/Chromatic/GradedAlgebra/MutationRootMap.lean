import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RationalCutIdentity
import OAI.Combinatorics.Chromatic.QuantumTorus.SymplecticTorusMap
import OAI.Combinatorics.Chromatic.QuantumTorus.MutationFiberArithmetic

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

def mutationShear (p : M) : M →+ M where
  toFun m:=m-(Ω p m) • p
  map_zero':=by simp
  map_add':=by intro a b; simp only [map_add,add_zsmul]; abel

def mutationShearInverse (p : M) : M →+ M where
  toFun m:=m+(Ω p m) • p
  map_zero':=by simp
  map_add':=by intro a b; simp only [map_add,add_zsmul]; abel

lemma mutationShear_left_inverse (p : M) (hp : Ω p p=0) (m : M) :
    mutationShearInverse Ω p (mutationShear Ω p m)=m := by
  change (m-Ω p m • p)+Ω p (m-Ω p m • p) • p=m
  rw [map_sub,map_zsmul,hp,smul_zero,sub_zero,sub_add_cancel]
lemma mutationShear_right_inverse (p : M) (hp : Ω p p=0) (m : M) :
    mutationShear Ω p (mutationShearInverse Ω p m)=m := by
  change (m+Ω p m • p)-Ω p (m+Ω p m • p) • p=m
  rw [map_add,map_zsmul,hp,smul_zero,add_zero,add_sub_cancel_right]

def mutationShearEquiv (p : M) (hp : Ω p p=0) : M ≃+ M where
  toFun:=mutationShear Ω p
  invFun:=mutationShearInverse Ω p
  left_inv:=mutationShear_left_inverse Ω p hp
  right_inv:=mutationShear_right_inverse Ω p hp
  map_add':=(mutationShear Ω p).map_add

lemma mutationShear_pairing (hΩ : ∀m,Ω m m=0) (p a b : M) :
    Ω (mutationShear Ω p a) (mutationShear Ω p b)=Ω a b := by
  have hs : Ω a p= -Ω p a:=by
    have H:=hΩ (a+p)
    simp only [map_add,AddMonoidHom.add_apply,hΩ] at H
    omega
  change Ω (a-Ω p a • p) (b-Ω p b • p)=Ω a b
  simp only [map_sub,map_zsmul,AddMonoidHom.sub_apply,AddMonoidHom.zsmul_apply,
    smul_eq_mul,hΩ,hs]
  ring

def mutatedCoefficientMap (α : I → ℤ) : (I → ℤ) →+ (I → ℤ) where
  toFun d:=fun i=>if i=pc then -d pc+∑j∈Finset.univ.erase pc,max 0 (-α j)*d j else d i
  map_zero':=by ext i; simp
  map_add':=by
    intro a b; ext i
    by_cases hi : i=pc
    · subst i; simp only [ite_true,Pi.add_apply,neg_add,mul_add,Finset.sum_add_distrib]; ring
    · simp [hi]

@[simp] lemma mutatedCoefficientMap_off (α : I → ℤ) (d : I → ℤ) (i : I) (hi : i≠pc) :
    mutatedCoefficientMap pc α d i=d i := by simp [mutatedCoefficientMap,hi]
@[simp] lemma mutatedCoefficientMap_at (α : I → ℤ) (d : I → ℤ) :
    mutatedCoefficientMap pc α d pc= -d pc+∑j∈Finset.univ.erase pc,max 0 (-α j)*d j := by
  simp [mutatedCoefficientMap]

lemma mutatedCoefficientMap_involutive (α : I → ℤ) :
    Function.Involutive (mutatedCoefficientMap pc α) := by
  intro d; ext i
  by_cases hi : i=pc
  · subst i
    rw [mutatedCoefficientMap_at,mutatedCoefficientMap_at]
    have HH : (∑j∈Finset.univ.erase pc,max 0 (-α j)*mutatedCoefficientMap pc α d j)=
        ∑j∈Finset.univ.erase pc,max 0 (-α j)*d j:=by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mutatedCoefficientMap_off pc α d j (Finset.mem_erase.mp hj).1]
    rw [HH]; ring
  · rw [mutatedCoefficientMap_off pc α _ i hi,mutatedCoefficientMap_off pc α _ i hi]

def mutatedRoots : (I → ℤ) →+ M := C.comp (mutatedCoefficientMap pc (mutationPairing Ω C pc))
def mutatedCoordinates : M →+ (I → ℤ) :=
  (mutatedCoefficientMap pc (mutationPairing Ω C pc)).comp coord

include hcoord in
lemma mutatedCoordinates_retraction (d : I → ℤ) :
    mutatedCoordinates Ω C coord pc (mutatedRoots Ω C pc d)=d := by
  change mutatedCoefficientMap pc (mutationPairing Ω C pc)
    (coord (C (mutatedCoefficientMap pc (mutationPairing Ω C pc) d)))=d
  rw [hcoord]
  exact mutatedCoefficientMap_involutive pc _ d

lemma mutatedRoot_p : simpleRoot (mutatedRoots Ω C pc) pc= -simpleRoot C pc := by
  have he : mutatedCoefficientMap pc (mutationPairing Ω C pc) (Pi.single pc 1)=
      -(Pi.single pc 1 : I → ℤ):=by
    ext i
    by_cases hi : i=pc
    · subst i
      rw [mutatedCoefficientMap_at]
      have HH : (∑j∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc j)*((Pi.single pc 1 : I → ℤ) j))=0:=by
        apply Finset.sum_eq_zero
        intro j hj
        simp [(Finset.mem_erase.mp hj).1]
      rw [HH]; simp
    · rw [mutatedCoefficientMap_off pc _ _ i hi]
      simp [hi]
  change C (mutatedCoefficientMap pc (mutationPairing Ω C pc) (Pi.single pc 1))= -C (Pi.single pc 1)
  rw [he,map_neg]

lemma mutatedRoot_off (i : I) (hi : i≠pc) :
    simpleRoot (mutatedRoots Ω C pc) i=simpleRoot C i+
      max 0 (-mutationPairing Ω C pc i) • simpleRoot C pc := by
  have he : mutatedCoefficientMap pc (mutationPairing Ω C pc) (Pi.single i 1)=
      (Pi.single i 1 : I → ℤ)+max 0 (-mutationPairing Ω C pc i) • Pi.single pc 1:=by
    ext j
    by_cases hj : j=pc
    · subst j
      rw [mutatedCoefficientMap_at]
      have HH : (∑a∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc a)*((Pi.single i 1 : I → ℤ) a))=
          max 0 (-mutationPairing Ω C pc i):=by
        rw [Finset.sum_eq_single i]
        · simp
        · intro a ha hai; simp [hai]
        · simp [hi]
      rw [HH]
      simp [Ne.symm hi]
    · rw [mutatedCoefficientMap_off pc _ _ j hj]
      simp [Pi.single_apply,hj]
  change C (mutatedCoefficientMap pc (mutationPairing Ω C pc) (Pi.single i 1))=_
  rw [he,map_add,map_zsmul]
  rfl

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
def centeredCrossing (p m : M) (t : ℕ) : Torus v Ω :=
  ∑j : Fin (t+1),Torus.monomial v Ω (m+(j:ℕ) • p) ((centeredPolynomial v t).coeff j)
include hΩ in
lemma cut_centered_identity (p m : M) (t : ℕ) (ht : Ω p m=(t:ℤ)) :
    Torus.push v Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p)
      (centeredCrossing v Ω p m t)=centeredCrossing v Ω (-p) m t := by
  unfold centeredCrossing
  rw [map_sum]
  have H (j : Fin (t+1)) :
      Torus.push v Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p)
        (Torus.monomial v Ω (m+(j:ℕ) • p) ((centeredPolynomial v t).coeff j))=
      Torus.monomial v Ω (m+(j.rev:ℕ) • (-p)) ((centeredPolynomial v t).coeff j.rev) := by
    rw [Torus.push_monomial]
    have hj : (j:ℕ)≤t := by have HH:=j.isLt; omega
    have hr : (j.rev:ℕ)=t-(j:ℕ):=by rw [Fin.val_rev]; omega
    have he : mutationShear Ω p (m+(j:ℕ) • p)=m+(j.rev:ℕ) • (-p) := by
      change (m+(j:ℕ) • p)-Ω p (m+(j:ℕ) • p) • p=_
      rw [map_add,map_nsmul,hΩ,smul_zero,add_zero,ht]
      rw [←natCast_zsmul,←natCast_zsmul,smul_neg]
      rw [hr]
      have Hcast : ((t-(j:ℕ):ℕ):ℤ)=(t:ℤ)-(j:ℕ):=by omega
      rw [Hcast,sub_smul]
      abel
    rw [he,hr,centeredPolynomial_coeff_symmetry v t j hj]
  simp_rw [H]
  exact Equiv.sum_comp Fin.revPerm
    (fun j : Fin (t+1)=>Torus.monomial v Ω (m+(j:ℕ) • (-p)) ((centeredPolynomial v t).coeff j))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
