import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockSiteOneBody
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardEnergyLower

namespace OAI

/-! Exact identification of the compressed Coulomb CAR Hamiltonian
with the full half-filled Hubbard variational problem. -/

noncomputable section
open scoped BigOperators Classical InnerProductSpace
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

variable {Edge : Type*} [Fintype Edge]

def hubbardOneBodyMatrix (m : ℕ) (V : Fin (m+1) → Fin (m+1) → ℝ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    Fin ((2*m+1)+1) → Fin ((2*m+1)+1) → ℂ :=
  spinLift m (fun i j => graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j -
    if i=j then ((∑ k, V i k : ℝ):ℂ) else 0)

def hubbardCoulombTensor (m : ℕ) (U : ℝ) (V : Fin (m+1) → Fin (m+1) → ℝ)
    (a b c d : Fin ((2*m+1)+1)) : ℂ :=
  if a=c ∧ b=d then siteCoulombCoefficient U V (modeSite m a) (modeSite m b) else 0

theorem hubbardOneBodyMatrix_split (m : ℕ) (V : Fin (m+1) → Fin (m+1) → ℝ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    hubbardOneBodyMatrix m V left right t = fun a b =>
      spinLift m (graphHoppingMatrix m left right (fun e => (t e:ℂ))) a b +
        if a=b then -((∑ j, V (modeSite m a) j : ℝ):ℂ) else 0 := by
  funext a b
  obtain ⟨⟨i,σ⟩,rfl⟩ := (siteModes m).surjective a
  obtain ⟨⟨j,τ⟩,rfl⟩ := (siteModes m).surjective b
  change _ = _ + if siteMode m i σ=siteMode m j τ then _ else 0
  simp only [hubbardOneBodyMatrix,spinLift,modeSite,Equiv.symm_apply_apply,
    siteMode_eq_iff]
  by_cases hij : i=j <;> by_cases hστ : σ=τ <;> simp [hij,hστ,sub_eq_add_neg]

theorem hubbardCAR_operator (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hdiag : ∀ i, V i i=0)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
      twoBodyOperator (hubbardCoulombTensor m U V) =
        siteChargeOperator m U V + graphHopping m left right (fun e => (t e:ℂ)) := by
  rw [hubbardOneBodyMatrix_split]
  have hadd {Q : ℕ} (K L : Fin (Q+1) → Fin (Q+1) → ℂ) :
      oneBodyOperator (fun a b => K a b+L a b) = oneBodyOperator K+oneBodyOperator L := by
    simp only [oneBodyOperator,add_smul,Finset.sum_add_distrib]
  rw [hadd,oneBodyOperator_graphHopping]
  have hd := directCoulomb_operator m U V hdiag
  change _ + twoBodyOperator (fun a b c d => if a=c ∧ b=d then
    siteCoulombCoefficient U V (modeSite m a) (modeSite m b) else 0) = _
  rw [← hd]
  abel

theorem hubbardCAR_halfFilled (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j=V j i)
    (hdiag : ∀ i, V i i=0) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    (oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
      twoBodyOperator (hubbardCoulombTensor m U V)) x =
        (chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))) x -
          (((1/2:ℝ)*∑ i, ∑ j, V i j : ℝ):ℂ) • x := by
  rw [hubbardCAR_operator m U V hdiag,LinearMap.add_apply,
    siteChargeOperator_halfFilled m U V hsymm x hx,LinearMap.add_apply]
  abel

theorem hubbardCAR_form (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j=V j i)
    (hdiag : ∀ i, V i i=0) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    (occupationInner (2*m+1) x
      ((oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
        twoBodyOperator (hubbardCoulombTensor m U V)) x)).re =
      hubbardFermionForm m U V left right t x -
        ((1/2:ℝ)*∑ i, ∑ j, V i j)*fockMass x := by
  rw [hubbardCAR_halfFilled m U V hsymm hdiag left right t x hx,
    occupationInner_fockCoordinates,map_sub,map_smul,inner_sub_right,inner_smul_right]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  rw [← euclidean_real_inner,← hubbardFermionForm,inner_self_eq_norm_sq_to_K]
  have hreal (r : ℝ) : ((r:ℂ)^2).re = r^2 := by
    rw [pow_two,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
    ring
  change hubbardFermionForm m U V left right t x -
    ((1/2:ℝ)*∑ i, ∑ j, V i j)*((‖fockCoordinates (2*m+1) x‖:ℂ)^2).re = _
  rw [hreal,fockCoordinates_norm_sq]

theorem hubbardCAR_lower (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j=V j i)
    (hdiag : ∀ i, V i i=0) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    (hubbardFermionBottom m U V left right t-(1/2:ℝ)*∑ i, ∑ j, V i j)*fockMass x ≤
      (occupationInner (2*m+1) x
        ((oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
          twoBodyOperator (hubbardCoulombTensor m U V)) x)).re := by
  rw [hubbardCAR_form m U V hsymm hdiag left right t x hx,sub_mul]
  exact sub_le_sub_right (hubbardFermionBottom_lower m U V left right t x hx) _

theorem hubbardCAR_approximation_lower (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j=V j i)
    (hdiag : ∀ i, V i i=0) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) (energy error : ℝ)
    (herr : |energy-(occupationInner (2*m+1) x
      ((oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
        twoBodyOperator (hubbardCoulombTensor m U V)) x)).re| ≤ error*fockMass x) :
    (hubbardFermionBottom m U V left right t-(1/2:ℝ)*∑ i, ∑ j, V i j-error)*
      fockMass x ≤ energy := by
  have h := hubbardCAR_lower m U V hsymm hdiag left right t x hx
  have he := (abs_le.mp herr).1
  nlinarith

theorem hubbardCAR_approximation_upper (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j=V j i)
    (hdiag : ∀ i, V i i=0) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) (energy error a : ℝ)
    (herr : |energy-(occupationInner (2*m+1) x
      ((oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
        twoBodyOperator (hubbardCoulombTensor m U V)) x)).re| ≤ error*fockMass x)
    (ha : hubbardFermionForm m U V left right t x ≤ a*fockMass x) :
    energy ≤ (a-(1/2:ℝ)*∑ i, ∑ j, V i j+error)*fockMass x := by
  rw [hubbardCAR_form m U V hsymm hdiag left right t x hx] at herr
  have he := (abs_le.mp herr).2
  nlinarith

end ContinuumCoulomb.HubbardGlobal

end

end OAI
