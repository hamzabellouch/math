import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNZeroFactor
import OAI.Combinatorics.Chromatic.GradedAlgebra.StringBackshift

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus RawShuffle PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

lemma convolution_comm_isotropic (f g : (I→ℕ) → R)
    (h : ∀d e,f d≠0 → g e≠0 → Ω (P d) (P e)=0)
    (h' : ∀d e,g d≠0 → f e≠0 → Ω (P d) (P e)=0) :
    convolution v Ω P f g=convolution v Ω P g f := by
  classical
  funext d
  rw [convolution_of_isotropic_support v Ω P f g h,
    convolution_of_isotropic_support v Ω P g f h']
  let E : DimensionSplit d ≃ DimensionSplit d := {
    toFun:=fun s=>DimensionSplit.ofPair s.right s.left (by rw [add_comm,DimensionSplit.left_add_right])
    invFun:=fun s=>DimensionSplit.ofPair s.right s.left (by rw [add_comm,DimensionSplit.left_add_right])
    left_inv:=by
      intro s
      funext i
      apply Fin.ext
      change d i-(d i-(s i).val)=(s i).val
      have H:=(s i).isLt
      omega
    right_inv:=by
      intro s
      funext i
      apply Fin.ext
      change d i-(d i-(s i).val)=(s i).val
      have H:=(s i).isLt
      omega }
  apply Fintype.sum_equiv E
  intro s
  dsimp only [E,Equiv.coe_fn_mk]
  rw [DimensionSplit.left_ofPair,DimensionSplit.right_ofPair,mul_comm]

variable (w : I → ℕ) [Fact (∀i,0<w i)]
lemma push_inverse_adjoint_of_convolution (hΩ : ∀m,Ω m m=0) (m : M)
    (f q : (I→ℕ) → R) (hf : f 0=1)
    (hq : f=convolution v Ω P (fun d=>f d*↑(v^(2*Ω (P d) m))) q) :
    PowerSeries.invOfUnit (push w v Ω P f) 1*C (Torus.X v Ω m)*push w v Ω P f=
      C (Torus.X v Ω m)*push w v Ω P q := by
  let F:=push w v Ω P f
  let X:=C (Torus.X v Ω m)
  let Q:=push w v Ω P q
  have H : F*(X*Q)=X*F := by
    dsimp only [F,X,Q]
    rw [←mul_assoc,push_twist w v Ω P hΩ,mul_assoc,←push_convolution,←hq]
  have Hi : invOfUnit F 1*F=1 :=
    PowerSeries.invOfUnit_mul _ 1 (push_constant w v Ω P f hf)
  change invOfUnit F 1*X*F=X*Q
  calc
    _ = invOfUnit F 1*(X*F) := mul_assoc _ _ _
    _ = invOfUnit F 1*(F*(X*Q)) := by rw [H]
    _ = _ := by rw [←mul_assoc,Hi,one_mul]
end
end ElementaryPositivity.WeightedTorusSeries

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WallUnits WeightedTorusSeries
open PowerSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D)
variable (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)
variable (m : M) (htwist : ∀d,τ d= -Ω (P d) m)

include hdim hτ hiso htwist in
lemma stringSeries_inverse_convolution :
    stringSeries a dim k he=
      convolution LaurentRay.vUnit Ω P
        (fun d=>stringSeries a dim k he d*↑(LaurentRay.vUnit^(2*Ω (P d) m)))
        (stripSeries a t dim (fun s=>k s-2*(t s:ℤ)) τ hτ
          (backshiftString_admissible a t dim k τ hτ he)) := by
  let hg:=backshiftString_admissible a t dim k τ hτ he
  let g:=stringSeries a dim (fun s=>k s-2*(t s:ℤ)) hg
  let q:=stripSeries a t dim (fun s=>k s-2*(t s:ℤ)) τ hτ hg
  have H : (fun d=>stringSeries a dim k he d*↑(LaurentRay.vUnit^(2*Ω (P d) m)))=g := by
    funext d
    rw [LaurentRay.vUnit_zpow]
    dsimp only [g]
    rw [backshiftString_series a t dim k τ hτ he d]
    rw [htwist,mul_neg]
  rw [H]
  change stringSeries a dim k he=convolution LaurentRay.vUnit Ω P g q
  have hgs : ∀d,g d≠0 → d∈D := fun d h=>stringSeries_support a dim _ hg D hdim d h
  have hqs : ∀d,q d≠0 → d∈D := fun d h=>stripSeries_support a t dim _ hg D hdim τ hτ d h
  rw [convolution_comm_isotropic LaurentRay.vUnit Ω P g q
    (fun d e hd he=>hiso d (hgs d hd) e (hqs e he))
    (fun d e hd he=>hiso d (hqs d hd) e (hgs e he))]
  funext d
  rw [convolution_of_isotropic_support LaurentRay.vUnit Ω P q g
    (fun d e hd he=>hiso d (hqs d hd) e (hgs e he))]
  exact backstripString_series a t dim k τ hτ he d

variable (w : I → ℕ) [Fact (∀i,0<w i)]
include hdim hτ hiso htwist in
lemma stringSeries_inverse_adjoint (hΩ : ∀x,Ω x x=0) (hzero : stringSeries a dim k he 0=1) :
    invOfUnit (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) 1*
        C (Torus.X LaurentRay.vUnit Ω m)*push w LaurentRay.vUnit Ω P (stringSeries a dim k he)=
      C (Torus.X LaurentRay.vUnit Ω m)*push w LaurentRay.vUnit Ω P
        (stripSeries a t dim (fun s=>k s-2*(t s:ℤ)) τ hτ
          (backshiftString_admissible a t dim k τ hτ he)) := by
  exact push_inverse_adjoint_of_convolution LaurentRay.vUnit Ω P w hΩ m _ _ hzero
    (stringSeries_inverse_convolution a t dim k he D hdim τ hτ Ω P hiso m htwist)

include hdim hτ hiso htwist in

theorem stringSeries_inverse_adjoint_positive (hΩ : ∀x,Ω x x=0)
    (hzero : stringSeries a dim k he 0=1) :
    IntegralPositive Ω
      (invOfUnit (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) 1*
        C (Torus.X LaurentRay.vUnit Ω m)*push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) := by
  rw [stringSeries_inverse_adjoint a t dim k he D hdim τ hτ Ω P hiso m htwist w hΩ hzero]
  exact (completedPositive_C_X Ω m).mul Ω (push_positive Ω w P _
    (fun d=>LaurentPositive.series _ (stripEnergy_admissible a t dim _ τ hτ
      (backshiftString_admissible a t dim k τ hτ he) d)))
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
open QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]
local instance (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
variable (hΩ : ∀x,Ω x x=0)
variable (hgeom : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (θ : ℝ) (m : M)
variable (hm : ∀d∈slopeDimensions c η hc θ,Ω (P d) m≤0)

include hΩ hgeom hm in
lemma primitiveFactor_inverse_adjoint_positive :
    IntegralPositive Ω
      (invOfUnit (push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)) 1*
        C (Torus.X LaurentRay.vUnit Ω m)*
        push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)) := by
  let dim : SlopeStringStart a c η hc θ → (I→ℕ) := fun s=>s.1.val.1.val
  let τ : (I→ℕ) →+ ℤ := -((Ω.flip m).comp P)
  let t : SlopeStringStart a c η hc θ → ℕ := fun s=>(τ (dim s)).toNat
  have hdim : ∀s,dim s∈slopeDimensions c η hc θ := fun s=>s.1.val.1.property
  have ht : ∀s,(t s:ℤ)=τ (dim s) := fun s=>Int.toNat_of_nonneg (neg_nonneg.mpr (hm _ (hdim s)))
  have hi : ∀d∈slopeDimensions c η hc θ,∀e∈slopeDimensions c η hc θ,Ω (P d) (P e)=0 := by
    intro d hd e he
    rw [hgeom,eulerForm_slopeDimensions_symm a c η hc θ ⟨d,hd⟩ ⟨e,he⟩,sub_self]
  exact stringSeries_inverse_adjoint_positive (slopeStartRowType a c η hc θ) t dim
    (slopeStartParameter a κ c η hc θ) (primitiveCountsEnergy_admissible a κ c η hc θ)
    (slopeDimensions c η hc θ) hdim τ ht Ω P hi m (fun _=>rfl) w hΩ
    (primitiveCountsSeries_zero a κ c η hc θ)

variable (h : M →+ ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)
include hΩ hgeom hm hh in

theorem finiteInput_zero_inverse_adjoint_positive (ε : I → Bool)
    (ha : ∀i,a i i=elementaryDiagonal ε i) :
    let F := PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
      (zeroProject LaurentRay.vUnit Ω h) (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε))
    IntegralPositive Ω (invOfUnit F 1*C (Torus.X LaurentRay.vUnit Ω m)*F) := by
  dsimp only
  rw [←literalInput_primitiveFactor a κ c η hc w Ω P hgeom h θ hh ε ha]
  exact primitiveFactor_inverse_adjoint_positive a κ c η hc w Ω P hΩ hgeom θ m hm

end
end ElementaryPositivity.RawShuffle

end

end OAI
