import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TorusPositive
import OAI.Combinatorics.Chromatic.GradedAlgebra.StringStripSeries
import OAI.Combinatorics.Chromatic.GradedAlgebra.WeightedPushTwist

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WallUnits WeightedTorusSeries
open PowerSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D)

def stringSeries (d : I→ℕ) : LaurentSeries ℚ := series _ (he d)

omit [Fintype I] [DecidableEq I] in
include hdim in
lemma stringSeries_support (d : I→ℕ) (hd : stringSeries a dim k he d≠0) : d∈D := by
  classical
  by_contra H
  let : IsEmpty (StringCounts a dim d) := ⟨fun x=>H (x.property ▸
    countDimension_mem _ _ D (fun s=>hdim s.1) x.val)⟩
  apply hd
  ext j
  rw [stringSeries,series_coeff]
  simp

variable (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
omit [Fintype I] [DecidableEq I] in
include hdim in
lemma stripSeries_support (d : I→ℕ) (hd : stripSeries a t dim k τ hτ he d≠0) : d∈D := by
  classical
  by_contra H
  let : IsEmpty (StripCounts a t dim d) := ⟨fun x=>H (x.property ▸
    countDimension_mem _ _ D (fun s=>hdim s.1) x.val)⟩
  apply hd
  ext j
  rw [stripSeries,series_coeff]
  simp

variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)
variable (m : M) (htwist : ∀d,τ d=Ω (P d) m)

include hiso hdim htwist hτ in
lemma stringSeries_twist_convolution :
    (fun d=>stringSeries a dim k he d*↑(LaurentRay.vUnit^(2*Ω (P d) m)))=
      convolution LaurentRay.vUnit Ω P (stripSeries a t dim k τ hτ he)
        (stringSeries a dim k he) := by
  funext d
  rw [LaurentRay.vUnit_zpow,←htwist]
  rw [convolution_of_isotropic_support LaurentRay.vUnit Ω P _ _
    (fun x y hx hy=>hiso x (stripSeries_support a t dim k he D hdim τ hτ x hx)
      y (stringSeries_support a dim k he D hdim y hy))]
  exact stringStrip_scaled a t dim k τ hτ he d

variable (w : I → ℕ) [Fact (∀i,0<w i)]
include hiso hdim htwist hτ in
lemma stringSeries_adjoint (hΩ : ∀x,Ω x x=0) (hzero : stringSeries a dim k he 0=1) :
    push w LaurentRay.vUnit Ω P (stringSeries a dim k he)*C (Torus.X LaurentRay.vUnit Ω m)*
        invOfUnit (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) 1=
      C (Torus.X LaurentRay.vUnit Ω m)*push w LaurentRay.vUnit Ω P (stripSeries a t dim k τ hτ he) := by
  exact push_adjoint_of_convolution w LaurentRay.vUnit Ω P hΩ m _ _ hzero
    (stringSeries_twist_convolution a t dim k he D hdim τ hτ Ω P hiso m htwist)

include hiso hdim htwist hτ in

theorem stringSeries_adjoint_positive (hΩ : ∀x,Ω x x=0)
    (hzero : stringSeries a dim k he 0=1) :
    IntegralPositive Ω
      (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)*C (Torus.X LaurentRay.vUnit Ω m)*
        invOfUnit (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) 1) := by
  rw [stringSeries_adjoint a t dim k he D hdim τ hτ Ω P hiso m htwist w hΩ hzero]
  exact (completedPositive_C_X Ω m).mul Ω (push_positive Ω w P _
    (fun d=>LaurentPositive.series _ (stripEnergy_admissible a t dim k τ hτ he d)))

end
end ElementaryPositivity.UnitSelections

end

end OAI
