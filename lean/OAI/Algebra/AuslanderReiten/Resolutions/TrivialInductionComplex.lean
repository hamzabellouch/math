import OAI.Algebra.AuslanderReiten.Modules.TrivialInduction
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCategory
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "T" => TrivialExtension k R

variable {ι : Type*} {c : ComplexShape ι}

def dualComplex (P : HomologicalComplex (ModuleCat.{u} R) c) :
    HomologicalComplex (ModuleCat.{u} T) c :=
  ((BalancedTensor.functor (k := k) (R := R) (S := T) (F := Coinduced k R)).mapHomologicalComplex c).obj P

def inducedComplex (P : HomologicalComplex (ModuleCat.{u} R) c) :
    HomologicalComplex (ModuleCat.{u} T) c :=
  ((BalancedTensor.functor (k := k) (R := R) (S := T) (F := Middle (k := k) (R := R))).mapHomologicalComplex c).obj P

def quotientComplex (P : HomologicalComplex (ModuleCat.{u} R) c) :
    HomologicalComplex (ModuleCat.{u} T) c :=
  ((BalancedTensor.functor (k := k) (R := R) (S := T) (F := Quotient (k := k) (R := R))).mapHomologicalComplex c).obj P

def sequence (P : HomologicalComplex (ModuleCat.{u} R) c) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} T) c) :=
  BalancedTensor.complexSequence (k := k) inclusion projection inclusion_left
    projection_left projection_inclusion P

theorem sequence_shortExact (P : HomologicalComplex (ModuleCat.{u} R) c)
    [∀ i, Module.Finite R (P.X i)] [∀ i, Module.Projective R (P.X i)] :
    (sequence (k := k) P).ShortExact :=
  BalancedTensor.complexSequence_shortExact inclusion projection inclusion_left
    projection_left projection_inclusion inclusion_injective inclusion_projection_exact
    projection_surjective P

instance induced_term_projective (P : HomologicalComplex (ModuleCat.{u} R) c) (i : ι)
    [Module.Finite R (P.X i)] [Module.Projective R (P.X i)] :
    Module.Projective T ((inducedComplex (k := k) P).X i) :=
  BalancedTensor.projective

instance induced_term_finite (P : HomologicalComplex (ModuleCat.{u} R) c) (i : ι)
    [Module.Finite R (P.X i)] [Module.Projective R (P.X i)] :
    Module.Finite T ((inducedComplex (k := k) P).X i) :=
  BalancedTensor.finite

theorem dualComplex_ideal_zero (P : HomologicalComplex (ModuleCat.{u} R) c) (i : ι)
    (ψ : Module.Dual k R) (z : (dualComplex (k := k) P).X i) :
    TrivialExtension.inr ψ • z = 0 := by
  have hz : ∀ w : BalancedTensor k R (Coinduced k R) (P.X i),
      TrivialExtension.inr ψ • w = 0 := by
    intro w
    induction w using BalancedTensor.induction_on with
    | zero => exact smul_zero _
    | tmul φ v => rw [BalancedTensor.smul_tmul, dual_ideal_annihilates, BalancedTensor.zero_tmul]
    | add x y hx hy => rw [smul_add, hx, hy, zero_add]
  exact hz z

variable (P : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Finite R (P.X i)] [∀ i, Module.Projective R (P.X i)]
    [HasDerivedCategory (ModuleCat.{u} (TrivialExtension k R))]

def triangle : CategoryTheory.Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} T)) :=
  DerivedCategory.triangleOfSES (sequence_shortExact (k := k) P)

theorem triangle_distinguished :
    triangle (k := k) P ∈ distTriang (DerivedCategory (ModuleCat.{u} T)) :=
  DerivedCategory.triangleOfSES_distinguished (sequence_shortExact (k := k) P)

end ArExplicit.TrivialInduction

end

end OAI
