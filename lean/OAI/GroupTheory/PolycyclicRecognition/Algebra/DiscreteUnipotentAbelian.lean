import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingUnipotentLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Abelian
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Polynomial

namespace OAI

/-! # Discrete abelian unipotent groups are finitely generated

The logarithm is additive on a commuting unipotent group. The inducing
representation and the continuous exponential make its logarithmic image a
discrete integral submodule of a finite-dimensional real vector space.
This is the abelian and central-subgroup step of lattice finiteness.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Topology

variable {H A : Type*} [CommGroup H] [TopologicalSpace H] [DiscreteTopology H]
  [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] [CompleteSpace A]

theorem finitelyGenerated_of_discrete_unipotent_representation
    (ρ : H →* Aˣ) (hρ : Topology.IsInducing (fun h => (ρ h : A)))
    (hnil : ∀ h, IsNilpotent ((ρ h : A) - 1)) : Group.FG H := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let log : H → A := fun h => nilpotentLog ((ρ h : A) - 1)
  have he (h : H) : NormedSpace.exp (log h) = (ρ h : A) := by
    rw [analytic_exp_eq_nilpotent_exp (nilpotentLog_nilpotent _ (hnil h)),
      exp_nilpotentLog _ (hnil h)]
    exact add_sub_cancel 1 (ρ h : A)
  have hlog : Topology.IsInducing log := by
    apply Topology.IsInducing.of_comp (continuous_of_discreteTopology)
      NormedSpace.exp_continuous
    simpa only [Function.comp_def, he] using hρ
  let etag : Additive H ≃ₜ H :=
    { toEquiv := Additive.toMul
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  have htag : Topology.IsInducing (Additive.toMul : Additive H → H) := etag.isInducing
  have hlog' : Topology.IsInducing (fun x : Additive H => log x.toMul) := hlog.comp htag
  let l : Additive H →+ A :=
    { toFun := fun h => log h.toMul
      map_zero' := by
        change nilpotentLog ((ρ 1 : A) - 1) = 0
        rw [map_one, Units.val_one, sub_self]
        simpa only [IsNilpotent.exp_zero, sub_self] using
          (nilpotentLog_exp (0 : A) ⟨1, pow_one 0⟩)
      map_add' := by
        intro x y
        have hc : Commute (ρ x.toMul : A) (ρ y.toMul : A) := by
          have hh : ρ x.toMul * ρ y.toMul = ρ y.toMul * ρ x.toMul := by
            calc
              _ = ρ (x.toMul * y.toMul) := (ρ.map_mul _ _).symm
              _ = ρ (y.toMul * x.toMul) := congrArg ρ (mul_comm _ _)
              _ = _ := ρ.map_mul _ _
          exact congrArg Units.val hh
        have hcc := (hc.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
        have hh := nilpotentLog_unipotent_mul hcc (hnil x.toMul) (hnil y.toMul)
        simpa only [log, toMul_add, map_mul, Units.val_mul,
          add_sub_cancel] using hh }
  let L := l.range
  let k : Additive H ≃+ L := AddEquiv.ofBijective l.rangeRestrict
    ⟨fun x y h => hlog'.injective (congrArg Subtype.val h), l.rangeRestrict_surjective⟩
  let e : Additive H ≃ₜ L :=
    { toEquiv := k.toEquiv
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := by
        apply hlog'.continuous_iff.mpr
        change Continuous (fun z : L => log (k.symm z).toMul)
        convert (continuous_subtype_val : Continuous (fun z : L => (z : A))) using 1
        funext z
        exact congrArg Subtype.val (k.apply_symm_apply z) }
  let : DiscreteTopology L := e.discreteTopology
  let M : Submodule ℤ A := L.toIntSubmodule
  let : DiscreteTopology M := inferInstanceAs (DiscreteTopology L)
  have hM : Module.Finite ℤ M := inferInstance
  let : AddGroup.FG L := Module.Finite.iff_addGroup_fg.mp hM
  have hH : AddGroup.FG (Additive H) :=
    AddGroup.fg_of_surjective (f := k.symm.toAddMonoidHom) k.symm.surjective
  exact GroupFG.iff_add_fg.mpr hH

theorem polycyclic_of_discrete_unipotent_representation
    (ρ : H →* Aˣ) (hρ : Topology.IsInducing (fun h => (ρ h : A)))
    (hnil : ∀ h, IsNilpotent ((ρ h : A) - 1)) : IsPolycyclic H := by
  let := finitelyGenerated_of_discrete_unipotent_representation ρ hρ hnil
  exact isPolycyclic_of_finitelyGenerated_commGroup H

end PolycyclicRecognition

end

end OAI
