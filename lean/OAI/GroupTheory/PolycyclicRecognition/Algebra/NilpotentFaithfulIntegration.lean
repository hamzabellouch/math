import OAI.GroupTheory.PolycyclicRecognition.Geometry.DerivationFlowRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectIntegration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegrationToUnipotentModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnconditionalNilpotentCoordinates

namespace OAI

/-! # Nilpotent-source integration into a faithfully represented Lie group

The proof uses codimension-one induction. The representation of the target
need not be unipotent; it identifies conjugation along the complementary
one-parameter subgroup. The source model is constructed unconditionally.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem integrate_polynomial_nilpotent_to_faithful
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A)
    (hexp : ∀ v, ρ (Exp v) = algebraExpUnit (j v))
    (L : Type) [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
    [P : PolynomialExponentialCoordinates L] (hnil : LieRing.IsNilpotent L)
    (f : L →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ∃ φ : L →* G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, E)) ∞ φ ∧
      ∀ x, φ x = Exp (f x) := by
  have hmain : ∀ n : ℕ, ∀ (V : Type) [RealNormedLieAlgebra V] [FiniteDimensional ℝ V]
      [PV : PolynomialExponentialCoordinates V], Module.finrank ℝ V = n →
      LieRing.IsNilpotent V → ∀ f : V →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G,
      ∃ φ : V →* G, ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ φ ∧ ∀ x, φ x = Exp (f x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ PV hv hV f
      let : LieRing.IsNilpotent V := hV
      by_cases hs : Subsingleton V
      · let := hs
        refine ⟨1, contMDiff_const, ?_⟩
        intro x
        have hx : x = 0 := Subsingleton.elim _ _
        simp only [hx, map_zero, hExp.map_zero, MonoidHom.one_apply]
      · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hs
        obtain ⟨C⟩ := exists_nilpotentCodimensionOneData (L := V)
        let := C.normedIdeal
        let normedI : NormedAddCommGroup C.ideal := inferInstance
        let : NormedAddCommGroup C.ideal := normedI
        let : AddCommGroup C.ideal := normedI.toAddCommGroup
        let : MetricSpace C.ideal := normedI.toMetricSpace
        let : UniformSpace C.ideal :=
          normedI.toMetricSpace.toPseudoMetricSpace.toUniformSpace
        let : TopologicalSpace C.ideal :=
          normedI.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        let : IsTopologicalAddGroup C.ideal := inferInstance
        let : ChartedSpace C.ideal C.ideal := chartedSpaceSelf _
        have hI : LieRing.IsNilpotent C.ideal := C.ideal_nilpotent
        obtain ⟨PI⟩ := polynomialExponentialCoordinates_nilpotent C.ideal hI
        let := PI
        have hdim : Module.finrank ℝ C.ideal < n := hv ▸ C.finrank_ideal_lt
        let fi : C.ideal →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G :=
          f.comp C.ideal.incl
        obtain ⟨k, hk, hkexp⟩ := ih (Module.finrank ℝ C.ideal) hdim C.ideal rfl hI fi
        let D := C.derivation
        have hD : IsNilpotent D.toLinearMap := C.derivation_nilpotent
        have hinter (x : C.ideal) : fi (D x) = ⁅f C.unit, fi x⁆ := by
          change f ⁅C.unit, (x : V)⁆ = ⁅f C.unit, f (x : V)⁆
          exact f.map_lie _ _
        have hact (t : ℝ) (x : C.ideal) : k (nilpotentDerivationFlow D hD t x) =
            Exp (t • f C.unit) * k x * (Exp (t • f C.unit))⁻¹ := by
          rw [hkexp, hkexp]
          exact derivationFlow_group_conjugation D hD Exp ρ hρ j hexp
            fi.toLinearMap (f C.unit) hinter t x
        let S := C.ideal × ℝ
        let normedS : NormedAddCommGroup S := by
          change NormedAddCommGroup (C.ideal × ℝ)
          infer_instance
        let : NormedAddCommGroup S := normedS
        let : AddCommGroup S := normedS.toAddCommGroup
        let : MetricSpace S := normedS.toMetricSpace
        let : UniformSpace S := normedS.toMetricSpace.toPseudoMetricSpace.toUniformSpace
        let : TopologicalSpace S :=
          normedS.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        let : ChartedSpace S S := chartedSpaceSelf _
        let : T0Space S := @MetricSpace.instT0Space S normedS.toMetricSpace
        let : T2Space S := inferInstance
        let : CompleteSpace S := FiniteDimensional.complete ℝ S
        let : Group S := derivationSemidirectGroup D hD
        let : MulOneClass S := (derivationSemidirectGroup D hD).toMulOneClass
        let : Mul S := (derivationSemidirectGroup D hD).toMul
        let : One S := (derivationSemidirectGroup D hD).toOne
        let : LieGroup (𝓘(ℝ, S)) ⊤ S := derivationSemidirectLieGroup D hD
        let N := nilpotentModelOfPolynomialIdeal C PI
        have hnS : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, S)) S) :=
          N.tangent_nilpotent hV
        let ψ : S →* G := derivationSemidirectHom D hD Exp hExp k (f C.unit) hact
        have hψ : ContMDiff (𝓘(ℝ, S)) (𝓘(ℝ, E)) ∞ ψ :=
          contMDiff_derivationSemidirectHom D hD Exp hExp k (f C.unit) hact hk
        have dk : HasMFDerivAt (𝓘(ℝ, C.ideal)) (𝓘(ℝ, E)) k 1
            fi.toLinearMap.toContinuousLinearMap := by
          apply (hk.mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
          ext x
          exact mfderiv_eq_of_exponential_compatibility
            PolynomialExponentialCoordinates.isGroupExponential_identity hExp k
            (hk.mdifferentiable (by simp)) fi.toLinearMap hkexp x
        have hdψ := hasMFDerivAt_derivationSemidirectHom D hD Exp hExp k (f C.unit) hact
          fi.toLinearMap.toContinuousLinearMap dk
        have hψder (v : GroupLieAlgebra (𝓘(ℝ, S)) S) :
            mfderiv (𝓘(ℝ, S)) (𝓘(ℝ, E)) ψ 1 v = f (C.split v) := by
          have hone : (1 : S) = 0 := derivationSemidirect_one D hD
          rw [hone, hdψ.mfderiv]
          change f (v.1 : V) + v.2 • f C.unit = f ((v.1 : V) + v.2 • C.unit)
          rw [map_add, map_smul]
        obtain ⟨m, c, σ, q, hσ, _, dq, hc⟩ :=
          exists_semidirect_unipotent_representation (Module.finBasis ℝ C.ideal) D hD hnS
        let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
        obtain ⟨η, hη, hηexp, _⟩ := integrate_to_unipotent_model
          groupExponential groupExponential_isGroupExponential hnS σ hσ q dq c hc N.equiv.toLieHom
        let φ : V →* G := ψ.comp η
        refine ⟨φ, hψ.comp hη, ?_⟩
        intro x
        change ψ (η x) = Exp (f x)
        rw [hηexp]
        have he := groupExponential_isGroupExponential.map_of_mdifferentiable
          hExp ψ (hψ.mdifferentiable (by simp)) (N.equiv x)
        erw [hψder] at he
        exact he.trans (congrArg (fun z => Exp (f z)) (C.split.apply_symm_apply x))
  exact hmain (Module.finrank ℝ L) L rfl hnil f

end PolycyclicRecognition

end

end OAI
