import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoverGeometry
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRootWidths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportLegs

namespace OAI

/-! # Logarithmic root distortion in the genuine Cartan cover

Ambient conjugation identities lift to the nilpotent coordinate because its
inclusion is injective. No injectivity of the whole cover projection is used.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial
  semidirectProductTopology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The root exponential in the first coordinate of the semidirect cover. -/
def CartanFactorModel.semidirectRootExp
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (v : rootSpace H χ) : F.N.carrier ⋊[F.action] F.D.carrier :=
  SemidirectProduct.inl (F.ExpN (F.N.equiv (CartanWordModel.rootInIdeal χ hχ v)))

include T in
theorem CartanFactorModel.semidirect_root_logarithmic_distortion
    (hExpG : IsGroupExponential ExpG)
    (dS : ProperChainMetric (F.N.carrier ⋊[F.action] F.D.carrier))
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero) :
    letI := dS.compatibleMetric
    ∃ C : ℝ, 0 < C ∧ ∀ v : rootSpace H χ,
      dist 1 (F.semidirectRootExp χ hχ v) ≤ C * Real.log (2 + ‖v‖) := by
  let := dS.compatibleMetric
  let : IsIsometricSMul (F.N.carrier ⋊[F.action] F.D.carrier)
      (F.N.carrier ⋊[F.action] F.D.carrier) := dS.isometric_compatibleMetric
  let : TopologicalSpace (rootSpace H χ) :=
    (rootNormedAddCommGroup H χ).toUniformSpace.toTopologicalSpace
  obtain ⟨m, hm, τ, j, hind, hmatch⟩ := exponentialLinearRealizationInput_intrinsic
    ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hτ : Function.Injective τ := by
    intro g k he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  have hc : Continuous (fun v : rootSpace H χ => ExpG v) := by
    apply hind.continuous_iff.mpr
    change Continuous (fun v : rootSpace H χ => (τ (ExpG v) : Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch]
    exact Units.continuous_val.comp
      (algebraExpUnit_continuous.comp (representedRootVector H χ j).continuous)
  have hN : Continuous (fun v : rootSpace H χ =>
      F.ExpN (F.N.equiv (CartanWordModel.rootInIdeal χ hχ v))) := by
    apply F.closedN.isEmbedding.continuous_iff.mpr
    change Continuous (fun v : rootSpace H χ =>
      F.inclusionN (F.ExpN (F.N.equiv (CartanWordModel.rootInIdeal χ hχ v))))
    have he : (fun v : rootSpace H χ =>
        F.inclusionN (F.ExpN (F.N.equiv (CartanWordModel.rootInIdeal χ hχ v)))) =
        (fun v : rootSpace H χ => ExpG v) := by
      funext v
      exact F.compatibleN _
    rw [he]
    exact hc
  have hES : Continuous (F.semidirectRootExp χ hχ) :=
    (continuous_semidirect_inl F.action).comp hN
  obtain ⟨h, hh⟩ := exists_contracting_root_direction H χ hχ
  let dD : ℝ → F.D.carrier := fun t => F.ExpD (F.D.equiv ((-t) • h))
  let d : ℝ → F.N.carrier ⋊[F.action] F.D.carrier :=
    fun t => SemidirectProduct.inr (dD t)
  have hdG (t : ℝ) : F.inclusionD (dD t) =
      ExpG (t • (-(h : GroupLieAlgebra (𝓘(ℝ, EG)) G))) := by
    dsimp only [dD]
    rw [F.compatibleD]
    change ExpG ((-t) • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = _
    rw [neg_smul, smul_neg]
  have hdD : Continuous dD := by
    apply F.closedD.isEmbedding.continuous_iff.mpr
    change Continuous (fun t => F.inclusionD (dD t))
    simp_rw [hdG]
    exact continuous_exp_line_of_published_realization T ExpG hExpG
      exponentialLinearRealizationInput_intrinsic _
  have hd : Continuous d := (continuous_semidirect_inr F.action).comp hdD
  have hdD0 : dD 0 = 1 := by
    apply F.closedD.injective
    rw [hdG, zero_smul, hExpG.map_zero, map_one]
  have hdDmul (s t : ℝ) : dD (s + t) = dD s * dD t := by
    apply F.closedD.injective
    rw [map_mul, hdG, hdG, hdG]
    exact hExpG.map_add_smul _ s t
  have hd0 : d 0 = 1 := by simp only [d, hdD0, map_one]
  have hdmul (s t : ℝ) : d (s + t) = d s * d t := by
    simp only [d, hdDmul, map_mul]
  apply root_logarithmic_distortion H χ (F.semidirectRootExp χ hχ) hES h hh d hd hd0 hdmul
  intro v t _
  change SemidirectProduct.inl _ = SemidirectProduct.inr (dD t) *
    SemidirectProduct.inl _ * (SemidirectProduct.inr (dD t))⁻¹
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  apply congrArg SemidirectProduct.inl
  apply F.closedN.injective
  rw [F.conjugation, F.compatibleN, F.compatibleN, hdG]
  apply hτ
  simp only [map_mul, map_inv, hmatch, map_smul, map_neg, smul_neg]
  exact represented_root_exp_inverse_conjugation H χ j h t v

end PolycyclicRecognition

end

end OAI
