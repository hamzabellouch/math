import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBasisSection
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHeightKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightLipschitz

namespace OAI

/-! # Canonical height without a global exponential chart

The logarithmic adjoint diagonal is projected back to the canonical linear
quotient using a linear left inverse. Exponential basis products give a
continuous section and prove the quotient-map property.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [IsTopologicalGroup G] [PreconnectedSpace G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_intrinsic_canonical_height_with_kernel {a : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    ∃ π : G →* Multiplicative W,
      Continuous (fun g => (π g).toAdd) ∧
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
      (∃ s : W → G, Continuous s ∧ s 0 = 1 ∧ ∀ w, (π (s w)).toAdd = w) ∧
      (∀ g, adjointMatrixHom T.basis g = 1 → π g = 1) ∧
      ∃ P : (Fin a → ℝ) →L[ℝ] W, ∀ g,
        (π g).toAdd = P (fun i => Real.log (adjointMatrixHom T.basis g i i)) := by
  let d : E →ₗ[ℝ] W := q.toLinearMap.comp (heightProjection T.character)
  have hd : Function.Surjective d :=
    q.surjective.comp (heightProjection_surjective T.character)
  let : FiniteDimensional ℝ W := Module.Finite.of_surjective d hd
  let k : W →ₗ[ℝ] (Fin a → ℝ) :=
    LinearMap.pi fun i => (heightCharacter T.character i).comp q.symm.toLinearMap
  have hk : Function.Injective k := by
    intro u v huv
    apply q.symm.injective
    apply sub_eq_zero.mp
    apply heightCharacters_separate T.character
    intro i
    change heightCharacter T.character i (q.symm u - q.symm v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun huv i)
  obtain ⟨p, hp⟩ := k.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hk)
  have hpk (w : W) : p (k w) = w := LinearMap.congr_fun hp w
  let c := intrinsicAdjointCharacterHom T hExp
  let π : G →* Multiplicative W :=
    { toFun g := Multiplicative.ofAdd (p (c g).toAdd)
      map_one' := by
        apply Multiplicative.ext
        change p (c 1).toAdd = 0
        rw [map_one]
        exact map_zero p
      map_mul' g h := by
        apply Multiplicative.ext
        change p (c (g * h)).toAdd = p (c g).toAdd + p (c h).toAdd
        rw [map_mul, toAdd_mul, map_add] }
  have hc : Continuous (fun g => (π g).toAdd) :=
    p.continuous_of_finiteDimensional.comp (continuous_intrinsicAdjointCharacterHom T hExp)
  have hπ (x : E) : (π (Exp x)).toAdd = d x := by
    change p (c (Exp x)).toAdd = d x
    have hcx : (c (Exp x)).toAdd = k (d x) := by
      funext i
      apply (intrinsicAdjointCharacterHom_exp T hExp x i).trans
      change T.character i x = heightCharacter T.character i
        (q.symm (q (heightProjection T.character x)))
      rw [q.symm_apply_apply]
      exact (heightCharacter_projection T.character i x).symm
    rw [hcx, hpk]
  refine ⟨π, hc, hπ, integrated_height_surjective T q Exp π hπ,
    isQuotientMap_of_exponential_linear_quotient hExp d hd π hπ hc, ?_, ?_, ?_⟩
  · exact exists_continuous_section_of_exponential_linear_quotient hExp d hd π hπ
  · intro g hg
    apply Multiplicative.ext
    change p (c g).toAdd = 0
    have hcg : (c g).toAdd = 0 := by
      funext i
      change Real.log (adjointMatrixHom T.basis g i i) = 0
      rw [hg]
      simp
    rw [hcg, map_zero]
  · exact ⟨p.toContinuousLinearMap, fun _ => rfl⟩

/-- The canonical height and its section, without exposing the optional
adjoint-kernel property used in the representation construction. -/
theorem exists_intrinsic_canonical_height {a : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    ∃ π : G →* Multiplicative W,
      Continuous (fun g => (π g).toAdd) ∧
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
      ∃ s : W → G, Continuous s ∧ s 0 = 1 ∧ ∀ w, (π (s w)).toAdd = w := by
  obtain ⟨π, hc, he, hs, hq, hsection, _, _⟩ :=
    exists_intrinsic_canonical_height_with_kernel T q hExp
  exact ⟨π, hc, he, hs, hq, hsection⟩

section Metric

variable {EM GM WM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [FiniteDimensional ℝ EM] [MetricSpace GM] [ChartedSpace EM GM]
  [Group GM] [LieGroup (𝓘(ℝ, EM)) ⊤ GM] [IsTopologicalGroup GM]
  [PreconnectedSpace GM] [IsIsometricSMul GM GM] [ProperSpace GM]
  [NormedAddCommGroup WM] [NormedSpace ℝ WM]

/-- Metric compatibility of intrinsic height requires neither Dixmier nor
an independent triangular representation premise. -/
theorem exists_lipschitz_intrinsic_canonical_height {a : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EM)) GM) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] WM) (chains : LinearMetricChains GM)
    {Exp : GroupLieAlgebra (𝓘(ℝ, EM)) GM → GM} (hExp : IsGroupExponential Exp) :
    ∃ π : GM →* Multiplicative WM,
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  obtain ⟨π, hc, he, hs, hq, _⟩ := exists_intrinsic_canonical_height T q hExp
  exact ⟨π, he, hs, hq, continuous_height_lipschitz chains π hc⟩

end Metric
end PolycyclicRecognition

end

end OAI
