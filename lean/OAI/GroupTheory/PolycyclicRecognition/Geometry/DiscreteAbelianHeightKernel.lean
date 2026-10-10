import OAI.GroupTheory.PolycyclicRecognition.Algebra.DiscreteUnipotentAbelian
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntrinsicKernelPacking

namespace OAI

/-! # Discrete abelian subgroups of the actual height kernel

The intrinsic kernel realization supplies the unipotence needed by the
logarithmic lattice argument. In particular this applies to central subgroups
in the remaining nilpotent lattice-finiteness argument.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem finitelyGenerated_discrete_abelian_height_kernel
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W)
    (he : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (Γ : Subgroup G) [DiscreteTopology Γ]
    (hcomm : ∀ x y : Γ, x * y = y * x) (hΓ : Γ ≤ π.ker) : Group.FG Γ := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : CommGroup Γ := { (inferInstance : Group Γ) with mul_comm := hcomm }
  let d := q.toLinearMap.comp (heightProjection T.character)
  have hπ : Continuous π := (contMDiff_height_of_exponential_linear hExp π d he).continuous
  obtain ⟨N, ExpN, hExpN, ι, _, _, hιExp, hrange⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ he
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal N).2 ExpN hExpN
    (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  obtain ⟨m, _, j, ρ, hj, hu, hn, hρ, _, hρExp⟩ :=
    exists_intrinsic_faithful_triangular_representation T Exp hExp
  have hind := intrinsic_triangular_representation_inducing T Exp hExp j hj hu ρ hρ hρExp
  let σ := ρ.comp Γ.subtype
  have hσ : Topology.IsInducing (fun γ : Γ => (σ γ : Matrix (Fin m) (Fin m) ℝ)) :=
    hind.comp Topology.IsInducing.subtypeVal
  apply finitelyGenerated_of_discrete_unipotent_representation σ hσ
  intro γ
  have hg : (γ : G) ∈ Set.range ι := by
    rw [hrange]
    exact hΓ γ.property
  obtain ⟨n, hn'⟩ := hg
  obtain ⟨v, hv⟩ := cN.surjective n
  have hx : Exp (N.equiv.symm v) = (γ : G) := by
    rw [← hιExp]
    simp only [N.equiv.apply_symm_apply]
    rw [← hcN, hv, hn']
  change IsNilpotent ((ρ (γ : G) : Matrix (Fin m) (Fin m) ℝ) - 1)
  rw [← hx, hρExp, coe_algebraExpUnit]
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact isNilpotent_analytic_exp_sub_one (hn _ (N.equiv.symm v).property)

end PolycyclicRecognition

end

end OAI
