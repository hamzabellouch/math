import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicExponentialSmooth
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothExponentialHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentedExponentialLogSmooth
import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightKernelCoordinates

namespace OAI

/-! # Smooth global coordinates from the height and its nilpotent kernel

These are product coordinates from a smooth section, not a claim that the
ambient exponential is surjective. They suffice for the metric contraction.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem exists_intrinsic_smooth_product_coordinates
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (he : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    let V := Fin (finrank ℝ T.kernelIdeal) → ℝ
    ∃ φ : (V × W) ≃ₜ G, φ 0 = 1 ∧
      ContMDiff (𝓘(ℝ, V × W)) (𝓘(ℝ, E)) ∞ φ ∧
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, V × W)) ∞ φ.symm := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let d : E →ₗ[ℝ] W := q.toLinearMap.comp (heightProjection T.character)
  have hd : Function.Surjective d := q.surjective.comp (heightProjection_surjective T.character)
  obtain ⟨s, _, hs, hs0, hsπ, _⟩ :=
    exists_smooth_section_of_exponential_linear_quotient hExp d hd π he
  let sC : C(Multiplicative W, G) := ⟨fun w => s w.toAdd, hs.continuous⟩
  have hsC (w : Multiplicative W) : π (sC w) = w := Multiplicative.ext (hsπ w.toAdd)
  obtain ⟨N, ExpN, hExpN, ι, hι, _, hιExp, hrange⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ he
  let b := finBasis ℝ T.kernelIdeal
  obtain ⟨c, hc, _, _⟩ := exists_height_kernel_coordinates T Exp hExp π N
    (nilpotentPublishedInputs.haar T.kernelIdeal N) ExpN hExpN ι hι hιExp hrange b
  let V := Fin (finrank ℝ T.kernelIdeal) → ℝ
  let φ : (V × W) ≃ₜ G :=
    ((Homeomorph.prodCongr c (Homeomorph.refl W)).trans
      (Homeomorph.prodComm π.ker W)).trans (quotientSectionHomeomorph π hπ sC hsC).symm
  have hφ (p : V × W) : φ p = Exp (b.equivFun.symm p.1) * s p.2 := by
    change (c p.1 : G) * s p.2 = _
    rw [hc]
  have hφ0 : φ 0 = 1 := by
    rw [hφ]
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero, ZeroMemClass.coe_zero,
      hExp.map_zero, hs0, mul_one]
  have hExpS := intrinsic_exponential_contMDiff T Exp hExp
  let B : V →L[ℝ] E :=
    (T.kernelIdeal.incl.toLinearMap.comp b.equivFun.symm.toLinearMap).toContinuousLinearMap
  have hφS : ContMDiff (𝓘(ℝ, V × W)) (𝓘(ℝ, E)) ∞ φ := by
    have hh := (hExpS.comp (B.contDiff.contMDiff.comp contDiff_fst.contMDiff)).mul
      (hs.comp contDiff_snd.contMDiff)
    exact hh.congr hφ
  have hπS : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, W)) ∞ (fun g => (π g).toAdd) :=
    contMDiff_height_of_exponential_linear hExp π d he
  let r : G → G := fun g => g * (s (π g).toAdd)⁻¹
  have hr : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ r :=
    contMDiff_id.mul (hs.comp hπS).inv
  have hrker (g : G) : r g ∈ π.ker := by
    change π (g * (s (π g).toAdd)⁻¹) = 1
    rw [map_mul, map_inv, show π (s (π g).toAdd) = π g from Multiplicative.ext (hsπ _)]
    exact mul_inv_cancel _
  let f : G → V := fun g => c.symm ⟨r g, hrker g⟩
  have hf : Continuous f := c.symm.continuous.comp (hr.continuous.subtype_mk hrker)
  obtain ⟨m, _, j, ρ, hj, _, _, hρ, _, hρExp⟩ :=
    exists_intrinsic_faithful_triangular_representation T Exp hExp
  have hρS := contMDiff_of_continuous_unitsHom hExp ρ (Units.continuous_val.comp hρ)
  let J : V →L[ℝ] Matrix (Fin m) (Fin m) ℝ :=
    j.toLinearMap.toContinuousLinearMap.comp B
  let F : V → Matrix (Fin m) (Fin m) ℝ := fun v => NormedSpace.exp (J v)
  have hF (v : V) : ContDiffAt ℝ ∞ F v :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (J v)).contDiffAt.comp v J.contDiff.contDiffAt
  have hD (v : V) : HasFDerivAt F ((fderiv ℝ NormedSpace.exp (J v)).comp J) v :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (J v)).differentiableAt.hasFDerivAt.comp v J.hasFDerivAt
  have hi (v : V) : Function.Injective ((fderiv ℝ NormedSpace.exp (J v)).comp J) := by
    intro u w huv
    apply b.equivFun.symm.injective
    apply Subtype.val_injective
    exact represented_exponential_differential_injective T j hj (B v) huv
  have hcomp : F ∘ f = fun g => (ρ (r g) : Matrix (Fin m) (Fin m) ℝ) := by
    funext g
    have hh := hc (f g)
    have hk : (c (f g) : G) = r g := congrArg Subtype.val (c.apply_symm_apply ⟨r g, hrker g⟩)
    rw [hk] at hh
    change NormedSpace.exp (j (B (f g))) = _
    rw [hh, hρExp]
    rfl
  have hfS : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ f := by
    intro g
    apply contMDiffAt_of_comp_of_injective_differential hf.continuousAt (hF _) (hD _) (hi _)
    rw [hcomp]
    exact (hρS.comp hr) g
  have hinv (g : G) : φ.symm g = (f g, (π g).toAdd) := rfl
  refine ⟨φ, hφ0, hφS, ?_⟩
  exact (hfS.prodMk_space hπS).congr hinv

/-- Reindex the product coordinates by one finite real coordinate space. -/
theorem exists_intrinsic_smooth_coordinates
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (he : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    ∃ (n : ℕ) (φ : (Fin n → ℝ) ≃ₜ G), φ 0 = 1 ∧
      ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E)) ∞ φ ∧
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, Fin n → ℝ)) ∞ φ.symm := by
  obtain ⟨φ, h0, hf, hb⟩ := exists_intrinsic_smooth_product_coordinates T q Exp hExp π hπ he
  let V := (Fin (finrank ℝ T.kernelIdeal) → ℝ) × W
  let e := (finBasis ℝ V).equivFun.symm.toContinuousLinearEquiv
  refine ⟨finrank ℝ V, e.toHomeomorph.trans φ, ?_, ?_, ?_⟩
  · change φ (e 0) = 1
    rw [map_zero, h0]
  · exact hf.comp e.contDiff.contMDiff
  · exact e.symm.contDiff.contMDiff.comp hb

end PolycyclicRecognition

end

end OAI
