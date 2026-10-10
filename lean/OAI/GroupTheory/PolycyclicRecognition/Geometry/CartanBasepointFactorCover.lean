import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBasepointBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHeight

namespace OAI

/-! # The pointwise inverse-image cover from Cartan adjoint bounds -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set Metric
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (hbijN : Function.Bijective F.ExpN)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)

omit [FiniteDimensional ℝ W] in
include hπExp in
/-- Converting the two adjoint image inclusions to the actual factor
change gives both the density-cover condition and the suffix support. -/
theorem basepoint_factor_cover
    (hφ : ∀ h : H, F.action (F.ExpD (F.D.equiv h)) =
      M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN h)
    {K : ℝ} (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (A C B D : Set F.N.carrier) {RH HT : ℝ}
    (hbound : ∀ h : H, ‖(finBasis ℝ H).equivFun h‖ ≤ RH →
      ‖eW (heightProjection T.character (h : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ HT →
      (M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN h '' A ⊆ C) ∧
      (M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN h '' B ⊆ D))
    (hprod : ∀ x ∈ C, ∀ u ∈ C, ∀ a ∈ C, x⁻¹ * u⁻¹ * a ∈ B)
    (g : G) (u : F.N.carrier) (k : F.D.carrier) (h : H)
    (he : F.ExpD (F.D.equiv h) = k)
    (hkheight : (π (F.inclusionD k)).toAdd = (π g).toAdd)
    (hlog : ‖(finBasis ℝ H).equivFun h‖ ≤ RH)
    (hsmall : K * dist 1 g ≤ HT) (hu : u ∈ C) :
    (∀ a₀ ∈ A, ∀ a ∈ C, (F.action k a₀)⁻¹ * u⁻¹ * a ∈ B) ∧
      (F.action k) ⁻¹' B ⊆ D := by
  have hhheight : ‖eW (heightProjection T.character (h : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ HT := by
    have heheight : eW (heightProjection T.character (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) =
        (π g).toAdd := by rw [← hπExp, ← F.compatibleD, he, hkheight]
    rw [heheight]
    have hh := hLip g 1
    simp only [map_one, toAdd_one, sub_zero, dist_comm g] at hh
    exact hh.trans hsmall
  have hfront := (hbound h hlog hhheight).1
  have hnlog : ‖(finBasis ℝ H).equivFun (-h)‖ ≤ RH := by
    simpa only [map_neg, norm_neg] using hlog
  have hnheight : ‖eW (heightProjection T.character ((-h : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ HT := by
    change ‖eW (heightProjection T.character (-(h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))‖ ≤ _
    simpa only [map_neg, norm_neg] using hhheight
  have hback := (hbound (-h) hnlog hnheight).2
  have hact : F.action k = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN h := by
    rw [← he]; exact hφ h
  have heinv : F.ExpD (F.D.equiv (-h)) = k⁻¹ := by rw [map_neg, F.isExpD.map_neg, he]
  have hactinv : F.action k⁻¹ = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN (-h) := by
    rw [← heinv]; exact hφ (-h)
  constructor
  · intro a₀ ha₀ a ha
    apply hprod (F.action k a₀) _ u hu a ha
    rw [hact]
    exact hfront (mem_image_of_mem _ ha₀)
  · intro v hv
    have hx := hback (mem_image_of_mem _ hv)
    rw [← hactinv] at hx
    simpa only [map_inv, MulAut.inv_apply_self] using hx

end PolycyclicRecognition.CartanWordModel

end

end OAI
