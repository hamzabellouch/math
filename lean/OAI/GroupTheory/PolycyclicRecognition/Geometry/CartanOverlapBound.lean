import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOverlapCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CartanVanishingHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceSmallExponentialProducts

namespace OAI

/-! # Subexponential coordinate bounds for nonunique lifts

The small bounded displacement contributes a vanishing-height adjoint
term. The overlap contributes the Cartan logarithm of `d * b * e⁻¹`.
The finite Dynkin formula bounds their product in the nilpotent factor.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include hunimod in
theorem exists_subexponential_overlap_difference_bound
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) (scale RH RV RZ η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hRH0 : ∀ n, 0 ≤ RH n)
    (hRV0 : ∀ n, 0 ≤ RV n) (hRZ0 : ∀ n, 0 ≤ RZ n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hRV : HasSubexponentialUpperBoundSeq scale RV)
    (hRZ : HasSubexponentialUpperBoundSeq scale RZ) (hη : Tendsto η atTop (𝓝 0)) :
    ∃ S : ℕ → ℝ, (∀ n, 0 ≤ S n) ∧ HasSubexponentialUpperBoundSeq scale S ∧
      ∀ n (u v a : F.N.carrier) (d e bD : F.D.carrier),
        F.inclusionN v * F.inclusionD e =
          (F.inclusionN u * F.inclusionD d) * (F.inclusionN a * F.inclusionD bD) →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RH n →
        ‖eW (heightProjection T.character
          (cartanLog H F.D.equiv F.ExpD hbijD d : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
            η n * scale n →
        a ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
          (WordBasisSelections.basis M.letter M.wordList γ) (RV n) →
        ‖(finBasis ℝ H).equivFun
          (cartanLog H F.D.equiv F.ExpD hbijD (d * bD * e⁻¹))‖ ≤ RZ n →
        u⁻¹ * v ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv) b (S n) := by
  obtain ⟨A, hA, ha⟩ := CartanFactorModel.exists_overlap_coordinate_bound (H := H) b
  obtain ⟨R, hR0, hR, hbound⟩ := M.exists_vanishing_height_adjoint_bound T hunimod eW b b
    scale RH RV η hs hscale hRH0 hRV0 hRH hRV hη
  let Z := fun n => A * RZ n
  have hZ0 (n : ℕ) : 0 ≤ Z n := mul_nonneg hA (hRZ0 n)
  have hZ : HasSubexponentialUpperBoundSeq scale Z :=
    (sequence_subexponential_upper_const hs A).mul hRZ
      (Eventually.of_forall (fun _ => hA))
  obtain ⟨S, hS0, hS, hprod⟩ := exists_sequence_small_product_bound F.N.equiv
    F.ExpN F.isExpN dynkin M.bound_zero b scale R Z hs hscale hR0 hZ0 hR hZ
  refine ⟨S, hS0, hS, ?_⟩
  intro n u v a d e bD he hd hh hsmall hz
  obtain ⟨z, hzproj, hzmul⟩ := factor_overlap_difference F.action F.inclusionN
    F.inclusionD F.conjugation u v a d e bD he
  let vz := F.N.equiv.symm ((Equiv.ofBijective F.ExpN hbijN).symm z)
  have hvz : F.ExpN (F.N.equiv vz) = z := by
    change F.ExpN (F.N.equiv (F.N.equiv.symm _)) = z
    rw [F.N.equiv.apply_symm_apply]
    exact (Equiv.ofBijective F.ExpN hbijN).apply_symm_apply z
  have hzeq := F.overlap_log_eq hinjG hbijN hbijD z (d * bD * e⁻¹) hzproj
  have hvzbound : ‖b.equivFun vz‖ ≤ Z n :=
    (ha vz _ hzeq).trans (mul_le_mul_of_nonneg_left hz hA)
  obtain ⟨va, hva, hvabound⟩ := hsmall
  let hdlog := cartanLog H F.D.equiv F.ExpD hbijD d
  have hact : F.action d a = F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H hdlog va)) := by
    rw [← hva, cartan_action_eq_adjoint_of_published_realization T M F hExpG realize
      hbijN hbijD dynkin d]
    exact integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkin F.isExpN
      M.bound_zero (cartanIdealAdjointAutomorphism T H hdlog) va
  obtain ⟨w, hw, hwbound⟩ := hprod n 0 le_rfl
    (cartanIdealAdjointAutomorphism T H hdlog va) vz
    (hbound n γ hdlog va hd hh hvabound) (by simpa using hvzbound)
  refine ⟨w, ?_, ?_⟩
  · simpa only [Function.comp_apply, ← hact, hvz, ← hzmul] using hw
  · simpa using hwbound

end PolycyclicRecognition.CartanWordModel

end

end OAI
