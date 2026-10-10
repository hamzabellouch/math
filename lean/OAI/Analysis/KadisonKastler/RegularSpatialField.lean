import OAI.Analysis.KadisonKastler.RegularFieldMembership
import OAI.Analysis.KadisonKastler.SpatialSliceRecovery

namespace OAI

/-! # First-leg fields in the relative commutant of the product centralizer -/

namespace KadisonKastler

open MeasureTheory UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]

/-- In the Fourier decomposition of a central core operator, constant
product-centralizer commutation removes the entire second tensor leg.
The coefficient field is obtained by a concrete slice, so measurability
and its norm bound are retained. -/
theorem first_leg_field_of_product_centralizer
    (M : VonNeumannAlgebra H) {D : VonNeumannAlgebra K} {Ω : K}
    (L : LocalProductSwaps D Ω) (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (F : ℝ → SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (T : RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
      RegularCoreHilbert (SpatialHilbert H K))
    (hFT : RepresentsOperatorField volume F T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖F t‖ ≤ C)
    (hT : T ∈ regularTensorAlgebra (spatialProductAlgebra M D))
    (hcomm : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D →
      ProductStateCentralizes D Ω u → Commute T
        (regularConstantHom volume (spatialRight (H := H) (u : K →L[ℂ] K)))) :
    ∃ A : ℝ → H →L[ℂ] H,
      (∀ ξ, AEStronglyMeasurable (fun t => A t ξ) volume) ∧
      (∀ᵐ t ∂volume, ‖A t‖ ≤ C) ∧ (∀ᵐ t ∂volume, A t ∈ M) ∧
      RepresentsOperatorField volume (fun t => spatialLeft (K := K) (A t)) T := by
  let S : Set (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    {b | ∃ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D ∧
      ProductStateCentralizes D Ω u ∧ b = spatialRight (H := H) (u : K →L[ℂ] K)}
  have hS (b) (hb : b ∈ S) : ‖b‖ ≤ 1 := by
    obtain ⟨u, _, _, rfl⟩ := hb
    change ‖spatialTensorOp (1 : H →L[ℂ] H) (u : K →L[ℂ] K)‖ ≤ 1
    have hId : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := norm_unitary_le_one 1
    calc
      _ ≤ ‖(1 : H →L[ℂ] H)‖ * ‖(u : K →L[ℂ] K)‖ := spatialTensorOp_norm_le _ _
      _ ≤ 1 * 1 := mul_le_mul hId (norm_unitary_le_one u) (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hcommS (b) (hb : b ∈ S) : Commute T (regularConstantHom volume b) := by
    obtain ⟨u, hu, hc, rfl⟩ := hb
    exact hcomm u hu hc
  have hc := hFT.commute_set_ae S hS hcommS
  have hm := hFT.mem_algebra_ae (spatialProductAlgebra M D) hT
  let A : ℝ → H →L[ℂ] H := fun t => tensorVectorSlice Ω (F t)
  have he : ∀ᵐ t ∂volume, F t = spatialLeft (K := K) (A t) := by
    filter_upwards [hc, hm] with t hct hmt
    obtain ⟨a, ha, hFa⟩ := spatial_relative_commutant_of_local_swaps M L hΩ hsep
      (F t) hmt (fun u hu hcu => (hct _ ⟨u, hu, hcu, rfl⟩).eq.symm)
    have hAa : A t = a := by
      dsimp [A]
      rw [hFa, tensorVectorSlice_spatialLeft Ω hΩ]
    exact hFa.trans (congrArg (spatialLeft (K := K)) hAa.symm)
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro ξ
    exact (tensorVector Ω).adjoint.continuous.comp_aestronglyMeasurable
      (hmeas (tensorVector Ω ξ))
  · filter_upwards [hbound] with t ht
    exact (norm_tensorVectorSlice_le Ω hΩ (F t)).trans ht
  · filter_upwards [hm] with t ht
    exact tensorVectorSlice_mem M D Ω (F t) ht
  · intro f
    filter_upwards [hFT f, he] with t ht het
    exact ht.trans (congrArg (fun B : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
      B (f t)) het)

end

end KadisonKastler

end OAI
