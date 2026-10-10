import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAutomorphism

namespace OAI

/-! # Haar preservation for the integrated automorphisms

A determinant-one Lie automorphism preserves Lebesgue measure in exponential
coordinates. The global chart transfers this identity to actual group Haar
measure; no invariant-measure premise for the automorphism is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  {n : ℕ} (b : Basis (Fin n) ℝ L)

omit [FiniteDimensional ℝ L] [T2Space G] in
include hchart in
/-- In exponential coordinates, the integrated automorphism preserves the
same measure exactly when its linear determinant has absolute value one.
Here the positive determinant-one case suffices for Cartan conjugation. -/
theorem exponentialConjugate_measurePreserving
    (F : L ≃ₗ⁅ℝ⁆ L) (hdet : LinearMap.det F.toLinearEquiv.toLinearMap = 1) :
    MeasurePreserving (exponentialConjugate e Exp hbij F)
      (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume)
      (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume) := by
  let A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (b.equivFun.symm.trans F.toLinearEquiv).trans b.equivFun
  let f : (Fin n → ℝ) ≃ₜ G :=
    (b.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : (f : (Fin n → ℝ) → G) = (Exp ∘ e) ∘ b.equivFun.symm := by
    funext t
    exact hchart _
  have hAdet : LinearMap.det A.toLinearMap = 1 := by
    have hd := congrArg Units.val (LinearEquiv.det_conj F.toLinearEquiv b.equivFun)
    have hd' : LinearMap.det A.toLinearMap = LinearMap.det F.toLinearEquiv.toLinearMap := by
      simpa only [LinearEquiv.coe_det] using hd
    exact hd'.trans hdet
  have hA : MeasurePreserving A volume volume := by
    refine ⟨A.toContinuousLinearEquiv.continuous.measurable, ?_⟩
    change Measure.map A.toLinearMap volume = volume
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [hAdet]; norm_num),
      hAdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul]
  have hsem : Function.Semiconj f A (exponentialConjugate e Exp hbij F) := by
    intro t
    rw [hf]
    change Exp (e (b.equivFun.symm (A t))) = _
    simp only [A, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact (exponentialConjugate_apply_exp e Exp hbij F (b.equivFun.symm t)).symm
  have heq : (exponentialConjugate e Exp hbij F : G → G) =
      f ∘ A ∘ f.symm := by
    funext g
    obtain ⟨t, rfl⟩ := f.surjective g
    simpa only [Function.comp_apply, f.symm_apply_apply] using (hsem t).symm
  have hmeas : Measurable (exponentialConjugate e Exp hbij F) := by
    rw [heq]
    exact f.continuous.measurable.comp
      (A.toContinuousLinearEquiv.continuous.measurable.comp f.symm.continuous.measurable)
  have hm := f.measurable.measurePreserving volume
  have hh := hm.of_semiconj hA hsem hmeas
  rwa [hf] at hh

omit [FiniteDimensional ℝ L] [T2Space G] in
include hchart in
/-- The same explicit coordinate measure has the exact weighted-box volume.
Thus its automorphism invariance and its box normalization are compatible. -/
theorem exponentialCoordinate_weighted_box_measure
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    {I : Type*} (X : I → L) (S : Finset (FreeMagma I))
    (cost : S → ℝ) (β : WordBasisSelections X S) (r R : ℝ) (hR : 0 ≤ R) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (exponentialCoordinateBox (Exp ∘ e)
        (exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun i => cost (β.val i)) r) R) =
      ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates X S b₀) β.val).det| *
        ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) *
          ENNReal.ofReal (2 * R) ^ finrank ℝ L := by
  let f := (Exp ∘ e) ∘ b₀.equivFun.symm
  let c : (Fin (finrank ℝ L) → ℝ) ≃ₜ G :=
    (b₀.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : f = c := by
    funext t
    exact (hchart _).symm
  have hm : MeasurableEmbedding f := by rw [hf]; exact c.measurableEmbedding
  rw [exponentialCoordinateBox_eq_weighted_image X S b₀ β cost r R hR (Exp ∘ e)]
  change (Measure.map f volume) (f '' _) = _
  rw [hm.map_apply, Set.preimage_image_eq _ hm.injective]
  exact volume_weightedCoordinateBox _ _ _ _ _

variable [SimplyConnectedSpace G]

omit [FiniteDimensional ℝ L] in
include hchart b in
/-- The published exponential Haar theorem supplies one Haar measure
preserved by every determinant-one integrated automorphism. -/
theorem exists_haar_preserved_by_exponentialConjugate
    (haar : NilpotentExponentialHaarInput E G)
    (hExp : IsGroupExponential Exp) (hnil : LieRing.IsNilpotent L) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧
      ∀ F : L ≃ₗ⁅ℝ⁆ L, LinearMap.det F.toLinearEquiv.toLinearMap = 1 →
        MeasurePreserving (exponentialConjugate e Exp hbij F) μ μ := by
  let b' := b.map e.toLinearEquiv
  let f := (Exp ∘ e) ∘ b.equivFun.symm
  have hf : f = Exp ∘ b'.equivFun.symm := by
    funext t
    change Exp (e (b.equivFun.symm t)) = Exp ((b.map e.toLinearEquiv).equivFun.symm t)
    rw [Basis.map_equivFun]
    rfl
  refine ⟨Measure.map f volume, ?_, ?_⟩
  · rw [hf]
    exact (haar.2 Exp hExp (e.nilpotent_iff_equiv_nilpotent.mp hnil)).2 n b'
  · intro F hF
    exact exponentialConjugate_measurePreserving e Exp hbij chart hchart b F hF

end PolycyclicRecognition

end

end OAI
