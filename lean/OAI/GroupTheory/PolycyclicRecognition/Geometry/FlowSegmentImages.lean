import OAI.GroupTheory.PolycyclicRecognition.Geometry.WordChartFlowHeight
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates

namespace OAI

/-! # Exact height images of the graded horizontal segments -/

noncomputable section
namespace PolycyclicRecognition

open Module Set

theorem isCompact_segment_real {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (x y : W) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))

theorem SupportDatum.templateSupport_affine_segment
    {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B] (P : SupportDatum W I B)
    (w v : W) {T : ℝ} (hT : 0 ≤ T) :
    P.templateSupport (segment ℝ w (w + T • v)) = T * P.segmentSupport v := by
  have he : segment ℝ w (w + T • v) = (fun y => y + w) '' segment ℝ 0 (T • v) := by
    simpa only [add_zero, zero_add, add_comm] using
      (segment_translate_image ℝ w (0 : W) (T • v)).symm
  rw [he, P.templateSupport_translate (isCompact_segment_real _ _) ⟨_, left_mem_segment ℝ _ _⟩,
    P.templateSupport_segment, P.segmentSupport_smul_of_nonneg _ hT]

/-- The zero-time point is retained by the limiting polynomial group law. -/
theorem gradedWordChartFlow_zero
    {L G I : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G]
    [Fintype I] [DecidableEq I]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (Exp : L → G) (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (hweight : ∀ i j k,
      (WordBasisSelections.basis X S β).repr
          ⁅(WordBasisSelections.basis X S β) i, (WordBasisSelections.basis X S β) j⁆ k ≠ 0 →
        bracketWordExponent (fun _ : I => 1) (β.val i) +
            bracketWordExponent (fun _ : I => 1) (β.val j) ≤
          bracketWordExponent (fun _ : I => 1) (β.val k))
    (v : L) (z : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, 0) = z := by
  dsimp only [dynkinFlowMap, ContinuousMap.coe_mk]
  rw [zero_smul]
  exact (gradedCoordinateBracket_groupLaws _ _ hweight Exp hinj hzero hneg hadd a hm).2.2.1 z

theorem affine_interval_image {W : Type*} [AddCommGroup W] [Module ℝ W]
    (w v : W) {T : ℝ} (hT : 0 < T) :
    (fun t : ℝ => w + t • v) '' Icc 0 T = segment ℝ w (w + T • v) := by
  rw [segment_eq_image']
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t / T, ⟨div_nonneg ht.1 hT.le, (div_le_one hT).mpr ht.2⟩, ?_⟩
    simp only [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hT.ne']
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * T, ⟨mul_nonneg ht.1 hT.le, ?_⟩, ?_⟩
    · simpa using mul_le_mul_of_nonneg_right ht.2 hT.le
    · simp only [add_sub_cancel_left, smul_smul]

/-- The entire limiting horizontal segment has exactly its expected
affine height image, including both endpoints. -/
theorem gradedWordChartFlow_height_image
    {L G W I : Type*} [LieRing L] [LieAlgebra ℝ L]
    [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) (z : Fin (finrank ℝ L) → ℝ) {T : ℝ} (hT : 0 < T)
    (hweight : ∀ i j k,
      (WordBasisSelections.basis X S β).repr
          ⁅(WordBasisSelections.basis X S β) i, (WordBasisSelections.basis X S β) j⁆ k ≠ 0 →
        bracketWordExponent (fun _ : I => 1) (β.val i) +
            bracketWordExponent (fun _ : I => 1) (β.val j) ≤
          bracketWordExponent (fun _ : I => 1) (β.val k)) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let F := dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
    (fun y => h (b.equivFun.symm y)) '' ((fun t => F (z, t)) '' Icc 0 T) =
      segment ℝ (h (b.equivFun.symm z)) (h (b.equivFun.symm z) + T • h v) := by
  dsimp only
  rw [← image_comp]
  convert affine_interval_image (h ((WordBasisSelections.basis X S β).equivFun.symm z)) (h v) hT using 1
  congr 1
  funext t
  exact gradedWordChartFlow_height X S β h hh Exp π hπ a hm v z t hweight

end PolycyclicRecognition

end

end OAI
