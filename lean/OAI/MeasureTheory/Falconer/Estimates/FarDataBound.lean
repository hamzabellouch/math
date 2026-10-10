import OAI.MeasureTheory.Falconer.Estimates.FarKernelDataEstimates
import OAI.MeasureTheory.Falconer.Fourier.FarIntegralAssembly

namespace OAI

/-! # The complete conditional far estimate on the exact original state class -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

 theorem exists_far_data_bound
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M q : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C Cerr : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ 0 ≤ Cerr ∧
      ∀ (D : JetStateFarData m B), D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss →
      ∀ (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3)),
      ENNReal.ofReal D.prefactor *
        (∫⁻ z in farDisplacementRegion (m+3) D.a D.h,
          ENNReal.ofReal ‖D.kernel f g w₀ Ψ z‖ ∂D.originalMeasure) ≤
        (∑ b ∈ Finset.Icc (D.a+9) (D.h+6), D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b) +
        ENNReal.ofReal D.prefactor *
          (2+((Finset.Icc (D.a+9) (D.h+6)).card:ℝ≥0∞)) *
          ENNReal.ofReal (Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss))*D.originalMeasure univ := by
  obtain ⟨B₁,C₁,hB₁,hC₁,hstationary⟩ := exists_far_data_stationary_band m K L M (by omega) hΨ hs
  obtain ⟨B₂,C₂,hB₂,hC₂,hreplace⟩ := exists_far_data_replacement hgnomonic hquadratic
    m K L M hM hML hΨ.continuous.measurable hpos hs hW hΨW
  obtain ⟨B₃,H,S,hB₃,hH,hS,hnoncomp⟩ := exists_far_data_noncomparable hgnomonic hquadratic
    m K L M q hM hML hΨ hpos hs hW hΨW
  let B := max (max B₁ B₂) (max B₃ (descriptorJetBound (m+3) K))
  let V := (sphereMeasure (m+3)).real univ
  let Cnc := H*V*(2:ℝ)^q+4*W*S*(2*V+S)
  let Cerr := max Cnc C₂
  have hB₁B : B₁ ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB₂B : B₂ ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hB₃B : B₃ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBB : descriptorJetBound (m+3) K ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hCnc : 0 ≤ Cnc := by dsimp [Cnc,V]; positivity
  have hCerr : 0 ≤ Cerr := hCnc.trans (le_max_left _ _)
  refine ⟨B,C₁,Cerr,hB₁.trans hB₁B,hC₁,hCerr,?_⟩
  intro D hloss horder f g w₀
  let ε := Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hnc : ∀ z ∈ leftNoncomparableFar (m+3) D.a D.h ∪
      rightNoncomparableFar (m+3) D.a D.h, ‖D.kernel f g w₀ Ψ z‖ ≤ ε := by
    intro z hz
    have ht := hnoncomp B hB₃B D hloss horder f g w₀ z hz
    have hc := noncomparable_coefficient_common hH hW hS
      (show 0 ≤ V from measureReal_nonneg)
      (sq_nonneg (B₃^K*D.Z⁻¹)) (sq_nonneg ((descriptorJetBound (m+3) K)^K*D.Z⁻¹))
      (sq_nonneg (B^K*D.Z⁻¹)) (show 0 ≤ (2:ℝ)^q by positivity)
      (normalized_jet_bound_mono (zero_le_one.trans hB₃) hB₃B D.Z_pos K 2)
      (normalized_jet_bound_mono (zero_le_one.trans (descriptorJetBound_one_le _ _)) hBB D.Z_pos K 2)
    have hc' := hc.trans_eq (show
        (H*V*(2:ℝ)^q+4*W*S*(2*V+S))*((B^K*D.Z⁻¹)^2)^2 =
          Cnc*(B^K*D.Z⁻¹)^4 by dsimp [Cnc]; ring)
    exact ht.trans ((mul_le_mul_of_nonneg_right hc' (by positivity)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Cnc C₂) (by positivity)) (by positivity)))
  have herr : ∀ z ∈ comparableFarRegion (m+3) D.a D.h,
      ‖D.kernel f g w₀ Ψ z-D.stationaryKernel f g w₀ M Ψ z‖ ≤ ε := by
    intro z hz
    apply (hreplace B hB₂B D horder f g w₀ z hz).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul (le_max_right Cnc C₂)
      (normalized_jet_bound_mono (zero_le_one.trans hB₂) hB₂B D.Z_pos K 4)
      (by positivity) hCerr
  have hsband (b : ℕ) (hb : b ∈ Finset.Icc (D.a+9) (D.h+6)) :
      ENNReal.ofReal D.prefactor *
        (∫⁻ z in comparableFarRegion (m+3) D.a D.h ∩ comparableLengthBand (m+3) b,
          ENNReal.ofReal ‖D.stationaryKernel f g w₀ M Ψ z‖ ∂D.originalMeasure) ≤
        D.collisionTerm w₀ (C₁*(B^K*D.Z⁻¹)^4) b :=
    (hstationary B hB₁B D f g w₀ b hb).trans
      (D.collisionTerm_mono w₀
        (mul_le_mul_of_nonneg_left (normalized_jet_bound_mono (zero_le_one.trans hB₁)
          hB₁B D.Z_pos K 4) hC₁) b)
  have hf := far_integral_assembly (m+3) D.a D.h D.originalMeasure
    (D.kernel f g w₀ Ψ) (D.stationaryKernel f g w₀ M Ψ) hε hnc herr
  apply (mul_le_mul' (le_refl (ENNReal.ofReal D.prefactor)) hf).trans
  rw [mul_add,Finset.mul_sum]
  apply add_le_add
  · exact Finset.sum_le_sum hsband
  · exact le_of_eq (by dsimp [ε]; ring)

end Falconer

end OAI
