import OAI.Analysis.LipschitzHilbert.Phase.ActualBandDiagonal
import OAI.Analysis.LipschitzHilbert.Fourier.BandProjectedHigh
import OAI.Analysis.LipschitzHilbert.Estimates.PlanarPairingEnergy

namespace OAI

/-! The high-disparity bound for the localized finite time operator,
combining the diagonal bin estimate and the full commutator error under
the martingale variation and directional maximal hypotheses. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped FourierTransform Topology
namespace LipschitzHilbert.PacketRepresentation

theorem actual_band_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi : SchwartzMap ℝ ℂ) (c C a M : ℝ)
    (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M) :
    ∃ D A L0 : ℝ, 0<D ∧ 0<A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (topLength W w : ℝ), 0<topLength → 0<W → 0<w → w≤W →
      5*(w/W)≤c/2 → c/2≤C →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ),
      (∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C) →
    ∀ (F E ratio : ℝ), 0<F → 0<E → 0<ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r m : ℝ, 600*(r-l)≤1 →
      (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      Real.exp (L^(9/10:ℝ))≤m → m≤2*Real.exp (L^(9/10:ℝ)) → W=m*w →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength)
        (fun z => field (planeCoordinates z)) f z*star (g z) ∂planeMeasure‖≤
        A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  obtain ⟨D,A,Lbase,hD,hA,hbase,hmain⟩ := band_projected_high hVariation hLL psi c C a M hc hC ha hM hpsi
  obtain ⟨Lerr,herr⟩ := eventually_atTop.1
    (eventually_totalProjectedBinError (𝓕⁻ psi : SchwartzMap ℝ ℂ) C hC)
  refine ⟨D,A+1,max Lbase Lerr,hD,by linarith,hbase.trans (le_max_left _ _),?_⟩
  intro L hL N topLength W w htop hW hw hwW hsmall hcC htime hlength field hfield hfieldBound
    f g hband F E ratio hF hE hr heq hlog hfInf hgInf hfL1 hgL1 hfE hgE l r m hstrip hfstrip hgstrip
    hmlo hmhi hWeq
  have hLb : Lbase≤L := (le_max_left _ _).trans hL
  have hLe : Lerr≤L := (le_max_right _ _).trans hL
  have hL16 : 16≤L := hbase.trans hLb
  have hLp : 0<L := by linarith
  have hmone : 1≤m := (Real.one_le_exp (Real.rpow_nonneg hLp.le (9/10:ℝ))).trans hmlo
  have hu : LipschitzWith 2 (fun z : ℝ×ℝ => field (planeCoordinates z)) := by
    simpa only [mul_one] using product_slope_lipschitz field hfield
  have hdiag := hmain L hLb N topLength W w htop hW hw hwW hsmall hcC htime hlength
    field hfield hfieldBound f g f.continuous.measurable g.continuous.measurable
    (f.memLp 2 planeMeasure) (g.memLp 2 planeMeasure) f.integrable g.integrable
    F E ratio hF hE hr heq hlog hfInf hgInf hfL1 hgL1 hfE hgE l r m hstrip hfstrip hgstrip hmlo hmhi hWeq
  let u := fun z : ℝ×ℝ => field (planeCoordinates z)
  let error := totalProjectedBinError (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength w W c C u f
  have heEnergy : (∫ z, ‖error z‖^2 ∂planeMeasure)≤L^(-40:ℝ)*(∫ z, ‖f z‖^2 ∂planeMeasure) :=
    herr L hLe N topLength w W c m htop hw hW hmone hWeq hmhi htime u hu f
      (positive_band_abs_bound f w c C hw hc hband)
  have heMem : MemLp error 2 planeMeasure :=
    (totalProjectedBinError_energy (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength w W c C m
      htop hw hW hC hmone hWeq u hu f (positive_band_abs_bound f w c C hw hc hband)).1
  have hePair := planar_pairing_bound_of_energy error g heMem (g.memLp 2 planeMeasure)
    L (∫ z, ‖f z‖^2 ∂planeMeasure) hLp (integral_nonneg fun _ => sq_nonneg _) heEnergy
  have heBound : ‖∫ z, error z*star (g z) ∂planeMeasure‖≤L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
    calc
      _ ≤ L^(-20:ℝ)*Real.sqrt (∫ z, ‖f z‖^2 ∂planeMeasure)*
          Real.sqrt (∫ z, ‖g z‖^2 ∂planeMeasure) := hePair
      _ ≤ L^(-20:ℝ)*Real.sqrt F*Real.sqrt E := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfE) (by positivity))
          (Real.sqrt_le_sqrt hgE) (Real.sqrt_nonneg _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤L) (by norm_num : (-20:ℝ)≤-19))
          (Real.sqrt_nonneg F)) (Real.sqrt_nonneg E)
  have hwidth : r-l≤1/4 := by linarith
  have hfull : (∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength)
      u f z*star (g z) ∂planeMeasure)=
      ∫ z, shortSlopeOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength)
        u f z*star (g z) ∂planeMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z =>
      (shortSlopeOperator_pairing_eq _ u f g l r hwidth hfstrip hgstrip z).symm
  rw [hfull,actualBand_pairing_eq_diagonal psi N topLength w W c C htop hw hW hc hC u hu f g
    hband l r hwidth hfstrip hgstrip]
  exact (norm_sub_le _ _).trans ((add_le_add hdiag heBound).trans_eq (by ring))

end LipschitzHilbert.PacketRepresentation

end

end OAI
