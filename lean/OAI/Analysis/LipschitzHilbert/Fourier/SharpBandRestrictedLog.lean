import OAI.Analysis.LipschitzHilbert.Fourier.SharpBandUniformHigh
import OAI.Analysis.LipschitzHilbert.Fourier.SharpBandScalarEndpoints
import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedLogNumerics

namespace OAI

/-! The three actual sharp band regimes give the logarithmic restricted
estimate on Schwartz tests, uniformly in the inner endpoint and width. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem log_mass_ratio (F E ratio : ℝ) (hF : 0<F) (hr : 0<ratio)
    (heq : E=ratio^2*F) : Real.log (F/E)= -2*Real.log ratio := by
  have hE : 0<E := heq ▸ mul_pos (pow_pos hr 2) hF
  rw [Real.log_div hF.ne' hE.ne',heq,Real.log_mul (pow_pos hr 2).ne' hF.ne',Real.log_pow]
  ring

theorem actual_sharp_band_restricted_log (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, 0<epsilon → epsilon≤R → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      0<planeMeasure.real F → 0<planeMeasure.real E →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ l r : ℝ, 600*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
        (schwartzVerticalProjection p w 0 f) g‖≤
        C*((1+|Real.log (planeMeasure.real F/planeMeasure.real E)|)^3)⁻¹*
          Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨Cb,hCb,hbasic⟩ := actual_sharp_band_basic hVariation p hp
  obtain ⟨Cr,hCr,hreverse⟩ := actual_sharp_band_reverse hVariation p hp
  obtain ⟨Ch,L0,hCh,hL0,hhigh⟩ := actual_sharp_band_uniform_high hVariation hLL hH p hp
  obtain ⟨D,hD,hexp⟩ := exponential_log_weight (9/20) (by norm_num)
  let C := Cb*(1+2*L0)^3+Cr*D+27*Ch
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro epsilon R w he heR hRquarter hw field hfield hfieldBound f g hf hg E F hE hF hEfin hFfin
    hFpos hEpos hgs hfs l r hstrip hfstrip hgstrip
  let a := planeMeasure.real F
  let b := planeMeasure.real E
  let weight := ((1+|Real.log (a/b)|)^3)⁻¹
  let root := Real.sqrt a*Real.sqrt b
  let u := fun z : ℝ×ℝ => field (planeCoordinates z)
  let value := kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection p w 0 f) g
  have ha : 0<a := hFpos
  have hb : 0<b := hEpos
  have hwgt : 0≤weight := by dsimp [weight]; positivity
  have hroot : 0≤root := by dsimp [root]; positivity
  have hu : LipschitzWith 2 u := by simpa only [u,mul_one] using product_slope_lipschitz field hfield
  have hub (z) : |u z|≤1 := (hfieldBound _).trans (by norm_num)
  have hwidth : r-l≤1/4 := by linarith only [hstrip]
  have hbpos : 0≤Cb*(1+2*L0)^3 := by positivity
  have hrpos : 0≤Cr*D := by positivity
  have hhpos : 0≤27*Ch := by positivity
  have hCbC : Cb*(1+2*L0)^3≤C := by dsimp [C]; linarith only [hrpos,hhpos]
  have hCrC : Cr*D≤C := by dsimp [C]; linarith only [hbpos,hhpos]
  have hChC : 27*Ch≤C := by dsimp [C]; linarith only [hbpos,hrpos]
  change ‖value‖≤C*weight*Real.sqrt a*Real.sqrt b
  rw [mul_assoc (C*weight)]
  change ‖value‖≤C*weight*root
  by_cases hba : b≤a
  · have hbound := hreverse epsilon R w he heR hw u hu hub f g hf hg E F hE hF hEfin hFfin
      hFpos hEpos hba hgs hfs l r hwidth hfstrip hgstrip
    let x := Real.log (a/b)
    have hx : 0≤x := Real.log_nonneg ((one_le_div hb).2 hba)
    have hpow : (b/a)^(9/20:ℝ)=Real.exp (-(9/20:ℝ)*x) := by
      rw [Real.rpow_def_of_pos (div_pos hb ha)]
      congr 1
      dsimp [x]
      rw [Real.log_div hb.ne' ha.ne',Real.log_div ha.ne' hb.ne']
      ring
    have hxweight : ((1+x)^3)⁻¹=weight := by
      dsimp only [weight,x]
      rw [abs_of_nonneg hx]
    have hdecay := hexp x hx
    rw [hxweight] at hdecay
    calc
      ‖value‖ ≤ Cr*root*Real.exp (-(9/20:ℝ)*x) := by
        simpa only [a,b,root,Real.sqrt_mul ha.le,hpow] using hbound
      _ ≤ Cr*root*(D*weight) := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hCr.le hroot)
      _ = (Cr*D)*weight*root := by ring
      _ ≤ C*weight*root := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCrC hwgt) hroot
  · let ratio := Real.sqrt (b/a)
    obtain ⟨hr,heq⟩ := sqrt_mass_ratio a b ha hb
    let L := Real.log ratio
    have hlog : Real.log (a/b)= -2*L := log_mass_ratio a b ratio ha hr heq
    have hab : a≤b := (lt_of_not_ge hba).le
    have hlognonpos : Real.log (a/b)≤0 := Real.log_nonpos (div_pos ha hb).le ((div_le_one hb).2 hab)
    have hL : 0≤L := by linarith only [hlog,hlognonpos]
    have habs : |Real.log (a/b)|=2*L := by rw [abs_of_nonpos hlognonpos,hlog]; ring
    by_cases hLL0 : L0≤L
    · have hbound := hhigh L hLL0 epsilon R w he heR hRquarter hw field hfield hfieldBound f g
        a b ratio ha hb hr heq rfl hf hg
        (restrictedSchwartz_l1 f hf F hF hFfin hfs) (restrictedSchwartz_l1 g hg E hE hEfin hgs)
        (restrictedSchwartz_energy f hf F hF hFfin hfs) (restrictedSchwartz_energy g hg E hE hEfin hgs)
        l r hstrip hfstrip hgstrip
      have hweight := high_log_weight L (by linarith only [hL0,hLL0])
      have hwid : ((1+2*L)^3)⁻¹=weight := by dsimp only [weight]; rw [habs]
      rw [hwid] at hweight
      calc
        ‖value‖ ≤ Ch*L^(-19:ℝ)*root := by simpa only [mul_assoc,root] using hbound
        _ ≤ Ch*(27*weight)*root := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hweight hCh.le) hroot
        _ = (27*Ch)*weight*root := by ring
        _ ≤ C*weight*root := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hChC hwgt) hroot
    · have hbound := hbasic epsilon R w he heR hw u hu hub f g hf hg E F hE hF hEfin hFfin hgs hfs
        l r hwidth hfstrip hgstrip
      have hweight : 1≤(1+2*L0)^3*weight := by
        have h := bounded_log_weight (2*L) (2*L0) (by positivity) (by linarith only [hLL0])
        simpa only [weight,habs] using h
      calc
        ‖value‖ ≤ Cb*root := by simpa only [a,b,root,mul_assoc] using hbound
        _ ≤ Cb*root*((1+2*L0)^3*weight) :=
          le_mul_of_one_le_right (mul_nonneg hCb.le hroot) hweight
        _ = (Cb*(1+2*L0)^3)*weight*root := by ring
        _ ≤ C*weight*root := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCbC hwgt) hroot

end LipschitzHilbert.PacketRepresentation

end

end OAI
