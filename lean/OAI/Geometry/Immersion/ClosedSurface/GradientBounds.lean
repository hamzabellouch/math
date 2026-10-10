import OAI.Geometry.Immersion.ClosedSurface.ModeBounds
import OAI.Geometry.Immersion.ClosedSurface.QuadraticMean

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma contDiffOn_coordDeriv_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Base} (hU : IsOpen U) {f : Base → E} (hf : ContDiffOn ℝ ∞ f U) (v : Base) :
    ContDiffOn ℝ ∞ (coordDeriv v f) U := by
  intro p hp
  exact (contDiffAt_coordDeriv ((hf p hp).contDiffAt (hU.mem_nhds hp)) v).contDiffWithinAt


def gradientAmplitude {n : ℕ} (τ : ℝ) (Z : Field n) (v : Base) : Field n :=
  fun p => coordDeriv v Z p + (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • Z p

lemma gradientAmplitude_eq {n : ℕ} (τ : ℝ) (Z : Field n) (v : Base) (p : Base) :
    gradientAmplitude τ Z v p =
      ClosedSurfaceR4.QuadraticMean.derivativeAmplitude τ Prod.fst Z v p := by
  simp [gradientAmplitude, ClosedSurfaceR4.QuadraticMean.derivativeAmplitude,
    coordDeriv, fderiv_fst]

lemma contDiffOn_gradientAmplitude {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {Z : Field n} (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) (v : Base) :
    ContDiffOn ℝ ∞ (gradientAmplitude τ Z v) U := by
  have hh : ContDiffOn ℝ ∞ (fun p => (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • Z p) U := by
    simpa only [Pi.smul_def'] using
      (contDiffOn_const (c := Complex.I / (τ : ℂ) * (v.1 : ℂ))).smul hZ
  exact (contDiffOn_coordDeriv_vector hU hZ v).add hh

lemma gradientAmplitude_sub_leading {n : ℕ} (τ : ℝ) (Z V : Field n) (v p : Base) :
    gradientAmplitude τ Z v p - (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • V p =
      coordDeriv v Z p + (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • (Z p - V p) := by
  simp only [gradientAmplitude, smul_sub]
  abel

lemma weighted_modeApprox_free {n : ℕ} {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hVsm : ContDiffOn ℝ ∞ V U)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 1) K)
    (hbV : WeightedBound U s (m + q + 1) C V) :
    WeightedBound U s m ((1 + freeModeConstant n m K q) * C)
      (modeApprox τ G V (fun _ => 0) q) := by
  have he := weighted_modeApprox_free_sub hτ hG h hs hτs hs1 hK hC hVsm hX hY hV q m hc hbV
  have hz := contDiffOn_modeApprox τ h hVsm (f := fun _ => 0) contDiffOn_const q
  have hv := hbV.mono_order (show m ≤ m + q + 1 by omega)
  have ha := hv.add h.isOpen.uniqueDiffOn hs.le hVsm (hz.sub hVsm) he
  have ha' : WeightedBound U s m (C + freeModeConstant n m K q * (τ / s) * C)
      (modeApprox τ G V (fun _ => 0) q) := ha.congr (fun _ _ => by dsimp only; abel)
  apply ha'.mono_const
  have hrat : τ / s ≤ 1 := (div_le_one hs).2 hτs
  have hnon := mul_nonneg (freeModeConstant_nonneg n m q hK) hC
  nlinarith [mul_le_mul_of_nonneg_left hrat hnon]

def gradientErrorConstant (n m : ℕ) (K : ℝ) (q : ℕ) : ℝ :=
  1 + freeModeConstant n (m + 1) K q + freeModeConstant n m K q

lemma gradientErrorConstant_pos (n m q : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 < gradientErrorConstant n m K q := by
  have h1 := freeModeConstant_nonneg n (m + 1) q hK
  have h0 := freeModeConstant_nonneg n m q hK
  unfold gradientErrorConstant
  linarith




theorem weighted_gradientAmplitude_free_error {n : ℕ} {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hVsm : ContDiffOn ℝ ∞ V U)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 2) K)
    (hbV : WeightedBound U s (m + q + 2) C V)
    (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m (gradientErrorConstant n m K q * (C / s))
      (fun p => gradientAmplitude τ (modeApprox τ G V (fun _ => 0) q) v p -
        (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • V p) := by
  have hm : m + 1 + q + 1 = m + q + 2 := by omega
  have hc' : ReconstructionCoefficientBound G U s (m + 1 + q + 1) K := hm.symm ▸ hc
  have hb' : WeightedBound U s (m + 1 + q + 1) C V := hm.symm ▸ hbV
  have hbZ := weighted_modeApprox_free hτ hG h hs hτs hs1 hK hC hVsm hX hY hV q (m + 1) hc' hb'
  have hZsm := contDiffOn_modeApprox τ h hVsm (f := fun _ => 0) contDiffOn_const q
  have hd := hbZ.directional h.isOpen hs hZsm v
  have hdn : 0 ≤ (1 + freeModeConstant n (m + 1) K q) * C / s := by
    exact div_nonneg (mul_nonneg (by linarith [freeModeConstant_nonneg n (m + 1) q hK]) hC) hs.le
  have hd' : WeightedBound U s m ((1 + freeModeConstant n (m + 1) K q) * C / s)
      (coordDeriv v (modeApprox τ G V (fun _ => 0) q)) := by
    exact hd.mono_const (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hv hdn)
  have he := weighted_modeApprox_free_sub hτ hG h hs hτs hs1 hK hC hVsm hX hY hV q m
    (hc.mono_order (by omega)) (hbV.mono_order (by omega))
  have hen := mul_nonneg (mul_nonneg (freeModeConstant_nonneg n m q hK)
    (div_nonneg hτ.le hs.le)) hC
  have he' := he.complex_smul_pi h.isOpen.uniqueDiffOn hs hen (hZsm.sub hVsm)
    (Complex.I / (τ : ℂ) * (v.1 : ℂ))
  have hnorm : ‖Complex.I / (τ : ℂ) * (v.1 : ℂ)‖ ≤ 1 / τ := by
    rw [norm_mul, norm_div]
    simp only [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    exact mul_le_of_le_one_right (div_nonneg zero_le_one hτ.le)
      (by simpa only [Real.norm_eq_abs] using (norm_fst_le v).trans hv)
  have he'' : WeightedBound U s m (freeModeConstant n m K q * C / s)
      (fun p => (Complex.I / (τ : ℂ) * (v.1 : ℂ)) •
        (modeApprox τ G V (fun _ => 0) q p - V p)) := by
    apply he'.mono_const
    calc
      _ ≤ (1 / τ) * (freeModeConstant n m K q * (τ / s) * C) :=
        mul_le_mul_of_nonneg_right hnorm hen
      _ = _ := by field_simp [ne_of_gt hτ]
  have hsc : ContDiffOn ℝ ∞ (fun p => (Complex.I / (τ : ℂ) * (v.1 : ℂ)) •
      (modeApprox τ G V (fun _ => 0) q p - V p)) U := by
    simpa only [Pi.smul_def'] using
      (contDiffOn_const (c := Complex.I / (τ : ℂ) * (v.1 : ℂ))).smul (hZsm.sub hVsm)
  have ha := hd'.add h.isOpen.uniqueDiffOn hs.le (contDiffOn_coordDeriv_vector h.isOpen hZsm v) hsc he''
  have heq : (1 + freeModeConstant n (m + 1) K q) * C / s + freeModeConstant n m K q * C / s =
      gradientErrorConstant n m K q * (C / s) := by unfold gradientErrorConstant; ring
  rw [heq] at ha
  exact ha.congr (fun p _ => gradientAmplitude_sub_leading τ _ V v p)

end ClosedSurfaceR4.SmallModes

end

end OAI
