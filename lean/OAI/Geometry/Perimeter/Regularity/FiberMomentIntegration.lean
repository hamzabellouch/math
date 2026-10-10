import OAI.Geometry.Perimeter.Regularity.MollifiedFiberMoment

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary

variable {n : ℕ}

def normalCylinder (v : Euc n) (hv : ‖v‖ = 1) (K : Set (normalPlane v))
    (b : ℝ) : Set (Euc n) :=
  normalCoordinates v hv '' (K ×ˢ Icc (-b) b)

theorem isCompact_normalCylinder {v : Euc n} (hv : ‖v‖ = 1)
    {K : Set (normalPlane v)} (hK : IsCompact K) (b : ℝ) :
    IsCompact (normalCylinder v hv K b) :=
  (hK.prod isCompact_Icc).image (by
    change Continuous (fun x : normalPlane v × ℝ ↦ (x.1:Euc n)+x.2•v)
    exact (continuous_subtype_val.comp continuous_fst).add (continuous_snd.smul continuous_const))

theorem integral_normalCylinder {v : Euc n} (hv : ‖v‖ = 1)
    {K : Set (normalPlane v)} (hK : IsCompact K) {b : ℝ} (hb : 0 ≤ b)
    {f : Euc n → ℝ} (hf : Continuous f) :
    (∫ x in normalCylinder v hv K b, f x) =
      ∫ y in K, ∫ s in (-b)..b, f ((y:Euc n)+s•v) := by
  rw [normalCylinder, (normalCoordinates_measurePreserving v hv).setIntegral_image_emb
    (normalCoordinates v hv).measurableEmbedding]
  have hc : Continuous (fun x : normalPlane v × ℝ ↦ f ((x.1:Euc n)+x.2•v)) :=
    hf.comp ((continuous_subtype_val.comp continuous_fst).add
      (continuous_snd.smul continuous_const))
  have hi : IntegrableOn (fun x : normalPlane v × ℝ ↦ f ((x.1:Euc n)+x.2•v))
      (K ×ˢ Icc (-b) b) (volume.prod volume) := hc.continuousOn.integrableOn_compact (hK.prod (isCompact_Icc (a := -b) (b := b)))
  change (∫ x in K ×ˢ Icc (-b) b, f ((x.1:Euc n)+x.2•v) ∂volume.prod volume) = _
  rw [setIntegral_prod _ hi]
  apply setIntegral_congr_fun hK.measurableSet
  intro y _
  dsimp only
  rw [intervalIntegral.integral_of_le (by linarith : -b ≤ b), integral_Icc_eq_integral_Ioc]

theorem continuous_profile_integral {v : Euc n} (f : Euc n → ℝ)
    (hf : Continuous f) (l u : ℝ) :
    Continuous (fun y : normalPlane v ↦ ∫ s in l..u, f ((y:Euc n)+s•v)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hf.comp ((continuous_subtype_val.comp continuous_fst).add
    (continuous_snd.smul continuous_const))

theorem mollified_fiber_integrated_defect {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖ = 1) {k : Euc n → ℝ}
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (hp : ∀ x, 0 ≤ k x) (hu : ∫ x, k x = 1)
    {a b ε R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+ε < b)
    (hs : Function.support k ⊆ Metric.ball 0 ε)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0))
    {K : Set (normalPlane v)} (hK : IsCompact K) (hKR : ∀ y ∈ K, ‖y‖+b+ε ≤ R) :
    let q := phaseMollification E k
    let H := fun y : normalPlane v ↦ -b+∫ s in (-b)..b, q ((y:Euc n)+s•v)
    let M := ∫ x in normalCylinder v hv K b,
      (inner ℝ v x)^2 * (-fderiv ℝ q x v)
    0 ≤ M - ∫ y in K, (H y)^2 ∧
    M - ∫ y in K, (H y)^2 ≤
      4*b*(∫ x in normalCylinder v hv K b, q x*(1-q x)) +
      8*b^2*(∫ x in normalCylinder v hv K b, max (fderiv ℝ q x v) 0) := by
  dsimp only
  let q := phaseMollification E k
  have hq : Continuous q := (phaseMollification_contDiff hE hk hc).continuous
  have hd : Continuous (fun x ↦ fderiv ℝ q x v) :=
    ((phaseMollification_contDiff hE hk hc).continuous_fderiv (by simp)).clm_apply continuous_const
  have hm : Continuous (fun x ↦ (inner ℝ v x)^2*(-fderiv ℝ q x v)) :=
    (continuous_const.inner continuous_id).pow 2 |>.mul hd.neg
  have hiM := integral_normalCylinder hv hK hb hm
  have hiD := integral_normalCylinder hv hK hb (hq.mul ((continuous_const (y := (1:ℝ))).sub hq))
  have hiP := integral_normalCylinder hv hK hb (hd.max (continuous_const (y := (0:ℝ))))
  have he (y : normalPlane v) (s : ℝ) : inner ℝ v ((y:Euc n)+s•v) = s := by
    rw [inner_add_right, real_inner_smul_right,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property,
      real_inner_self_eq_norm_sq,hv]
    ring
  dsimp only [q,Pi.mul_apply,Pi.sub_apply] at hiD
  dsimp only [q] at hiM hiP
  simp_rw [he, ← mollifiedNormalProfile_deriv hE hk hc v] at hiM
  simp_rw [← mollifiedNormalProfile_deriv hE hk hc v] at hiP
  rw [hiM,hiD,hiP]
  let A := fun y : normalPlane v ↦ ∫ s in (-b)..b,
    s^2*(-deriv (mollifiedNormalProfile E k v y) s)
  let B := fun y : normalPlane v ↦ (-b+∫ s in (-b)..b, q ((y:Euc n)+s•v))^2
  let D := fun y : normalPlane v ↦ ∫ s in (-b)..b, q ((y:Euc n)+s•v)*(1-q ((y:Euc n)+s•v))
  let P := fun y : normalPlane v ↦ ∫ s in (-b)..b, max (deriv (mollifiedNormalProfile E k v y) s) 0
  have hA : Continuous A := by
    have h := continuous_profile_integral (v := v) _ hm (-b) b
    dsimp only [q] at h
    simp_rw [he, ← mollifiedNormalProfile_deriv hE hk hc v] at h
    exact h
  have hB : Continuous B :=
    (continuous_const.add (continuous_profile_integral (v := v) q hq (-b) b)).pow 2
  have hD : Continuous D := continuous_profile_integral (v := v) _
    (hq.mul ((continuous_const (y := (1:ℝ))).sub hq)) (-b) b
  have hP : Continuous P := by
    have h := continuous_profile_integral (v := v) _ (hd.max (continuous_const (y := (0:ℝ)))) (-b) b
    dsimp only [q] at h
    simp_rw [← mollifiedNormalProfile_deriv hE hk hc v] at h
    exact h
  have hAi : IntegrableOn A K volume := hA.continuousOn.integrableOn_compact hK
  have hBi : IntegrableOn B K volume := hB.continuousOn.integrableOn_compact hK
  have hDi : IntegrableOn D K volume := hD.continuousOn.integrableOn_compact hK
  have hPi : IntegrableOn P K volume := hP.continuousOn.integrableOn_compact hK
  change 0 ≤ (∫ y in K, A y)-(∫ y in K, B y) ∧
    (∫ y in K, A y)-(∫ y in K, B y) ≤ 4*b*(∫ y in K, D y)+8*b^2*(∫ y in K, P y)
  rw [← integral_sub hAi hBi, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hDi.const_mul _) (hPi.const_mul _)]
  have hpoint (y : normalPlane v) (hy : y ∈ K) :=
    mollifiedNormalProfile_flux_defect hE hv hk hc hp hu ha hb hab hs hphase y (hKR y hy)
  constructor
  · exact setIntegral_nonneg hK.measurableSet fun y hy ↦ (hpoint y hy).1
  · exact setIntegral_mono_on (hAi.sub hBi) ((hDi.const_mul _).add (hPi.const_mul _))
      hK.measurableSet fun y hy ↦ (hpoint y hy).2

end RPISingularHarnack

end

end OAI
