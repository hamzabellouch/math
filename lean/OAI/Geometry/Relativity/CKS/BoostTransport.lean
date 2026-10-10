import OAI.Geometry.Relativity.CKS.BoostDivergence

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open Set

def normalizeAmbient (x : E) : E := ‖x‖⁻¹ • x

def weightedPullback (p : E) (t : ℝ) (F : E → ℝ) (x : E) : ℝ :=
  (flowD p t x)⁻¹ ^2 * F (flowPhi p t x)

def normalizedPullback (p : E) (F : E → ℝ) (z : ℝ × E) : ℝ :=
  weightedPullback p z.1 F (normalizeAmbient z.2)

lemma boostField_tangent (p : E) (n : Sphere) : inner ℝ (n:E) (boostField p n) = 0 := by
  simp [boostField, inner_sub_right, inner_smul_right, real_inner_comm]

lemma normalizeAmbient_smooth {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ normalizeAmbient x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

@[simp] lemma normalizeAmbient_sphere (n : Sphere) : normalizeAmbient n = n := by
  simp [normalizeAmbient]

lemma norm_derivative_sphere (n : Sphere) : HasFDerivAt (norm : E → ℝ) (innerSL ℝ (n:E)) n := by
  have h := (Real.hasDerivAt_sqrt (show ‖(n:E)‖^2 ≠ 0 by rw [sphere_norm]; norm_num)).comp_hasFDerivAt (n:E)
    (hasStrictFDerivAt_norm_sq (n:E)).hasFDerivAt
  convert! h using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg x)).symm
  · ext x
    simp

lemma normalizeAmbient_fderiv_tangent (n : Sphere) (Y : E) (hY : inner ℝ (n:E) Y = 0) :
    fderiv ℝ normalizeAmbient n Y = Y := by
  have hi := (hasDerivAt_inv (show ‖(n:E)‖ ≠ 0 by rw [sphere_norm]; norm_num)).comp_hasFDerivAt (n:E)
    (norm_derivative_sphere n)
  have h := hi.smul (hasFDerivAt_id (n:E))
  change HasFDerivAt normalizeAmbient _ n at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, hY]

lemma flowPhi_smooth_at (p : E) (t : ℝ) (n : Sphere) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => flowPhi p z.1 z.2) (t,(n:E)) :=
  (((flowD_smooth p).contDiffAt).inv (flowD_pos p t n).ne').smul (flowS_smooth p).contDiffAt

lemma flowPhi_nonzero (p : E) (t : ℝ) (n : Sphere) : flowPhi p t n ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [flowPhi_norm]; norm_num

lemma flowPhi_fderiv (p : E) (t : ℝ) (n : Sphere) (Y : E) :
    fderiv ℝ (flowPhi p t) n Y =
      (flowD p t n)⁻¹ • flowSLinear p t Y -
        (flowDLinear p t Y/(flowD p t n)^2) • flowS p t n := by
  have hi := (hasDerivAt_inv (flowD_pos p t n).ne').comp_hasFDerivAt (n:E) (flowD_fderivative p t n)
  have h := hi.smul (flowS_fderivative p t n)
  change HasFDerivAt (flowPhi p t) _ n at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Function.comp_apply]
  module

lemma flowPhi_derivative (p : E) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => flowPhi p t n)
      ((flowD p t n)⁻¹ • ((1+t/flowEnergy p t*inner ℝ p (n:E)) • p) -
        ((t*‖p‖^2/flowEnergy p t+inner ℝ p (n:E))/(flowD p t n)^2) • flowS p t n) t := by
  convert! ((flowD_derivative p t n).inv (flowD_pos p t n).ne').smul (flowS_derivative p t n) using 1
  module

lemma flowPhi_transport (p : E) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => flowPhi p t n)
      ((flowEnergy p t)⁻¹ • fderiv ℝ (flowPhi p t) n (boostField p n)) t := by
  convert! flowPhi_derivative p t n using 1
  rw [flowPhi_fderiv]
  have hS := flowS_transport p t (n:E)
  have hD := flowD_transport p t (n:E)
  have hS' : flowSLinear p t (boostField p n) =
      flowEnergy p t • ((1+t/flowEnergy p t*inner ℝ p (n:E)) • p) - inner ℝ p (n:E) • flowS p t n :=
    eq_sub_of_add_eq hS.symm
  have hD' : flowDLinear p t (boostField p n) =
      flowEnergy p t * (t*‖p‖^2/flowEnergy p t+inner ℝ p (n:E)) - inner ℝ p (n:E)*flowD p t n :=
    eq_sub_of_add_eq hD.symm
  rw [hS', hD']
  have hE := (flowEnergy_pos p t).ne'
  have hden := (flowD_pos p t n).ne'
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hE, hden]
  ring

lemma weightedPullback_smooth_at (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => weightedPullback p z.1 F z.2) (t,(n:E)) := by
  have hc := hF.contDiffAt (CKSSphericalHarmonics.puncturedSpace.isOpen.mem_nhds (flowPhi_nonzero p t n))
  have hd : ContDiffAt ℝ ∞ (fun z : ℝ × E => (flowD p z.1 z.2)⁻¹ ^2) (t,(n:E)) :=
    ((flowD_smooth p).contDiffAt.inv (flowD_pos p t n).ne').pow 2
  exact hd.mul (hc.comp (t,(n:E)) (flowPhi_smooth_at p t n))

lemma weightedPullback_spatial_derivative (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) (Y : E) :
    fderiv ℝ (weightedPullback p t F) n Y =
      (2*(flowD p t n)⁻¹*(-flowDLinear p t Y/(flowD p t n)^2))*F (flowPhi p t n) +
        (flowD p t n)⁻¹ ^2 * fderiv ℝ F (flowPhi p t n) (fderiv ℝ (flowPhi p t) n Y) := by
  have hphi : DifferentiableAt ℝ (flowPhi p t) (n:E) := by
    convert! ((flowPhi_smooth_at p t n).comp (n:E) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hf := (hF.contDiffAt (CKSSphericalHarmonics.puncturedSpace.isOpen.mem_nhds (flowPhi_nonzero p t n))).differentiableAt (by simp)
  have ha := ((hasDerivAt_inv (flowD_pos p t n).ne').pow 2).comp_hasFDerivAt (n:E) (flowD_fderivative p t n)
  have h := ha.mul (hf.hasFDerivAt.comp (n:E) hphi.hasFDerivAt)
  change HasFDerivAt (weightedPullback p t F) _ n at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
  ring

lemma weightedPullback_transport (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => weightedPullback p t F n)
      ((flowEnergy p t)⁻¹ * (fderiv ℝ (weightedPullback p t F) n (boostField p n) -
        2*inner ℝ p (n:E)*weightedPullback p t F n)) t := by
  have hf := (hF.contDiffAt (CKSSphericalHarmonics.puncturedSpace.isOpen.mem_nhds (flowPhi_nonzero p t n))).differentiableAt (by simp)
  have h := (((flowD_derivative p t n).inv (flowD_pos p t n).ne').pow 2).mul
    (hf.hasFDerivAt.comp_hasDerivAt t (flowPhi_transport p t n))
  convert! h using 1
  rw [weightedPullback_spatial_derivative p hF]
  simp only [map_smul, smul_eq_mul, weightedPullback, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply, Pi.inv_apply, Function.comp_apply]
  have hD := flowD_transport p t (n:E)
  have hD' : flowDLinear p t (boostField p n) =
      flowEnergy p t * (t*‖p‖^2/flowEnergy p t+inner ℝ p (n:E)) - inner ℝ p (n:E)*flowD p t n :=
    eq_sub_of_add_eq hD.symm
  rw [hD']
  field_simp [(flowEnergy_pos p t).ne', (flowD_pos p t n).ne']
  ring

lemma normalizedPullback_smooth (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) :
    ContDiffOn ℝ ∞ (normalizedPullback p F) (Set.univ ×ˢ (CKSSphericalHarmonics.puncturedSpace : Set E)) := by
  intro z hz
  let n : Sphere := CKSSphericalHarmonics.normalizeSphere ⟨z.2,hz.2⟩
  have h := weightedPullback_smooth_at p hF z.1 n
  exact (h.comp z (contDiffAt_fst.prodMk ((normalizeAmbient_smooth hz.2).comp z contDiffAt_snd))).contDiffWithinAt

lemma normalizedPullback_spatial (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun x => normalizedPullback p F (t,x)) CKSSphericalHarmonics.puncturedSpace :=
  (normalizedPullback_smooth p hF).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨Set.mem_univ _,hx⟩)

@[simp] lemma normalizedPullback_sphere (p : E) (F : E → ℝ) (t : ℝ) (n : Sphere) :
    normalizedPullback p F (t,(n:E)) = weightedPullback p t F n := by
  simp [normalizedPullback]

lemma normalizedPullback_fderiv_tangent (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    fderiv ℝ (fun x => normalizedPullback p F (t,x)) n (boostField p n) =
      fderiv ℝ (weightedPullback p t F) n (boostField p n) := by
  have hf := ((weightedPullback_smooth_at p hF t n).comp (n:E) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hn := (normalizeAmbient_smooth (CKSSphericalHarmonics.sphere_ne_zero n)).differentiableAt (by simp)
  change fderiv ℝ ((weightedPullback p t F) ∘ normalizeAmbient) n _ = _
  have hf' : DifferentiableAt ℝ (weightedPullback p t F) (normalizeAmbient n) := by
    rw [normalizeAmbient_sphere]
    convert! hf
  rw [fderiv_comp (n:E) hf' hn, ContinuousLinearMap.comp_apply, normalizeAmbient_sphere,
    normalizeAmbient_fderiv_tangent n _ (boostField_tangent p n)]

lemma normalizedPullback_transport (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => normalizedPullback p F (t,(n:E)))
      ((flowEnergy p t)⁻¹ * (fderiv ℝ (fun x => normalizedPullback p F (t,x)) n (boostField p n) -
        2*inner ℝ p (n:E)*normalizedPullback p F (t,(n:E)))) t := by
  simp only [normalizedPullback_sphere, normalizedPullback_fderiv_tangent p hF]
  exact weightedPullback_transport p hF t n

end
end CKSLorentz

end

end OAI
