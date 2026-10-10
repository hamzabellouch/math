import OAI.Geometry.Relativity.CKS.BoostTransport

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open Set MeasureTheory
open CKSSphericalHarmonics (puncturedSpace surfaceMeasure smoothRestriction)

def pullbackRate (p : E) (F : E → ℝ) (z : ℝ × E) : ℝ :=
  fderiv ℝ (normalizedPullback p F) z (1,0)

lemma normalizedDomain_open : IsOpen (Set.univ ×ˢ (puncturedSpace : Set E) : Set (ℝ × E)) :=
  isOpen_univ.prod puncturedSpace.isOpen

lemma pullbackRate_smooth (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    ContDiffOn ℝ ∞ (pullbackRate p F) (Set.univ ×ˢ (puncturedSpace : Set E)) :=
  ((normalizedPullback_smooth p hF).fderiv_of_isOpen normalizedDomain_open (by simp)).clm_apply contDiffOn_const

lemma pullback_time_derivative (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => normalizedPullback p F (t,(n:E))) (pullbackRate p F (t,(n:E))) t := by
  have hg := ((normalizedPullback_smooth p hF).contDiffAt (x := (t,(n:E)))
    (normalizedDomain_open.mem_nhds ⟨mem_univ t,CKSSphericalHarmonics.sphere_ne_zero n⟩)).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => (t,(n:E))) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (n:E))
  convert! hg.hasFDerivAt.comp_hasDerivAt t hline using 1

lemma pullbackRate_transport (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (t : ℝ) (n : Sphere) :
    pullbackRate p F (t,(n:E)) =
      (flowEnergy p t)⁻¹ * (fderiv ℝ (fun x => normalizedPullback p F (t,x)) n (boostField p n) -
        2*inner ℝ p (n:E)*normalizedPullback p F (t,(n:E))) :=
  (pullback_time_derivative p hF t n).unique (normalizedPullback_transport p hF t n)

lemma continuous_restrict_sphere {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Set.univ ×ˢ (puncturedSpace : Set E))) :
    Continuous (fun z : ℝ × Sphere => G (z.1,(z.2:E))) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hi : Continuous (fun z : ℝ × Sphere => (z.1,(z.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have ho : ContinuousAt G (z.1,(z.2:E)) :=
    (hG.contDiffAt (x := (z.1,(z.2:E))) (normalizedDomain_open.mem_nhds
      ⟨mem_univ _, CKSSphericalHarmonics.sphere_ne_zero z.2⟩)).continuousAt
  exact ho.comp (f := fun z : ℝ × Sphere => (z.1,(z.2:E))) hi.continuousAt

lemma sphere_integrable_smooth {H : E → ℝ} (hH : ContDiffOn ℝ ∞ H puncturedSpace) :
    Integrable (fun n : Sphere => H n) surfaceMeasure :=
  (smoothRestriction H hH).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma boostField_smooth (p : E) : ContDiff ℝ ∞ (boostField p) :=
  contDiff_const.sub ((ContDiff.inner ℝ contDiff_const contDiff_id).smul contDiff_id)

lemma pullbackRate_integral_zero (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) (t : ℝ) :
    ∫ n : Sphere, pullbackRate p F (t,(n:E)) ∂surfaceMeasure = 0 := by
  let G : E → ℝ := fun x => normalizedPullback p F (t,x)
  have hG : ContDiffOn ℝ ∞ G puncturedSpace := normalizedPullback_spatial p hF t
  have hDG : ContDiffOn ℝ ∞ (fun x => fderiv ℝ G x (boostField p x)) puncturedSpace :=
    (hG.fderiv_of_isOpen puncturedSpace.isOpen (by simp)).clm_apply (boostField_smooth p).contDiffOn
  have hqG : ContDiffOn ℝ ∞ (fun x => inner ℝ p x * G x) puncturedSpace :=
    (ContDiff.inner ℝ contDiff_const contDiff_id).contDiffOn.mul hG
  have he : (fun n : Sphere => pullbackRate p F (t,(n:E))) =
      fun n : Sphere => (flowEnergy p t)⁻¹ * (fderiv ℝ G n (boostField p n) - 2*(inner ℝ p (n:E)*G n)) := by
    funext n
    rw [pullbackRate_transport p hF]
    dsimp only [G]; ring
  rw [he, integral_const_mul, integral_sub (sphere_integrable_smooth hDG) ((sphere_integrable_smooth hqG).const_mul 2), integral_const_mul]
  have hi := CKSSphericalHarmonics.sphereIntegral_boostField hG p
  change (∫ n : Sphere, fderiv ℝ G n (boostField p n) ∂surfaceMeasure) = _ at hi
  rw [hi]; ring

lemma normalizedIntegral_derivative_zero (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ n : Sphere, normalizedPullback p F (t,(n:E)) ∂surfaceMeasure) 0 t₀ := by
  let H (t : ℝ) (n : Sphere) := normalizedPullback p F (t,(n:E))
  let R (t : ℝ) (n : Sphere) := pullbackRate p F (t,(n:E))
  have hH : Continuous (fun z : ℝ × Sphere => H z.1 z.2) :=
    continuous_restrict_sphere (normalizedPullback_smooth p hF)
  have hR : Continuous (fun z : ℝ × Sphere => R z.1 z.2) :=
    continuous_restrict_sphere (pullbackRate_smooth p hF)
  have hHt (t : ℝ) : Continuous (H t) := by
    have hc : Continuous (fun n : Sphere => (t,n)) := continuous_const.prodMk continuous_id
    exact Continuous.comp (f := fun n : Sphere => (t,n))
      (g := fun z : ℝ × Sphere => H z.1 z.2) hH hc
  have hRt (t : ℝ) : Continuous (R t) := by
    have hc : Continuous (fun n : Sphere => (t,n)) := continuous_const.prodMk continuous_id
    exact Continuous.comp (f := fun n : Sphere => (t,n))
      (g := fun z : ℝ × Sphere => R z.1 z.2) hR hc
  let K : Set (ℝ × Sphere) := Icc (t₀-1) (t₀+1) ×ˢ univ
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hR.continuousOn
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := surfaceMeasure) (x₀ := t₀) (s := Ioo (t₀-1) (t₀+1))
    (F := H) (F' := R) (bound := fun _ => C)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun t => (hHt t).aestronglyMeasurable)
    ((hHt t₀).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hRt t₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun n t ht => hC (t,n) ⟨⟨ht.1.le,ht.2.le⟩, mem_univ n⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun n t _ => pullback_time_derivative p hF t n)
  convert! h.2 using 1
  exact (pullbackRate_integral_zero p hF t₀).symm

theorem flow_area_substitution (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) (t : ℝ) :
    ∫ n : Sphere, (flowD p t n)⁻¹ ^2 * F (flowPhi p t n) ∂surfaceMeasure =
      ∫ n : Sphere, F n ∂surfaceMeasure := by
  let H (t : ℝ) (n : Sphere) := normalizedPullback p F (t,(n:E))
  have hd := normalizedIntegral_derivative_zero p hF
  have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have hzero : ∀ n : Sphere, H 0 n = F n := by
    intro n
    simp [H, normalizedPullback_sphere, weightedPullback, flowPhi, flowD, flowEnergy,
      flowS, flowCoeff]
  have ht : ∀ n : Sphere, H t n = (flowD p t n)⁻¹ ^2 * F (flowPhi p t n) := by
    intro n
    rw [show H t n = weightedPullback p t F n by exact normalizedPullback_sphere p F t n]
    rfl
  change (∫ n : Sphere, H t n ∂surfaceMeasure) = ∫ n : Sphere, H 0 n ∂surfaceMeasure at he
  simpa only [hzero,ht] using he

end
end CKSLorentz

end

end OAI
