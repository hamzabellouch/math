import OAI.Geometry.Relativity.CKS.HeatRegularity

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma smooth_harmonicCoefficients_summable {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    Summable (fun l => harmonicCoefficient l (toL2 (smoothRestriction F hF))) := by
  have h := rotatedHarmonicCoefficient_rapid hF [] 0
  simp only [pow_zero, one_mul, rotatedHarmonicCoefficient_nil] at h
  exact (summable_nat_add_iff 2).mp h.of_norm

theorem smooth_harmonicCoefficients_tsum {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    (∑' l, harmonicCoefficient l (toL2 (smoothRestriction F hF))) = smoothRestriction F hF := by
  apply toL2_injective
  rw [toL2.map_tsum (smooth_harmonicCoefficients_summable hF)]
  simp_rw [toL2_harmonicCoefficient]
  exact (harmonicProjections_hasSum _).tsum_eq

lemma sphereEval_C (a : ℝ) : sphereEval (C a) = a • (1 : C(Sphere, ℝ)) := by
  ext x
  simp [sphereEval]

lemma sphereIntegral_constant (a : ℝ) : sphereIntegral (sphereEval (C a)) = a * sphereArea := by
  rw [sphereEval_C, map_smul]
  rfl

lemma harmonicProjection_zero_of_mean_zero (f : C(Sphere, ℝ)) (hf : sphereIntegral f = 0) :
    harmonicProjection 0 (toL2 f) = 0 := by
  apply ext_inner_right ℝ
  intro v
  obtain ⟨p, hp, hΔ, he⟩ := harmonicL2_exists_polynomial v
  have hpC : p = C (p.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous _).mpr hp)
  simp only [harmonicProjection, inner_zero_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← he, inner_toL2, hpC, sphereEval_C]
  rw [mul_smul_comm, mul_one, map_smul, hf, smul_zero]

lemma first_moments_pairing_zero (f : C(Sphere, ℝ))
    (hf : ∀ i : Fin 3, sphereIntegral (f * sphereCoordinate i) = 0)
    {p : Poly} (hp : p.IsHomogeneous 1) : sphereIntegral (f * sphereEval p) = 0 := by
  have hm : p ∈ Submodule.span ℝ (Set.range (X : Fin 3 → Poly)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hp
  clear hp
  induction hm using Submodule.span_induction with
  | mem p hp => obtain ⟨i, rfl⟩ := hp; simpa only [sphereEval_X] using hf i
  | zero => simp
  | add p q hp hq ihp ihq => simp [map_add, mul_add, ihp, ihq]
  | smul a p hp ihp => simp [map_smul, ihp]

lemma harmonicProjection_one_of_first_moments (f : C(Sphere, ℝ))
    (hf : ∀ i : Fin 3, sphereIntegral (f * sphereCoordinate i) = 0) :
    harmonicProjection 1 (toL2 f) = 0 := by
  apply ext_inner_right ℝ
  intro v
  obtain ⟨p, hp, hΔ, he⟩ := harmonicL2_exists_polynomial v
  simp only [harmonicProjection, inner_zero_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← he, inner_toL2]
  exact first_moments_pairing_zero f hf hp

lemma harmonicCoefficient_zero_of_mean (f : C(Sphere, ℝ)) {m : ℝ}
    (hf : sphereIntegral f = m * sphereArea) :
    harmonicCoefficient 0 (toL2 f) = sphereEval (C m) := by
  have hm : toL2 (sphereEval (C m)) ∈ harmonicL2 0 := by
    exact ⟨sphereEval (C m), ⟨C m, ⟨isHomogeneous_C (Fin 3) m, by simp [laplacian_apply]⟩, rfl⟩, rfl⟩
  have h := harmonicProjection_zero_of_mean_zero (f - sphereEval (C m)) (by
    rw [map_sub, hf, sphereIntegral_constant, sub_self])
  rw [map_sub, map_sub, sub_eq_zero] at h
  apply toL2_injective
  rw [toL2_harmonicCoefficient, h]
  exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨toL2 (sphereEval (C m)), hm⟩ : harmonicL2 0))

lemma harmonicCoefficient_one_of_first_moments (f : C(Sphere, ℝ))
    (hf : ∀ i : Fin 3, sphereIntegral (f * sphereCoordinate i) = 0) :
    harmonicCoefficient 1 (toL2 f) = 0 := by
  apply toL2_injective
  rw [toL2_harmonicCoefficient, harmonicProjection_one_of_first_moments f hf, map_zero]
  rfl

def Balanced (f : C(Sphere, ℝ)) (m : ℝ) : Prop :=
  sphereIntegral f = m * sphereArea ∧ ∀ i : Fin 3, sphereIntegral (f * sphereCoordinate i) = 0

lemma smooth_high_harmonics_initial {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) {m : ℝ}
    (hbal : Balanced (smoothRestriction F hF) m) :
    sphereEval (C m) + (∑' n, harmonicCoefficient (n + 2) (toL2 (smoothRestriction F hF))) =
      smoothRestriction F hF := by
  have h := (smooth_harmonicCoefficients_summable hF).sum_add_tsum_nat_add 2
  rw [smooth_harmonicCoefficients_tsum hF] at h
  simpa [Finset.sum_range_succ, harmonicCoefficient_zero_of_mean _ hbal.1,
    harmonicCoefficient_one_of_first_moments _ hbal.2] using h

def sphereHeatJet (p : ℕ → Poly) (a : HeatJet) (t : ℝ) : C(Sphere, ℝ) :=
  iteratedDeriv a.1 (CKSSpectralHeat.heat (fun n => sphereEval (rotationWord a.2 (p n)))) t

lemma sphereHeatJet_eq (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    (t : ℝ) (x : Sphere) :
    sphereHeatJet p a t x = jointHeatSeries p a (t, (x : Ambient)) := by
  rw [sphereHeatJet, CKSSpectralHeat.heat_deriv _ (hp a.2)]
  change (ContinuousMap.evalCLM ℝ x) (∑' n, _) = _
  rw [(ContinuousMap.evalCLM ℝ x).map_tsum
    (CKSSpectralHeat.term_deriv_summable _ (hp a.2) a.1 t)]
  unfold jointHeatSeries
  congr 1
  funext n
  rw [CKSSpectralHeat.term_deriv]
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul,
    heatTerm, temporalJet, radialExtension_on_sphere]

lemma sphereHeatJet_decay (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖sphereHeatJet p a t‖ ≤ Real.exp (-6 * t) *
      ∑' n, CKSSpectralHeat.eigenvalue n ^ a.1 * ‖sphereEval (rotationWord a.2 (p n))‖ :=
  CKSSpectralHeat.heat_decay _ (hp a.2) a.1 ht

lemma sphereHeatJet_smooth (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × Sphere => sphereHeatJet p a z.1 z.2) := by
  simpa only [sphereHeatJet_eq p hp a] using jointHeatSeries_sphere_smooth p hp a

lemma sphereHeatJet_initial {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    {m : ℝ} (hb : Balanced (smoothRestriction F hF) m) :
    sphereEval (C m) + sphereHeatJet (heatPolynomials (smoothRestriction F hF)) (0, []) 0 =
      smoothRestriction F hF := by
  simpa only [sphereHeatJet, iteratedDeriv_zero, rotationWord, heatPolynomials,
    harmonicCoefficientPolynomial_restriction, CKSSpectralHeat.heat_initial] using
    smooth_high_harmonics_initial hF hb

lemma jointHeatSeries_fderiv_tsum (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    {z : SpaceTime} (hz : z ∈ heatDomain) (v : SpaceTime) :
    fderiv ℝ (jointHeatSeries p a) z v = ∑' n,
      (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) v := by
  rw [(jointHeatSeries_hasFDerivAt p hp a hz).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Summable.tsum_finsetSum (fun o _ =>
    (jointHeatSeries_summable p hp (heatNext a o) hz).mul_right (heatField o z v))]
  apply Finset.sum_congr rfl
  intro o ho
  exact (tsum_mul_right).symm

lemma heatTerm_directional_rotation (p : ℕ → Poly) (a : HeatJet) (n : ℕ)
    (t : ℝ) {x : Ambient} (hx : x ≠ 0) (i j : Fin 3) :
    (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n (t, x) • heatField o (t, x))
      (0, rotationGenerator i j x) = heatTerm p (a.1, (i,j) :: a.2) n (t, x) := by
  rw [heatTerm_derivative_identity]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, zero_mul, mul_zero, add_zero]
  rw [← (radial_polynomial_hasFDerivAt (rotationWord a.2 (p n)) hx).fderiv]
  change temporalJet a.1 n t * smoothRotation i j
    (radialExtension (sphereEval (rotationWord a.2 (p n)))) x = _
  rw [smoothRotation_radial_polynomial _ i j hx]
  rfl

def spatialHeat (p : ℕ → Poly) (a : HeatJet) (t : ℝ) (x : Ambient) : ℝ :=
  jointHeatSeries p a (t, x)

lemma spatialHeat_smooth (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) (t : ℝ) :
    ContDiffOn ℝ ∞ (spatialHeat p a t) puncturedSpace :=
  (jointHeatSeries_smooth p hp a).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)

lemma spatialHeat_rotation (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    (t : ℝ) {x : Ambient} (hx : x ≠ 0) (i j : Fin 3) :
    smoothRotation i j (spatialHeat p a t) x = spatialHeat p (a.1, (i,j) :: a.2) t x := by
  have hd := (jointHeatSeries_hasFDerivAt p hp a (z := (t,x)) hx).comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change HasFDerivAt (spatialHeat p a t) _ x at hd
  rw [smoothRotation, hd.fderiv]
  change (∑ o, jointHeatSeries p (heatNext a o) (t,x) • heatField o (t,x))
    (0, rotationGenerator i j x) = _
  rw [← (jointHeatSeries_hasFDerivAt p hp a hx).fderiv,
    jointHeatSeries_fderiv_tsum p hp a hx]
  simp_rw [heatTerm_directional_rotation p a _ t hx i j]
  rfl

lemma spatialHeat_time_derivative (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    (t : ℝ) {x : Ambient} (hx : x ≠ 0) :
    HasDerivAt (fun s => spatialHeat p a s x) (spatialHeat p (a.1+1, a.2) t x) t := by
  have hd := (jointHeatSeries_hasFDerivAt p hp a (z := (t,x)) hx).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  convert! hd using 1
  simp only [Fintype.sum_option, add_apply,
    sum_apply, smul_apply, heatField,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', map_zero, Finset.sum_const_zero,
    add_zero, smul_eq_mul, mul_one, mul_zero, heatNext, spatialHeat]

end
end CKSSphericalHarmonics

end

end OAI
