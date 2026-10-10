import OAI.Analysis.Mahler.SphereFlux
import OAI.Analysis.Mahler.SphereVolumeOrientation
import OAI.Analysis.Mahler.SphereDensityRestriction
import OAI.Analysis.Mahler.SphereOrientation
import OAI.Analysis.Mahler.HomogeneousSphereIntegral
import OAI.Analysis.Mahler.SmallSphereLimits
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

open scoped BigOperators TensorProduct
open MeasureTheory Metric

namespace Mahler

private def restMap {κ : Type*} (σ : Equiv.Perm (Fin 1 ⊕ κ))
    (h : σ (Sum.inl 0) = Sum.inl 0) (j : κ) : κ :=
  match he : σ (Sum.inr j) with
  | .inl i => False.elim (by
      have hi : i = 0 := Subsingleton.elim _ _
      have hh := σ.injective (he.trans (by simpa [hi] using h.symm))
      cases hh)
  | .inr k => k

private lemma restMap_spec {κ : Type*} (σ : Equiv.Perm (Fin 1 ⊕ κ))
    (h : σ (Sum.inl 0) = Sum.inl 0) (j : κ) :
    Sum.inr (restMap σ h j) = σ (Sum.inr j) := by
  unfold restMap
  split
  · rename_i i he
    have hi : i = 0 := Subsingleton.elim _ _
    have hh := σ.injective (he.trans (by simpa [hi] using h.symm))
    cases hh
  · rename_i k he
    exact he.symm

private lemma perm_fixed_first_mem {κ : Type*} (σ : Equiv.Perm (Fin 1 ⊕ κ))
    (h : σ (Sum.inl 0) = Sum.inl 0) :
    σ ∈ (Equiv.Perm.sumCongrHom (Fin 1) κ).range := by
  have hs : σ.symm (Sum.inl 0) = Sum.inl 0 := by
    apply σ.injective
    simpa using h.symm
  let e : Equiv.Perm κ :=
    { toFun := restMap σ h
      invFun := restMap σ.symm hs
      left_inv := by
        intro j
        apply Sum.inr_injective (α := Fin 1)
        rw [restMap_spec, restMap_spec, σ.symm_apply_apply]
      right_inv := by
        intro j
        apply Sum.inr_injective (α := Fin 1)
        rw [restMap_spec, restMap_spec, σ.apply_symm_apply] }
  refine ⟨(Equiv.refl _, e), ?_⟩
  ext s
  cases s with
  | inl i =>
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using h.symm
  | inr j => exact restMap_spec σ h j

/-- The shuffle product has coefficient one on an outward normal followed
by tangent vectors. This includes its normalization, in arbitrary degree. -/
lemma wedge_one_outward {T κ : Type*} [AddCommGroup T] [Module ℝ T]
    [Fintype κ] [DecidableEq κ]
    (a : T [⋀^Fin 1]→ₗ[ℝ] ℂ) (B : T [⋀^κ]→ₗ[ℝ] ℂ)
    (x : T) (v : κ → T) (hx : a (fun _ => x) = 1)
    (hv : ∀ j, a (fun _ => v j) = 0) :
    wedge a B (Sum.elim (fun _ => x) v) = B v := by
  classical
  let q0 : Equiv.Perm.ModSumCongr (Fin 1) κ := Quotient.mk'' (1 : Equiv.Perm (Fin 1 ⊕ κ))
  change (LinearMap.mul' ℝ ℂ) (a.domCoprod B (Sum.elim (fun _ => x) v)) = _
  simp only [AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  rw [Finset.sum_eq_single q0]
  · simp [q0, AlternatingMap.domCoprod.summand_mk'', hx,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply]
  · intro q hq hne
    induction q using Quotient.inductionOn' with
    | h σ =>
      have hn : σ (Sum.inl 0) ≠ Sum.inl 0 := by
        intro he
        apply hne
        apply QuotientGroup.eq.mpr
        simpa using perm_fixed_first_mem σ he
      obtain ⟨j, hj⟩ : ∃ j, σ (Sum.inl 0) = Sum.inr j := by
        cases he : σ (Sum.inl 0) with
        | inl i => exact False.elim (hn (he.trans (congrArg Sum.inl (Subsingleton.elim i 0))))
        | inr j => exact ⟨j, rfl⟩
      have hz : a (fun i => Sum.elim (fun _ => x) v (σ (Sum.inl i))) = 0 := by
        convert hv j using 1
        congr 1
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simp [hi, hj]
      simp [AlternatingMap.domCoprod.summand_mk'',
        MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, hz]
  · simp

/-- Ordered identification of the normal slot and recursive boundary slots. -/
def densityBridgeSlots (k : ℕ) :
    (Fin 1 ⊕ (Fin 1 ⊕ WedgePowerSlots k)) ≃ Fin ((2*k+1)+1) :=
  (sphereFrameSlots k).trans (ambientFinEquiv k)

lemma densityBridgeSlots_normal (k : ℕ) (i : Fin 1) :
    densityBridgeSlots k (Sum.inl i) = 0 := by
  exact ambientFinEquiv_real_zero k

lemma densityBridgeSlots_tangent (k : ℕ) (j : Fin 1 ⊕ WedgePowerSlots k) :
    densityBridgeSlots k (Sum.inr j) = (boundaryFinEquiv k j).succ := by
  cases j with
  | inl i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ambientFinEquiv_imag_zero k
  | inr j => exact ambientFinEquiv_tail k j

lemma densityBridgeSlots_frame (k : ℕ) :
    sphereFrame k ∘ densityBridgeSlots k = sphereFluxFrame k := by
  funext s
  exact sphereFrame_interleaved k (sphereFrameSlots k s)

lemma densityBridgeSlots_cons (k : ℕ) (x : ComplexEuclidean (k+1))
    (v : Fin (2*k+1) → ComplexEuclidean (k+1)) :
    Matrix.vecCons x v ∘ densityBridgeSlots k =
      Sum.elim (fun _ => x) (v ∘ boundaryFinEquiv k) := by
  funext s
  cases s with
  | inl i => simp [Function.comp_def, densityBridgeSlots_normal]
  | inr j => simp [Function.comp_def, densityBridgeSlots_tangent]

/-- The recursive shuffle density is the normalized outward cofactor
coefficient. The slot equivalence preserves its positive orientation. -/
theorem sphereDensity_eq_orientedDensity {k : ℕ} {x : ComplexEuclidean (k+1)}
    (hx : ‖x‖ = 1)
    (B : ComplexEuclidean (k+1) [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ) :
    sphereDensity k x B = orientedDensity (sphereFrame k) (sphereVolume k)
      (B.domDomCongr (boundaryFinEquiv k)) x := by
  classical
  let A := (wedge (sphereNormal x) B).domDomCongr (densityBridgeSlots k)
  have hframe : A (sphereFrame k) = sphereDensity k x B := by
    change wedge (sphereNormal x) B (sphereFrame k ∘ densityBridgeSlots k) = _
    rw [densityBridgeSlots_frame]
    rfl
  have hA : A = A (sphereFrame k) • sphereVolume k := by
    apply topForm_ext_on_basis (sphereFrame k).toBasis
    change A (sphereFrame k) = A (sphereFrame k) * sphereVolume k (sphereFrame k)
    rw [sphereVolume_orthonormalFrame, mul_one]
  obtain ⟨v, hv, hvol⟩ := exists_outward_tangent_frame hx
  have hnormal : sphereNormal x (fun _ => x) = 1 := by
    change (inner ℝ x x : ℂ) = 1
    simp [hx]
  have hav : A (Matrix.vecCons x v) = B (v ∘ boundaryFinEquiv k) := by
    change wedge (sphereNormal x) B (Matrix.vecCons x v ∘ densityBridgeSlots k) = _
    rw [densityBridgeSlots_cons]
    apply wedge_one_outward _ _ _ _ hnormal
    intro j
    change (inner ℝ x (v (boundaryFinEquiv k j)) : ℂ) = 0
    simp [hv]
  have he := congrArg (fun C => C (Matrix.vecCons x v)) hA
  change A (Matrix.vecCons x v) = A (sphereFrame k) * sphereVolume k (Matrix.vecCons x v) at he
  rw [hav, hframe, hvol, mul_one] at he
  have hd := orientedDensity_spec (sphereFrame k) (sphereVolume k)
    (sphereVolume_frame_ne_zero k) (B.domDomCongr (boundaryFinEquiv k)) hx v hv
  rw [hvol, mul_one] at hd
  exact he.symm.trans hd

/-- The area integrals agree pointwise for an arbitrary boundary form field.
No integrability hypothesis is needed for this real-valued identity. -/
theorem sphereFlux_eq_integral_sphereDensity (k : ℕ)
    (B : ComplexEuclidean (k+1) →
      ComplexEuclidean (k+1) [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ) :
    sphereFlux k (fun x => (B x).domDomCongr (boundaryFinEquiv k)) =
      ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
        (sphereDensity k z (B z)).re ∂sphereArea (k+1) := by
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : ‖(z : ComplexEuclidean (k+1))‖ = 1 := by simp
  exact congrArg Complex.re (sphereDensity_eq_orientedDensity hz (B z)).symm

/-- The actual boundary density is integrable: C2 regularity and compactness
supply this premise, rather than assuming an integral exists. -/
lemma integrable_sphereBoundaryDensity {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ}
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 2 u (z : ComplexEuclidean (k+1))) :
    Integrable (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      sphereDensity k z (boundaryForm u k z)) (sphereArea (k+1)) := by
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  let : CompactSpace (sphere (0 : ComplexEuclidean (k+1)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ComplexEuclidean (k+1)) 1)
  have hc : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      sphereDensity k z (boundaryForm u k z)) := by
    simpa using continuous_radiusFluxDensity 1 hu
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The complex flux used for the rescaling limit and the real cofactor flux
used for homogeneous deformation have exactly the same real part. -/
theorem unitSphereFlux_re_eq_sphereFlux {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ}
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 2 u (z : ComplexEuclidean (k+1))) :
    (unitSphereFlux k u).re = sphereFlux k (boundaryFormFin (dcLinear u)) := by
  unfold unitSphereFlux sphereFlux
  have hi := integral_re (integrable_sphereBoundaryDensity hu)
  simp only [RCLike.re_eq_complex_re] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : ‖(z : ComplexEuclidean (k+1))‖ = 1 := by simp
  exact congrArg Complex.re (sphereDensity_eq_orientedDensity hz (boundaryForm u k z))

/-- For the homogeneous polynomial, the endpoint equality
requires only the mass hypotheses. -/
theorem MassHypotheses.unitSphereFlux_re_eq_homogeneousSphereFlux {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    (unitSphereFlux k (logTau (polynomialMap G))).re = homogeneousSphereFlux k N G := by
  apply unitSphereFlux_re_eq_sphereFlux
  intro z
  apply contDiffAt_logTau_of_open isOpen_univ (Set.mem_univ (z : ComplexEuclidean (k+1)))
    (fun j => (polynomialMap_differentiable G j).differentiableOn)
  have hz : (z : ComplexEuclidean (k+1)) ≠ 0 := by
    intro he
    have hh : ‖(z : ComplexEuclidean (k+1))‖ = 1 := by simp
    simp [he] at hh
  exact tau_pos_of_component_ne_zero (h.leading_nonzero z hz)

/-- The varying-radius surface integrals converge to the actual homogeneous
cofactor endpoint. No unproved homogeneous-flux constancy is used here. -/
theorem MassHypotheses.small_sphere_real_flux_limit {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Filter.Tendsto (fun r => (radiusSphereFlux k (logTau f) r).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (homogeneousSphereFlux k N G)) := by
  rw [← h.unitSphereFlux_re_eq_homogeneousSphereFlux]
  exact Complex.continuous_re.continuousAt.tendsto.comp h.small_sphere_surface_integral_limit

end Mahler

end OAI
