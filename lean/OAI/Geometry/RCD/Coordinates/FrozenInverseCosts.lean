import OAI.Geometry.RCD.Coordinates.NormalizedUpdate
import OAI.Geometry.RCD.Coordinates.DifferentialStep

namespace OAI

/-!
# Inverse-derivative costs in frozen coordinates

The covariance identity is used only near the testing point, where the
Jacobian is represented by continuous linear equivalences. Differentiating
this local identity transports the normalized inverse costs with exactly
one factor of `r⁻¹` per source derivative.
-/

open Filter
open scoped Topology InnerProductSpace ContDiff

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Evaluation on a fixed vector commutes with each finite-order derivative. -/
theorem iteratedFDeriv_clm_apply_fixed {K : E → E →L[ℝ] E} {x : E} {m : ℕ}
    (hK : ContDiffAt ℝ m K x) (w : E) (xi : Fin m → E) :
    iteratedFDeriv ℝ m (fun y => K y w) x xi = iteratedFDeriv ℝ m K x xi w := by
  have h := (ContinuousLinearMap.apply ℝ E w).iteratedFDeriv_comp_left hK le_rfl
  exact congrArg (fun f => f xi) h

/-- Transport of operator jets through a local frozen covariance identity. -/
theorem frozen_operator_jet_transport (T : E ≃L[ℝ] E) (x xi w : E) (r : ℝ)
    {Ko Kn : E → E →L[ℝ] E} {m : ℕ}
    (hKo : ContDiffAt ℝ m Ko x) (hKn : ContDiffAt ℝ m Kn 0)
    (hcov : (fun z => Kn z ((T.symm : E →L[ℝ] E).adjoint w)) =ᶠ[𝓝 0]
      (fun z => Ko (frozenSource r T x z) w)) :
    iteratedFDeriv ℝ m Kn 0 (fun _ => T xi) ((T.symm : E →L[ℝ] E).adjoint w) =
      r ^ m • iteratedFDeriv ℝ m Ko x (fun _ => xi) w := by
  let L : E →L[ℝ] E := r • (T.symm : E →L[ℝ] E)
  have hvalue : ContDiffAt ℝ m (fun y => Ko y w) x := hKo.clm_apply contDiffAt_const
  have hvalue' : ContDiffAt ℝ m (fun y => Ko y w) (x + L 0) := by simpa using hvalue
  have hjet := congrArg (fun f => f (fun _ => T xi)) ((hcov.iteratedFDeriv ℝ m).eq_of_nhds)
  calc
    _ = iteratedFDeriv ℝ m (fun z => Kn z ((T.symm : E →L[ℝ] E).adjoint w))
        0 (fun _ => T xi) := (iteratedFDeriv_clm_apply_fixed hKn _ _).symm
    _ = iteratedFDeriv ℝ m (fun z => Ko (frozenSource r T x z) w) 0 (fun _ => T xi) := hjet
    _ = iteratedFDeriv ℝ m (fun y => Ko y w) x (fun _ => r • xi) := by
      have h := iteratedFDeriv_comp_affine_apply L (fun y => Ko y w) x 0 m hvalue'
        (fun _ => T xi)
      simpa [frozenSource, L] using h
    _ = r ^ m • iteratedFDeriv ℝ m (fun y => Ko y w) x (fun _ => xi) := by
      rw [(iteratedFDeriv ℝ m (fun y => Ko y w) x).map_smul_univ]
      simp
    _ = _ := by rw [iteratedFDeriv_clm_apply_fixed hKo]

/-- The inverse covariance holds in a neighborhood, so it may be
differentiated without assuming invertibility away from that neighborhood. -/
theorem inverseTranspose_normalized_eventually {r : ℝ} (hr : r ≠ 0)
    (T : E ≃L[ℝ] E) (x : E) (h : E → E) (e : E → E ≃L[ℝ] E)
    (hh : ContDiffAt ℝ 3 h x)
    (hlocal : ∀ᶠ y in 𝓝 x, fderiv ℝ h y = (e y : E →L[ℝ] E)) (w : E) :
    (fun z => operatorInverseTranspose (fderiv ℝ (normalizedCoordinates r T x h) z)
      ((T.symm : E →L[ℝ] E).adjoint w)) =ᶠ[𝓝 0]
    (fun z => operatorInverseTranspose (fderiv ℝ h (frozenSource r T x z)) w) := by
  have hsource : Continuous (frozenSource r T x) := by
    unfold frozenSource
    fun_prop
  have htend : Tendsto (frozenSource r T x) (𝓝 0) (𝓝 x) := by
    simpa [frozenSource] using hsource.tendsto (0 : E)
  have hreg : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 h y := hh.eventually (by norm_num)
  filter_upwards [htend.eventually hlocal, htend.eventually hreg] with z hz hhz
  have hj : fderiv ℝ (normalizedCoordinates r T x h) z =
      (T.symm.trans (e (frozenSource r T x z)) : E →L[ℝ] E) := by
    rw [fderiv_normalizedCoordinates hr T x z h (hhz.differentiableAt (by norm_num)), hz]
    rfl
  rw [hj, hz, operatorInverseTranspose_equiv, operatorInverseTranspose_equiv]
  exact inverseTranspose_normalized_apply T (e (frozenSource r T x z)) w

/-- The lower metric estimate and normalized source jets imply the first
two original-space inverse costs, with the same constant at every point
and scale. All invertibility data outside the center are local. -/
theorem exists_frozen_inverse_derivative_cost {A : ℝ} (hA : 1 ≤ A) :
    ∃ C : ℝ, Real.sqrt A ≤ C ∧ 2 * A ≤ C ∧
      ∀ (B r : ℝ), 0 < B → 0 < r → ∀ (T : E ≃L[ℝ] E) (x : E)
        (h : E → E) (e : E → E ≃L[ℝ] E),
      ContDiffAt ℝ 3 h x →
      (∀ᶠ y in 𝓝 x, fderiv ℝ h y = (e y : E →L[ℝ] E)) →
      (∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖fderiv ℝ h x xi‖ ^ 2) →
      (∀ m, 2 ≤ m → m ≤ 3 →
        ‖iteratedFDeriv ℝ m (normalizedCoordinates r T x h) 0‖ ≤
          B ^ (m - 1) * (m.factorial : ℝ) ^ 3) →
      let K := fun y => operatorInverseTranspose (fderiv ℝ h y)
      ∀ xi w : E,
        ‖fderiv ℝ K x xi w‖ ≤
          8 * C * B / r * ‖T xi‖ * ‖(T.symm : E →L[ℝ] E).adjoint w‖ ∧
        ‖diagonalSecond K x xi w‖ ≤
          216 * C * B ^ 2 / r ^ 2 * ‖T xi‖ ^ 2 * ‖(T.symm : E →L[ℝ] E).adjoint w‖ := by
  obtain ⟨C, hC0, hC1, hcost⟩ := exists_inverseTranspose_low_order_cost (E := E) hA
  refine ⟨C, hC0, hC1, ?_⟩
  intro B r hB hr T x h e hh hlocal hlower hjets
  let g := normalizedCoordinates r T x h
  let Ko := fun y => operatorInverseTranspose (fderiv ℝ h y)
  let Kn := fun z => operatorInverseTranspose (fderiv ℝ g z)
  have he : fderiv ℝ h x = (e x : E →L[ℝ] E) := Filter.EventuallyEq.eq_of_nhds hlocal
  have hunit : IsUnit (fderiv ℝ h x) := by rw [he]; exact (e x).toUnit.isUnit
  have hsource : ContDiffAt ℝ 3 (frozenSource r T x) 0 := by
    unfold frozenSource
    fun_prop
  have hg : ContDiffAt ℝ 3 g 0 := by
    have hh' : ContDiffAt ℝ 3 h (frozenSource r T x 0) := by simpa [frozenSource] using hh
    exact ((hh'.comp 0 hsource).sub contDiffAt_const).const_smul r⁻¹
  have hgJ : fderiv ℝ g 0 = (T.symm.trans (e x) : E →L[ℝ] E) := by
    change fderiv ℝ (normalizedCoordinates r T x h) 0 = _
    rw [fderiv_normalizedCoordinates hr.ne' T x 0 h]
    · simp only [frozenSource, map_zero, smul_zero, add_zero, he]
      rfl
    · simpa [frozenSource] using hh.differentiableAt (by norm_num)
  have hgunit : IsUnit (fderiv ℝ g 0) := by rw [hgJ]; exact (T.symm.trans (e x)).toUnit.isUnit
  have hginv : ‖Ring.inverse (fderiv ℝ g 0)‖ ≤ Real.sqrt A := by
    have heLower : ∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖e x xi‖ ^ 2 := by
      simpa only [he, ContinuousLinearEquiv.coe_coe] using hlower
    have heInv : Ring.inverse (fderiv ℝ g 0) =
        (T : E →L[ℝ] E) ∘L ((e x).symm : E →L[ℝ] E) := by
      rw [hgJ]
      change Ring.inverse ((T.symm.trans (e x)).toUnit : E →L[ℝ] E) = _
      rw [Ring.inverse_unit]
      rfl
    rw [heInv]
    exact norm_frozen_comp_inverse_le T (e x) hA heLower
  have hKo : ContDiffAt ℝ 2 Ko x :=
    contDiffAt_inverseTranspose_field (hh.fderiv_right (m := 2) (by norm_num)) hunit
  have hKn : ContDiffAt ℝ 2 Kn 0 :=
    contDiffAt_inverseTranspose_field (hg.fderiv_right (m := 2) (by norm_num)) hgunit
  have hbounds := (hcost B hB g 0 hg hgunit hginv hjets).2
  dsimp only
  intro xi w
  have hcov := inverseTranspose_normalized_eventually hr.ne' T x h e hh hlocal w
  have ht1 := frozen_operator_jet_transport T x xi w r
    (hKo.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) (hKn.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hcov
  have ht2 := frozen_operator_jet_transport T x xi w r hKo hKn hcov
  simp only [iteratedFDeriv_one_apply, pow_one] at ht1
  change fderiv ℝ Kn 0 (T xi) ((T.symm : E →L[ℝ] E).adjoint w) =
    r • fderiv ℝ Ko x xi w at ht1
  rw [← diagonalSecond_eq hKn, ← diagonalSecond_eq hKo] at ht2
  obtain ⟨hb1, hb2⟩ := hbounds (T xi) ((T.symm : E →L[ℝ] E).adjoint w)
  change ‖fderiv ℝ Kn 0 (T xi) ((T.symm : E →L[ℝ] E).adjoint w)‖ ≤ _ at hb1
  change ‖diagonalSecond Kn 0 (T xi) ((T.symm : E →L[ℝ] E).adjoint w)‖ ≤ _ at hb2
  rw [ht1, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hb1
  rw [ht2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)] at hb2
  constructor
  · calc
      _ ≤ (8 * C * B * ‖T xi‖ * ‖(T.symm : E →L[ℝ] E).adjoint w‖) / r :=
        (le_div_iff₀ hr).2 (by nlinarith [hb1])
      _ = _ := by ring
  · calc
      _ ≤ (216 * C * B ^ 2 * ‖T xi‖ ^ 2 * ‖(T.symm : E →L[ℝ] E).adjoint w‖) / r ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hr)).2 (by nlinarith [hb2])
      _ = _ := by ring

end RegularPointCoordinates

end

end OAI
