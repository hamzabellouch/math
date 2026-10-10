import OAI.Geometry.Convex.GeneralMahler.Polar

namespace OAI
/-! Cone-volume identities. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real WithLp
open scoped ENNReal NNReal Topology Pointwise RealInnerProductSpace
namespace GeneralMahler
namespace Body
variable {n : ℕ}

theorem vol_pos (K : Body n) : 0 < (volume (K : Set (Rn n))).toReal := by
  refine ENNReal.toReal_pos ?_ K.isCompact.measure_lt_top.ne
  exact ne_of_gt (lt_of_lt_of_le (isOpen_interior.measure_pos volume K.has_interior)
    (measure_mono interior_subset))

/-- Slice integral of a cone at a vertical dual vector. -/
theorem chi_axis (K : Body n) (r : ℝ) (hr : 0 < r) :
    chi K.cone (pair r 0) =
      (r⁻¹ ^ (n+1)) * n.factorial * (volume (K : Set (Rn n))).toReal := by
  classical
  let C : Set (LiftSpace n) := K.cone
  let v := (volume (K : Set (Rn n))).toReal
  let f := C.indicator fun p => Real.exp (-⟪pair r 0,p⟫)
  have hi : Integrable f :=
    (integrable_indicator_iff K.cone.isClosed.measurableSet).mpr
      (chi_integrable (axis_dual_interior K r hr))
  let e := MeasurableEquiv.toLp 2 (ℝ × Rn n)
  have he : MeasurePreserving e :=
    WithLp.volume_preserving_toLp ℝ (Rn n)
  have H : chi K.cone (pair r 0) = ∫ t : ℝ, ∫ y : Rn n, f (pair t y) := by
    unfold chi
    rw [← integral_indicator K.cone.isClosed.measurableSet]
    change (∫ x, f x) = _
    rw [← he.integral_comp']
    exact integral_prod _ ((integrable_map_equiv e f).mp (by change Integrable f (Measure.map e volume); rw [he.map_eq]; exact hi))
  let g : ℝ → ℝ := fun t => t ^ n * exp (-(r*t)) * v
  have heq : (fun t : ℝ => ∫ y : Rn n, f (pair t y)) =ᵐ[volume] (Ioi 0).indicator g := by
    filter_upwards [show ∀ᵐ t : ℝ, t ≠ 0 from by
      rw [ae_iff]; simp] with t ht
    rcases lt_or_gt_of_ne ht with h|h
    · have hh (y : Rn n) : f (pair t y) = 0 := indicator_of_notMem (by
        change pair t y ∉ K.cone
        rw [pair_mem_cone]; exact fun hx => h.not_ge hx.1) _
      simp [hh,h.not_gt]
    have ha : ∀ y : Rn n, pair t y ∈ C ↔ y ∈ t • (K : Set (Rn n)) := by
      intro y
      change pair t y ∈ K.cone ↔ _
      rw [pair_mem_cone, Set.mem_smul_set]
      simp only [h.le, true_and, SetLike.mem_coe, eq_comm]
    have he : (fun y : Rn n => f (pair t y)) =
        (t • (K:Set (Rn n))).indicator (fun y => exp (-(r*t))) := by
      ext y
      by_cases hh : y ∈ t • (K:Set (Rn n))
      · rw [indicator_of_mem hh]
        change C.indicator _ _ = _
        rw [indicator_of_mem ((ha y).mpr hh), pair_inner, inner_zero_left, add_zero, mul_comm]
      · exact (indicator_of_notMem (mt (ha y).mp hh) _).trans ((indicator_of_notMem hh _).symm)
    change (∫ y, f (pair t y)) = _
    rw [indicator_of_mem (mem_Ioi.mpr h)]
    rw [he, integral_indicator (K.isCompact.smul _).isClosed.measurableSet, setIntegral_const,
      measureReal_def, addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    change |t ^ Module.finrank ℝ (Rn n)| * v * exp _ = g t
    rw [abs_of_pos (by positivity)]
    have heR : Module.finrank ℝ (Rn n) = n := by simp [Rn]
    rw [heR]; dsimp only [g]; ring
  have hR : (n : ℝ) + 1 > 0 := by positivity
  have J := Real.integral_rpow_mul_exp_neg_mul_Ioi hR hr
  have HH : r⁻¹ ^ ((n:ℝ)+1) = r⁻¹^(n+1) := by
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  rw [H, integral_congr_ae heq, integral_indicator measurableSet_Ioi]
  change (∫ t : ℝ in Ioi 0, t ^ n * exp (-(r*t)) * v) = _
  rw [integral_mul_const]
  simp only [add_sub_cancel_right, Real.rpow_natCast, one_div,
    Real.Gamma_nat_eq_factorial, HH] at J
  rw [J]

/-- Shear of cone coordinates for translations. -/
def shear (z : Rn n) : (LiftSpace n) ≃ₗ[ℝ] LiftSpace n where
  toFun p := pair (hgt p) (horiz p + hgt p • z)
  invFun p := pair (hgt p) (horiz p - hgt p • z)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by
    simp only [hgt_add, horiz_add, add_smul, add_add_add_comm (horiz p) (horiz q)]
    rfl
  map_smul' a p := by
    simp only [hgt_smul, horiz_smul, smul_pair, smul_add, smul_smul, RingHom.id_apply]

theorem shear_off (K : Body n) (z : Rn n) :
    K.cone = pushCone (shear z) (K.off z).cone := by
  ext p
  rw [mem_pushCone]
  change p ∈ K.cone ↔ pair _ _ ∈ (K.off z).cone
  conv_lhs => rw [← hgt_horiz_pair p]
  rw [pair_mem_cone, pair_mem_cone]
  apply and_congr_right; intro ht
  constructor
  · rintro ⟨x,hx,he⟩
    refine ⟨x-z,?_,?_⟩
    · simpa [sub_eq_add_neg, add_left_comm] using hx
    · rw [smul_sub,he]
  · rintro ⟨x,hx,he⟩
    refine ⟨z+x, hx,?_⟩
    rw [smul_add,add_comm]
    exact (sub_eq_iff_eq_add).mp he

theorem cone_volume (K : Body n) (z : Rn n) (hz : z ∈ interior (K:Set (Rn n)))
    (r : ℝ) (hr : 0 < r) :
    chi K.cone (pair 1 0) * chi (posDual K.cone) (pair r (r • z))
    = r⁻¹ ^ (n+1) * (n.factorial:ℝ)^2 * ((volume (K : Set (Rn n))).toReal *
      (volume (polarAt K z)).toReal) := by
  let K' := K.off z
  have hk' := off_interior hz
  have hsc : contra (shear z) (pair 1 0) = pair 1 0 := by
    apply ext_inner_left ℝ
    intro p
    obtain ⟨p,rfl⟩ := (shear z).surjective p
    rw [pair_contra]
    change ⟪p,pair 1 0⟫ = ⟪pair _ _,pair 1 0⟫
    conv_lhs => rw [← hgt_horiz_pair p]
    rw [pair_inner,pair_inner,inner_zero_right,inner_zero_right]
  have hsu : shear z (pair r 0) = pair r (r • z) := by
    change pair r (0 + r • z) = _
    rw [zero_add]
  have hv : volume (K' : Set (Rn n)) = volume (K : Set (Rn n)) :=
    measure_preimage_add _ _ _
  rw [shear_off K z, ← hsu, ← hsc, chi_transform, ← cone_polarSlice (K.off z) hk',
    chi_axis _ 1 zero_lt_one, chi_axis _ _ hr, polarSlice_volume,
    polar_off K z]
  change _ * _ * (volume (K': Set (Rn n))).toReal * _ = _
  rw [hv]; simp only [inv_one,one_pow]; ring

end Body
end GeneralMahler

end

end OAI
