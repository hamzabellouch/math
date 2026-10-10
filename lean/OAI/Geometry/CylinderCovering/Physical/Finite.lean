import OAI.Geometry.CylinderCovering.Physical.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Radial.PairedSweep
import OAI.Geometry.CylinderCovering.Radial.ActualEndpoint

namespace OAI

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
noncomputable section

namespace RadialPhysical.PhysicalFiniteProof
open CylinderCovering

private abbrev vec := RadialPairedSweep.point

private def upperW (b eta s : ℝ) : Space :=
  (-eta / 2 * (s^2+b^2)) • vec 0 1 0 +
    (height b * eta * s) • vec 0 0 1

private def lowerW (b eta s : ℝ) : Space :=
  (eta / 2 * (s^2+b^2)) • vec 1 0 0 +
    (height b * eta * s) • vec 0 0 1

private lemma upperW_deriv (b eta s : ℝ) :
    HasDerivAt (upperW b eta)
      ((-eta) • (vec 0 0 (-height b) + s • vec 0 1 0)) s := by
  have hd := ((((hasDerivAt_id s).pow 2).add_const (b^2)).const_mul (-eta/2)).smul_const (vec 0 1 0)
  have he := ((hasDerivAt_id s).const_mul (height b * eta)).smul_const (vec 0 0 1)
  have hder := hd.add he
  change HasDerivAt _ _ s at hder
  convert! hder using 1
  ext i
  fin_cases i <;> simp [vec, RadialPairedSweep.point] <;> ring

private lemma lowerW_deriv (b eta s : ℝ) :
    HasDerivAt (lowerW b eta)
      (eta • (vec 0 0 (height b) + s • vec 1 0 0)) s := by
  have hd := ((((hasDerivAt_id s).pow 2).add_const (b^2)).const_mul (eta/2)).smul_const (vec 1 0 0)
  have he := ((hasDerivAt_id s).const_mul (height b * eta)).smul_const (vec 0 0 1)
  have hder := hd.add he
  change HasDerivAt _ _ s at hder
  convert! hder using 1
  ext i
  fin_cases i <;> simp [vec, RadialPairedSweep.point] <;> ring

private lemma height_pos {b : ℝ} (hb : 0 < b) : 0 < height b :=
  mul_pos (Real.sqrt_pos.mpr (by norm_num)) hb

private lemma axialBound_pos (centered : Bool) {b : ℝ} (hb : 0 < b) :
    0 < axialBound centered b := by
  cases centered <;> simp [axialBound] <;> positivity

def upperData (centered : Bool) (b eta : ℝ) (hb : 0 < b) (T : ℝ → ℝ)
    (hT : ContinuousOn T (Icc (-b) b))
    (hT0 : ∀ s ∈ Icc (-b) b, 0 ≤ T s) : RadialSweep.Data where
  e := vec 1 0 0
  a := vec 0 0 (-height b)
  b := vec 0 1 0
  p₀ := vec 0 0 (height b)
  α := -b
  β := b
  L := axialBound centered b
  R := T
  lam := fun _ => -eta
  w := upperW b eta
  interval_nonempty := by linarith
  length_pos := axialBound_pos centered hb
  normal_unit := RadialPairedSweep.point_x_unit
  a_perp := by simp [vec, RadialPairedSweep.point_inner]
  b_perp := by simp [vec, RadialPairedSweep.point_inner]
  origin_perp := by simp [vec, RadialPairedSweep.point_inner]
  independent := RadialPairedSweep.upper_independent (height_pos hb)
  cap_continuous := hT
  cap_nonneg := hT0
  scalar_continuous := continuousOn_const
  velocity_continuous :=
    (continuous_iff_continuousAt.mpr (fun s => (upperW_deriv b eta s).continuousAt)).continuousOn
  velocity_perp := by
    intro s _
    simp [upperW, inner_add_right, inner_smul_right, vec, RadialPairedSweep.point_inner]
  aligned := fun s _ => (upperW_deriv b eta s).hasDerivWithinAt

def lowerData (centered : Bool) (b eta : ℝ) (hb : 0 < b) (T : ℝ → ℝ)
    (hT : ContinuousOn T (Icc (-b) b))
    (hT0 : ∀ s ∈ Icc (-b) b, 0 ≤ T s) : RadialSweep.Data where
  e := vec 0 1 0
  a := vec 0 0 (height b)
  b := vec 1 0 0
  p₀ := vec 0 0 (height b * (if centered then -1 else 0))
  α := -b
  β := b
  L := axialBound centered b
  R := T
  lam := fun _ => eta
  w := lowerW b eta
  interval_nonempty := by linarith
  length_pos := axialBound_pos centered hb
  normal_unit := RadialPairedSweep.point_y_unit
  a_perp := by simp [vec, RadialPairedSweep.point_inner]
  b_perp := by simp [vec, RadialPairedSweep.point_inner]
  origin_perp := by simp [vec, RadialPairedSweep.point_inner]
  independent := RadialPairedSweep.lower_independent (height_pos hb)
  cap_continuous := hT
  cap_nonneg := hT0
  scalar_continuous := continuousOn_const
  velocity_continuous :=
    (continuous_iff_continuousAt.mpr (fun s => (lowerW_deriv b eta s).continuousAt)).continuousOn
  velocity_perp := by
    intro s _
    simp [lowerW, inner_add_right, inner_smul_right, vec, RadialPairedSweep.point_inner]
  aligned := fun s _ => (lowerW_deriv b eta s).hasDerivWithinAt

variable (centered : Bool) (b eta : ℝ) (hb : 0 < b) (T : ℝ → ℝ)
  (hT : ContinuousOn T (Icc (-b) b))
  (hT0 : ∀ s ∈ Icc (-b) b, 0 ≤ T s)

lemma upperData_point (s rho x : ℝ) :
    (upperData centered b eta hb T hT hT0).p₀ +
      rho • ((upperData centered b eta hb T hT hT0).a +
        s • (upperData centered b eta hb T hT hT0).b) +
      x • ((upperData centered b eta hb T hT hT0).e +
        (upperData centered b eta hb T hT hT0).w s) =
      upperPoint b eta rho s x := by
  ext i
  fin_cases i <;> simp [upperData, upperW, upperPoint, point, vec,
    RadialPairedSweep.point] <;> ring

lemma lowerData_point (s rho y : ℝ) :
    (lowerData centered b eta hb T hT hT0).p₀ +
      rho • ((lowerData centered b eta hb T hT hT0).a +
        s • (lowerData centered b eta hb T hT hT0).b) +
      y • ((lowerData centered b eta hb T hT hT0).e +
        (lowerData centered b eta hb T hT hT0).w s) =
      lowerPoint centered b eta rho s y := by
  cases centered <;> ext i <;>
    fin_cases i <;> simp [lowerData, lowerW, lowerPoint, point, vec,
      RadialPairedSweep.point] <;> ring

lemma upperData_sweep : RadialSweep.sweep (upperData centered b eta hb T hT hT0) =
    upperSweepOn centered b eta T (Icc (-b) b) := by
  ext z
  simp only [RadialSweep.sweep, upperSweepOn, mem_ofPred_eq, upperData_point]
  rfl

lemma lowerData_sweep : RadialSweep.sweep (lowerData centered b eta hb T hT hT0) =
    lowerSweepOn centered b eta T (Icc (-b) b) := by
  ext z
  simp only [RadialSweep.sweep, lowerSweepOn, mem_ofPred_eq, lowerData_point]
  rfl

lemma upperData_localSweep (N : ℕ) (i : Fin N) :
    RadialSweep.localSweep (upperData centered b eta hb T hT hT0) N i =
      upperSweepOn centered b eta T (RadialRiemann.cell (-b) b N i) := by
  ext z
  simp only [RadialSweep.localSweep, upperSweepOn, mem_ofPred_eq, upperData_point]
  rfl

lemma lowerData_localSweep (N : ℕ) (i : Fin N) :
    RadialSweep.localSweep (lowerData centered b eta hb T hT hT0) N i =
      lowerSweepOn centered b eta T (RadialRiemann.cell (-b) b N i) := by
  ext z
  simp only [RadialSweep.localSweep, lowerSweepOn, mem_ofPred_eq, lowerData_point]
  rfl

lemma upperData_direction (s : ℝ) :
    RadialSweep.direction (upperData centered b eta hb T hT hT0) s =
      upperPhysicalAxis b eta s := by
  have hv : vec 1 0 0 + upperW b eta s = point b 1 (-eta*(s^2+b^2)/2) (eta*s) := by
    ext i
    fin_cases i <;> simp [upperW, point, vec, RadialPairedSweep.point] <;> ring
  change ‖vec 1 0 0 + upperW b eta s‖⁻¹ • (vec 1 0 0 + upperW b eta s) = _
  rw [hv]
  rfl

lemma lowerData_direction (s : ℝ) :
    RadialSweep.direction (lowerData centered b eta hb T hT hT0) s =
      lowerPhysicalAxis b eta s := by
  have hv : vec 0 1 0 + lowerW b eta s = point b (eta*(s^2+b^2)/2) 1 (eta*s) := by
    ext i
    fin_cases i <;> simp [lowerW, point, vec, RadialPairedSweep.point] <;> ring
  change ‖vec 0 1 0 + lowerW b eta s‖⁻¹ • (vec 0 1 0 + lowerW b eta s) = _
  rw [hv]
  rfl

lemma upperData_actualBase (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    RadialSweep.actualBase (upperData centered b eta hb T hT hT0) N tag i =
      upperPhysicalBase centered b eta T N tag i := by
  unfold RadialSweep.actualBase upperPhysicalBase
  rw [upperData_direction, upperData_localSweep]

lemma lowerData_actualBase (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    RadialSweep.actualBase (lowerData centered b eta hb T hT hT0) N tag i =
      lowerPhysicalBase centered b eta T N tag i := by
  unfold RadialSweep.actualBase lowerPhysicalBase
  rw [lowerData_direction, lowerData_localSweep]

lemma upperData_kappa :
    RadialSweep.kappa (upperData centered b eta hb T hT hT0) = height b := by
  change Real.sqrt (inner ℝ (vec 0 0 (-height b)) (vec 0 0 (-height b)) *
    inner ℝ (vec 0 1 0) (vec 0 1 0) -
      (inner ℝ (vec 0 0 (-height b)) (vec 0 1 0))^2) = height b
  simp only [vec, RadialPairedSweep.point_inner]
  convert Real.sqrt_sq (height_pos hb).le using 1
  congr 1
  ring

lemma lowerData_kappa :
    RadialSweep.kappa (lowerData centered b eta hb T hT hT0) = height b := by
  change Real.sqrt (inner ℝ (vec 0 0 (height b)) (vec 0 0 (height b)) *
    inner ℝ (vec 1 0 0) (vec 1 0 0) -
      (inner ℝ (vec 0 0 (height b)) (vec 1 0 0))^2) = height b
  simp only [vec, RadialPairedSweep.point_inner]
  convert Real.sqrt_sq (height_pos hb).le using 1
  congr 1
  ring

private lemma upperW_norm_sq (b eta s : ℝ) :
    ‖upperW b eta s‖^2 = eta^2 * ((s^2+b^2)^2/4 + height b^2*s^2) := by
  have hv : upperW b eta s = vec 0 (-eta/2*(s^2+b^2)) (height b*eta*s) := by
    ext i
    fin_cases i <;> simp [upperW, vec, RadialPairedSweep.point]
  rw [hv, RadialPairedSweep.point_norm_sq]
  ring

private lemma lowerW_norm_sq (b eta s : ℝ) :
    ‖lowerW b eta s‖^2 = eta^2 * ((s^2+b^2)^2/4 + height b^2*s^2) := by
  have hv : lowerW b eta s = vec (eta/2*(s^2+b^2)) 0 (height b*eta*s) := by
    ext i
    fin_cases i <;> simp [lowerW, vec, RadialPairedSweep.point]
  rw [hv, RadialPairedSweep.point_norm_sq]
  ring

lemma upperData_weightedArea :
    RadialSweep.weightedArea (upperData centered b eta hb T hT hT0) =
      scaledCost b eta T / 2 := by
  unfold RadialSweep.weightedArea
  rw [upperData_kappa]
  change height b * (∫ s in -b..b,
    T s^2 / (2*Real.sqrt (1+‖upperW b eta s‖^2))) = _
  calc
    _ = height b * (∫ s in -b..b, scaledDensity b eta T s / 2) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      change T s^2 / (2 * Real.sqrt (1 + ‖upperW b eta s‖^2)) = scaledDensity b eta T s / 2
      rw [upperW_norm_sq]
      unfold scaledDensity
      ring
    _ = scaledCost b eta T / 2 := by
      rw [intervalIntegral.integral_div]
      unfold scaledCost
      ring

lemma lowerData_weightedArea :
    RadialSweep.weightedArea (lowerData centered b eta hb T hT hT0) =
      scaledCost b eta T / 2 := by
  unfold RadialSweep.weightedArea
  rw [lowerData_kappa]
  change height b * (∫ s in -b..b,
    T s^2 / (2*Real.sqrt (1+‖lowerW b eta s‖^2))) = _
  calc
    _ = height b * (∫ s in -b..b, scaledDensity b eta T s / 2) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      change T s^2 / (2 * Real.sqrt (1 + ‖lowerW b eta s‖^2)) = scaledDensity b eta T s / 2
      rw [lowerW_norm_sq]
      unfold scaledDensity
      ring
    _ = scaledCost b eta T / 2 := by
      rw [intervalIntegral.integral_div]
      unfold scaledCost
      ring

lemma physicalActualCost_eq (N : ℕ) (tagU tagL : Fin N → ℝ) :
    physicalActualCost centered b eta T N tagU tagL =
      RadialSweep.actualCost (upperData centered b eta hb T hT hT0) N tagU +
      RadialSweep.actualCost (lowerData centered b eta hb T hT hT0) N tagL := by
  simp only [physicalActualCost, RadialSweep.actualCost,
    upperData_actualBase, lowerData_actualBase]

end RadialPhysical.PhysicalFiniteProof

namespace RadialPhysical
open CylinderCovering PhysicalFiniteProof

theorem physical_finite : PhysicalFiniteStatement := by
  intro centered b eta hb T hT hT0 tagU tagL htagU htagL
  obtain ⟨U, hU, hUlim⟩ := RadialSweep.aligned_radial_sweep
    (upperData centered b eta hb T hT hT0) tagU htagU
  obtain ⟨L, hL, hLlim⟩ := RadialSweep.aligned_radial_sweep
    (lowerData centered b eta hb T hT hT0) tagL htagL
  obtain ⟨hAU, hAUb, _hAUlim⟩ := RadialSweep.actual_radial_sweep
    (upperData centered b eta hb T hT hT0) tagU htagU
  obtain ⟨hAL, hALb, _hALlim⟩ := RadialSweep.actual_radial_sweep
    (lowerData centered b eta hb T hT hT0) tagL htagL
  have hbound : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop,
      physicalActualCost centered b eta T N (tagU N) (tagL N) ≤
        scaledCost b eta T + δ := by
    intro δ hδ
    filter_upwards [hAUb (δ/2) (by linarith), hALb (δ/2) (by linarith)] with N hUN hLN
    rw [physicalActualCost_eq centered b eta hb T hT hT0]
    rw [upperData_weightedArea] at hUN
    rw [lowerData_weightedArea] at hLN
    linarith
  refine ⟨U, L, ?_, ?_, hbound, ?_⟩
  · intro N hN
    obtain ⟨hUa, hUc⟩ := hU N hN
    obtain ⟨hLa, hLc⟩ := hL N hN
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hUi := (hAU N hN).1 i
      have hLi := (hAL N hN).1 i
      simp only [upperData_direction, upperData_actualBase] at hUi
      simp only [lowerData_direction, lowerData_actualBase] at hLi
      refine ⟨(hUa i).1.trans (upperData_direction centered b eta hb T hT hT0 _),
        (hLa i).1.trans (lowerData_direction centered b eta hb T hT hT0 _), ?_, ?_,
        ⟨hUi.1, hUi.2.1, hUi.2.2.1, hUi.2.2.2.1, hUi.2.2.2.2.1⟩,
        ⟨hLi.1, hLi.2.1, hLi.2.2.1, hLi.2.2.2.1, hLi.2.2.2.2.1⟩⟩
      · rw [(hUa i).2.1]
        exact hUi.2.2.2.2.2
      · rw [(hLa i).2.1]
        exact hLi.2.2.2.2.2
    · have hAc := (hAU N hN).2
      simp only [upperData_sweep] at hUc
      simp only [upperData_sweep, upperData_direction, upperData_actualBase] at hAc
      intro z hz
      exact ⟨hUc z hz, hAc z hz⟩
    · have hAc := (hAL N hN).2
      simp only [lowerData_sweep] at hLc
      simp only [lowerData_sweep, lowerData_direction, lowerData_actualBase] at hAc
      intro z hz
      exact ⟨hLc z hz, hAc z hz⟩
  · have hlim := hUlim.add hLlim
    rw [upperData_weightedArea, lowerData_weightedArea] at hlim
    simpa only [add_halves] using hlim
  · apply le_of_forall_pos_le_add
    intro δ hδ
    apply _root_.OAI.RadialActualSweep.limsup_le_of_nonneg_of_le_tendsto
      (bound := fun _ => scaledCost b eta T + δ)
    · intro N
      exact add_nonneg (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
        (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
    · exact hbound δ hδ
    · exact tendsto_const_nhds

end RadialPhysical

end

end OAI
