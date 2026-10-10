import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions
import OAI.Geometry.CylinderCovering.Radial.Assembly

namespace OAI

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
noncomputable section

namespace CylinderCovering.RadialPairedSweep

lemma point_inner (x y z u v w : ℝ) :
    inner ℝ (point x y z) (point u v w) = x*u + y*v + z*w := by
  simp [point, TriangularCovering.inner_coord]

lemma point_norm_sq (x y z : ℝ) : ‖point x y z‖ ^ 2 = x^2+y^2+z^2 := by
  rw [← real_inner_self_eq_norm_sq, point_inner]
  ring

lemma point_x_unit : ‖point 1 0 0‖ = 1 := by
  have := point_norm_sq 1 0 0
  nlinarith [norm_nonneg (point 1 0 0)]

lemma point_y_unit : ‖point 0 1 0‖ = 1 := by
  have := point_norm_sq 0 1 0
  nlinarith [norm_nonneg (point 0 1 0)]

lemma upper_independent {h : ℝ} (hh : 0 < h) :
    LinearIndependent ℝ ![point 0 0 (-h), point 0 1 0] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h₁ := congrArg (fun v : Space => v 1) hst
  have h₂ := congrArg (fun v : Space => v 2) hst
  simp [point] at h₁ h₂
  constructor
  · exact h₂.resolve_right (ne_of_gt hh)
  · exact h₁

lemma lower_independent {h : ℝ} (hh : 0 < h) :
    LinearIndependent ℝ ![point 0 0 h, point 1 0 0] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h₀ := congrArg (fun v : Space => v 0) hst
  have h₂ := congrArg (fun v : Space => v 2) hst
  simp [point] at h₀ h₂
  constructor
  · exact h₂.resolve_right (ne_of_gt hh)
  · exact h₀

lemma G_deriv (q : ℝ) : HasDerivAt RadialCaps.G q q := by
  unfold RadialCaps.G
  convert! (((hasDerivAt_id q).pow 2).const_add 1).div_const 2 using 1
  simp

private def upperW (h ε q : ℝ) : Space :=
  (-ε * RadialCaps.G q) • point 0 1 0 + (h * ε * q) • point 0 0 1

private def lowerW (h ε q : ℝ) : Space :=
  (ε * RadialCaps.G q) • point 1 0 0 + (h * ε * q) • point 0 0 1

lemma upperW_deriv (h ε q : ℝ) :
    HasDerivAt (upperW h ε) ((-ε) • (point 0 0 (-h) + q • point 0 1 0)) q := by
  have hd : HasDerivAt (fun y : ℝ => (-ε * RadialCaps.G y) • point 0 1 0)
      ((-ε*q) • point 0 1 0) q :=
    ((G_deriv q).const_mul (-ε)).smul_const (point 0 1 0)
  have he : HasDerivAt (fun y : ℝ => (h*ε*y) • point 0 0 1)
      ((h*ε) • point 0 0 1) q := by
    simpa only [mul_one, id_eq] using
      ((hasDerivAt_id q).const_mul (h*ε)).smul_const (point 0 0 1)
  have hder := hd.add he
  change HasDerivAt _ _ q at hder
  convert! hder using 1
  ext i
  fin_cases i <;> simp [point]
  ring

lemma lowerW_deriv (h ε q : ℝ) :
    HasDerivAt (lowerW h ε) (ε • (point 0 0 h + q • point 1 0 0)) q := by
  have hd : HasDerivAt (fun y : ℝ => (ε * RadialCaps.G y) • point 1 0 0)
      ((ε*q) • point 1 0 0) q :=
    ((G_deriv q).const_mul ε).smul_const (point 1 0 0)
  have he : HasDerivAt (fun y : ℝ => (h*ε*y) • point 0 0 1)
      ((h*ε) • point 0 0 1) q := by
    simpa only [mul_one, id_eq] using
      ((hasDerivAt_id q).const_mul (h*ε)).smul_const (point 0 0 1)
  have hder := hd.add he
  change HasDerivAt _ _ q at hder
  convert! hder using 1
  ext i
  fin_cases i <;> simp [point]
  ring

def upperData (h ε : ℝ) (hh : 0 < h) (R : ℝ → ℝ)
    (hR : ContinuousOn R (Icc (-1 : ℝ) 1))
    (hR0 : ∀ q ∈ Icc (-1 : ℝ) 1, 0 ≤ R q) : RadialSweep.Data where
  e := point 1 0 0
  a := point 0 0 (-h)
  b := point 0 1 0
  p₀ := point 0 0 h
  α := -1
  β := 1
  L := 2
  R := R
  lam := fun _ => -ε
  w := upperW h ε
  interval_nonempty := by norm_num
  length_pos := by norm_num
  normal_unit := point_x_unit
  a_perp := by simp [point_inner]
  b_perp := by simp [point_inner]
  origin_perp := by simp [point_inner]
  independent := upper_independent hh
  cap_continuous := hR
  cap_nonneg := hR0
  scalar_continuous := continuousOn_const
  velocity_continuous := by
    exact (continuous_iff_continuousAt.mpr (fun q => (upperW_deriv h ε q).continuousAt)).continuousOn
  velocity_perp := by
    intro q _
    simp [upperW, inner_add_right, inner_smul_right, point_inner]
  aligned := fun q _ => (upperW_deriv h ε q).hasDerivWithinAt

def lowerData (h ε : ℝ) (hh : 0 < h) (R : ℝ → ℝ)
    (hR : ContinuousOn R (Icc (-1 : ℝ) 1))
    (hR0 : ∀ q ∈ Icc (-1 : ℝ) 1, 0 ≤ R q) : RadialSweep.Data where
  e := point 0 1 0
  a := point 0 0 h
  b := point 1 0 0
  p₀ := point 0 0 (-h)
  α := -1
  β := 1
  L := 2
  R := R
  lam := fun _ => ε
  w := lowerW h ε
  interval_nonempty := by norm_num
  length_pos := by norm_num
  normal_unit := point_y_unit
  a_perp := by simp [point_inner]
  b_perp := by simp [point_inner]
  origin_perp := by simp [point_inner]
  independent := lower_independent hh
  cap_continuous := hR
  cap_nonneg := hR0
  scalar_continuous := continuousOn_const
  velocity_continuous := by
    exact (continuous_iff_continuousAt.mpr (fun q => (lowerW_deriv h ε q).continuousAt)).continuousOn
  velocity_perp := by
    intro q _
    simp [lowerW, inner_add_right, inner_smul_right, point_inner]
  aligned := fun q _ => (lowerW_deriv h ε q).hasDerivWithinAt

lemma upperW_eq (h ε q : ℝ) :
    upperW h ε q = point 0 (-ε * RadialCaps.G q) (h*ε*q) := by
  ext i
  fin_cases i <;> simp [upperW, point]

lemma lowerW_eq (h ε q : ℝ) :
    lowerW h ε q = point (ε * RadialCaps.G q) 0 (h*ε*q) := by
  ext i
  fin_cases i <;> simp [lowerW, point]

variable (h ε : ℝ) (hh : 0 < h) (R : ℝ → ℝ)
  (hR : ContinuousOn R (Icc (-1 : ℝ) 1))
  (hR0 : ∀ q ∈ Icc (-1 : ℝ) 1, 0 ≤ R q)

lemma upperData_sweep : RadialSweep.sweep (upperData h ε hh R hR hR0) = upperSweep h ε R := by
  ext z
  constructor
  · rintro ⟨q, hq, ρ, hρ, s, hs, hz⟩
    refine ⟨q, hq, ρ, hρ, s, hs, ?_⟩
    rw [hz]
    ext i
    fin_cases i <;> simp [upperData, upperW, point] <;> ring
  · rintro ⟨q, hq, ρ, hρ, s, hs, hz⟩
    refine ⟨q, hq, ρ, hρ, s, hs, ?_⟩
    rw [hz]
    ext i
    fin_cases i <;> simp [upperData, upperW, point] <;> ring

lemma lowerData_sweep : RadialSweep.sweep (lowerData h ε hh R hR hR0) = lowerSweep h ε R := by
  ext z
  constructor
  · rintro ⟨q, hq, ρ, hρ, s, hs, hz⟩
    refine ⟨q, hq, ρ, hρ, s, hs, ?_⟩
    rw [hz]
    ext i
    fin_cases i <;> simp [lowerData, lowerW, point] <;> ring
  · rintro ⟨q, hq, ρ, hρ, s, hs, hz⟩
    refine ⟨q, hq, ρ, hρ, s, hs, ?_⟩
    rw [hz]
    ext i
    fin_cases i <;> simp [lowerData, lowerW, point] <;> ring

lemma upperData_direction (q : ℝ) :
    RadialSweep.direction (upperData h ε hh R hR hR0) q = upperAxis h ε q := by
  have hv : point 1 0 0 + upperW h ε q = point 1 (-ε * RadialCaps.G q) (h*ε*q) := by
    ext i
    fin_cases i <;> simp [upperW, point]
  change ‖point 1 0 0 + upperW h ε q‖⁻¹ • (point 1 0 0 + upperW h ε q) = _
  rw [hv]
  rfl

lemma lowerData_direction (q : ℝ) :
    RadialSweep.direction (lowerData h ε hh R hR hR0) q = lowerAxis h ε q := by
  have hv : point 0 1 0 + lowerW h ε q = point (ε * RadialCaps.G q) 1 (h*ε*q) := by
    ext i
    fin_cases i <;> simp [lowerW, point]
  change ‖point 0 1 0 + lowerW h ε q‖⁻¹ • (point 0 1 0 + lowerW h ε q) = _
  rw [hv]
  rfl

lemma upperData_kappa : RadialSweep.kappa (upperData h ε hh R hR hR0) = h := by
  change Real.sqrt (inner ℝ (point 0 0 (-h)) (point 0 0 (-h)) *
    inner ℝ (point 0 1 0) (point 0 1 0) - (inner ℝ (point 0 0 (-h)) (point 0 1 0))^2) = h
  simp only [point_inner]
  convert Real.sqrt_sq hh.le using 1
  congr 1
  ring

lemma lowerData_kappa : RadialSweep.kappa (lowerData h ε hh R hR hR0) = h := by
  change Real.sqrt (inner ℝ (point 0 0 h) (point 0 0 h) *
    inner ℝ (point 1 0 0) (point 1 0 0) - (inner ℝ (point 0 0 h) (point 1 0 0))^2) = h
  simp only [point_inner]
  convert Real.sqrt_sq hh.le using 1
  congr 1
  ring

lemma upperW_norm_sq (q : ℝ) : ‖upperW h ε q‖^2 =
    ε^2 * (RadialCaps.G q^2 + h^2*q^2) := by
  rw [upperW_eq, point_norm_sq]
  ring

lemma lowerW_norm_sq (q : ℝ) : ‖lowerW h ε q‖^2 =
    ε^2 * (RadialCaps.G q^2 + h^2*q^2) := by
  rw [lowerW_eq, point_norm_sq]
  ring

lemma upperData_weightedArea :
    RadialSweep.weightedArea (upperData h ε hh R hR hR0) = h * physicalCost h ε R := by
  unfold RadialSweep.weightedArea
  rw [upperData_kappa]
  congr 1
  apply intervalIntegral.integral_congr
  intro q _
  change R q^2 / (2 * Real.sqrt (1 + ‖upperW h ε q‖^2)) = _
  rw [upperW_norm_sq]

lemma lowerData_weightedArea :
    RadialSweep.weightedArea (lowerData h ε hh R hR hR0) = h * physicalCost h ε R := by
  unfold RadialSweep.weightedArea
  rw [lowerData_kappa]
  congr 1
  apply intervalIntegral.integral_congr
  intro q _
  change R q^2 / (2 * Real.sqrt (1 + ‖lowerW h ε q‖^2)) = _
  rw [lowerW_norm_sq]

theorem paired_radial_sweeps : PairedStatement := by
  intro h ε hh R hR hR0 tagU tagL htagU htagL
  obtain ⟨U, hU, hUlim⟩ := RadialSweep.aligned_radial_sweep
    (upperData h ε hh R hR hR0) tagU htagU
  obtain ⟨L, hL, hLlim⟩ := RadialSweep.aligned_radial_sweep
    (lowerData h ε hh R hR hR0) tagL htagL
  refine ⟨U, L, ?_, ?_⟩
  · intro N hN
    obtain ⟨hUa, hUc⟩ := hU N hN
    obtain ⟨hLa, hLc⟩ := hL N hN
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact ⟨(hUa i).1.trans (upperData_direction h ε hh R hR hR0 _),
        (hLa i).1.trans (lowerData_direction h ε hh R hR hR0 _)⟩
    · simpa only [upperData_sweep] using hUc
    · simpa only [lowerData_sweep] using hLc
  · have hlim := hUlim.add hLlim
    rw [upperData_weightedArea, lowerData_weightedArea] at hlim
    convert hlim using 1
    first | rfl | ring_nf

lemma physicalCost_sqrt_two : physicalCost (Real.sqrt 2) ε R = RadialCaps.Q R ε := by
  unfold physicalCost RadialCaps.Q
  apply intervalIntegral.integral_congr
  intro q _
  simp [RadialCaps.D0, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

include hh hR hR0 in

theorem exists_pair_below {K : Set Space} {B : ℝ}
    (hcover : K ⊆ upperSweep h ε R ∪ lowerSweep h ε R)
    (hbudget : 2 * h * physicalCost h ε R < B)
    (tagU tagL : (N : ℕ) → Fin N → ℝ)
    (htagU : ∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N))
    (htagL : ∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) :
    ∃ N : ℕ, 0 < N ∧ ∃ U L : Fin N → TriangularCovering.TriCylinder,
      (∀ i, (U i).axis = upperAxis h ε (tagU N i) ∧
        (L i).axis = lowerAxis h ε (tagL N i)) ∧
      (∀ z ∈ K, (∃ i, z ∈ (U i).carrier) ∨ (∃ i, z ∈ (L i).carrier)) ∧
      TriangularCovering.totalArea U + TriangularCovering.totalArea L < B := by
  obtain ⟨U, L, hUL, hlim⟩ := paired_radial_sweeps h ε hh R hR hR0 tagU tagL htagU htagL
  obtain ⟨N, hN, hcost⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hlim.eventually_lt_const hbudget)).exists
  obtain ⟨haxis, hupper, hlower⟩ := hUL N hN
  refine ⟨N, hN, U N, L N, haxis, ?_, hcost⟩
  intro z hz
  rcases hcover hz with hu | hl
  · exact Or.inl (hupper z hu)
  · exact Or.inr (hlower z hl)

end CylinderCovering.RadialPairedSweep

end

end OAI
