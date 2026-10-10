import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions
import OAI.Geometry.RuledCovering.Main
import OAI.Geometry.CylinderCovering.Rational.Field

namespace OAI

noncomputable section
open Set MeasureTheory

namespace SlopeRational

lemma physicalScale_pos : 0 < physicalScale := by
  unfold physicalScale
  positivity

def reflectionIsometry : Space ≃ₗᵢ[ℝ] Space where
  toFun := reflection
  invFun := reflection
  left_inv z := by ext i; fin_cases i <;> simp [reflection, RuledApproximation.vec3]
  right_inv z := by ext i; fin_cases i <;> simp [reflection, RuledApproximation.vec3]
  map_add' z w := by ext i; fin_cases i <;> simp [reflection, RuledApproximation.vec3]; ring
  map_smul' c z := by ext i; fin_cases i <;> simp [reflection, RuledApproximation.vec3]
  norm_map' z := by
    change ‖reflection z‖ = ‖z‖
    have hsq : ‖reflection z‖ ^ 2 = ‖z‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, reflection, RuledApproximation.vec3,
        Fin.sum_univ_succ]
      ring
    nlinarith [norm_nonneg (reflection z), norm_nonneg z]

lemma lowerSweep_mem_iff (d ε q : ℝ) (z : Space) :
    z ∈ lowerSweep d ε q ↔
      ∃ p ∈ labelDomain d ε q, ∃ x : ℝ, |x| ≤ 1 / 2 ∧
        z = RuledApproximation.vec3 x
          (p 0 + ε * x * a d (p 0) (p 1))
          (physicalScale * (p 1 + ε * x * b d (p 0) (p 1))) := by
  constructor
  · rintro ⟨p, hp, x, hx, rfl⟩
    refine ⟨p, hp, x, hx, ?_⟩
    ext i
    fin_cases i
    · rfl
    · change p 0 + x * (ε * a d (p 0) (p 1)) = p 0 + ε * x * a d (p 0) (p 1)
      ring
    · change physicalScale * (p 1 + x * (ε * b d (p 0) (p 1))) =
        physicalScale * (p 1 + ε * x * b d (p 0) (p 1))
      ring
  · rintro ⟨p, hp, x, hx, rfl⟩
    refine ⟨p, hp, x, hx, ?_⟩
    ext i
    fin_cases i
    · rfl
    · change p 0 + ε * x * a d (p 0) (p 1) = p 0 + x * (ε * a d (p 0) (p 1))
      ring
    · change physicalScale * (p 1 + ε * x * b d (p 0) (p 1)) =
        physicalScale * (p 1 + x * (ε * b d (p 0) (p 1)))
      ring

lemma upperSweep_mem_iff (d ε q : ℝ) (z : Space) :
    z ∈ upperSweep d ε q ↔
      ∃ p ∈ labelDomain d ε q, ∃ y : ℝ, |y| ≤ 1 / 2 ∧
        z = RuledApproximation.vec3
          (p 0 - ε * y * a d (p 0) (p 1)) y
          (-physicalScale * (p 1 - ε * y * b d (p 0) (p 1))) := by
  constructor
  · rintro ⟨w, ⟨p, hp, y, hy, rfl⟩, rfl⟩
    refine ⟨p, hp, y, hy, ?_⟩
    ext i
    fin_cases i
    · change p 0 + y * (-ε * a d (p 0) (p 1)) = p 0 - ε * y * a d (p 0) (p 1)
      ring
    · rfl
    · change -(physicalScale * (p 1 + y * (-ε * b d (p 0) (p 1)))) =
        -physicalScale * (p 1 - ε * y * b d (p 0) (p 1))
      ring
  · rintro ⟨p, hp, y, hy, rfl⟩
    refine ⟨RuledApproximation.vec3 y
      (p 0 + y * (-ε • field d p) 0)
      (physicalScale * (p 1 + y * (-ε • field d p) 1)), ⟨p, hp, y, hy, rfl⟩, ?_⟩
    ext i
    fin_cases i
    · change p 0 + y * (-ε * a d (p 0) (p 1)) = p 0 - ε * y * a d (p 0) (p 1)
      ring
    · rfl
    · change -(physicalScale * (p 1 + y * (-ε * b d (p 0) (p 1)))) =
        -physicalScale * (p 1 - ε * y * b d (p 0) (p 1))
      ring

theorem finite_sweeps_of_regular
    {d ε q : ℝ}
    (hD : IsCompact (labelDomain d ε q))
    (hplus : RuledApproximation.SmoothNear 1 (labelDomain d ε q)
      (fun p => ε • field d p))
    (hminus : RuledApproximation.SmoothNear 1 (labelDomain d ε q)
      (fun p => -ε • field d p))
    (hspecPlus : ∀ p ∈ labelDomain d ε q,
      RuledApproximation.HyperbolicAt (1 / 2) (fun p => ε • field d p) p)
    (hspecMinus : ∀ p ∈ labelDomain d ε q,
      RuledApproximation.HyperbolicAt (1 / 2) (fun p => -ε • field d p) p)
    {e : ℝ} (he : 0 < e) :
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.parallelogram
      (lowerSweep d ε q ∪ upperSweep d ε q) (2 * weightedCost d ε q + e) := by
  have hp := RuledApproximation.physical_hyperbolic_cover physicalScale_pos
    (by norm_num : (0 : ℝ) < 1 / 2) hD hplus hspecPlus (half_pos he)
  have hm := RuledApproximation.physicalHyperbolic physicalScale (1 / 2)
    (labelDomain d ε q) (fun p => -ε • field d p) physicalScale_pos
    (by norm_num) hD hminus hspecMinus (e / 2) (half_pos he)
    reflectionIsometry.toIsometryEquiv
  have hweight (p : Plane) :
      RuledApproximation.physicalWeight physicalScale (-ε • field d p) =
        RuledApproximation.physicalWeight physicalScale (ε • field d p) := by
    rw [neg_smul, RuledApproximation.physicalWeight_neg]
  simp_rw [hweight] at hm
  change RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.parallelogram
    (lowerSweep d ε q) (weightedCost d ε q + e / 2) at hp
  change RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.parallelogram
    (upperSweep d ε q) (weightedCost d ε q + e / 2) at hm
  convert hp.union hm using 1
  ring

lemma spectrum_small_on_wedge {d r c : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hc : c ≠ 0) (hcd : |c| < 8 * d) :
    0 < (1 / 2 : ℝ) * (|c| * (d / (4 * (r + d) ^ 2))) ∧
      (1 / 2 : ℝ) * (|c| * (d / (4 * (r + d) ^ 2))) < 1 := by
  have hrd : 0 < r + d := by linarith
  have hden : 0 < 4 * (r + d) ^ 2 := by positivity
  constructor
  · exact mul_pos (by norm_num) (mul_pos (abs_pos.mpr hc) (div_pos hd hden))
  · have hmul : |c| * d < 8 * d ^ 2 := by nlinarith
    have hsq : d ^ 2 ≤ (r + d) ^ 2 := by nlinarith
    have heq : (1 / 2 : ℝ) * (|c| * (d / (4 * (r + d) ^ 2))) =
        |c| * d / (8 * (r + d) ^ 2) := by
      field_simp
      ring
    rw [heq]
    apply (div_lt_one (by positivity : 0 < 8 * (r + d) ^ 2)).2
    nlinarith

lemma scaled_hyperbolic_of_spectrum
    {V : Plane → Plane} {p : Plane} {c lam : ℝ}
    (hdiff : DifferentiableAt ℝ V p) (hc : c ≠ 0)
    (hlam : 0 < lam) (hsmall : (1 / 2 : ℝ) * (|c| * lam) < 1)
    (hplus : Module.End.HasEigenvalue (fderiv ℝ V p).toLinearMap lam)
    (hminus : Module.End.HasEigenvalue (fderiv ℝ V p).toLinearMap (-lam)) :
    RuledApproximation.HyperbolicAt (1 / 2) (fun z => c • V z) p := by
  rw [RuledApproximation.HyperbolicAt, fderiv_fun_const_smul hdiff]
  refine ⟨|c| * lam, mul_pos (by norm_num) (mul_pos (abs_pos.mpr hc) hlam),
    hsmall, ?_, ?_⟩
  · by_cases hcp : 0 ≤ c
    · simpa [abs_of_nonneg hcp] using RuledApproximation.eigenvalue_smul _ hplus c
    · have hcn : c < 0 := lt_of_not_ge hcp
      simpa [abs_of_neg hcn] using RuledApproximation.eigenvalue_smul _ hminus c
  · by_cases hcp : 0 ≤ c
    · simpa [abs_of_nonneg hcp] using RuledApproximation.eigenvalue_smul _ hminus c
    · have hcn : c < 0 := lt_of_not_ge hcp
      simpa [abs_of_neg hcn] using RuledApproximation.eigenvalue_smul _ hplus c

lemma smoothNear_const_smul {D : Set Plane} {V : Plane → Plane}
    (hV : RuledApproximation.SmoothNear 1 D V) (c : ℝ) :
    RuledApproximation.SmoothNear 1 D (fun p => c • V p) := by
  obtain ⟨U, hU, hDU, hreg⟩ := hV
  exact ⟨U, hU, hDU, hreg.const_smul c⟩

theorem rational_hyperbolic {d c ε q : ℝ} (hd : 0 < d) (hc : c ≠ 0)
    (hcd : |c| < 8 * d) {p : Plane} (hp : p ∈ labelDomain d ε q) :
    RuledApproximation.HyperbolicAt (1 / 2) (fun z => c • field d z) p := by
  have hden := (denominator_pos_of_mem_wedge hd hp.1).ne'
  have heig := field_eigenvalues d hden
  have hl := (eigenvalue_bound_on_wedge hd hp.1).1
  have hs := (spectrum_small_on_wedge hd (radius_nonneg_of_mem_wedge hp.1) hc hcd).2
  exact scaled_hyperbolic_of_spectrum
    ((field_contDiffAt d hden).differentiableAt (by norm_num)) hc hl hs heig.1 heig.2

theorem finite_sweeps {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (hsmall : ε < 8 * d)
    (q : ℝ) {e : ℝ} (he : 0 < e) :
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.parallelogram
      (lowerSweep d ε q ∪ upperSweep d ε q) (2 * weightedCost d ε q + e) := by
  obtain ⟨U, hU, hDU, hreg⟩ := field_smoothNear_labelDomain hd ε q
  have hsmooth : RuledApproximation.SmoothNear 1 (labelDomain d ε q) (field d) :=
    ⟨U, hU, hDU, hreg.of_le (by norm_num)⟩
  apply finite_sweeps_of_regular (labelDomain_isCompact d ε q)
    (smoothNear_const_smul hsmooth ε) (smoothNear_const_smul hsmooth (-ε))
  · intro p hp
    exact rational_hyperbolic hd hε.ne' (by simpa [abs_of_pos hε] using hsmall) hp
  · intro p hp
    exact rational_hyperbolic hd (neg_ne_zero.mpr hε.ne')
      (by simpa [abs_of_pos hε] using hsmall) hp
  · exact he

theorem finite_strict_cover_of_coverage_cost {d ε q : ℝ}
    (hd : 0 < d) (hε : 0 < ε) (hsmall : ε < 8 * d)
    (hcoverage : referenceTetrahedron ⊆ lowerSweep d ε q ∪ upperSweep d ε q)
    (hcost : weightedCost d ε q < physicalScale / 8) :
    ∃ n : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
      (∀ i, (C i).parallelogram) ∧
      referenceTetrahedron ⊆ RuledApproximation.familySet C ∧
      RuledApproximation.familyArea C < physicalScale / 4 := by
  let e := (physicalScale / 4 - 2 * weightedCost d ε q) / 2
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨n, C, hC, hcov, harea⟩ := finite_sweeps hd hε hsmall q he
  refine ⟨n, C, hC, hcoverage.trans hcov, ?_⟩
  dsimp [e] at harea
  linarith

end SlopeRational

end

end OAI
