import OAI.Geometry.CylinderCovering.Physical.CostVariantsDefinitions
import OAI.Geometry.CylinderCovering.Physical.Coordinates
import OAI.Geometry.CylinderCovering.Radial.CapCosts
import OAI.Geometry.CylinderCovering.Radial.SqrtCap

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RadialPhysical
open CylinderCovering

lemma canonicalProfile_eq_H (r : ℝ) : canonicalProfile r = RadialCaps.H r := by
  unfold canonicalProfile RadialCaps.H
  ring

lemma canonicalCost_eq_Q (ε : ℝ) (R : ℝ → ℝ) :
    canonicalCost ε R = RadialCaps.Q R ε := by
  unfold canonicalCost RadialCaps.Q canonicalSpeed RadialCaps.D0 RadialCaps.G
  congr 1
  funext r
  congr 3
  ring

lemma scaled_linear_cost_eq {b : ℝ} (hb : 0 < b) (η β : ℝ) :
    scaledCost b η (linearCap b η β) =
      (b * height b / 2) * RadialCaps.Q (RadialCaps.linearCap β (effectiveTilt b η))
        (effectiveTilt b η) := by
  rw [scaledCost_dictionary hb]
  simp_rw [linearCap_dictionary, canonicalProfile_eq_H]
  exact congrArg (fun x => (b * height b / 2) * x)
    (canonicalCost_eq_Q _ _)

lemma scaled_square_cost_eq {b : ℝ} (hb : 0 < b) (η β : ℝ) :
    scaledCost b η (squareCap b η β) =
      (b * height b / 2) * RadialSqrtCap.cost β (effectiveTilt b η) := by
  rw [scaledCost_dictionary hb]
  simp_rw [squareCap_dictionary, canonicalProfile_eq_H]
  exact congrArg (fun x => (b * height b / 2) * x)
    (canonicalCost_eq_Q _ _)

lemma physical_reference_pos {b : ℝ} (hb : 0 < b) : 0 < b * height b / 2 := by
  unfold height
  positivity

theorem scaled_linear_remainder {b β η : ℝ} (hb : 0 < b) (hβ : 0 ≤ β)
    (hs : 4 * (β + 2) * effectiveTilt b η ^ 2 ≤ 1) :
    |scaledCost b η (linearCap b η β) - quadraticCost b η β| ≤
      (b * height b / 2) * (24 * (β + 2) ^ 2) * effectiveTilt b η ^ 4 := by
  rw [scaled_linear_cost_eq hb]
  unfold quadraticCost relativeQuadraticTerm
  rw [← mul_sub, abs_mul, abs_of_pos (physical_reference_pos hb)]
  exact (mul_le_mul_of_nonneg_left (RadialCaps.linear_cost_remainder hβ hs)
    (physical_reference_pos hb).le).trans_eq (by ring)

theorem scaled_square_remainder {b β η : ℝ} (hb : 0 < b) (hβ : 0 ≤ β)
    (hs : |effectiveTilt b η| ≤ 1) :
    |scaledCost b η (squareCap b η β) - quadraticCost b η β| ≤
      (b * height b / 2) * (14 + 10 * β) * effectiveTilt b η ^ 4 := by
  rw [scaled_square_cost_eq hb]
  unfold quadraticCost relativeQuadraticTerm
  rw [← mul_sub, abs_mul, abs_of_pos (physical_reference_pos hb)]
  exact (mul_le_mul_of_nonneg_left (RadialSqrtCap.cost_expansion hβ hs)
    (physical_reference_pos hb).le).trans_eq (by ring)

theorem scaled_linear_bigO {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (a : ℝ) :
    (fun τ => scaledCost b (a * τ) (linearCap b (a * τ) β) -
      quadraticCost b (a * τ) β) =O[𝓝[>] (0 : ℝ)] (fun τ => τ ^ 4) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨(b * height b / 2) * (24 * (β + 2) ^ 2) * (a * b ^ 2) ^ 4, ?_⟩
  have hs : ∀ᶠ τ : ℝ in 𝓝 0, 4 * (β + 2) * effectiveTilt b (a * τ) ^ 2 < 1 :=
    (show ContinuousAt (fun τ : ℝ => 4 * (β + 2) * effectiveTilt b (a * τ) ^ 2) 0 by
      unfold effectiveTilt; fun_prop).eventually_lt continuousAt_const (by simp [effectiveTilt])
  filter_upwards [hs.filter_mono nhdsWithin_le_nhds] with τ hτ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ τ ^ 4)]
  convert scaled_linear_remainder hb hβ hτ.le using 1
  unfold effectiveTilt
  ring

theorem scaled_square_bigO {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (a : ℝ) :
    (fun τ => scaledCost b (a * τ) (squareCap b (a * τ) β) -
      quadraticCost b (a * τ) β) =O[𝓝[>] (0 : ℝ)] (fun τ => τ ^ 4) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨(b * height b / 2) * (14 + 10 * β) * (a * b ^ 2) ^ 4, ?_⟩
  have hs : ∀ᶠ τ : ℝ in 𝓝 0, |effectiveTilt b (a * τ)| < 1 :=
    (show ContinuousAt (fun τ : ℝ => |effectiveTilt b (a * τ)|) 0 by
      unfold effectiveTilt; fun_prop).eventually_lt continuousAt_const (by simp [effectiveTilt])
  filter_upwards [hs.filter_mono nhdsWithin_le_nhds] with τ hτ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ τ ^ 4)]
  convert scaled_square_remainder hb hβ hτ.le using 1
  unfold effectiveTilt
  ring

theorem scaled_linear_strict {b β : ℝ} (hb : 0 < b) (hβ : 0 < β)
    (hβmax : β < 1 / 60) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      scaledCost b η (linearCap b η β) < b * height b / 2 := by
  have hs : ∀ᶠ η : ℝ in 𝓝 0,
      4 * (β + 2) * effectiveTilt b η ^ 2 < 1 :=
    (show ContinuousAt (fun η : ℝ => 4 * (β + 2) * effectiveTilt b η ^ 2) 0 by
      unfold effectiveTilt; fun_prop).eventually_lt continuousAt_const (by simp [effectiveTilt])
  have hg : ∀ᶠ η : ℝ in 𝓝 0,
      24 * (β + 2) ^ 2 * effectiveTilt b η ^ 2 < 1 / 30 - 2 * β :=
    (show ContinuousAt (fun η : ℝ => 24 * (β + 2) ^ 2 * effectiveTilt b η ^ 2) 0 by
      unfold effectiveTilt; fun_prop).eventually_lt continuousAt_const
        (by simp only [effectiveTilt, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero]; linarith)
  filter_upwards [eventually_mem_nhdsWithin, hs.filter_mono nhdsWithin_le_nhds,
    hg.filter_mono nhdsWithin_le_nhds] with η hη hs hg
  have hηpos : 0 < η := hη
  have he : 0 < effectiveTilt b η := by unfold effectiveTilt; positivity
  have hcost : RadialCaps.Q (RadialCaps.linearCap β (effectiveTilt b η))
      (effectiveTilt b η) < 1 := by
    apply RadialCaps.strict_of_remainder he (a := 1 / 30 - 2 * β)
      (K := 24 * (β + 2) ^ 2) _ hg
    convert RadialCaps.linear_cost_remainder hβ.le hs.le using 1
    congr 1
    ring
  rw [scaled_linear_cost_eq hb]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hcost (physical_reference_pos hb)

theorem scaled_square_strict {b β : ℝ} (hb : 0 < b) (hβ : 0 < β)
    (hβmax : β < 1 / 60) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      scaledCost b η (squareCap b η β) < b * height b / 2 := by
  have hs : ∀ᶠ η : ℝ in 𝓝 0, |effectiveTilt b η| < 1 :=
    (show ContinuousAt (fun η : ℝ => |effectiveTilt b η|) 0 by
      unfold effectiveTilt; fun_prop).eventually_lt continuousAt_const (by simp [effectiveTilt])
  have hg : ∀ᶠ η : ℝ in 𝓝 0,
      (14 + 10 * β) * effectiveTilt b η ^ 2 < 1 / 30 - 2 * β :=
    (show ContinuousAt (fun η : ℝ => (14 + 10 * β) * effectiveTilt b η ^ 2) 0 by
      unfold effectiveTilt; fun_prop).eventually_lt continuousAt_const
        (by simp only [effectiveTilt, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero]; linarith)
  filter_upwards [eventually_mem_nhdsWithin, hs.filter_mono nhdsWithin_le_nhds,
    hg.filter_mono nhdsWithin_le_nhds] with η hη hs hg
  have hηpos : 0 < η := hη
  have he : 0 < effectiveTilt b η := by unfold effectiveTilt; positivity
  have hcost : RadialSqrtCap.cost β (effectiveTilt b η) < 1 := by
    apply RadialCaps.strict_of_remainder he (a := 1 / 30 - 2 * β)
      (K := 14 + 10 * β) _ hg
    convert RadialSqrtCap.cost_expansion hβ.le hs.le using 1
    congr 1
    ring
  rw [scaled_square_cost_eq hb]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hcost (physical_reference_pos hb)

lemma scaledCost_mul (b η c : ℝ) (T : ℝ → ℝ) :
    scaledCost b η (fun s => c*T s) = c^2 * scaledCost b η T := by
  unfold scaledCost scaledDensity
  have hid (s : ℝ) : (c*T s)^2 /
      Real.sqrt (1+η^2*((s^2+b^2)^2/4+height b^2*s^2)) =
      c^2*(T s^2 / Real.sqrt (1+η^2*((s^2+b^2)^2/4+height b^2*s^2))) := by ring
  simp_rw [hid]
  rw [intervalIntegral.integral_const_mul]
  ring

lemma centered_linear_cost_eq (b η β : ℝ) :
    scaledCost b η (centeredLinearCap b η β) = 4*scaledCost b η (linearCap b η β) := by
  have hc : centeredLinearCap b η β = fun s => 2*linearCap b η β s := by
    funext s
    unfold centeredLinearCap linearCap capPolynomial
    ring
  rw [hc, scaledCost_mul]
  norm_num

theorem centered_linear_bigO {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (a : ℝ) :
    (fun τ => scaledCost b (a*τ) (centeredLinearCap b (a*τ) β) -
      2*b*height b*(1+relativeQuadraticTerm b (a*τ) β))
      =O[𝓝[>] (0:ℝ)] (fun τ => τ^4) := by
  apply ((scaled_linear_bigO hb hβ a).const_mul_left 4).congr_left
  intro τ
  rw [centered_linear_cost_eq]
  unfold quadraticCost
  ring

theorem centered_linear_strict {b β : ℝ} (hb : 0 < b) (hβ : 0 < β)
    (hβmax : β < 1/60) :
    ∀ᶠ η : ℝ in 𝓝[>] 0, scaledCost b η (centeredLinearCap b η β) < 2*b*height b := by
  filter_upwards [scaled_linear_strict hb hβ hβmax] with η hη
  rw [centered_linear_cost_eq]
  linarith

theorem physical_cost_table : PhysicalCostTableStatement := by
  unfold PhysicalCostTableStatement RelativeCostExpansion
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (scaled_linear_bigO (b := 1) (β := 1/120) (by norm_num) (by norm_num) 1).congr_left
    intro τ
    simp only [one_mul, quadraticCost]
    rw [(scaled_table_rational_rows τ).1]
    ring
  · apply (scaled_linear_bigO (b := 1/2) (β := 1/120) (by norm_num) (by norm_num) (1/2)).congr_left
    intro τ
    rw [show (1/2:ℝ)*τ = τ/2 by ring]
    unfold quadraticCost
    rw [(scaled_table_rational_rows τ).2.1]
    ring
  · apply (scaled_linear_bigO (b := 1/Real.sqrt 2) (β := 1/125) (by positivity) (by norm_num) 1).congr_left
    intro τ
    simp only [one_mul, quadraticCost]
    rw [scaled_table_sqrt_row]
    ring
  · apply (scaled_square_bigO (b := 1/Real.sqrt 2) (β := 1/125) (by positivity) (by norm_num) 1).congr_left
    intro τ
    simp only [one_mul, quadraticCost]
    rw [scaled_table_sqrt_row]
    ring
  · apply (scaled_linear_bigO (b := 1/2) (β := 4/625) (by norm_num) (by norm_num) 1).congr_left
    intro τ
    simp only [one_mul, quadraticCost]
    rw [(scaled_table_rational_rows τ).2.2.1]
    ring
  · apply (scaled_square_bigO (b := 1/2) (β := 1/120) (by norm_num) (by norm_num) 2).congr_left
    intro τ
    unfold quadraticCost
    rw [(scaled_table_rational_rows τ).2.2.2.1]
    ring
  · apply (scaled_linear_bigO (b := 1) (β := 1/200) (by norm_num) (by norm_num) 2).congr_left
    intro τ
    unfold quadraticCost
    rw [(scaled_table_rational_rows τ).2.2.2.2]
    ring

lemma inverse_sqrt_height : height (1/Real.sqrt 2) = 1 := by
  unfold height
  have h : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

lemma inverse_sqrt_effectiveTilt (η : ℝ) : effectiveTilt (1/Real.sqrt 2) η = η/2 := by
  unfold effectiveTilt
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

theorem nonorth_cost_eq (ε : ℝ) (R : ℝ → ℝ) :
    nonorthCost ε R = Real.sqrt 2 * RadialCaps.Q R ε := by
  unfold nonorthCost
  rw [centeredCost_dictionary (by positivity), inverse_sqrt_height, inverse_sqrt_effectiveTilt]
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  have he : 2*ε/2 = ε := by ring
  have hr (r : ℝ) : Real.sqrt 2 * (1/Real.sqrt 2*r) = r := by field_simp
  simp_rw [he, hr]
  rw [canonicalCost_eq_Q]
  have hc : 2*(1/Real.sqrt 2)*1 = Real.sqrt 2 := by
    field_simp
    nlinarith only [hs]
  rw [hc]

theorem nonorth_cubic_bigO :
    (fun ε => nonorthCost ε (RadialCaps.cubicCap 5 ε) -
      Real.sqrt 2*(1-ε^2/30+10*ε^3)) =O[𝓝[>] (0:ℝ)] (fun ε => ε^4) := by
  apply ((RadialCaps.cubic_cost_bigO (c := 5) (by norm_num)).const_mul_left (Real.sqrt 2)).congr_left
  intro ε
  rw [nonorth_cost_eq]
  ring

theorem nonorth_fractional_bigO :
    (fun ε => nonorthCost ε (RadialCaps.fractionalCap 1 ε) -
      Real.sqrt 2*(1-ε^2/30+2*ε^(5/2:ℝ))) =O[𝓝[>] (0:ℝ)] (fun ε => ε^4) := by
  apply ((RadialCaps.fractional_cost_bigO (c := 1) (by norm_num)).const_mul_left (Real.sqrt 2)).congr_left
  intro ε
  rw [nonorth_cost_eq]
  ring

lemma centered_fractional_cap_dictionary {η : ℝ} (hη : 0 < η) (r : ℝ) :
    centeredFractionalCap (1/Real.sqrt 2) η ((1/Real.sqrt 2)*r) =
      RadialCaps.fractionalCap (4*Real.sqrt 2) (η/2) r := by
  unfold centeredFractionalCap RadialCaps.fractionalCap RadialCaps.H
  rw [RadialCaps.rpow_five_halves hη,
    RadialCaps.rpow_five_halves (by positivity : 0 < η/2), Real.sqrt_div hη.le]
  simp only [mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  ring

lemma centered_fractional_cost_eq {η : ℝ} (hη : 0 < η) :
    scaledCost (1/Real.sqrt 2) η (centeredFractionalCap (1/Real.sqrt 2) η) =
      (2/Real.sqrt 2) * RadialCaps.Q
        (fun r => 1+(η/2)^2*(RadialCaps.H r+4*Real.sqrt η)) (η/2) := by
  rw [centeredCost_dictionary (by positivity), inverse_sqrt_height, inverse_sqrt_effectiveTilt,
    canonicalCost_eq_Q]
  have hc : (fun r => centeredFractionalCap (1/Real.sqrt 2) η ((1/Real.sqrt 2)*r)) =
      (fun r => 1+(η/2)^2*(RadialCaps.H r+4*Real.sqrt η)) := by
    funext r
    unfold centeredFractionalCap RadialCaps.H
    rw [RadialCaps.rpow_five_halves hη]
    simp only [mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [hc]
  ring

theorem centered_fractional_remainder {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hs : 6*η^2 ≤ 1) :
    |scaledCost (1/Real.sqrt 2) η (centeredFractionalCap (1/Real.sqrt 2) η) -
      (1/Real.sqrt 2)*(2-η^2/60+4*η^(5/2:ℝ))| ≤
      (108/Real.sqrt 2)*η^4 := by
  have hp := RadialCaps.padded_cost_remainder
    (b := 4*Real.sqrt η) (c := 4) (ε := η/2)
    (by positivity) (by nlinarith [Real.sqrt_le_one.mpr hη1]) (by norm_num)
    (by nlinarith only [hs])
  rw [centered_fractional_cost_eq hη, RadialCaps.rpow_five_halves hη]
  have he : (1/Real.sqrt 2)*(2-η^2/60+4*(η^2*Real.sqrt η)) =
      (2/Real.sqrt 2)*(1+(2*(4*Real.sqrt η)-1/30)*(η/2)^2) := by ring
  rw [he, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2/Real.sqrt 2)]
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 2/Real.sqrt 2)
  exact hh.trans_eq (by ring)

theorem centered_fractional_bigO :
    (fun η => scaledCost (1/Real.sqrt 2) η (centeredFractionalCap (1/Real.sqrt 2) η) -
      (1/Real.sqrt 2)*(2-η^2/60+4*η^(5/2:ℝ)))
      =O[𝓝[>] (0:ℝ)] (fun η => η^4) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨108/Real.sqrt 2, ?_⟩
  have hs : ∀ᶠ η : ℝ in 𝓝 0, 6*η^2 < 1 :=
    (show ContinuousAt (fun η : ℝ => 6*η^2) 0 by fun_prop).eventually_lt
      continuousAt_const (by norm_num)
  have h1 : ∀ᶠ η : ℝ in 𝓝 0, η < 1 :=
    continuousAt_id.eventually_lt continuousAt_const (by norm_num)
  filter_upwards [eventually_mem_nhdsWithin, hs.filter_mono nhdsWithin_le_nhds,
    h1.filter_mono nhdsWithin_le_nhds] with η hη hs h1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ η^4)] using
    centered_fractional_remainder hη h1.le hs.le

theorem centered_fractional_littleO :
    (fun η => scaledCost (1/Real.sqrt 2) η (centeredFractionalCap (1/Real.sqrt 2) η) -
      (1/Real.sqrt 2)*(2-η^2/60)) =o[𝓝[>] (0:ℝ)] (fun η => η^2) := by
  have h4 : (fun η : ℝ => η^4) =o[𝓝[>] (0:ℝ)] (fun η => η^2) :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 4)).mono nhdsWithin_le_nhds
  have hsqrt : (fun η : ℝ => Real.sqrt η) =o[𝓝[>] (0:ℝ)] (fun _ => (1:ℝ)) := by
    apply (Asymptotics.isLittleO_one_iff ℝ).mpr
    simpa using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hm : (fun η : ℝ => η^2*Real.sqrt η) =o[𝓝[>] (0:ℝ)] (fun η => η^2) := by
    simpa only [mul_one] using (Asymptotics.isBigO_refl (fun η : ℝ => η^2) (𝓝[>] (0:ℝ))).mul_isLittleO hsqrt
  have hf : (fun η : ℝ => η^(5/2:ℝ)) =o[𝓝[>] (0:ℝ)] (fun η => η^2) := by
    apply hm.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [eventually_mem_nhdsWithin] with η hη
    exact (RadialCaps.rpow_five_halves hη).symm
  apply ((centered_fractional_bigO.trans_isLittleO h4).add
    (hf.const_mul_left (4/Real.sqrt 2))).congr_left
  intro η
  ring

theorem centered_fractional_strict :
    ∀ᶠ η : ℝ in 𝓝[>] 0, scaledCost (1/Real.sqrt 2) η
      (centeredFractionalCap (1/Real.sqrt 2) η) < 2/Real.sqrt 2 := by
  have hs : ∀ᶠ η : ℝ in 𝓝 0, 6*η^2 < 1 :=
    (show ContinuousAt (fun η : ℝ => 6*η^2) 0 by fun_prop).eventually_lt
      continuousAt_const (by norm_num)
  have h1 : ∀ᶠ η : ℝ in 𝓝 0, η < 1 :=
    continuousAt_id.eventually_lt continuousAt_const (by norm_num)
  have hg : ∀ᶠ η : ℝ in 𝓝 0, 108*η^2+4*Real.sqrt η < 1/60 :=
    (show ContinuousAt (fun η : ℝ => 108*η^2+4*Real.sqrt η) 0 by fun_prop).eventually_lt
      continuousAt_const (by norm_num)
  filter_upwards [eventually_mem_nhdsWithin, hs.filter_mono nhdsWithin_le_nhds,
    h1.filter_mono nhdsWithin_le_nhds, hg.filter_mono nhdsWithin_le_nhds] with η hη hs h1 hg
  have hηpos : 0 < η := hη
  have hrem := (abs_le.mp (centered_fractional_remainder hηpos h1.le hs.le)).2
  rw [RadialCaps.rpow_five_halves hηpos] at hrem
  have hgap := mul_lt_mul_of_pos_right hg (sq_pos_of_pos hηpos)
  have hroot : 0 < Real.sqrt 2 := by positivity
  calc
    _ ≤ (1/Real.sqrt 2)*(2-η^2/60+4*(η^2*Real.sqrt η)) +
        (108/Real.sqrt 2)*η^4 := by linarith only [hrem]
    _ < 2/Real.sqrt 2 := by
      apply sub_neg.mp
      have he : (1/Real.sqrt 2)*(2-η^2/60+4*(η^2*Real.sqrt η)) +
          (108/Real.sqrt 2)*η^4 - 2/Real.sqrt 2 =
          ((108*η^2+4*Real.sqrt η)*η^2-(1/60)*η^2)/Real.sqrt 2 := by ring
      rw [he]
      exact div_neg_of_neg_of_pos (sub_neg.mpr hgap) hroot

theorem physical_cost_variants : PhysicalCostVariantsStatement where
  linearExpansion := fun _ _ a hb hβ => scaled_linear_bigO hb hβ a
  squareExpansion := fun _ _ a hb hβ => scaled_square_bigO hb hβ a
  linearSaving := fun _ _ hb hβ hβmax => scaled_linear_strict hb hβ hβmax
  squareSaving := fun _ _ hb hβ hβmax => scaled_square_strict hb hβ hβmax
  table := physical_cost_table
  centeredLinearExpansion := fun _ _ a hb hβ => centered_linear_bigO hb hβ a
  centeredLinearSaving := fun _ _ hb hβ hβmax => centered_linear_strict hb hβ hβmax
  centeredFractionalDictionary := fun _ hη r => centered_fractional_cap_dictionary hη r
  centeredFractionalExpansion := centered_fractional_bigO
  centeredFractionalLittleO := centered_fractional_littleO
  centeredFractionalSaving := centered_fractional_strict
  nonorthDictionary := nonorth_cost_eq
  nonorthCubic := nonorth_cubic_bigO
  nonorthFractional := nonorth_fractional_bigO

end RadialPhysical

end

end OAI
