import OAI.Geometry.CylinderCovering.Angular.Estimates
import OAI.Geometry.CylinderCovering.Cartesian.Caps
import OAI.Geometry.CylinderCovering.Cartesian.DomainDefinitions

namespace OAI

namespace AngularCartesianDirect

open CylinderCovering.CartesianCaps

theorem D_lipschitz_displaced (x y : ℝ)
    (hx : |x| ≤ 3 / 2) (hy : |y| ≤ 3 / 2) :
    |D x - D y| ≤ (57 / 4) * |x - y| := by
  have hx2 : x ^ 2 ≤ 9 / 4 := by
    nlinarith only [(abs_le.mp hx).1, (abs_le.mp hx).2]
  have hy2 : y ^ 2 ≤ 9 / 4 := by
    nlinarith only [(abs_le.mp hy).1, (abs_le.mp hy).2]
  have hsum : |x + y| ≤ 3 := (abs_add_le x y).trans (by linarith)
  have hfactor : |(x + y) * (1 / 4 + x ^ 2 + y ^ 2)| ≤ 57 / 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / 4 : ℝ) + x ^ 2 + y ^ 2)]
    calc
      |x + y| * (1 / 4 + x ^ 2 + y ^ 2) ≤
          3 * (1 / 4 + x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
      _ ≤ 57 / 4 := by linarith
  rw [D_sub_factor, abs_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hfactor (abs_nonneg (x-y))]

theorem displaced_polynomial_error {Y δ α τ : ℝ}
    (hY : |Y| ≤ 1) (hδ : |δ| ≤ τ) (hτ : τ ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    |D (Y - δ * α) - D Y| ≤ 8 * τ := by
  have hτ0 : 0 ≤ τ := (abs_nonneg δ).trans hδ
  have hdisp : |Y - δ * α - Y| ≤ τ / 2 := by
    have hmul := mul_le_mul hδ hα1 hα0 hτ0
    simpa only [sub_sub_cancel_left, abs_neg, abs_mul, abs_of_nonneg hα0,
      mul_one_div] using hmul
  have hlip := D_lipschitz_displaced (Y-δ*α) Y
    (AngularEstimates.displaced_intercept_bound hY hδ hτ hα0 hα1)
    (hY.trans (by norm_num))
  nlinarith only [hlip, hdisp, hτ0]

theorem failed_cap_gt {S H : ℝ} (hH : H < 1)
    (hfail : ¬ (S ≤ 1 ∧ S ≤ H)) : H < S := by
  by_contra hn
  have hSH : S ≤ H := le_of_not_gt hn
  exact hfail ⟨hSH.trans hH.le, hSH⟩

theorem discriminant_gain {α β Δ T Y δ S τ η M : ℝ}
    (hY : |Y| ≤ 1) (hδ : |δ| ≤ τ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2)
    (hΔ : 0 ≤ Δ) (_hM : 0 ≤ M) (hmesh : Δ ≤ M * τ ^ 2)
    (hsmall : (32 + M) * τ ≤ 2 * η)
    (houter : τ ^ 2 * (45 / 8 + η) < 1 / 2)
    (hS0 : 0 ≤ S) (hS : S = T - δ * β)
    (hsecant : β ^ 2 - α + 1 / 4 = Δ ^ 2 / 16)
    (hsector : |2 * β * S - (Y - δ * α)| ≤ Δ * S / 2)
    (hfail : ¬ (S ≤ 1 ∧ S ≤ 1 / 2 + τ ^ 2 * (D (Y - δ * α) + η))) :
    1 / 2 + τ ^ 2 * (D Y + η / 2) <
      Real.sqrt (T ^ 2 - δ * Y + δ ^ 2 / 4) := by
  have hDbound : D (Y - δ * α) ≤ 45 / 8 :=
    (AngularEstimates.cartesian_polynomial_bound
      (AngularEstimates.displaced_intercept_bound hY hδ hτ1 hα0 hα1)).2
  have hH : 1 / 2 + τ ^ 2 * (D (Y - δ * α) + η) < 1 := by
    have hm := mul_le_mul_of_nonneg_left hDbound (sq_nonneg τ)
    nlinarith only [hm, houter]
  have hcap := failed_cap_gt hH hfail
  have herr := displaced_polynomial_error hY hδ hτ1 hα0 hα1
  have hD := mul_le_mul_of_nonneg_left (abs_le.mp herr).1 (sq_nonneg τ)
  have hmesh' : |δ| * Δ ≤ M * τ ^ 3 := by
    have hm := mul_le_mul hδ hmesh hΔ hτ0
    nlinarith only [hm]
  have hmargin := mul_le_mul_of_nonneg_left hsmall (sq_nonneg τ)
  have hsqrt := AngularEstimates.cartesian_discriminant_sqrt hΔ hS0
    hsecant hS rfl hsector
  nlinarith only [hcap, hD, hmesh', hmargin, hsqrt]

theorem smallness_radius {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 ≤ τ → τ ≤ τ₀ →
      τ ≤ 1 ∧ (32 + M) * τ ≤ 2 * η ∧
        τ ^ 2 * (45 / 8 + η) < 1 / 2 := by
  have hd : 0 < (32 : ℝ) + M := by linarith
  have he : 0 < 4 * (6 + η) := by positivity
  refine ⟨min 1 (min (1 / (4 * (6 + η))) (η / (32 + M))),
    lt_min (by norm_num) (lt_min (div_pos (by norm_num) he) (div_pos hη hd)), ?_⟩
  intro τ hτ hbound
  have hτ1 : τ ≤ 1 := hbound.trans (min_le_left _ _)
  have hτrest := hbound.trans (min_le_right _ _)
  have hτa : τ ≤ 1 / (4 * (6 + η)) := hτrest.trans (min_le_left _ _)
  have hτb : τ ≤ η / (32 + M) := hτrest.trans (min_le_right _ _)
  have ha := (le_div_iff₀ he).mp hτa
  have hb := (le_div_iff₀ hd).mp hτb
  have hsq : τ ^ 2 ≤ τ := by nlinarith only [hτ, hτ1]
  have hc := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ (45 / 8 : ℝ) + η by linarith)
  refine ⟨hτ1, ?_, ?_⟩
  · nlinarith only [hb, hη]
  · nlinarith only [hc, ha, hτ]

theorem selected_domain_gain {l r T Y δ S τ η M : ℝ}
    (hl : -1 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1)
    (hY : |Y| ≤ 1) (hδ : |δ| ≤ τ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hM : 0 ≤ M) (hmesh : r - l ≤ M * τ ^ 2)
    (hsmall : (32 + M) * τ ≤ 2 * η)
    (houter : τ ^ 2 * (45 / 8 + η) < 1 / 2)
    (hS0 : 0 ≤ S) (hS : S = T - δ * ((l+r)/4))
    (hleft : l * S ≤ Y - δ * ((1+l*r)/4))
    (hright : Y - δ * ((1+l*r)/4) ≤ r * S)
    (hfail : (Y - δ * ((1+l*r)/4), S) ∉ domain τ η 1) :
    1 / 2 + τ ^ 2 * (D Y + η / 2) <
      Real.sqrt (T ^ 2 - δ * Y + δ ^ 2 / 4) := by
  have hal : |l| ≤ 1 := abs_le.mpr ⟨hl, hlr.trans hr⟩
  have har : |r| ≤ 1 := abs_le.mpr ⟨hl.trans hlr, hr⟩
  have hprod := CylinderCovering.CartesianCaps.abs_mul_le_one l r hal har
  have hα0 : 0 ≤ (1+l*r)/4 := by linarith [(abs_le.mp hprod).1]
  have hα1 : (1+l*r)/4 ≤ 1/2 := by linarith [(abs_le.mp hprod).2]
  have hangle : |Y - δ * ((1+l*r)/4)| ≤ S := by
    rw [abs_le]
    constructor
    · nlinarith only [hleft, mul_le_mul_of_nonneg_right hl hS0]
    · nlinarith only [hright, mul_le_mul_of_nonneg_right hr hS0]
  apply discriminant_gain hY hδ hτ0 hτ1 hα0 hα1 (sub_nonneg.mpr hlr)
    hM hmesh hsmall houter hS0 hS (AngularEstimates.ordinary_secant_identity l r)
    (AngularEstimates.sector_midpoint_error hleft hright)
  intro hf
  exact hfail ⟨hS0, hf.1, hangle, hf.2⟩

theorem uniform_selected_domain_gain {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 ≤ τ → τ ≤ τ₀ →
      ∀ l r T Y δ S : ℝ,
      -1 ≤ l → l ≤ r → r ≤ 1 → |Y| ≤ 1 → |δ| ≤ τ →
      r-l ≤ M*τ^2 → 0 ≤ S → S = T-δ*((l+r)/4) →
      l*S ≤ Y-δ*((1+l*r)/4) → Y-δ*((1+l*r)/4) ≤ r*S →
      (Y-δ*((1+l*r)/4), S) ∉ domain τ η 1 →
      1/2+τ^2*(D Y+η/2) < Real.sqrt (T^2-δ*Y+δ^2/4) := by
  obtain ⟨τ₀, hτ₀, hsmall⟩ := smallness_radius hη hM
  refine ⟨τ₀, hτ₀, ?_⟩
  intro τ hτ hτle l r T Y δ S hl hlr hr hY hδ hmesh hS0 hS hleft hright hfail
  obtain ⟨hτ1, hmarg, houter⟩ := hsmall τ hτ hτle
  exact selected_domain_gain hl hlr hr hY hδ hτ hτ1 hM hmesh hmarg houter
    hS0 hS hleft hright hfail

end AngularCartesianDirect

end OAI
