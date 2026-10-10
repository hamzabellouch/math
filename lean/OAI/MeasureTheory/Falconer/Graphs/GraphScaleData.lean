import OAI.MeasureTheory.Falconer.Angular.CapScaleGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-!
# The manuscript scales satisfy the analytic graph hypotheses

Depths a, p, v and L are normalized by the terminal depth. The actual
radial frequency is supplied by 2^frequency = R^v. All dimensional
constants and lower-scale requirements are explicit.
-/

namespace Falconer

noncomputable def graphDerivativeScale (R σ a p L c₀ C : ℝ) : ℝ :=
  C * (1 + R^σ * max 1 (R^(L-50*σ)) +
    (min c₀ (R^(a-p+10*σ)))⁻¹ + R^(-a)/R^(-p+30*σ))

theorem graph_scale_data (d : ℕ) {R σ a p v L c₀ C frequency : ℝ}
    (hR : 1 ≤ R) (hσ : 0 < σ) (hc₀ : 0 < c₀) (hcsmall : c₀ ≤ 1/2)
    (hC : 1 ≤ C) (hCdim : 4*Real.sqrt d ≤ C)
    (hh : p-a ≤ v-p+2*σ) (hL : L ≤ v-p+2*σ) (hq : 10*σ ≤ v-p)
    (hfrequency : (2 : ℝ)^frequency = R^v)
    (hlarge : 40*Real.sqrt d ≤ R^(20*σ)) (hlargeπ : 4*Real.pi ≤ R^(20*σ)) :
    let δ := min c₀ (R^(a-p+10*σ))
    let τ := R^(-p+30*σ)
    let D := graphDerivativeScale R σ a p L c₀ C
    0 < δ ∧ δ ≤ 1/2 ∧ 0 < τ ∧ 1 ≤ D ∧ δ⁻¹ ≤ D ∧
      Real.sqrt d*R^(-a) ≤ (τ/4)*D ∧
      2*Real.sqrt d*R^(-p)+8*δ*(Real.sqrt d*R^(-a)) ≤ τ/4 ∧
      4*Real.pi*R^(20*σ) ≤ (2 : ℝ)^frequency*τ ∧
      16*D/((2 : ℝ)^frequency*τ) ≤ (16*C*(4+c₀⁻¹))*R^(-(26*σ)) := by
  let δ := min c₀ (R^(a-p+10*σ))
  let τ := R^(-p+30*σ)
  let S := 1 + R^σ * max 1 (R^(L-50*σ)) + δ⁻¹ + R^(-a)/τ
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hδ : 0 < δ := lt_min hc₀ (Real.rpow_pos_of_pos hR0 _)
  have hτ : 0 < τ := Real.rpow_pos_of_pos hR0 _
  have hδsmall : δ ≤ 1/2 := (min_le_left _ _).trans hcsmall
  have hs₁ : 0 ≤ R^σ * max 1 (R^(L-50*σ)) := by positivity
  have hs₂ : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hs₃ : 0 ≤ R^(-a)/τ := by positivity
  have hSone : 1 ≤ S := by dsimp [S]; linarith
  have hSδ : δ⁻¹ ≤ S := by dsimp [S]; linarith
  have hSsp : R^(-a)/τ ≤ S := by dsimp [S]; linarith
  have hCS : S ≤ C*S := by nlinarith
  have hDone : 1 ≤ graphDerivativeScale R σ a p L c₀ C := hSone.trans hCS
  have hDδ : δ⁻¹ ≤ graphDerivativeScale R σ a p L c₀ C := hSδ.trans hCS
  have hsp : 4*Real.sqrt d*(R^(-a)/τ) ≤ graphDerivativeScale R σ a p L c₀ C := by
    calc
      _ ≤ C*(R^(-a)/τ) := mul_le_mul_of_nonneg_right hCdim (by positivity)
      _ ≤ C*S := mul_le_mul_of_nonneg_left hSsp (zero_le_one.trans hC)
  have hnorm : Real.sqrt d*R^(-a) ≤ (τ/4)*graphDerivativeScale R σ a p L c₀ C := by
    calc
      _ = (τ/4)*(4*Real.sqrt d*(R^(-a)/τ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsp (by positivity)
  have herr : 2*Real.sqrt d*R^(-p)+8*δ*(Real.sqrt d*R^(-a)) ≤ τ/4 := by
    have he := graph_cap_replacement_scale hR hσ.le (Real.sqrt_nonneg (d : ℝ)) hδ.le (min_le_right _ _)
    have hl := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ R^(-p+10*σ) by positivity)
    have hp : R^(20*σ)*R^(-p+10*σ) = τ := by
      rw [← Real.rpow_add hR0]
      congr 1
      ring
    rw [hp] at hl
    nlinarith
  have hfreq : 4*Real.pi*R^(20*σ) ≤ (2 : ℝ)^frequency*τ := by
    rw [hfrequency]
    have hp : R^(20*σ)*R^(20*σ) = R^(40*σ) := by
      rw [← Real.rpow_add hR0]
      congr 1
      ring
    calc
      _ ≤ R^(20*σ)*R^(20*σ) := mul_le_mul_of_nonneg_right hlargeπ (by positivity)
      _ = R^(40*σ) := hp
      _ ≤ _ := graph_radial_oscillation_size hR hq
  have hratio : 16*graphDerivativeScale R σ a p L c₀ C / ((2 : ℝ)^frequency*τ) ≤
      (16*C*(4+c₀⁻¹))*R^(-(26*σ)) := by
    rw [hfrequency]
    have hb := graph_nonstationary_ratio_bound hR hc₀ hσ.le hh hL hq
    calc
      _ = (16*C) * (S/(R^v*τ)) := by dsimp [graphDerivativeScale,S,δ,τ]; ring
      _ ≤ (16*C)*((4+c₀⁻¹)*R^(-(26*σ))) :=
        mul_le_mul_of_nonneg_left (by simpa only [S,δ,τ,neg_mul] using hb) (by positivity)
      _ = _ := by ring
  exact ⟨hδ,hδsmall,hτ,hDone,hDδ,hnorm,herr,hfreq,hratio⟩

/-- The two fixed-dimensional lower-scale conditions hold at all sufficiently
large terminal depths, with the derivative order already fixed. -/
theorem eventually_graph_scale_constants (d : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      40*Real.sqrt d ≤ ((2 : ℝ)^N)^(20*σ) ∧
      4*Real.pi ≤ ((2 : ℝ)^N)^(20*σ) := by
  have ht : Filter.Tendsto (fun N : ℕ => ((2 : ℝ)^N)^(20*σ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 20*σ)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact (ht.eventually (Filter.eventually_ge_atTop _)).and
    (ht.eventually (Filter.eventually_ge_atTop _))

end Falconer

end OAI
