import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeError
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeScale
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedModelOverlap

namespace OAI

/-! The actual early-stopped cube series has the full squared model,
including the controlled shared-prime pairs, with arbitrary log saving. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_cube_model_log_saving {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ) (hΦ' : ContDiff ℝ ∞ Φ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b A u : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ b → b ≤ X →
      0 < A → A ≤ b^2/(Real.log X)^(3*k) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (e : Eisenstein) (j k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j ≤ h →
      (Real.log X)^(k+1) ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j k₀ h Z Q early)
      ‖cubePoissonContribution S β u Φ A-cubeModelTerm S β u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  obtain ⟨C,D,hC,hD,hcube⟩ := stopped_cube_uniform_error (ι := ι) Φ hΦ hΦ'
  obtain ⟨M₁,hM₁,hcoeff⟩ := stopped_interval_energy (ι := ι) hξ hξz
  obtain ⟨M₂,hM₂,hoverlap⟩ := stopped_model_overlap (ι := ι) hξ hξz
  let M := M₁+M₂
  let K := 24*C*M^2+(72*D+36*‖cubeProfileIntegral Φ‖)*(2:ℝ)^(1/3:ℝ)*M^2/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : 0 < M := by dsimp [M]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+1,by positivity,?_⟩
  filter_upwards [hcoeff,hoverlap,eventually_ge_atTop (Real.exp 1)] with X hcoeff hoverlap hX
  intro δ b A u hδ hδone hb hbX hA hcut W hW e j k₀ h Z Q early hj hR
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X) j k₀ h Z Q early)
  let R := min (X^ξ) (geometricBinLower (1+δ) X h)
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hz1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hz : 0 < Real.log X := zero_lt_one.trans_le hz1
  have hRp : 0 < R := (pow_pos hz _).trans_le hR
  have hbp : 0 < b := by linarith
  have hAb : A ≤ 27*(b/2)^2 := by
    have hh := hcut.trans (div_le_self (sq_nonneg b) (one_le_pow₀ hz1))
    nlinarith [sq_nonneg b]
  have hmass : (∑ a ∈ S, ‖β a‖) ≤ 18*b*M := by
    calc
      _ ≤ ∑ _a ∈ S, M₁ := Finset.sum_le_sum
        ((hcoeff W hW _ 0 (b/2) b e hbp.le hbX).1)
      _ = (S.card:ℝ)*M₁ := by simp
      _ ≤ 18*b*M₁ := mul_le_mul_of_nonneg_right
        (primary_support_card_le S hbp.le (fun a ha =>
          ⟨(stoppedIntervalSupport_spec X (b/2) b e ha).1,
            (stoppedIntervalSupport_spec X (b/2) b e ha).2.2⟩)) hM₁.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [M]; linarith) (by positivity)
  have ho : (∑ a ∈ S, ∑ c ∈ S, if ¬IsCoprime a c then ‖β a‖*‖β c‖ else 0) ≤
      324*b^2*M^2*(Real.log X/Real.log 2)/R := by
    apply (hoverlap δ (b/2) b hδ hδone hbp.le hbX W hW e j k₀ h Z Q early hj hRp).trans
    gcongr
    dsimp [M]
    linarith
  have hc := hcube X ξ δ b A u hX1 hξz hδ hδone hb hbX hA hAb W e j k₀ h Z Q early hj hRp
  have hm := cube_model_coprimality_error S β u Φ hA.le (by linarith : 0 < b/2)
    (fun a ha => (Finset.mem_filter.mp ha).2.2.2.1.le)
  have htri : ‖cubePoissonContribution S β u Φ A-cubeModelTerm S β u Φ A‖ ≤
      ‖cubePoissonContribution S β u Φ A-coprimeCubeMainTerm S β u Φ A‖+
        ‖cubeModelTerm S β u Φ A-coprimeCubeMainTerm S β u Φ A‖ := by
    simpa only [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub
      (cubePoissonContribution S β u Φ A) (coprimeCubeMainTerm S β u Φ A)
      (cubeModelTerm S β u Φ A)
  apply (htri.trans (add_le_add hc hm)).trans
  calc
    _ ≤ (C*A/(27*(b/2))+D*A^(2/3:ℝ)*(b/2)^(-(1/3:ℝ))/9*
          ((2*Real.log X/Real.log 2)/R))*(18*b*M)^2+
        (A^(2/3:ℝ)*(b/2)^(-(1/3:ℝ))/9*‖cubeProfileIntegral Φ‖)*
          (324*b^2*M^2*(Real.log X/Real.log 2)/R) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmass 2) (by positivity))
      (mul_le_mul_of_nonneg_left ho (by positivity))
    _ ≤ K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k :=
      stopped_cube_error_scale hA hbp hz hC.le hD.le (_root_.norm_nonneg _) k hcut hR
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : K ≤ K+1) (by positivity)) (by positivity)

end CubicFirstMoment

end

end OAI
