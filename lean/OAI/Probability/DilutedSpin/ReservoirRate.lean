import OAI.Probability.DilutedSpin.RegularNodeEstimates

namespace OAI

section
namespace DilutedSpinGlass
open Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped NNReal Topology

/-- The old-site Poisson intensity, written so that its deficit from αN is
manifestly nonnegative. The exponent is p-1. -/
noncomputable def reservoirRate (α : ℝ≥0) (q N : ℕ) : ℝ≥0 :=
  α*N*((N:ℝ≥0)/(N+1))^q

lemma reservoirRate_nonzero (α : ℝ≥0) (hα : 0 < α) (q N : ℕ) (hN : 0 < N) :
    0 < reservoirRate α q N := by
  unfold reservoirRate
  positivity

lemma reservoirRate_le (α : ℝ≥0) (q N : ℕ) : reservoirRate α q N ≤ α*N := by
  apply mul_le_of_le_one_right (by positivity)
  exact pow_le_one₀ (by positivity) ((div_le_one (by positivity)).mpr (by simp))

lemma reservoirRate_lower (α : ℝ≥0) (q N : ℕ) :
    (α:ℝ)*((N:ℝ)-q) ≤ reservoirRate α q N := by
  have hden : (0:ℝ) < N+1 := by positivity
  have hx0 : (0:ℝ) ≤ N/(N+1) := by positivity
  have hx1 : (N:ℝ)/(N+1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hb := one_add_mul_sub_le_pow (R := ℝ) (a := (N:ℝ)/(N+1)) (by linarith : -1 ≤ (N:ℝ)/(N+1)) q
  have hh := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ α*N by positivity)
  have he : (N:ℝ)/(N+1)-1 = -1/(N+1) := by field_simp; ring
  rw [he] at hh
  have hqq : (N:ℝ)*q/(N+1) ≤ q := by
    rw [div_le_iff₀ hden]
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  change (α:ℝ)*((N:ℝ)-q) ≤ (α:ℝ)*N*((N:ℝ)/(N+1))^q
  calc
    _ ≤ (α:ℝ)*(N-N*q/(N+1)) := mul_le_mul_of_nonneg_left (by linarith) α.coe_nonneg
    _ = (α:ℝ)*N*(1+q*(-1/(N+1))) := by ring
    _ ≤ _ := hh

lemma reservoirRate_deficit_le (α : ℝ≥0) (q N : ℕ) :
    ((α*N-reservoirRate α q N:ℝ≥0):ℝ) ≤ (α:ℝ)*q := by
  rw [NNReal.coe_sub (reservoirRate_le α q N)]
  push_cast
  linarith [reservoirRate_lower α q N]

lemma reservoirRate_source (α : ℝ≥0) {p : ℕ} (hp : 1 ≤ p) (N : ℕ) :
    reservoirRate α (p-1) N = α*(N+1)*((N:ℝ≥0)/(N+1))^p := by
  have hd : (N:ℝ≥0)+1 ≠ 0 := by positivity
  have hp' : p=p-1+1 := by omega
  conv_rhs => rw [hp',pow_succ]
  unfold reservoirRate
  have he : (N:ℝ≥0)+1 ≠ 0 := hd
  field_simp

lemma reservoirRate_tendsto (α : ℝ≥0) (hα : 0 < α) (q : ℕ) :
    Tendsto (fun N => (reservoirRate α q N:ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun N => reservoirRate_lower α q N)
  have hn : Tendsto (fun N : ℕ => (N:ℝ)-(q:ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop (-(q:ℝ)) tendsto_natCast_atTop_atTop
  exact hn.const_mul_atTop hα

noncomputable def reservoirDistance (α : ℝ≥0) (q N : ℕ) : ℝ :=
  ((α*N-reservoirRate α q N:ℝ≥0):ℝ)/Real.sqrt (reservoirRate α q N)

lemma reservoirDistance_nonneg (α : ℝ≥0) (q N : ℕ) : 0 ≤ reservoirDistance α q N := by
  unfold reservoirDistance
  positivity

lemma reservoirDistance_tendsto (α : ℝ≥0) (hα : 0 < α) (q : ℕ) :
    Tendsto (reservoirDistance α q) atTop (𝓝 0) := by
  have hh := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp (reservoirRate_tendsto α hα q))).const_mul ((α:ℝ)*q)
  simp only [mul_zero] at hh
  apply squeeze_zero (reservoirDistance_nonneg α q) _ hh
  intro N
  exact mul_le_mul_of_nonneg_right (reservoirRate_deficit_le α q N) (by positivity)

lemma fullRoot_reservoirDistance {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] {M : ℕ}
    (ξ : Fin M → Measure Y) [∀ i, IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (α s : ℝ≥0) (hα : 0 < α) (q N : ℕ) (hN : 0 < N) :
    BoundedDistance (fullRootLaw ξ μ ν (α*N) s)
      (fullRootLaw ξ μ ν (reservoirRate α q N) s) (reservoirDistance α q N) := by
  have he : reservoirRate α q N+(α*N-reservoirRate α q N)=α*N :=
    add_tsub_cancel_of_le (reservoirRate_le α q N)
  simpa only [he,reservoirDistance] using fullRoot_boundedDistance ξ μ ν
    (reservoirRate α q N) (α*N-reservoirRate α q N) s (reservoirRate_nonzero α hα q N hN)

end DilutedSpinGlass

end

end OAI
