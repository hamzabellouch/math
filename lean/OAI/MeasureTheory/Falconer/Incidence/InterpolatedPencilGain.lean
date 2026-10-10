import OAI.MeasureTheory.Falconer.Incidence.InterpolatedIncidence
import OAI.MeasureTheory.Falconer.Geometry.ProjectionSampleBudget

namespace OAI

/-! A large pencil supplies the extra normalized gain at a regular scale.
This retains the actual minimum pencil size and the loss from unequal sizes. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem interpolated_pencil_normalized (N : ℕ) {s t u θ K m R : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hut : u < t) (hK : 1 ≤ K)
    (hm : 0 < m) (hR : 0 ≤ R) (hθ : 0 < θ) (hθ1 : θ < 1)
    (he : s*θ+2*(1-θ) = u)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ R*m ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m*m^(1-θ) ≤ ((P.biUnion T).card:ℝ)*
      (((K*(80*(1/(2:ℝ)^N))^s*R)^θ*(25921:ℝ)^(1-θ))*
        (1+K*planarPotentialConstant u t)) := by
  have hb := planar_interpolated_incidence N hs hu hut hK hm.le hθ hθ1 he
    P T hP hPchart hPball hT
  have heq : (K*(80*(1/(2:ℝ)^N))^s*(R*m))^θ =
      (K*(80*(1/(2:ℝ)^N))^s*R)^θ*m^θ := by
    rw [← mul_assoc,Real.mul_rpow (by positivity) hm.le]
  rw [heq] at hb
  have hmexp : m^(1-θ)*m^θ = m := by
    rw [← Real.rpow_add hm]
    norm_num
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hm θ)).1
  convert hb using 1
  · rw [mul_assoc,hmexp,pow_two]
  · ring

theorem large_pencil_growth (N : ℕ) {κ s t K m : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) (hs : 0 ≤ s) (hs1 : s ≤ 1-8*κ)
    (hgap : 2*κ ≤ t-s) (hK : 1 ≤ K) (hm : 0 < m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ K*m ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m*m^(κ/2) ≤ ((P.biUnion T).card:ℝ)*
      ((80*25921*(1+projectionGapConstant κ))*K^3*
        (1/(2:ℝ)^N)^(s*(1-κ/2))) := by
  let θ := 1-κ/2
  let u := s*θ+2*(1-θ)
  have hθ : 0 < θ := by dsimp [θ]; linarith only [hκ1]
  have hθ1 : θ < 1 := by dsimp [θ]; linarith only [hκ]
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hugap : κ ≤ t-u := by
    dsimp [u,θ]
    nlinarith only [hgap,mul_nonneg hs hκ.le]
  have hu1 : u ≤ 1 := by
    dsimp [u,θ]
    nlinarith only [hs1,hκ,mul_nonneg hs hκ.le]
  have hut : u < t := by linarith only [hugap,hκ]
  have hb := interpolated_pencil_normalized N hs hu hut hK hm
    (zero_le_one.trans hK) hθ hθ1 rfl P T hP hPchart hPball hT
  have hH := projectionGapConstant_pos hκ
  have hpot := planarPotentialConstant_gap hκ hu1 hugap
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have h80 : (80:ℝ)^s ≤ 80 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num) (show s ≤ 1 by linarith only [hs1,hκ])).trans
    norm_num
  have hKθ : (K*K)^θ ≤ K^2 := by
    simpa only [Real.rpow_one,pow_two] using
      Real.rpow_le_rpow_of_exponent_le (show 1 ≤ K*K by nlinarith only [hK]) hθ1.le
  have h80θ : ((80:ℝ)^s)^θ ≤ 80 := by
    calc
      _ ≤ (80:ℝ)^θ := Real.rpow_le_rpow (by positivity) h80 hθ.le
      _ ≤ 80 := by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 80) hθ1.le
  have hB : (25921:ℝ)^(1-θ) ≤ 25921 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 25921) (show 1-θ ≤ 1 by linarith only [hθ])
  have hker : (K*(80*(1/(2:ℝ)^N))^s*K)^θ ≤
      80*K^2*(1/(2:ℝ)^N)^(s*θ) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hδ.le]
    rw [show K*((80:ℝ)^s*(1/(2:ℝ)^N)^s)*K =
      ((K*K)*(80:ℝ)^s)*(1/(2:ℝ)^N)^s by ring,
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul hδ.le]
    calc
      _ ≤ K^2*80*(1/(2:ℝ)^N)^(s*θ) := by gcongr
      _ = _ := by ring
  have hpotbound : 1+K*planarPotentialConstant u t ≤ K*(1+projectionGapConstant κ) := by
    nlinarith only [mul_le_mul_of_nonneg_left hpot hK0.le,hK]
  have hbound : ((K*(80*(1/(2:ℝ)^N))^s*K)^θ*(25921:ℝ)^(1-θ))*
      (1+K*planarPotentialConstant u t) ≤
        (80*25921*(1+projectionGapConstant κ))*K^3*(1/(2:ℝ)^N)^(s*θ) := by
    calc
      _ ≤ (80*K^2*(1/(2:ℝ)^N)^(s*θ))*25921*(K*(1+projectionGapConstant κ)) := by
        apply mul_le_mul
        · exact mul_le_mul hker hB (by positivity) (by positivity)
        · exact hpotbound
        · have hp := planarPotentialConstant_pos hut; positivity
        · positivity
      _ = _ := by ring
  have hexp : 1-θ = κ/2 := by dsimp [θ]; ring
  rw [hexp] at hb hbound
  exact hb.trans (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _))

end Falconer

end OAI
