import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CubeGeometry
import OAI.Probability.MemoryPrecision.WeightedImage
import OAI.Probability.MemoryPrecision.WeightedSelection

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma cube_J_bound {d k : ℕ} (hd : 16 ≤ d) (hk : k ≤ (d/2)/4) :
    ∀ j : ℕ, j ≤ (d/2)/4-2 → J (3*(d/2:ℕ)/4:ℝ) k j ≤ (7:ℝ)^d := by
  have hp2 : 2 ≤ (d/2)/4 := by omega
  have hn4 : (((d/2)/4:ℕ):ℝ)*4 ≤ (d/2:ℕ) := by exact_mod_cast Nat.div_mul_le_self (d/2) 4
  have hn : ((d/2:ℕ):ℝ) ≤ d := by exact_mod_cast Nat.div_le_self d 2
  have hm : (k:ℝ) ≤ ((d/2)/4:ℕ) := by exact_mod_cast hk
  intro j hj
  have hj' : (j:ℝ)+2 ≤ ((d/2)/4:ℕ) := by exact_mod_cast (show j+2 ≤ (d/2)/4 by omega)
  have hgap : 0 < (3*(d/2:ℕ)/4:ℝ)-(j:ℝ)-(k:ℝ) := by linarith
  have hquot : (k:ℝ)/((3*(d/2:ℕ)/4:ℝ)-(j:ℝ)-(k:ℝ)) ≤ 1 := by
    rw [div_le_one hgap]
    linarith
  have h3 : (3:ℝ)^j ≤ (3:ℝ)^d := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2:ℝ)^(3*(d/2:ℕ)/4:ℝ) ≤ (2:ℝ)^d := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  calc
    J (3*(d/2:ℕ)/4:ℝ) k j = 1+(3:ℝ)^j*(2:ℝ)^(3*(d/2:ℕ)/4:ℝ)*
      ((k:ℝ)/((3*(d/2:ℕ)/4:ℝ)-(j:ℝ)-(k:ℝ))) := by unfold J; ring
    _ ≤ 1+(3:ℝ)^j*(2:ℝ)^(3*(d/2:ℕ)/4:ℝ)*1 := by gcongr
    _ ≤ 1+(3:ℝ)^d*(2:ℝ)^d := by rw [mul_one]; gcongr
    _ = 1+(6:ℝ)^d := by rw [← mul_pow]; norm_num
    _ ≤ (7:ℝ)^d := by
      simpa only [one_pow, show (1:ℝ)+6=7 by norm_num] using
        pow_add_pow_le (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 6 by norm_num) (show d ≠ 0 by omega)

lemma cube_weighted_ambient {d : ℕ} (hd : 2 ≤ d) {f : Cube d → ℝ≥0∞}
    {L : ℝ} (hf : CubeLocal f L) :
    AmbientBallBound (((CubeLaw d).withDensity f).map (CubeEmbedding d)) L (3*(d/2:ℕ)/4:ℝ) := by
  intro x r hr
  rw [weighted_image_ball _ (cubeEmbedding_measurable d)]
  apply (lintegral_mono_set (show {u | dist (CubeEmbedding d u) x ≤ r} ⊆
    CubeBall d (Real.sqrt (d/2:ℕ) • cubeProject d x) r from ?_)).trans
    (hf _ _ hr)
  intro u hu
  exact (cubeProject_parameter_dist hd u x).trans
    (mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg _))

lemma cubeBall_embedding_subset {d : ℕ} (hd : 2 ≤ d) (z : Space (d/2)) {r : ℝ}
    (u₀ : Cube d) (hu₀ : u₀ ∈ CubeBall d z r) :
    CubeBall d z r ⊆ CubeEmbedding d ⁻¹' Metric.closedBall (CubeEmbedding d u₀) (4*r) := by
  have hs : 0 < Real.sqrt (d/2:ℕ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d/2 by omega))
  intro u hu
  have hu' : dist u.val z ≤ Real.sqrt (d/2:ℕ)*r := hu
  have hu₀' : dist u₀.val z ≤ Real.sqrt (d/2:ℕ)*r := hu₀
  have hab : dist u.val u₀.val ≤ 2*Real.sqrt (d/2:ℕ)*r := by
    have := dist_triangle u.val z u₀.val
    rw [dist_comm z u₀.val] at this
    linarith
  apply (cubeEmbedding_dist hd u u₀).trans
  calc
    _ ≤ 2/Real.sqrt (d/2:ℕ)*(2*Real.sqrt (d/2:ℕ)*r) :=
      mul_le_mul_of_nonneg_left hab (by positivity)
    _ = 4*r := by field_simp [ne_of_gt hs]; ring

lemma weightedBlock_le_sum {X : Type*} {d m N : ℕ}
    (ι : X → Space d) (f : Fin N → X → ℝ≥0∞)
    {g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞}
    (hg : ∀ x, ∑ w, g w x ≤ 1) (x : X) : WeightedBlock ι f g x ≤ ∑ w, f w x := by
  unfold WeightedBlock
  calc
    _ ≤ ∫⁻ _A : Fin m → Space d, (∑ w, f w x) ∂Measure.pi (fun _ => stdGaussian (Space d)) := by
      apply lintegral_mono
      intro A
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_of_le_one_left' ((Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ w)).trans (hg _))
    _ = _ := by simp

def CubeBlockConstant : ℝ := 4*1344^3
lemma cubeBlockConstant_one : 1 ≤ CubeBlockConstant := by norm_num [CubeBlockConstant]

lemma cube_constant_scale {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) :
    (1344:ℝ)^d * (4*r)^(3*(d/2:ℕ)/4:ℝ) ≤ CubeBlockConstant^(d/2) * r^(3*(d/2:ℕ)/4:ℝ) := by
  rw [Real.mul_rpow (by norm_num) hr.le]
  have hp : (1344:ℝ)^d ≤ (1344^3:ℝ)^(d/2) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have h4 : (4:ℝ)^(3*(d/2:ℕ)/4:ℝ) ≤ (4:ℝ)^(d/2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := Nat.cast_nonneg (α := ℝ) (d/2)
    linarith
  calc
    _ = ((1344:ℝ)^d*(4:ℝ)^(3*(d/2:ℕ)/4:ℝ))*r^(3*(d/2:ℕ)/4:ℝ) := by ring
    _ ≤ ((1344^3:ℝ)^(d/2)*(4:ℝ)^(d/2))*r^(3*(d/2:ℕ)/4:ℝ) := by gcongr
    _ = _ := by rw [← mul_pow]; congr 2; norm_num [CubeBlockConstant]

def CubeBlockStatement : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ d k N : ℕ, 16 ≤ d → 1 ≤ k → k ≤ (d/2)/4 → 1 ≤ N →
    ∀ L : ℝ, 0 ≤ L → ∀ f : Fin N → Cube d → ℝ≥0∞,
      (∀ v, Measurable (f v)) → (∀ v u, f v u ≤ 1) → (∀ v, CubeLocal (f v) L) →
    ∀ g : Fin N → ((Fin k → Space d) × (Fin k → ℝ)) → ℝ≥0∞,
      (∀ v, Measurable (g v)) → (∀ x, ∑ v, g v x ≤ 1) →
      CubeLocal (WeightedBlock (CubeEmbedding d) f g)
        (C^(d/2) * (N:ℝ)^(1/(((d/2)/4:ℕ):ℝ)) * L)
theorem cube_block : CubeBlockStatement := by
  refine ⟨CubeBlockConstant, cubeBlockConstant_one, ?_⟩
  intro d k N hd hk hkp hN L hL f hf hf1 hloc g hg hgs z r hr
  by_cases hL0 : L = 0
  · simp only [hL0, mul_zero, zero_mul, ENNReal.ofReal_zero]
    calc
      _ ≤ ∫⁻ u in CubeBall d z r, ∑ w, f w u ∂CubeLaw d :=
        lintegral_mono (weightedBlock_le_sum _ _ hgs)
      _ = ∑ w, ∫⁻ u in CubeBall d z r, f w u ∂CubeLaw d :=
        lintegral_finsetSum _ (fun w _ => hf w)
      _ ≤ ∑ _w : Fin N, ENNReal.ofReal (L*r^(3*(d/2:ℕ)/4:ℝ)) :=
        Finset.sum_le_sum (fun w _ => hloc w z r hr)
      _ = 0 := by simp [hL0]
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
  by_cases hempty : CubeBall d z r = ∅
  · simp [hempty]
  obtain ⟨u₀,hu₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  let ν (w : Fin N) := ((CubeLaw d).withDensity (f w)).map (CubeEmbedding d)
  let (w : Fin N) : IsFiniteMeasure (ν w) := weighted_image_finite (CubeLaw d) (CubeEmbedding d) (f w) (hf1 w)
  have hν w : AmbientBallBound (ν w) L (3*(d/2:ℕ)/4:ℝ) := cube_weighted_ambient (by omega) (hloc w)
  have hp : 2 ≤ (d/2)/4 := by omega
  have hkd : k ≤ d := by omega
  have hgap : (k:ℝ)+(((d/2)/4:ℕ):ℝ)-2 < (3*(d/2:ℕ)/4:ℝ) := by
    have hp' : (((d/2)/4:ℕ):ℝ)*4 ≤ (d/2:ℕ) := by exact_mod_cast Nat.div_mul_le_self (d/2) 4
    have hk' : (k:ℝ) ≤ ((d/2)/4:ℕ) := by exact_mod_cast hkp
    have hn' : (8:ℝ) ≤ (d/2:ℕ) := by exact_mod_cast (show 8 ≤ d/2 by omega)
    linarith
  have hsel := localized_weighted_selection ν hp hk hkd (by norm_num : (1:ℝ) ≤ 7)
    hLpos hgap (cube_J_bound hd hkp) hν g hg hgs (CubeEmbedding d u₀) (by positivity : 0 < 4*r)
  have he := weightedBlock_mass_identity (CubeLaw d) (cubeEmbedding_measurable d) hf hf1 hg
    (show MeasurableSet (Metric.closedBall (CubeEmbedding d u₀) (4*r)) from Metric.isClosed_closedBall.measurableSet)
  apply (lintegral_mono_set (cubeBall_embedding_subset (by omega) z u₀ hu₀)).trans
  rw [he]
  apply hsel.trans (ENNReal.ofReal_le_ofReal ?_)
  have hscale := cube_constant_scale (d := d) (by omega) hr
  norm_num only [show (7:ℝ)*192=1344 by norm_num]
  calc
    _ = ((1344:ℝ)^d*(4*r)^(3*(d/2:ℕ)/4:ℝ))*((N:ℝ)^(1/(((d/2)/4:ℕ):ℝ))*L) := by ring
    _ ≤ (CubeBlockConstant^(d/2)*r^(3*(d/2:ℕ)/4:ℝ))*((N:ℝ)^(1/(((d/2)/4:ℕ):ℝ))*L) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = _ := by ring
end MemoryPrecision


end

end OAI
