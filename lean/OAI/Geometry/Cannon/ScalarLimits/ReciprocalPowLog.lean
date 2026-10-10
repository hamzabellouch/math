import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.ConnectedLimit

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open Set Filter Topology TopologicalSpace Metric

namespace CannonMeasureOscillation

open CannonScalarLimit Metric

lemma reciprocal_pow_log {a lam : ℝ} (ha : 1 < a) (hlam : 0 < lam) (l : ℕ) :
    ((a^l)⁻¹) ^ (Real.log lam / Real.log a) = (lam^l)⁻¹ := by
  have hap : 0 < a := zero_lt_one.trans ha
  have hlog : Real.log a ≠ 0 := (Real.log_pos ha).ne'
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos (inv_pos.mpr (pow_pos hap l)) _)
    (inv_pos.mpr (pow_pos hlam l))
  rw [Real.log_rpow (inv_pos.mpr (pow_pos hap l)),Real.log_inv,Real.log_inv,
    Real.log_pow,Real.log_pow]
  field_simp

theorem annular_to_holder {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : Set X) (hU : IsOpen U)
    (f : ℕ → C(U,ℝ)) (u : C(U,ℝ)) (μ : ℕ → FiniteMeasure X)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (a L E A lam : ℝ) (ha : 1 < a) (hL : 0 < L) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hlam : 1 < lam) (hmass : ∀ n, ((μ n).mass : ℝ) ≤ A)
    (hu : ∀ x, u x ∈ Icc (0:ℝ) 1)
    (hann : ∀ K : Set X, IsCompact K → K ⊆ U → ∃ l₀ m₀ : ℕ,
      ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n → ∀ o ∈ K, ∀ x y : U,
      dist x.val o ≤ (a^l)⁻¹/(2*L) → dist y.val o ≤ (a^l)⁻¹/(2*L) →
      (f n x-f n y)^2 ≤ (E/(lam^l))*(μ n {z | (a^l)⁻¹/4 ≤ dist z o ∧ dist z o ≤ 4*(a^l)⁻¹} : ℝ))
    (hf : Tendsto f atTop (𝓝 u)) :
    0 < Real.log lam/(2*Real.log a) ∧
      ∀ K : Set X, IsCompact K → K ⊆ U → ∃ D : ℝ, 0 ≤ D ∧
        ∀ x y : U, x.val ∈ K → y.val ∈ K →
          |u x-u y| ≤ D*(dist x y)^(Real.log lam/(2*Real.log a)) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let α := Real.log lam/(2*Real.log a)
  have hα : 0 < α := div_pos (Real.log_pos hlam) (mul_pos (by norm_num) (Real.log_pos ha))
  refine ⟨hα,fun K hK hKU => ?_⟩
  obtain ⟨l₀,m₀,hann⟩ := hann K hK hKU
  have hap : 0 < a := zero_lt_one.trans ha
  have hlamp : 0 < lam := zero_lt_one.trans hlam
  have hden : 0 < 2*L := by positivity
  let s₀ := (a^l₀)⁻¹/(2*L)
  have hs₀ : 0 < s₀ := by positivity
  let D₀ := Real.sqrt (E*A)*(a*(2*L))^α
  have hD₀ : 0 ≤ D₀ := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)
  refine ⟨max D₀ (s₀^α)⁻¹,le_trans hD₀ (le_max_left _ _),fun x y hx _hy => ?_⟩
  by_cases hxy : x = y
  · subst y
    simp only [sub_self,abs_zero,dist_self]
    positivity
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  by_cases hsmall : dist x y ≤ s₀
  · obtain ⟨l,hl,hl₁,hl₂⟩ := inverse_geometric_near ha l₀ (mul_pos hden hdist)
      (by simpa only [mul_comm] using (le_div_iff₀ hden).mp hsmall)
    have hinner : dist x y ≤ (a^l)⁻¹/(2*L) := (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hl₁)
    have hpair : (u x-u y)^2 ≤ (E/(lam^l))*A := by
      apply le_of_tendsto ((continuous_eval_const x).tendsto u |>.comp hf |>.sub
        ((continuous_eval_const y).tendsto u |>.comp hf) |>.pow 2)
      filter_upwards [hN.eventually (eventually_ge_atTop (l+m₀))] with n hn
      apply (hann l hl n hn x.val hx x y (by simp; positivity)
        (by simpa only [Subtype.dist_eq,dist_comm] using hinner)).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hE (pow_nonneg hlamp.le l))
      exact (show (μ n _ : ℝ) ≤ ((μ n).mass : ℝ) by exact_mod_cast (μ n).apply_le_mass _).trans
        (hmass n)
    have hid : ((a^l)⁻¹)^α * ((a^l)⁻¹)^α = (lam^l)⁻¹ := by
      rw [← Real.rpow_add (inv_pos.mpr (pow_pos hap l))]
      convert reciprocal_pow_log ha hlamp l using 1
      dsimp [α]
      field_simp
      ring_nf
    have hsq : (Real.sqrt (E*A)*((a^l)⁻¹)^α)^2 = (E/(lam^l))*A := by
      rw [mul_pow,Real.sq_sqrt (mul_nonneg hE hA),pow_two,hid]
      ring
    have hnear : |u x-u y| ≤ Real.sqrt (E*A)*((a^l)⁻¹)^α := by
      have hnn : 0 ≤ Real.sqrt (E*A)*((a^l)⁻¹)^α := by positivity
      have habs : |u x-u y|^2 = (u x-u y)^2 := sq_abs _
      nlinarith
    have hrpow := Real.rpow_le_rpow (inv_nonneg.mpr (pow_nonneg hap.le l)) hl₂.le hα.le
    have hround : Real.sqrt (E*A)*((a^l)⁻¹)^α ≤ D₀*(dist x y)^α := by
      apply (mul_le_mul_of_nonneg_left hrpow (Real.sqrt_nonneg _)).trans_eq
      dsimp [D₀]
      rw [show a*(2*L*dist x y) = (a*(2*L))*dist x y by ring,
        Real.mul_rpow (by positivity) hdist.le]
      ring
    exact (hnear.trans hround).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hdist.le _))
  · have hpow : s₀^α ≤ (dist x y)^α := Real.rpow_le_rpow hs₀.le (le_of_not_ge hsmall) hα.le
    have hone : 1 ≤ (s₀^α)⁻¹*(dist x y)^α := by
      have hp : 0 < s₀^α := Real.rpow_pos_of_pos hs₀ _
      calc
        1 = (s₀^α)⁻¹*s₀^α := (inv_mul_cancel₀ hp.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hp.le)
    have hunit : |u x-u y| ≤ 1 := abs_le.mpr ⟨by linarith [(hu x).1,(hu y).2],by linarith [(hu x).2,(hu y).1]⟩
    exact hunit.trans (hone.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hdist.le _)))

end CannonMeasureOscillation

end
end
end
end
end
end
end
end
end

end OAI
