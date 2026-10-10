import Mathlib
import OAI.Geometry.CAT0Fillings.Isoperimetry.SmallSets
import OAI.Geometry.CAT0Fillings.Sobolev.SmallSupport
import OAI.Geometry.CAT0Fillings.Sobolev.Truncation

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open BorelRestriction MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem almost_sobolev_from_small {n : ℕ} {T : Functional X n}
    {hT : IsMetricCurrent T} (q : ChartGeometry hT) {S B p : ℝ}
    (hS : 0 < S) (hB : 0 ≤ B) (hp : 1 < p)
    (hsmall : ∀ η ∈ Ioo (0:ℝ) 1, ∃ δ > 0,
      ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u → (∀ x, 0 ≤ u x) →
        (currentMassMeasure hT).real {x | 0 < u x} ≤ δ →
        S*(1-η)^2*lpNorm u (ENNReal.ofReal p) (currentMassMeasure hT)^2 ≤
          B*(q.energyMeasure u).real univ)
    {ε : ℝ} (hε : 0 < ε) (hεS : ε < S) :
    ∃ C ≥ (0:ℝ), ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
      (S-ε)*lpNorm u (ENNReal.ofReal p) (currentMassMeasure hT)^2 ≤
        B*(q.energyMeasure u).real univ + C*lpNorm u 2 (currentMassMeasure hT)^2 := by
  let μ := currentMassMeasure hT
  let t := ε/(4*S)
  have ht : 0 < t := div_pos hε (by positivity)
  have ht1 : t < 1 := (div_lt_one (by positivity : 0 < 4*S)).mpr (by linarith)
  have het : ε = 4*S*t := by dsimp [t]; field_simp
  obtain ⟨δ,hδ,hs⟩ := hsmall t ⟨ht,ht1⟩
  let A := S*(1-t)^2
  let d := μ.real univ ^ (ENNReal.ofReal p).toReal⁻¹ / Real.sqrt δ
  have hA : 0 < A := mul_pos hS (sq_pos_of_pos (sub_pos.mpr ht1))
  have hd : 0 ≤ d := by positivity
  have hcoeff : (S-ε)*(1+t) ≤ A := by
    dsimp only [A]
    rw [het]
    nlinarith [mul_nonneg hS.le (sq_nonneg t),mul_nonneg hS.le ht.le]
  refine ⟨A/t*d^2,by positivity,?_⟩
  intro u K hu
  have hu2n : 0 ≤ lpNorm u 2 μ := lpNorm_nonneg
  by_cases hu2 : lpNorm u 2 μ = 0
  · have haz := (lpNorm_eq_zero (continuous_memLp μ hu.continuous 2) (by norm_num)).mp hu2
    have hpz : lpNorm u (ENNReal.ofReal p) μ = 0 :=
      (lpNorm_eq_zero (continuous_memLp μ hu.continuous _) (by positivity)).mpr haz
    change (S-ε)*lpNorm u (ENNReal.ofReal p) μ^2 ≤ _
    rw [hpz]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact add_nonneg (mul_nonneg hB (measureReal_nonneg))
      (mul_nonneg (by positivity) (sq_nonneg _))
  have hu2p : 0 < lpNorm u 2 μ := lt_of_le_of_ne hu2n (Ne.symm hu2)
  let τ := lpNorm u 2 μ / Real.sqrt δ
  let z := positiveTrunc τ ∘ u
  have hτ : 0 ≤ τ := by positivity
  have hz := (positiveTrunc_lipschitz τ).comp hu
  have hsup := truncation_small_support μ hu.continuous hδ hu2p
  have hpos : ∀ x, 0 ≤ z x := fun x => le_max_right _ _
  have hzs := hs z (1*K) hz hpos hsup
  have henergy := q.energy_trunc_le hu hτ
  have hbound := hzs.trans (mul_le_mul_of_nonneg_left henergy hB)
  have hnorm := truncation_norm_bound μ hu.continuous
    (show 1 ≤ ENNReal.ofReal p by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le) ENNReal.ofReal_ne_top hτ
  have he : μ.real univ ^ (ENNReal.ofReal p).toReal⁻¹ * τ = d*lpNorm u 2 μ := by
    dsimp [τ,d]
    ring
  rw [he] at hnorm
  have hnormsq : lpNorm u (ENNReal.ofReal p) μ^2 ≤
      (lpNorm z (ENNReal.ofReal p) μ+d*lpNorm u 2 μ)^2 := by
    apply (sq_le_sq₀ lpNorm_nonneg (add_nonneg lpNorm_nonneg (mul_nonneg hd hu2n))).mpr hnorm
  have hyoung : (lpNorm z (ENNReal.ofReal p) μ+d*lpNorm u 2 μ)^2 ≤
      (1+t)*lpNorm z (ENNReal.ofReal p) μ^2+
        (1+t⁻¹)*(d*lpNorm u 2 μ)^2 := by
    apply (mul_le_mul_iff_right₀ ht).mp
    have hh := sq_nonneg (t*lpNorm z (ENNReal.ofReal p) μ-d*lpNorm u 2 μ)
    have hinv : t*t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    nlinarith
  have hbig := hnormsq.trans hyoung
  have hdiv : (S-ε) ≤ A/(1+t) := (le_div_iff₀ (by linarith)).mpr hcoeff
  have hmul := mul_le_mul_of_nonneg_left hbig (show 0 ≤ A/(1+t) from le_of_lt (div_pos hA (by linarith)))
  have hid : A/(1+t)*((1+t)*lpNorm z (ENNReal.ofReal p) μ^2+
      (1+t⁻¹)*(d*lpNorm u 2 μ)^2) =
      A*lpNorm z (ENNReal.ofReal p) μ^2+A/t*d^2*lpNorm u 2 μ^2 := by
    field_simp
    ring
  rw [hid] at hmul
  have hlo := mul_le_mul_of_nonneg_right hdiv (sq_nonneg (lpNorm u (ENNReal.ofReal p) μ))
  exact (hlo.trans hmul).trans (add_le_add hbound le_rfl)

theorem extremal_almost_sobolev {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (q : ChartGeometry hT.1) {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B))
    {ε : ℝ} (hε : 0 < ε) (hεS : ε < (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))) :
    ∃ C ≥ (0:ℝ), ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
      ((k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))-ε)*
        lpNorm u (ENNReal.ofReal (sobolevP (k+2))) (currentMassMeasure hT.1)^2 ≤
      4/((k+2:ℝ)-2)*(q.energyMeasure u).real univ +
        C*lpNorm u 2 (currentMassMeasure hT.1)^2 := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hB : 0 ≤ 4/((k+2:ℝ)-2) := div_nonneg (by norm_num) (by linarith)
  have hS : 0 < (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ)) := by
    have hω := omega_pos (by omega : 0 < k+2+1)
    unfold sphereArea
    positivity
  have hp : 1 < sobolevP (k+2) := by
    unfold sobolevP
    push_cast
    apply (lt_div_iff₀ (sub_pos.mpr hn)).mpr
    linarith
  apply almost_sobolev_from_small q hS hB hp ?_ hε hεS
  intro η hη
  have hpfill : 1 < fillingPower (k+1) := by
    unfold fillingPower
    push_cast
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith
  obtain ⟨δ,hδ,hi⟩ := small_restriction_mass_bound hX
    (fillingCoefficient_pos (by omega : 0 < k+1)).le hpfill hd hr hfill hT hz hm hext hη.1 hη.2
  refine ⟨δ,hδ.1,?_⟩
  intro u K hu hu0 hsupp
  have hh := small_support_sobolev hk hT hz hX q hη.1 hη.2 hi hu hu0 hsupp
  rw [←lpNorm_sq_moment (currentMassMeasure hT.1) hu.continuous hu0
    (lt_trans zero_lt_one hp)] at hh
  have hb := mul_le_mul_of_nonneg_left hh (sq_nonneg (1-η))
  have he : (1-η)^2 * (4/((k+2:ℝ)-2)*((1-η)⁻¹)^2*(q.energyMeasure u).real univ) =
      4/((k+2:ℝ)-2)*(q.energyMeasure u).real univ := by
    field_simp [(sub_pos.mpr hη.2).ne']
  rw [he] at hb
  nlinarith

end CAT0Fillings
end

end OAI
