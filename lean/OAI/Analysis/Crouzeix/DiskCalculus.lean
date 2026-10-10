import Mathlib
import OAI.Analysis.Crouzeix.Fourier
import OAI.Analysis.Crouzeix.Resolvent
import OAI.Analysis.Crouzeix.SteinMetric

namespace OAI

/-! Disk Calculus. -/

noncomputable section

open MeasureTheory

open scoped Topology

namespace CrouzeixHilbert.Disk

abbrev CircleSpace := AddCircle (1 : ℝ)

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev σ : Measure CircleSpace := AddCircle.haarAddCircle

section Series

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem inverse_one_sub_of_summable (a : A) (hs : Summable (fun n : ℕ => a ^ n)) :
    IsUnit (1 - a) ∧ Ring.inverse (1 - a) = ∑' n : ℕ, a ^ n := by
  let u : Aˣ := ⟨1 - a, ∑' n : ℕ, a ^ n, hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩
  refine ⟨⟨u, rfl⟩, ?_⟩
  change Ring.inverse (u : A) = _
  rw [Ring.inverse_unit]
  rfl

lemma norm_fourier (n : ℤ) (t : CircleSpace) : ‖fourier n t‖ = 1 := Circle.norm_coe _

lemma fourier_one_pow (n : ℕ) (t : CircleSpace) :
    (fourier 1 t) ^ n = fourier (n : ℤ) t := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, fourier_add]

lemma inverse_fourier_pow (n : ℕ) (t : CircleSpace) :
    ((fourier 1 t)⁻¹) ^ n = fourier (-(n : ℤ)) t := by
  rw [Complex.inv_eq_conj (norm_fourier _ _), ← map_pow, fourier_one_pow, fourier_neg]

lemma summable_diskPowers (D : A) (hD : spectralRadius ℂ D < 1) (t : CircleSpace) :
    Summable (fun n : ℕ => ((fourier 1 t)⁻¹ • D) ^ n) := by
  apply (Metric.summable_norm_pow D hD).of_norm_bounded
  intro n
  simp only [smul_pow, norm_smul, norm_pow, norm_inv, norm_fourier,
    inv_one, one_pow, one_mul, le_refl]

lemma disk_inverse_series (D : A) (hD : spectralRadius ℂ D < 1) (t : CircleSpace) :
    Ring.inverse (1 - (fourier 1 t)⁻¹ • D) =
      ∑' n : ℕ, fourier (-(n : ℤ)) t • D ^ n := by
  rw [(inverse_one_sub_of_summable _ (summable_diskPowers D hD t)).2]
  simp only [smul_pow, inverse_fourier_pow]

lemma continuous_diskInverse (D : A) (hD : spectralRadius ℂ D < 1) :
    Continuous (fun t : CircleSpace => Ring.inverse (1 - (fourier 1 t)⁻¹ • D)) := by
  simp_rw [disk_inverse_series D hD]
  refine continuous_tsum (fun n => (fourier _).continuous.smul continuous_const)
    (Metric.summable_norm_pow D hD) ?_
  intro n t
  simp only [norm_smul, norm_fourier, one_mul, le_refl]

lemma integral_fourier (n : ℤ) : ∫ t : CircleSpace, fourier n t ∂σ = if n = 0 then 1 else 0 := by
  have h := congrFun (@fourierCoeff_fourier 1 _ n) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Pi.single_apply,
    eq_comm] using h

lemma integral_fourier_smul (a : A) (n : ℤ) :
    ∫ t : CircleSpace, fourier n t • a ∂σ = if n = 0 then a else 0 := by
  rw [integral_smul_const, integral_fourier]
  split_ifs <;> simp

lemma integral_fourier_series (a : ℕ → A) (ha : Summable (fun n => ‖a n‖)) (k : ℕ → ℤ) :
    (∫ t : CircleSpace, ∑' n : ℕ, fourier (k n) t • a n ∂σ) =
      ∑' n : ℕ, if k n = 0 then a n else 0 := by
  rw [← integral_tsum_of_summable_integral_norm]
  · simp only [integral_fourier_smul]
  · intro n
    exact ((fourier _).continuous.smul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · simpa only [norm_smul, norm_fourier, one_mul, integral_const, probReal_univ, one_smul] using ha

end Series

section Density

variable {A : Type*} [CStarAlgebra A]

def phi (D : A) (t : CircleSpace) : A :=
  Ring.inverse (1 - (fourier 1 t)⁻¹ • D) +
    star (Ring.inverse (1 - (fourier 1 t)⁻¹ • D)) - 1

theorem continuous_phi (D : A) (hD : spectralRadius ℂ D < 1) : Continuous (phi D) :=
  ((continuous_diskInverse D hD).add (continuous_diskInverse D hD).star).sub continuous_const

theorem integrable_phi (D : A) (hD : spectralRadius ℂ D < 1) : Integrable (phi D) σ :=
  (continuous_phi D hD).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma phi_series (D : A) (hD : spectralRadius ℂ D < 1) (t : CircleSpace) :
    phi D t = (∑' n : ℕ, fourier (-(n : ℤ)) t • D ^ n) +
      (∑' n : ℕ, fourier (n : ℤ) t • star (D ^ n)) - 1 := by
  simp only [phi, disk_inverse_series D hD, tsum_star, star_smul, fourier_neg,
    starRingEnd_apply, star_star]

theorem integral_moment (D : A) (hD : spectralRadius ℂ D < 1) (j : ℕ) :
    ∫ t : CircleSpace, fourier (j : ℤ) t • phi D t ∂σ = D ^ j := by
  have hc₁ := continuous_diskInverse D hD
  have hi₁ : Integrable (fun t : CircleSpace => Ring.inverse (1 - (fourier 1 t)⁻¹ • D)) σ :=
    hc₁.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi₂ : Integrable (fun t : CircleSpace =>
      star (Ring.inverse (1 - (fourier 1 t)⁻¹ • D))) σ :=
    hc₁.star.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := Metric.summable_norm_pow D hD
  have hs' : Summable (fun n : ℕ => ‖star (D ^ n)‖) := by simpa only [norm_star] using hs
  have hleft : (∫ t : CircleSpace,
      fourier (j : ℤ) t • Ring.inverse (1 - (fourier 1 t)⁻¹ • D) ∂σ) = D ^ j := by
    simp_rw [disk_inverse_series D hD, ← tsum_const_smul'', smul_smul, ← fourier_add]
    rw [integral_fourier_series _ hs]
    convert tsum_ite_eq j (fun n : ℕ => D ^ n) using 1
    congr 1
    ext n
    simp only [add_neg_eq_zero, Nat.cast_inj, eq_comm]
  have hright : (∫ t : CircleSpace,
      fourier (j : ℤ) t • star (Ring.inverse (1 - (fourier 1 t)⁻¹ • D)) ∂σ) =
        if j = 0 then 1 else 0 := by
    simp_rw [disk_inverse_series D hD, tsum_star, star_smul, fourier_neg,
      starRingEnd_apply, star_star, ← tsum_const_smul'', smul_smul, ← fourier_add]
    rw [integral_fourier_series _ hs']
    by_cases hj : j = 0
    · simp [hj]
    · rw [ite_eq_right hj]
      have hz : ∀ n : ℕ, (if (j : ℤ) + (n : ℤ) = 0 then star (D ^ n) else 0) = 0 := by
        intro n
        simp only [← Nat.cast_add, Nat.cast_eq_zero, Nat.add_eq_zero_iff,
          hj, false_and, ↓reduceIte]
      simp only [hz, tsum_zero]
  simp only [phi, smul_sub, smul_add]
  have hsplit := integral_sub ((hi₁.fourier_smul (j : ℤ)).add
    (hi₂.fourier_smul (j : ℤ))) ((integrable_const (1 : A)).fourier_smul (j : ℤ))
  simp only [Pi.add_apply] at hsplit
  rw [hsplit, integral_add (hi₁.fourier_smul (j : ℤ)) (hi₂.fourier_smul (j : ℤ)),
    hleft, hright, integral_fourier_smul]
  simp only [Nat.cast_eq_zero, add_sub_cancel_right]

theorem integral_phi (D : A) (hD : spectralRadius ℂ D < 1) : ∫ t, phi D t ∂σ = 1 := by
  simpa only [Nat.cast_zero, fourier_zero, one_smul, pow_zero] using integral_moment D hD 0

end Density

section OperatorPositivity

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem phi_isPositive (D : Operator H) (hn : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (t : CircleSpace) : (phi D t).IsPositive := by
  exact isPositive_diskDensity D hn (fourier 1 t) (norm_fourier _ _)
    (inverse_one_sub_of_summable _ (summable_diskPowers D hD t)).1

end OperatorPositivity

end CrouzeixHilbert.Disk

end

end OAI
