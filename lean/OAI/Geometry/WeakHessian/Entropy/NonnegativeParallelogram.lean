import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology

namespace WeakHessianFunctional
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

structure NonnegativeParallelogram (q : V → ℝ) : Prop where
  nonneg : ∀ f, 0 ≤ q f
  smul : ∀ (a : ℝ) f, q (a • f) = a^2 * q f
  parallelogram : ∀ f g, q (f+g) + q (f-g) = 2 * q f + 2 * q g

def energyPolar (q : V → ℝ) (f g : V) : ℝ := (q (f+g) - q (f-g))/4

variable {q : V → ℝ} (hq : NonnegativeParallelogram q)
include hq

lemma NonnegativeParallelogram.zero : q 0 = 0 := by
  simpa only [zero_smul, zero_pow (by omega : (2:ℕ) ≠ 0), zero_mul] using hq.smul 0 (0:V)

lemma NonnegativeParallelogram.neg (f : V) : q (-f) = q f := by
  simpa using hq.smul (-1) f

lemma NonnegativeParallelogram.polar_comm (f g : V) : energyPolar q f g = energyPolar q g f := by
  have h : q (f-g) = q (g-f) := by rw [← neg_sub g f, hq.neg]
  simp only [energyPolar, add_comm f g, h]

lemma NonnegativeParallelogram.polar_add_left (f g h : V) :
    energyPolar q (f+g) h = energyPolar q f h + energyPolar q g h := by
  unfold energyPolar
  have h1 := hq.parallelogram (f+g+h) (f-h)
  have h2 := hq.parallelogram (f+g-h) (f+h)
  have h3 := hq.parallelogram (g+h) h
  have h4 := hq.parallelogram (g-h) h
  abel_nf at *
  simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_one] at *
  linarith

lemma NonnegativeParallelogram.polar_bound (f g : V) :
    |energyPolar q f g| ≤ (q f + q g)/2 := by
  rw [abs_le]
  have H := hq.parallelogram f g
  have hp := hq.nonneg (f+g)
  have hm := hq.nonneg (f-g)
  unfold energyPolar
  constructor <;> linarith

lemma NonnegativeParallelogram.polar_smul_left (a : ℝ) (f g : V) :
    energyPolar q (a • f) g = a * energyPolar q f g := by
  let T : ℝ →+ ℝ := AddMonoidHom.mk' (fun r => energyPolar q (r • f) g) (fun r s => by
    simpa only [add_smul] using hq.polar_add_left (r • f) (s • f) g)
  have hbound : IsBounded (T '' Metric.ball 0 1) := by
    apply (Metric.isBounded_closedBall (x := (0:ℝ)) (r := ((q f+q g)/2))).subset
    rintro y ⟨t, ht, rfl⟩
    change dist (energyPolar q (t • f) g) 0 ≤ (q f+q g)/2
    rw [Real.dist_eq, sub_zero]
    have H := hq.polar_bound (t • f) g
    rw [hq.smul] at H
    have ht' : |t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    have htsq : t^2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
    have hf := hq.nonneg f
    nlinarith
  have hcont : Continuous T := T.continuous_of_isBounded_nhds_zero (Metric.ball_mem_nhds 0 (by norm_num)) hbound
  have H := map_real_smul T hcont a (1:ℝ)
  simpa only [smul_eq_mul, mul_one, T, AddMonoidHom.mk'_apply, one_smul] using H

def NonnegativeParallelogram.bilin : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (energyPolar q) hq.polar_add_left hq.polar_smul_left
    (fun f g h => by rw [hq.polar_comm, hq.polar_add_left, hq.polar_comm g,
      hq.polar_comm h])
    (fun a f g => by
      simp only [smul_eq_mul]
      rw [hq.polar_comm, hq.polar_smul_left, hq.polar_comm g])

lemma NonnegativeParallelogram.polar_self (f : V) : energyPolar q f f = q f := by
  have H := hq.smul 2 f
  have heq : (2:ℝ) • f = f+f := by module
  rw [heq] at H
  simp only [energyPolar, sub_self, hq.zero]
  linarith

lemma NonnegativeParallelogram.polar_add (f g : V) :
    q (f+g) = q f + 2 * energyPolar q f g + q g := by
  have H := hq.parallelogram f g
  unfold energyPolar
  linarith

lemma NonnegativeParallelogram.polar_cauchySchwarz (f g : V) :
    (energyPolar q f g)^2 ≤ q f * q g := by
  have H : ∀ t : ℝ, 0 ≤ q f + 2*t*energyPolar q f g + t^2*q g := by
    intro t
    have h := hq.nonneg (f + t • g)
    rw [hq.polar_add, hq.polar_comm f, hq.polar_smul_left, hq.polar_comm g, hq.smul] at h
    nlinarith
  by_cases hg : q g = 0
  · have h1 := H (-(q f+1)/(2*energyPolar q f g))
    by_cases hp : energyPolar q f g = 0
    · simp [hp, hg]
    · have heq : q f + 2 * (-(q f+1)/(2*energyPolar q f g)) * energyPolar q f g +
          (-(q f+1)/(2*energyPolar q f g))^2 * q g = -1 := by
        rw [hg]
        field_simp [hp]
        ring
      rw [heq] at h1
      linarith
  · have h1 := H (-energyPolar q f g/q g)
    have hgpos : 0 < q g := lt_of_le_of_ne (hq.nonneg g) (Ne.symm hg)
    field_simp at h1
    nlinarith [sq_nonneg (energyPolar q f g)]

end WeakHessianFunctional

end
end InlinedFile0

end OAI
