import Mathlib
import OAI.Computability.MinUncut.Estimates.FaceUpdateSelf
import OAI.Computability.MinUncut.Estimates.Away

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.CubeRows
open BinaryFourier IndependentSquares
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι A W : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype W] [AddCommGroup W] [Module F₂ W]

omit [DecidableEq ι] [Fintype A] [Nonempty A] in
lemma collision_indicator (x y : ι → A) :
    (if ∃ i, x i=y i then (1:ℝ) else 0) ≤ ∑ i, if x i=y i then (1:ℝ) else 0 := by
  by_cases h : ∃ i, x i=y i
  · obtain ⟨i,hi⟩ := h
    simpa only [ite_eq_left (show ∃ j, x j=y j from ⟨i,hi⟩),ite_eq_left hi] using
      (Finset.single_le_sum (s := Finset.univ) (f := fun i => if x i=y i then (1:ℝ) else 0)
        (fun _ _ => by positivity) (Finset.mem_univ i))
  · simp only [ite_eq_right h]; exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma collision_probability :
    (𝔼 x : ι → A, 𝔼 y : ι → A, if ∃ i, x i=y i then (1:ℝ) else 0) ≤
      (Fintype.card ι:ℝ)/Fintype.card A := by
  have hf (x : ι → A) :
      (𝔼 y : ι → A, if ∃ i, x i=y i then (1:ℝ) else 0) ≤
        (Fintype.card ι:ℝ)/Fintype.card A := by
    calc
      _ ≤ 𝔼 y : ι → A, ∑ i, if x i=y i then (1:ℝ) else 0 :=
        Finset.expect_le_expect (fun y _ => collision_indicator x y)
      _ = ∑ i : ι, 𝔼 a : A, if x i=a then (1:ℝ) else 0 := by
        rw [Finset.expect_sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        exact Subbox.expect_coordinate (B := fun _ : ι => A) i (fun a => if x i=a then (1:ℝ) else 0)
      _ = _ := by simp [div_eq_mul_inv]
  exact (Finset.expect_le_expect (fun x _ => hf x)).trans_eq (Fintype.expect_const _)

omit [Nonempty A] [Module F₂ W] in
lemma cubeExpectation_abs_bound (i j : ι) (x y : ι → A)
    (V : (ι → Bool) → W → ℝ) {C : ℝ} (hC : 0≤C) (hV : ∀ ν w, |V ν w|≤C) :
    |cubeExpectation i j x y V| ≤ C^(2^Fintype.card ι) := by
  unfold cubeExpectation
  refine (Finset.abs_expect_le _ _).trans ?_
  apply (Finset.expect_le_expect (fun Bj _ => ?_)).trans_eq (Fintype.expect_const _)
  refine (Finset.abs_expect_le _ _).trans ?_
  apply (Finset.expect_le_expect (fun Bi _ => ?_)).trans_eq (Fintype.expect_const _)
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ ν : ι → Bool, |C| := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      (fun ν _ => (hV ν _).trans (le_abs_self C))
    _ = _ := by simp [abs_of_nonneg hC]

lemma full_cube_bound (i j : ι) (hij : i≠j) (V : (ι → A) → W → ℝ)
    (ε H C : ℝ) (hε : 0≤ε) (hC : 0≤C)
    (hcoef : ∀ x α, |coefficient (V x) α|≤ε)
    (henergy : ∀ x, (𝔼 w, (V x w)^2)≤H^2) (hV : ∀ x w, |V x w|≤C) :
    (𝔼 x : ι → A, 𝔼 y : ι → A,
      cubeExpectation i j x y (fun ν => V (vertex ν x y))) ≤
      C^(2^Fintype.card ι)*((Fintype.card ι:ℝ)/Fintype.card A) +
        (ε^2*H^2)^(2^Fintype.card (Other i j)) := by
  let D := (ε^2*H^2)^(2^Fintype.card (Other i j))
  have hD : 0≤D := by dsimp [D]; positivity
  have hpoint (x y : ι → A) :
      cubeExpectation i j x y (fun ν => V (vertex ν x y)) ≤
        C^(2^Fintype.card ι)*(if ∃ k, x k=y k then (1:ℝ) else 0)+D := by
    by_cases hxy : ∃ k, x k=y k
    · simp only [ite_eq_left hxy,mul_one]
      exact (le_abs_self _).trans ((cubeExpectation_abs_bound i j x y _ hC (fun ν => hV _)).trans (le_add_of_nonneg_right hD))
    · simp only [ite_eq_right hxy,mul_zero,zero_add]
      exact (le_abs_self _).trans (cubeExpectation_bound i j hij x y (by simpa only [not_exists] using hxy)
        _ ε H hε (fun ν => hcoef _) (fun ν => henergy _))
  calc
    _ ≤ 𝔼 x : ι → A, 𝔼 y : ι → A,
        (C^(2^Fintype.card ι)*(if ∃ k, x k=y k then (1:ℝ) else 0)+D) :=
      Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun y _ => hpoint x y))
    _ = C^(2^Fintype.card ι)*(𝔼 x : ι → A, 𝔼 y : ι → A, if ∃ k, x k=y k then (1:ℝ) else 0)+D := by
      simp only [Finset.expect_add_distrib,← Finset.mul_expect,Fintype.expect_const]
    _ ≤ _ := by
      simpa only [D,add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left (collision_probability (ι := ι) (A := A)) (pow_nonneg hC (2^Fintype.card ι))) D
end MinUncut.CubeRows

namespace MinUncut.Inner
open BinaryFourier
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}
variable {W : Type*} [Fintype W] [AddCommGroup W] [Module F₂ W]

def pairField (i j : Fin m) (V : Point m n → W → ℝ)
    (Bj : ({k : Fin m // k≠j} → Fin n) → W)
    (Bi : ({k : Fin m // k≠i} → Fin n) → W) (x : Point m n) : ℝ :=
  V x (Bj (face x j)+Bi (face x i))

omit [Module F₂ W] in
lemma pair_moment (hn : 0 < n) (i j : Fin m) (V : Point m n → W → ℝ) :
    (𝔼 Bj, 𝔼 Bi, Box.moment (pairField i j V Bj Bi)) =
      𝔼 x : Point m n, 𝔼 y : Point m n, CubeRows.cubeExpectation i j x y (fun ν => V (Box.vertex ν x y)) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  unfold Box.moment CubeRows.cubeExpectation pairField
  conv_lhs => arg 2; ext Bj; rw [Finset.expect_comm]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  conv_lhs => arg 2; ext Bj; rw [Finset.expect_comm]
  rw [Finset.expect_comm]
  rfl

theorem pair_correlation_power (hm : 0 < m) (hn : 0 < n) (i j : Fin m) (hij : i≠j)
    (V : Point m n → W → ℝ) (ε H C : ℝ) (hε : 0≤ε) (hC : 0≤C)
    (hcoef : ∀ x α, |coefficient (V x) α|≤ε)
    (henergy : ∀ x, (𝔼 w, (V x w)^2)≤H^2) (hV : ∀ x w, |V x w|≤C) :
    (𝔼 Bj, 𝔼 Bi, faceCorrelation (pairField i j V Bj Bi))^(2^m) ≤
      C^(2^m)*((m:ℝ)/n)+(ε^2*H^2)^(2^Fintype.card (CubeRows.Other i j)) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  calc
    _ ≤ 𝔼 Bj, (𝔼 Bi, faceCorrelation (pairField i j V Bj Bi))^(2^m) := Box.expect_pow_two_pow _ m
    _ ≤ 𝔼 Bj, 𝔼 Bi, faceCorrelation (pairField i j V Bj Bi)^(2^m) :=
      Finset.expect_le_expect (fun Bj _ => Box.expect_pow_two_pow _ m)
    _ ≤ 𝔼 Bj, 𝔼 Bi, Box.moment (pairField i j V Bj Bi) :=
      Finset.expect_le_expect (fun Bj _ => Finset.expect_le_expect (fun Bi _ => faceCorrelation_box_cs hm hn _))
    _ = _ := pair_moment hn i j V
    _ ≤ _ := by
      have hc := CubeRows.full_cube_bound i j hij V ε H C hε hC hcoef henergy hV
      simp only [Fintype.card_fin] at hc
      exact hc
end MinUncut.Inner
namespace MinUncut.Box
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma bounded_integrable {f : Ω → ℝ} {C : ℝ} (hf : AEStronglyMeasurable f μ)
    (hC : ∀ x, |f x|≤C) : Integrable f μ :=
  (MemLp.of_bound hf C (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x)) : MemLp f 2 μ).integrable (by norm_num)

lemma integral_pow_bound {f : Ω → ℝ} {C : ℝ} (hf : AEStronglyMeasurable f μ)
    (hC : ∀ x, |f x|≤C) (hpos : ∀ x, 0≤f x) (k : ℕ) :
    (∫ x, f x ∂μ)^k ≤ ∫ x, (f x)^k ∂μ := by
  apply (convexOn_pow k).map_integral_le (by fun_prop) isClosed_Ici
    (Eventually.of_forall hpos) (bounded_integrable hf hC)
  apply bounded_integrable (C := C^k) (hf.pow k)
  intro x
  simpa only [Function.comp_apply,Pi.pow_apply,abs_pow] using pow_le_pow_left₀ (abs_nonneg (f x)) (hC x) k

omit [IsProbabilityMeasure μ] in
lemma integral_expect {T : Type*} [Fintype T] (f : T → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) :
    (∫ x, (𝔼 t, f t x) ∂μ) = 𝔼 t, ∫ x, f t x ∂μ := by
  simp only [Finset.expect_eq_sum_div_card]
  rw [integral_div, integral_finsetSum _ (fun t _ => hf t)]
end MinUncut.Box

end

end OAI
