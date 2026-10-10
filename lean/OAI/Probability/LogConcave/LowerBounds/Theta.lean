import Mathlib
import OAI.Probability.LogConcave.LowerBounds.CouplingNoise
import OAI.Probability.LogConcave.Sampling.PiAppendLaw

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory
open WithLp

namespace LogConcaveSampling.LowerBound

lemma roundGaussianPair_law (d : ℕ) :
    MeasurePreserving (fun r : RoundRandom d => (r.1,r.2.1)) (roundRandomLaw d)
      ((stdGaussian (Point d)).prod (stdGaussian (Point d))) := by
  exact (MeasurePreserving.id (stdGaussian (Point d))).prod measurePreserving_fst

lemma roundTapeColumns_law (d q : ℕ) :
    MeasurePreserving (fun r : Fin q → RoundRandom d =>
      Fin.append (fun i => (r i).1) (fun i => (r i).2.1))
      (Measure.pi (fun _ : Fin q => roundRandomLaw d))
      (Measure.pi (fun _ : Fin (q+q) => stdGaussian (Point d))) := by
  have h₁ := measurePreserving_pi (fun _ : Fin q => roundRandomLaw d)
    (fun _ : Fin q => (stdGaussian (Point d)).prod (stdGaussian (Point d)))
    (fun _ => roundGaussianPair_law d)
  have h₂ := measurePreserving_arrowProdEquivProdArrow (Point d) (Point d) (Fin q)
    (fun _ => stdGaussian (Point d)) (fun _ => stdGaussian (Point d))
  have h₃ : MeasurePreserving (fun p : (Fin q → Point d) × (Fin q → Point d) =>
      Fin.append p.1 p.2)
      ((Measure.pi (fun _ : Fin q => stdGaussian (Point d))).prod
        (Measure.pi (fun _ : Fin q => stdGaussian (Point d))))
      (Measure.pi (fun _ : Fin (q+q) => stdGaussian (Point d))) :=
    ⟨by fun_prop,pi_append_law _ q q⟩
  exact h₃.comp (h₂.comp h₁)

theorem couplingColumns_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (couplingColumns (Ω := Ω) (d := d) (q := q)) (couplingLaw μ d q)
      (Measure.pi (fun _ : Fin (q+q+1) => stdGaussian (Point d))) := by
  have h₀ : MeasurePreserving (fun p : CouplingNoise Ω d q => (p.1.1.2,p.1.2))
      (couplingLaw μ d q)
      ((Measure.pi (fun _ : Fin q => roundRandomLaw d)).prod (stdGaussian (Point d))) :=
    (measurePreserving_snd.prod (MeasurePreserving.id _)).comp measurePreserving_fst
  have h₁ := (roundTapeColumns_law d q).prod (MeasurePreserving.id (stdGaussian (Point d)))
  have h₂ : MeasurePreserving
      (fun p : (Fin (q+q) → Point d) × Point d =>
        Fin.snoc (α := fun _ : Fin (q+q+1) => Point d) p.1 p.2)
      ((Measure.pi (fun _ : Fin (q+q) => stdGaussian (Point d))).prod (stdGaussian (Point d)))
      (Measure.pi (fun _ : Fin (q+q+1) => stdGaussian (Point d))) :=
    ⟨measurable_fin_snoc _,pi_snoc_law _ _⟩
  exact h₂.comp (h₁.comp h₀)

end LogConcaveSampling.LowerBound

open scoped BigOperators

namespace LogConcaveSampling.LowerBound

def theta (d k : ℕ) : ℝ := ((k : ℝ) + 1 / 2) * Real.pi / d

def eigenvalue (d k : ℕ) : ℝ := (3 + Real.cos (theta d k)) / 2

def weight (d n k : ℕ) : ℝ := Real.cos (n * theta d k)

theorem sum_half_grid_cos_eq_zero {d l : ℕ} (hl : 0 < l) (hld : l < 2 * d) :
    ∑ k ∈ Finset.range d, Real.cos ((l : ℝ) * theta d k) = 0 := by
  have hd : 0 < d := by omega
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hldr : (l : ℝ) < 2 * d := by exact_mod_cast hld
  let a : ℝ := l * Real.pi / d
  have ha : 0 < a / 2 := by dsimp [a]; positivity
  have hap : a / 2 < Real.pi := by
    dsimp [a]
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_lt_iff₀ hdr).mpr
    nlinarith [Real.pi_pos]
  have hs : Real.sin (a / 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ha hap).ne'
  have h := Real.sin_mul_sum_cos d a (a / 2)
  have harg₁ : (d : ℝ) * a / 2 = l * Real.pi / 2 := by dsimp [a]; field_simp
  have harg₂ : ((d : ℝ) - 1) * a / 2 + a / 2 = l * Real.pi / 2 := by
    dsimp [a]; field_simp; ring
  rw [harg₁, harg₂] at h
  have hz : Real.sin (l * Real.pi / 2) * Real.cos (l * Real.pi / 2) = 0 := by
    have hh := Real.sin_two_mul (l * Real.pi / 2)
    rw [show 2 * ((l : ℝ) * Real.pi / 2) = l * Real.pi by ring,
      Real.sin_nat_mul_pi] at hh
    linarith
  rw [hz] at h
  have hsum := (mul_eq_zero.mp h).resolve_left hs
  convert! hsum using 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  dsimp [a, theta]
  ring

theorem eigenvalue_bounds (d k : ℕ) : 1 ≤ eigenvalue d k ∧ eigenvalue d k ≤ 2 := by
  constructor <;> dsimp [eigenvalue]
  · linarith [Real.neg_one_le_cos (theta d k)]
  · linarith [Real.cos_le_one (theta d k)]

theorem sum_half_grid_cos_sq {d j : ℕ} (hj : 0 < j) (hjd : j < d) :
    ∑ k ∈ Finset.range d, (Real.cos ((j : ℝ) * theta d k)) ^ 2 = (d : ℝ) / 2 := by
  have hz := sum_half_grid_cos_eq_zero (l := 2 * j) (by omega) (by omega : 2 * j < 2 * d)
  simp_rw [Real.cos_sq]
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  have harg : ∀ k, 2 * ((j : ℝ) * theta d k) = ((2 * j : ℕ) : ℝ) * theta d k := by
    intro k
    push_cast
    ring
  simp_rw [harg]
  rw [← Finset.sum_div, hz]
  simp

theorem sum_half_grid_cos_mul_of_lt {d j k : ℕ} (hkj : k < j) (hjd : j + k < 2 * d) :
    ∑ a ∈ Finset.range d,
      Real.cos ((j : ℝ) * theta d a) * Real.cos ((k : ℝ) * theta d a) = 0 := by
  have hs := sum_half_grid_cos_eq_zero (l := j + k) (by omega) hjd
  have hd := sum_half_grid_cos_eq_zero (l := j - k) (by omega) (by omega : j - k < 2 * d)
  have hpoint : ∀ a : ℕ,
      2 * (Real.cos ((j : ℝ) * theta d a) * Real.cos ((k : ℝ) * theta d a)) =
        Real.cos (((j - k : ℕ) : ℝ) * theta d a) +
        Real.cos (((j + k : ℕ) : ℝ) * theta d a) := by
    intro a
    rw [← mul_assoc, Real.two_mul_cos_mul_cos, Nat.cast_sub hkj.le, Nat.cast_add]
    congr 2 <;> ring
  have hh : 2 * (∑ a ∈ Finset.range d,
      Real.cos ((j : ℝ) * theta d a) * Real.cos ((k : ℝ) * theta d a)) = 0 := by
    rw [Finset.mul_sum]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, hd, hs, add_zero]
  linarith

theorem sum_half_grid_cos_mul {d j k : ℕ} (hne : j ≠ k) (hjd : j + k < 2 * d) :
    ∑ a ∈ Finset.range d,
      Real.cos ((j : ℝ) * theta d a) * Real.cos ((k : ℝ) * theta d a) = 0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · simpa only [mul_comm] using sum_half_grid_cos_mul_of_lt h (by omega : k + j < 2 * d)
  · exact sum_half_grid_cos_mul_of_lt h hjd

theorem sum_half_grid_cos_triple_of_le {d n j k : ℕ}
    (hkj : k ≤ j) (hn : j + k < n) (hnd : n + j + k < 2 * d) :
    ∑ a ∈ Finset.range d,
      Real.cos ((n : ℝ) * theta d a) * Real.cos ((j : ℝ) * theta d a) *
        Real.cos ((k : ℝ) * theta d a) = 0 := by
  have hs := sum_half_grid_cos_mul (d := d) (j := n) (k := j + k) (by omega) (by omega)
  have hd := sum_half_grid_cos_mul (d := d) (j := n) (k := j - k) (by omega) (by omega)
  have hpoint : ∀ a : ℕ,
      2 * (Real.cos ((n : ℝ) * theta d a) * Real.cos ((j : ℝ) * theta d a) *
        Real.cos ((k : ℝ) * theta d a)) =
      Real.cos ((n : ℝ) * theta d a) * Real.cos (((j - k : ℕ) : ℝ) * theta d a) +
      Real.cos ((n : ℝ) * theta d a) * Real.cos (((j + k : ℕ) : ℝ) * theta d a) := by
    intro a
    have h := Real.two_mul_cos_mul_cos ((j : ℝ) * theta d a) ((k : ℝ) * theta d a)
    rw [Nat.cast_sub hkj, Nat.cast_add, sub_mul, add_mul, ← mul_add, ← h]
    ring
  have hh : 2 * (∑ a ∈ Finset.range d,
      Real.cos ((n : ℝ) * theta d a) * Real.cos ((j : ℝ) * theta d a) *
        Real.cos ((k : ℝ) * theta d a)) = 0 := by
    rw [Finset.mul_sum]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, hd, hs, add_zero]
  linarith

theorem sum_half_grid_cos_triple {d q j k : ℕ}
    (hj : j ≤ q) (hk : k ≤ q) (hqd : 4 * q + 1 < 2 * d) :
    ∑ a ∈ Finset.range d,
      Real.cos (((2 * q + 1 : ℕ) : ℝ) * theta d a) * Real.cos ((j : ℝ) * theta d a) *
        Real.cos ((k : ℝ) * theta d a) = 0 := by
  rcases le_total k j with h | h
  · exact sum_half_grid_cos_triple_of_le h (by omega) (by omega)
  · convert! sum_half_grid_cos_triple_of_le (d := d) (n := 2 * q + 1) h
      (by omega : k + j < 2 * q + 1) (by omega : 2 * q + 1 + k + j < 2 * d) using 1
    apply Finset.sum_congr rfl
    intro a _
    ring

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

theorem sum_half_grid_cos_sq_ite {d j : ℕ} (hj : j < d) :
    ∑ k ∈ Finset.range d, Real.cos ((j : ℝ) * theta d k) ^ 2 =
      if j = 0 then (d : ℝ) else (d : ℝ) / 2 := by
  by_cases h : j = 0
  · subst j
    simp
  · rw [ite_eq_right h]
    have hd := sum_half_grid_cos_eq_zero (d := d) (l := 2 * j) (by omega) (by omega)
    have hpoint : ∀ k : ℕ, 2 * Real.cos ((j : ℝ) * theta d k) ^ 2 =
        1 + Real.cos (((2 * j : ℕ) : ℝ) * theta d k) := by
      intro k
      rw [Nat.cast_mul, Nat.cast_ofNat]
      have hc := Real.cos_two_mul ((j : ℝ) * theta d k)
      rw [← mul_assoc] at hc
      linarith
    have hh : 2 * (∑ k ∈ Finset.range d, Real.cos ((j : ℝ) * theta d k) ^ 2) = d := by
      rw [Finset.mul_sum]
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib, hd]
      simp
    linarith

def cosineAmplitude (j : ℕ) : ℝ := if j = 0 then 1 else Real.sqrt 2

theorem cosineAmplitude_pos (j : ℕ) : 0 < cosineAmplitude j := by
  unfold cosineAmplitude
  split_ifs <;> positivity

theorem cosineAmplitude_sq_le_two (j : ℕ) : cosineAmplitude j ^ 2 ≤ 2 := by
  unfold cosineAmplitude
  split_ifs <;> norm_num

def cosineColumn (d j k : ℕ) : ℝ :=
  cosineAmplitude j * Real.cos ((j : ℝ) * theta d k) / Real.sqrt d

theorem cosineColumn_orthonormal {d j l : ℕ} (hd : 0 < d) (hj : j < d) (hl : l < d) :
    ∑ k ∈ Finset.range d, cosineColumn d j k * cosineColumn d l k =
      if j = l then (1 : ℝ) else 0 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt hdr.le
  have hp : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hdr).ne'
  have hcoeff : ∀ k : ℕ, cosineColumn d j k * cosineColumn d l k =
      (cosineAmplitude j * cosineAmplitude l / d) *
        (Real.cos ((j : ℝ) * theta d k) * Real.cos ((l : ℝ) * theta d k)) := by
    intro k
    simp only [cosineColumn]
    field_simp [hp, hdr.ne']
    rw [hs]
    ring
  simp_rw [hcoeff]
  rw [← Finset.mul_sum]
  by_cases h : j = l
  · subst l
    rw [ite_eq_left rfl]
    simp_rw [← pow_two]
    rw [sum_half_grid_cos_sq_ite hj]
    unfold cosineAmplitude
    split_ifs
    all_goals field_simp
    all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · rw [ite_eq_right h, sum_half_grid_cos_mul h (by omega), mul_zero]

theorem cosineColumn_sq_le {d j k : ℕ} (hd : 0 < d) :
    cosineColumn d j k ^ 2 ≤ 2 / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt hdr.le
  unfold cosineColumn
  rw [div_pow, mul_pow, hs]
  apply div_le_div_of_nonneg_right _ hdr.le
  have hc : Real.cos ((j : ℝ) * theta d k) ^ 2 ≤ 1 := by
    nlinarith [Real.cos_le_one ((j : ℝ) * theta d k),
      Real.neg_one_le_cos ((j : ℝ) * theta d k)]
  calc
    _ ≤ cosineAmplitude j ^ 2 * 1 := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ ≤ 2 := by simpa using cosineAmplitude_sq_le_two j

theorem cosineColumn_product_le {d j l k : ℕ} (hd : 0 < d) :
    |cosineColumn d j k * cosineColumn d l k| ≤ 2 / d := by
  have hj := cosineColumn_sq_le (j := j) (k := k) hd
  have hl := cosineColumn_sq_le (j := l) (k := k) hd
  have h := mul_self_nonneg (|cosineColumn d j k| - |cosineColumn d l k|)
  rw [abs_mul]
  nlinarith [sq_abs (cosineColumn d j k), sq_abs (cosineColumn d l k)]

theorem cosineColumn_weighted_orthogonal {d q j l : ℕ}
    (hj : j ≤ q) (hl : l ≤ q) (hqd : 4 * q + 1 < 2 * d) :
    ∑ k ∈ Finset.range d, weight d (2*q+1) k * cosineColumn d j k * cosineColumn d l k = 0 := by
  have hpoint : ∀ k : ℕ,
      weight d (2*q+1) k * cosineColumn d j k * cosineColumn d l k =
      (cosineAmplitude j * cosineAmplitude l / (Real.sqrt d) ^ 2) *
      (Real.cos (((2*q+1 : ℕ) : ℝ) * theta d k) *
        Real.cos ((j : ℝ) * theta d k) * Real.cos ((l : ℝ) * theta d k)) := by
    intro k
    simp only [cosineColumn, weight]
    ring
  simp_rw [hpoint]
  rw [← Finset.mul_sum, sum_half_grid_cos_triple hj hl hqd, mul_zero]

end LogConcaveSampling.LowerBound

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LogConcaveSampling.LowerBound

theorem integral_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  change (∫ x : ℝ, ((fun y : ℝ => y) ^ 4) x ∂gaussianReal 0 v) = _
  rw [← iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 v)
    (by simp) 4, mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  let f : ℝ → ℝ := fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)
  have hf : ∀ t, HasDerivAt f ((v : ℝ) * t * f t) t := by
    intro t
    convert! ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2).exp using 1
    dsimp [f]
    ring
  have h1 : deriv f = fun t => v * t * f t := funext fun t => (hf t).deriv
  have h2 : deriv (fun t => (v : ℝ) * t * f t) =
      fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t := by
    funext t
    convert! (((hasDerivAt_id t).const_mul (v : ℝ)).mul (hf t)).deriv using 1
    simp only [id_eq]
    ring
  have h3 : deriv (fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t) =
      fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t := by
    funext t
    convert! ((((hasDerivAt_id t).pow 2).const_mul ((v : ℝ) ^ 2)).const_add
      (v : ℝ) |>.mul (hf t)).deriv using 1
    simp only [id_eq, Pi.pow_apply]
    ring
  have h4 : deriv (fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t) 0 =
      3 * (v : ℝ) ^ 2 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).const_mul (3 * (v : ℝ) ^ 2)).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul ((v : ℝ) ^ 3))).mul (hf 0)).deriv
    convert! h using 1
    simp [f]
  change iteratedDeriv 4 f 0 = _
  rw [iteratedDeriv_succ', h1, iteratedDeriv_succ', h2,
    iteratedDeriv_succ', h3, iteratedDeriv_one, h4]

theorem integral_pow_two_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
  simpa using h

private theorem holder_four_four_two : ENNReal.HolderTriple 4 4 2 := by
  constructor
  change (↑(4 : ℝ≥0) : ℝ≥0∞)⁻¹ + (↑(4 : ℝ≥0) : ℝ≥0∞)⁻¹ = (↑(2 : ℝ≥0) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
    ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
  norm_num

section RandomVariables
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {X Y : Ω → ℝ} {v w : ℝ≥0}

theorem gaussian_memLp (hX : HasLaw X (gaussianReal 0 v) P) (p : ℝ≥0) :
    MemLp X p P := by
  have h := memLp_id_gaussianReal (μ := 0) (v := v) p
  rw [← hX.map_eq] at h
  exact h.comp_of_map hX.aemeasurable

theorem gaussian_integral_sq (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ^ 2 ∂P = (v : ℝ) := by
  calc
    _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v := hX.integral_comp (by fun_prop)
    _ = _ := integral_pow_two_gaussianReal v

theorem gaussian_integral_fourth (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ^ 4 ∂P = 3 * (v : ℝ) ^ 2 := by
  calc
    _ = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v := hX.integral_comp (by fun_prop)
    _ = _ := integral_pow_four_gaussianReal v

theorem gaussian_sq_memLp (hX : HasLaw X (gaussianReal 0 v) P) :
    MemLp (fun ω => X ω ^ 2) 2 P := by
  let : ENNReal.HolderTriple 4 4 2 := holder_four_four_two
  have h4 : MemLp X (4 : ℝ≥0∞) P := by simpa using gaussian_memLp hX 4
  simp only [pow_two]
  exact h4.mul h4

theorem gaussian_sq_variance [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 0 v) P) :
    Var[fun ω => X ω ^ 2; P] = 2 * (v : ℝ) ^ 2 := by
  rw [variance_eq_sub (gaussian_sq_memLp hX), gaussian_integral_sq hX]
  simp only [Pi.pow_apply, ← pow_mul]
  rw [show 2 * 2 = 4 from rfl, gaussian_integral_fourth hX]
  ring

theorem independent_gaussian_product_variance [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 0 v) P) (hY : HasLaw Y (gaussianReal 0 w) P)
    (hXY : IndepFun X Y P) :
    Var[fun ω => X ω * Y ω; P] = (v : ℝ) * w := by
  let : ENNReal.HolderTriple 4 4 2 := holder_four_four_two
  have h4X : MemLp X (4 : ℝ≥0∞) P := by simpa using gaussian_memLp hX 4
  have h4Y : MemLp Y (4 : ℝ≥0∞) P := by simpa using gaussian_memLp hY 4
  have hmem : MemLp (fun ω => X ω * Y ω) 2 P := h4X.mul h4Y
  rw [variance_eq_sub hmem]
  have hmean : ∫ ω, X ω * Y ω ∂P = 0 := by
    rw [hXY.integral_fun_mul_eq_mul_integral hX.aemeasurable.aestronglyMeasurable
      hY.aemeasurable.aestronglyMeasurable, hX.integral_eq, integral_id_gaussianReal]
    simp
  have hsq := (hXY.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
    (hX.aemeasurable.pow_const 2).aestronglyMeasurable
    (hY.aemeasurable.pow_const 2).aestronglyMeasurable
  simp only [Function.comp_def, id_eq] at hsq
  rw [gaussian_integral_sq hX, gaussian_integral_sq hY] at hsq
  simpa only [Pi.pow_apply, mul_pow, hmean, zero_pow (by decide : 2 ≠ 0), sub_zero] using hsq

end RandomVariables
end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped BigOperators

def gaussianRow (b : ℕ) : Measure (Fin b → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance gaussianRow_probability (b : ℕ) : IsProbabilityMeasure (gaussianRow b) := by
  unfold gaussianRow
  infer_instance

def gaussianRows (d b : ℕ) : Measure (Fin d → Fin b → ℝ) :=
  Measure.pi fun _ => gaussianRow b

instance gaussianRows_probability (d b : ℕ) : IsProbabilityMeasure (gaussianRows d b) := by
  unfold gaussianRows
  infer_instance

theorem gaussianRow_coordinate_law {b : ℕ} (i : Fin b) :
    HasLaw (fun x : Fin b → ℝ => x i) (gaussianReal 0 1) (gaussianRow b) :=
  (measurePreserving_eval (fun _ : Fin b => gaussianReal 0 1) i).hasLaw

theorem gaussianRow_coordinates_independent {b : ℕ} :
    iIndepFun (fun i (x : Fin b → ℝ) => x i) (gaussianRow b) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem gaussianRow_product_memLp {b : ℕ} (i j : Fin b) :
    MemLp (fun x : Fin b → ℝ => x i * x j) 2 (gaussianRow b) := by
  let : ENNReal.HolderTriple 4 4 2 := holder_four_four_two
  have hi : MemLp (fun x : Fin b → ℝ => x i) (4 : ℝ≥0∞) (gaussianRow b) := by
    simpa using gaussian_memLp (gaussianRow_coordinate_law i) 4
  have hj : MemLp (fun x : Fin b → ℝ => x j) (4 : ℝ≥0∞) (gaussianRow b) := by
    simpa using gaussian_memLp (gaussianRow_coordinate_law j) 4
  exact hi.mul hj

theorem gaussianRow_product_mean {b : ℕ} (i j : Fin b) :
    ∫ x : Fin b → ℝ, x i * x j ∂gaussianRow b = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simpa [← pow_two] using
      gaussian_integral_sq (gaussianRow_coordinate_law i)
  · rw [ite_eq_right h, (gaussianRow_coordinates_independent.indepFun h).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable, (gaussianRow_coordinate_law i).integral_eq,
      integral_id_gaussianReal, zero_mul]

theorem gaussianRow_product_variance {b : ℕ} (i j : Fin b) :
    Var[fun x : Fin b → ℝ => x i * x j; gaussianRow b] = if i = j then 2 else 1 := by
  by_cases h : i = j
  · subst j
    simpa [← pow_two] using
      gaussian_sq_variance (gaussianRow_coordinate_law i)
  · rw [ite_eq_right h]
    simpa using independent_gaussian_product_variance (gaussianRow_coordinate_law i)
      (gaussianRow_coordinate_law j) (gaussianRow_coordinates_independent.indepFun h)

def gaussianRowSum {d b : ℕ} (c : Fin d → ℝ) (i j : Fin b)
    (x : Fin d → Fin b → ℝ) : ℝ := ∑ k, c k * (x k i * x k j)

theorem gaussianRowSum_memLp {d b : ℕ} (c : Fin d → ℝ) (i j : Fin b) :
    MemLp (gaussianRowSum c i j) 2 (gaussianRows d b) := by
  apply memLp_finsetSum
  intro k _
  exact ((gaussianRow_product_memLp i j).const_mul (c k)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin d => gaussianRow b) k)

theorem gaussianRowSum_mean {d b : ℕ} (c : Fin d → ℝ) (i j : Fin b) :
    ∫ x, gaussianRowSum c i j x ∂gaussianRows d b =
      (if i = j then 1 else 0) * ∑ k, c k := by
  unfold gaussianRowSum
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    have hrow : ∀ k : Fin d,
        ∫ x : Fin d → Fin b → ℝ, x k i * x k j ∂gaussianRows d b =
          if i = j then 1 else 0 := by
      intro k
      calc
        _ = ∫ y : Fin b → ℝ, y i * y j ∂gaussianRow b :=
          (measurePreserving_eval (fun _ : Fin d => gaussianRow b) k).hasLaw.integral_comp
            (by fun_prop)
        _ = _ := gaussianRow_product_mean i j
    simp_rw [hrow]
    rw [← Finset.sum_mul, mul_comm]
  · intro k _
    exact (((gaussianRow_product_memLp i j).const_mul (c k)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin d => gaussianRow b) k)).integrable (by norm_num)

theorem gaussianRowSum_variance {d b : ℕ} (c : Fin d → ℝ) (i j : Fin b) :
    Var[gaussianRowSum c i j; gaussianRows d b] =
      (if i = j then 2 else 1) * ∑ k, (c k) ^ 2 := by
  have h := variance_sum_pi (μ := fun _ : Fin d => gaussianRow b)
    (X := fun k (y : Fin b → ℝ) => c k * (y i * y j))
    (fun k => (gaussianRow_product_memLp i j).const_mul (c k))
  simp only [variance_const_mul, gaussianRow_product_variance] at h
  convert! h using 1
  · congr 1
    ext x
    simp [gaussianRowSum]
  · rw [← Finset.sum_mul, mul_comm]

theorem gaussianRowSum_variance_le {d b : ℕ} (hd : 0 < d) (c : Fin d → ℝ)
    (hc : ∀ k, |c k| ≤ 2 / d) (i j : Fin b) :
    Var[gaussianRowSum c i j; gaussianRows d b] ≤ 8 / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [gaussianRowSum_variance]
  have hfactor : (if i = j then (2 : ℝ) else 1) ≤ 2 := by split_ifs <;> norm_num
  have hsum : (∑ k, (c k) ^ 2) ≤ d * (2 / d : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin d, (2 / d : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hc k)
      _ = _ := by simp
  have hn : 0 ≤ ∑ k, (c k) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ 2 * ∑ k, (c k) ^ 2 := mul_le_mul_of_nonneg_right hfactor hn
    _ ≤ 2 * (d * (2 / d : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 8 / d := by field_simp; ring

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped BigOperators

def rowDeviationEnergy {ι : Type*} [Fintype ι] {d b : ℕ}
    (c : ι → Fin d → ℝ) (a z : ι → Fin b) (x : Fin d → Fin b → ℝ) : ℝ :=
  ∑ i, (gaussianRowSum (c i) (a i) (z i) x -
    (if a i = z i then (1 : ℝ) else 0) * ∑ k, c i k) ^ 2

theorem rowDeviationEnergy_nonneg {ι : Type*} [Fintype ι] {d b : ℕ}
    (c : ι → Fin d → ℝ) (a z : ι → Fin b) (x : Fin d → Fin b → ℝ) :
    0 ≤ rowDeviationEnergy c a z x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem rowDeviationEnergy_measurable {ι : Type*} [Fintype ι] {d b : ℕ}
    (c : ι → Fin d → ℝ) (a z : ι → Fin b) : Measurable (rowDeviationEnergy c a z) := by
  unfold rowDeviationEnergy gaussianRowSum
  fun_prop

theorem rowDeviationEnergy_integrable {ι : Type*} [Fintype ι] {d b : ℕ}
    (c : ι → Fin d → ℝ) (a z : ι → Fin b) :
    Integrable (rowDeviationEnergy c a z) (gaussianRows d b) := by
  apply integrable_finsetSum
  intro i _
  exact ((gaussianRowSum_memLp (c i) (a i) (z i)).sub (memLp_const _)).integrable_sq

theorem rowDeviationEnergy_mean {ι : Type*} [Fintype ι] {d b : ℕ}
    (c : ι → Fin d → ℝ) (a z : ι → Fin b) :
    ∫ x, rowDeviationEnergy c a z x ∂gaussianRows d b =
      ∑ i, Var[gaussianRowSum (c i) (a i) (z i); gaussianRows d b] := by
  unfold rowDeviationEnergy
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [variance_eq_integral (gaussianRowSum_memLp (c i) (a i) (z i)).aestronglyMeasurable.aemeasurable,
      gaussianRowSum_mean]
  · intro i _
    exact ((gaussianRowSum_memLp (c i) (a i) (z i)).sub (memLp_const _)).integrable_sq

theorem rowDeviationEnergy_mean_le {ι : Type*} [Fintype ι] {d b : ℕ}
    (hd : 0 < d) (c : ι → Fin d → ℝ) (a z : ι → Fin b)
    (hc : ∀ i k, |c i k| ≤ 2 / d) :
    ∫ x, rowDeviationEnergy c a z x ∂gaussianRows d b ≤
      8 * Fintype.card ι / d := by
  rw [rowDeviationEnergy_mean]
  calc
    _ ≤ ∑ _ : ι, (8 : ℝ) / d :=
      Finset.sum_le_sum fun i _ => gaussianRowSum_variance_le hd (c i) (hc i) (a i) (z i)
    _ = _ := by simp; ring

theorem rowDeviationEnergy_tail {ι : Type*} [Fintype ι] {d b : ℕ}
    (hd : 0 < d) (c : ι → Fin d → ℝ) (a z : ι → Fin b)
    (hc : ∀ i k, |c i k| ≤ 2 / d) {T : ℝ} (hT : 0 < T) :
    (gaussianRows d b).real {x | T ≤ rowDeviationEnergy c a z x} ≤
      (8 * Fintype.card ι / d) / T := by
  apply (le_div_iff₀ hT).mpr
  rw [mul_comm]
  exact (mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (rowDeviationEnergy_nonneg c a z))
    (rowDeviationEnergy_integrable c a z) T).trans
    (rowDeviationEnergy_mean_le hd c a z hc)

end LogConcaveSampling.LowerBound

open scoped BigOperators
open Matrix

namespace LogConcaveSampling.LowerBound

def matrixEnergy {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 2

theorem matrixEnergy_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) : 0 ≤ matrixEnergy M := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem quadratic_form_bound_of_energy {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (hM : matrixEnergy M ≤ τ ^ 2)
    (x : ι → ℝ) : |dotProduct x (M *ᵥ x)| ≤ τ * dotProduct x x := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => M p.1 p.2) (fun p => x p.1 * x p.2)
  have ht : (∑ p : ι × ι, M p.1 p.2 * (x p.1 * x p.2)) =
      dotProduct x (M *ᵥ x) := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : (∑ p : ι × ι, (x p.1 * x p.2) ^ 2) = (dotProduct x x) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [mul_pow]
    rw [← Finset.sum_mul_sum]
    simp only [dotProduct, pow_two]
  rw [ht, hs, Fintype.sum_prod_type] at hcs
  have hnon : 0 ≤ dotProduct x x := by
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hle : (dotProduct x (M *ᵥ x)) ^ 2 ≤ (τ * dotProduct x x) ^ 2 := by
    calc
      _ ≤ matrixEnergy M * (dotProduct x x) ^ 2 := hcs
      _ ≤ τ ^ 2 * (dotProduct x x) ^ 2 := mul_le_mul_of_nonneg_right hM (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hτ hnon)).mp (by simpa using hle)

theorem gram_control_on_column_span {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] [DecidableEq κ] (B : Matrix κ ι ℝ) (p : κ → ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 2)
    (hG : matrixEnergy (B.transpose * B - 1) ≤ τ ^ 2)
    (hT : matrixEnergy (B.transpose * diagonal p * B) ≤ τ ^ 2) :
    ∀ u ∈ Submodule.span ℝ (Set.range B.col),
      |dotProduct u (diagonal p *ᵥ u)| ≤ 2 * τ * dotProduct u u := by
  intro u hu
  rw [← Matrix.range_mulVecLin] at hu
  obtain ⟨x, rfl⟩ := hu
  change |dotProduct (B *ᵥ x) (diagonal p *ᵥ (B *ᵥ x))| ≤
    2 * τ * dotProduct (B *ᵥ x) (B *ᵥ x)
  have hg := quadratic_form_bound_of_energy (B.transpose * B - 1) hτ hG x
  have ht := quadratic_form_bound_of_energy (B.transpose * diagonal p * B) hτ hT x
  have hgram : dotProduct x ((B.transpose * B - 1) *ᵥ x) =
      dotProduct (B *ᵥ x) (B *ᵥ x) - dotProduct x x := by
    rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec,
      dotProduct_transpose_mulVec]
  have hstat : dotProduct x ((B.transpose * diagonal p * B) *ᵥ x) =
      dotProduct (B *ᵥ x) (diagonal p *ᵥ (B *ᵥ x)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]
  rw [hgram] at hg
  rw [hstat] at ht
  have hnorm : dotProduct x x ≤ 2 * dotProduct (B *ᵥ x) (B *ᵥ x) := by
    have hx : 0 ≤ dotProduct x x := by
      exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    have hlow := (abs_le.mp hg).1
    nlinarith
  calc
    _ ≤ τ * dotProduct x x := ht
    _ ≤ _ := by nlinarith

end LogConcaveSampling.LowerBound

open scoped BigOperators
open Polynomial

end LowerProof
end
end
end

end OAI
