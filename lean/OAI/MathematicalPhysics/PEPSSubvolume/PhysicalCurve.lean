import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Filters
import OAI.MathematicalPhysics.PEPSSubvolume.SpectralPowers
import OAI.MathematicalPhysics.PEPSSubvolume.Interpolation

namespace OAI

/-! Actual complex filter curves, boundary bounds and positive norms. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open Set Filter Complex Complex.HadamardThreeLines
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.PhysicalCurve
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder
open PolynomialPEPS.Subvolume.SpectralCurve

variable {L q : ℕ}

def amplitudeCLM (ψ : State L q) : Operator L q →L[ℂ] ℂ :=
  (innerSL ℂ ψ).comp <| (ContinuousLinearMap.apply ℂ (State L q) ψ).comp
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Configuration L q)).toAlgEquiv.toAlgHom.toLinearMap.toContinuousLinearMap

@[simp] theorem amplitudeCLM_apply (ψ : State L q) (M : Operator L q) :
    amplitudeCLM ψ M = inner ℂ ψ (asMap M ψ) := rfl

variable (X : ℕ → Finset (Vertex L))
  (U : (j : ℕ) → unitary (Matrix (RegionConfiguration q (X j))
    (RegionConfiguration q (X j)) ℂ))
  (r : (j : ℕ) → RegionConfiguration q (X j) → ℝ)

def prefixCurve (n : ℕ) (z : ℂ) : Operator L q :=
  orderedPrefix (fun j => liftLocal (X j) (curve (U j) (r j) z)) n

@[simp] theorem prefixCurve_zero (z : ℂ) : prefixCurve X U r 0 z = 1 := rfl
@[simp] theorem prefixCurve_succ (n : ℕ) (z : ℂ) :
    prefixCurve X U r (n+1) z =
      liftLocal (X n) (curve (U n) (r n) z) * prefixCurve X U r n z := rfl

@[simp] theorem prefixCurve_at_zero (n : ℕ) : prefixCurve X U r n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefixCurve_succ, curve_zero, liftLocal_one, ih, one_mul]

theorem hasDerivAt_liftCurve (j : ℕ) (z : ℂ) :
    HasDerivAt (fun w => liftLocal (X j) (curve (U j) (r j) w))
      (liftLocal (X j) (spectralHom (U j)
        (fun i => (r j i : ℂ) * Complex.exp (z * (r j i : ℂ))))) z := by
  let T : Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ →L[ℂ]
      Operator L q := (localLiftHom (q := q) (X j)).toAlgHom.toLinearMap.toContinuousLinearMap
  exact T.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_curve (U j) (r j) z)

theorem differentiable_prefixCurve (n : ℕ) : Differentiable ℂ (prefixCurve X U r n) := by
  induction n with
  | zero => exact differentiable_const _
  | succ n ih =>
    have hl : Differentiable ℂ (fun z => liftLocal (X n) (curve (U n) (r n) z)) :=
      fun z => (hasDerivAt_liftCurve X U r n z).differentiableAt
    exact hl.mul ih

theorem hasDerivAt_prefixCurve_zero (n : ℕ) :
    HasDerivAt (prefixCurve X U r n)
      (∑ j ∈ Finset.range n, liftLocal (X j)
        (spectralHom (U j) (fun i => (r j i : ℂ)))) 0 := by
  induction n with
  | zero =>
    change HasDerivAt (fun _ : ℂ => (1 : Operator L q)) 0 0
    exact hasDerivAt_const _ _
  | succ n ih =>
    have hj := hasDerivAt_liftCurve X U r n 0
    simp only [zero_mul, Complex.exp_zero, mul_one] at hj
    apply (hj.mul ih).congr_deriv
    simp only [Finset.sum_range_succ, prefixCurve_at_zero, curve_zero, liftLocal_one,
      one_mul, mul_one]
    exact add_comm _ _

def amplitude (ψ : State L q) (n : ℕ) (z : ℂ) : ℂ :=
  amplitudeCLM ψ (prefixCurve X U r n z)

@[simp] theorem amplitude_zero (ψ : State L q) (hψ : ‖ψ‖ = 1) (n : ℕ) :
    amplitude X U r ψ n 0 = 1 := by
  simp only [amplitude, prefixCurve_at_zero, amplitudeCLM_apply, asMap, map_one,
    one_apply_eq_self, inner_self_eq_norm_sq_to_K, hψ, one_pow]

theorem differentiable_amplitude (ψ : State L q) (n : ℕ) :
    Differentiable ℂ (amplitude X U r ψ n) :=
  (amplitudeCLM ψ).differentiable.comp (differentiable_prefixCurve X U r n)

theorem hasDerivAt_amplitude_zero (ψ : State L q) (n : ℕ) :
    HasDerivAt (amplitude X U r ψ n)
      (∑ j ∈ Finset.range n, Matrix.trace
        (spectralHom (U j) (fun i => (r j i : ℂ)) * reducedDensity ψ (X j))) 0 := by
  have hd := (amplitudeCLM ψ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_prefixCurve_zero X U r n)
  apply hd.congr_deriv
  simp only [map_sum, amplitudeCLM_apply, inner_liftLocal_trace]

theorem prefixCurve_unitary (n : ℕ) (z : ℂ) (hz : z.re = 0) :
    prefixCurve X U r n z ∈ unitary (Operator L q) := by
  apply orderedPrefix_unitary (fun j => liftUnitary (X j)
    ⟨curve (U j) (r j) z, curve_mem_unitary (U j) (r j) z hz⟩) n

theorem amplitude_left (ψ : State L q) (hψ : ‖ψ‖ = 1) (n : ℕ)
    (z : ℂ) (hz : z.re = 0) : ‖amplitude X U r ψ n z‖ ≤ 1 := by
  have hu := norm_asMap_unitary (L := L) (q := q)
    ⟨_,prefixCurve_unitary X U r n z hz⟩ ψ
  exact (norm_inner_le_norm ψ (asMap (prefixCurve X U r n z) ψ)).trans_eq
    (by rw [hu, hψ, one_mul])

theorem norm_prefixCurve_le_one (hr : ∀ j i, r j i ≤ 0) (n : ℕ)
    (z : ℂ) (hz : 0 ≤ z.re) : ‖prefixCurve X U r n z‖ ≤ 1 := by
  induction n with
  | zero =>
    nontriviality (Operator L q)
    simp only [prefixCurve_zero, norm_one, le_refl]
  | succ n ih =>
    have hloc : ‖liftLocal (X n) (curve (U n) (r n) z)‖ ≤ 1 := by
      have hc := norm_curve_le (U n) (r n) z 0 (fun i => mul_nonpos_of_nonneg_of_nonpos hz (hr n i))
      have hl := NonUnitalStarAlgHom.norm_apply_le (localLiftHom (q := q) (X n))
        (curve (U n) (r n) z)
      exact hl.trans (by simpa only [Real.exp_zero] using hc)
    rw [prefixCurve_succ]
    exact (norm_mul_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul hloc ih (norm_nonneg _) zero_le_one)

theorem amplitude_stripBound (hr : ∀ j i, r j i ≤ 0)
    (ψ : State L q) (hψ : ‖ψ‖ = 1) (n : ℕ) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖amplitude X U r ψ n z‖ ≤ 1 := by
  have hm : ‖asMap (prefixCurve X U r n z)‖ ≤ 1 := by
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Configuration L q) _‖ ≤ 1
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact norm_prefixCurve_le_one X U r hr n z hz
  calc
    ‖amplitude X U r ψ n z‖ ≤ ‖ψ‖ * ‖asMap (prefixCurve X U r n z) ψ‖ := norm_inner_le_norm (𝕜 := ℂ) ψ _
    _ ≤ ‖ψ‖ * (‖asMap (prefixCurve X U r n z)‖ * ‖ψ‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ 1 := by simpa only [hψ, one_mul, mul_one] using hm

end PolynomialPEPS.Subvolume.PhysicalCurve

namespace PolynomialPEPS.Subvolume.PhysicalCurve
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder
open PolynomialPEPS.Subvolume.SpectralCurve
variable {L q : ℕ}

variable (X : ℕ → Finset (Vertex L))
  (U : (j : ℕ) → unitary (Matrix (RegionConfiguration q (X j))
    (RegionConfiguration q (X j)) ℂ))

def powerRates (p : (j : ℕ) → RegionConfiguration q (X j) → ℝ) (a : ℕ → ℝ) :
    (j : ℕ) → RegionConfiguration q (X j) → ℝ :=
  fun j i => a j / 2 * Real.log (p j i)

theorem powerRates_nonpos (p : (j : ℕ) → RegionConfiguration q (X j) → ℝ)
    (hp : ∀ j i, 0 < p j i) (hsum : ∀ j, ∑ i, p j i = 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) : ∀ j i, powerRates X p a j i ≤ 0 := by
  intro j i
  have hpi : p j i ≤ 1 := by
    rw [← hsum j]
    exact Finset.single_le_sum (fun k _ => (hp j k).le) (Finset.mem_univ i)
  exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (ha j).le (by norm_num))
    (Real.log_nonpos (hp j i).le hpi)

theorem amplitude_right_of_optimizer (hq : 0 < q) (hX : Monotone X)
    (p : (j : ℕ) → RegionConfiguration q (X j) → ℝ)
    (hp : ∀ j i, 0 < p j i) (hsum : ∀ j, ∑ i, p j i = 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (ψ : State L q) (n : ℕ)
    (F : FilterFamily q n (fun j => X j.val))
    (hF : IsFilterOptimizer ψ (fun j => a j.val) F)
    (z : ℂ) (hz : z.re = 1) :
    ‖amplitude X U (powerRates X p a) ψ n z‖ ≤ ‖ψ‖ * ‖filteredVector F ψ‖ := by
  let r := powerRates X p a
  let V : (j : ℕ) → unitary (Matrix (RegionConfiguration q (X j))
      (RegionConfiguration q (X j)) ℂ) := fun j =>
    ⟨curve (U j) (r j) (z-1), curve_mem_unitary (U j) (r j) (z-1) (by simp [hz])⟩
  let P : (j : ℕ) → Matrix (RegionConfiguration q (X j))
      (RegionConfiguration q (X j)) ℂ := fun j => curve (U j) (r j) 1
  have hP : ∀ j, (P j).PosSemidef := fun j => curve_posSemidef (U j) (r j) 1
  let G : (j : ℕ) → LocalPositiveFilter q (X j) := fun j =>
    ⟨gaugedMatrix hq X hX V P j, gaugedMatrix_posSemidef hq X hX V P hP j⟩
  have hG : FilterFeasible (fun j : Fin n => a j.val) (fun j : Fin n => G j.val) := by
    intro j
    change (∑ i, Real.rpow
      ((gaugedMatrix_posSemidef hq X hX V P hP j.val).isHermitian.eigenvalues i)
        (2 / a j.val)) = 1
    rw [gaugedMatrix_eigenvalues hq X hX V P hP j.val]
    exact tracePower_curve_one (U j.val) (p j.val) (hp j.val) (hsum j.val) (a j.val) (ha j.val)
  have heq (j : ℕ) : curve (U j) (r j) z = (V j : Matrix _ _ ℂ) * P j := by
    change curve (U j) (r j) z = curve (U j) (r j) (z-1) * curve (U j) (r j) 1
    rw [← curve_add, sub_add_cancel]
  have hv : ‖asMap (prefixCurve X U r n z) ψ‖ =
      ‖filteredVector (fun j : Fin n => G j.val) ψ‖ := by
    change ‖asMap (orderedPrefix (fun j => liftLocal (X j) (curve (U j) (r j) z)) n) ψ‖ = _
    simp_rw [heq]
    rw [norm_orderedPrefix_gauge hq X hX V P]
    change _ = ‖asMap (orderedFilterProduct (fun j : Fin n => G j.val)) ψ‖
    rw [orderedFilterProduct_eq_prefix]
  calc
    ‖amplitude X U r ψ n z‖ ≤ ‖ψ‖ * ‖asMap (prefixCurve X U r n z) ψ‖ :=
      norm_inner_le_norm (𝕜 := ℂ) ψ _
    _ = ‖ψ‖ * ‖filteredVector (fun j : Fin n => G j.val) ψ‖ := by rw [hv]
    _ ≤ ‖ψ‖ * ‖filteredVector F ψ‖ :=
      mul_le_mul_of_nonneg_left (hF.2 _ hG) (norm_nonneg _)

theorem curve_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : unitary (Matrix ι ι ℂ)) (b : ι → ℝ) (z : ℂ) :
    IsUnit (curve V b z) := by
  apply isUnit_iff_exists.mpr
  refine ⟨curve V b (-z), ?_, ?_⟩
  · rw [← curve_add, add_neg_cancel, curve_zero]
  · rw [← curve_add, neg_add_cancel, curve_zero]

theorem prefixCurve_isUnit
    (r : (j : ℕ) → RegionConfiguration q (X j) → ℝ) (n : ℕ) (z : ℂ) :
    IsUnit (prefixCurve X U r n z) := by
  induction n with
  | zero => exact isUnit_one
  | succ n ih =>
    exact ((curve_isUnit (U n) (r n) z).map (localLiftHom (q := q) (X n))).mul ih

theorem norm_asMap_pos_of_isUnit (M : Operator L q) (hM : IsUnit M)
    (ψ : State L q) (hψ : ψ ≠ 0) : 0 < ‖asMap M ψ‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hu : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Configuration L q) M) :=
    hM.map Matrix.toEuclideanCLM
  obtain ⟨T,hT⟩ := hu.exists_left_inv
  have hv := congrArg (fun f : State L q →L[ℂ] State L q => f ψ) hT
  change T (asMap M ψ) = ψ at hv
  rw [hz, map_zero] at hv
  exact hψ hv.symm

include U in

theorem optimizer_norm_pos
    (p : (j : ℕ) → RegionConfiguration q (X j) → ℝ)
    (hp : ∀ j i, 0 < p j i) (hsum : ∀ j, ∑ i, p j i = 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (ψ : State L q) (hψ : ‖ψ‖ = 1) (n : ℕ)
    (F : FilterFamily q n (fun j => X j.val))
    (hF : IsFilterOptimizer ψ (fun j => a j.val) F) :
    0 < ‖filteredVector F ψ‖ := by
  let r := powerRates X p a
  let G : (j : ℕ) → LocalPositiveFilter q (X j) := fun j =>
    ⟨curve (U j) (r j) 1, curve_posSemidef (U j) (r j) 1⟩
  have hG : FilterFeasible (fun j : Fin n => a j.val) (fun j : Fin n => G j.val) := by
    intro j
    exact tracePower_curve_one (U j.val) (p j.val) (hp j.val) (hsum j.val)
      (a j.val) (ha j.val)
  have hψ0 : ψ ≠ 0 := by
    intro hz
    simp only [hz, norm_zero] at hψ
    exact zero_ne_one hψ
  have hg : 0 < ‖filteredVector (fun j : Fin n => G j.val) ψ‖ := by
    unfold filteredVector
    rw [orderedFilterProduct_eq_prefix]
    exact norm_asMap_pos_of_isUnit (prefixCurve X U r n 1)
      (prefixCurve_isUnit X U r n 1) ψ hψ0
  exact hg.trans_le (hF.2 _ hG)

theorem optimizer_cost_le_trace_rates (hq : 0 < q) (hX : Monotone X)
    (p : (j : ℕ) → RegionConfiguration q (X j) → ℝ)
    (hp : ∀ j i, 0 < p j i) (hsum : ∀ j, ∑ i, p j i = 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (ψ : State L q) (hψ : ‖ψ‖ = 1) (n : ℕ)
    (F : FilterFamily q n (fun j => X j.val))
    (hF : IsFilterOptimizer ψ (fun j => a j.val) F) :
    -Real.log (‖filteredVector F ψ‖ ^ 2) ≤
      -2 * (∑ j ∈ Finset.range n, Matrix.trace
        (spectralHom (U j) (fun i => ((powerRates X p a j i) : ℂ)) *
          reducedDensity ψ (X j))).re := by
  let r := powerRates X p a
  have hpos := optimizer_norm_pos X U p hp hsum a ha ψ hψ n F hF
  have hb : BddAbove ((norm ∘ amplitude X U r ψ n) '' verticalClosedStrip 0 1) := by
    refine ⟨1, ?_⟩
    rintro b ⟨z,hz,rfl⟩
    exact amplitude_stripBound X U r (powerRates_nonpos X p hp hsum a ha)
      ψ hψ n z hz.1
  have hr : ∀ z ∈ re ⁻¹' {1}, ‖amplitude X U r ψ n z‖ ≤ ‖filteredVector F ψ‖ := by
    intro z hz
    have h := amplitude_right_of_optimizer X U hq hX p hp hsum a ha ψ n F hF z hz
    simpa only [hψ, one_mul] using h
  have h := FilterInterpolation.threeLines_tangent_zero hpos
    (amplitude_zero X U r ψ hψ n)
    (hasDerivAt_amplitude_zero X U r ψ n)
    (differentiable_amplitude X U r ψ n).diffContOnCl hb
    (fun z hz => amplitude_left X U r ψ hψ n z hz) hr
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

end PolynomialPEPS.Subvolume.PhysicalCurve

end

end OAI
