import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.Regularized

namespace OAI

/-! Simplex stationarity and clipped marginal coordinates. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder

open scoped BigOperators Topology
open Filter Set
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Stationarity

lemma deriv_nonpos_of_right_max {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ f 0) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_right
  have h1 : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [self_mem_nhdsWithin, h1] with t ht ht1
  simp only [Set.mem_Ioi] at ht
  simp only [Set.mem_Iio] at ht1
  simpa only [zero_add, smul_eq_mul] using
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (sub_nonpos.mpr (hmax t ⟨ht.le, ht1.le⟩))

lemma simplex_clip {n : Type*} [Fintype n] [DecidableEq n]
    (x r : n → ℝ) {b : ℝ} (hb : 0 < b)
    (hx : (∀ index, 0 ≤ x index) ∧ ∑ index, x index = 1)
    (hr : ∀ i, 0 ≤ r i) (hrsum : 0 < ∑ i, r i)
    (hg : ∀ i, r i / (x i + b) ≤ ∑ k, x k * (r k / (x k + b))) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, x i + b = max b (r i / c) := by
  let c : ℝ := ∑ k, x k * (r k / (x k + b))
  have hxb (i : n) : 0 < x i + b := add_pos_of_nonneg_of_pos (hx.1 i) hb
  have hc : 0 < c := by
    by_contra h
    have hh : ∀ i, r i = 0 := by
      intro i
      have hh := (div_le_iff₀ (hxb i)).mp ((hg i).trans (le_of_not_gt h))
      have hh' : r i ≤ 0 := by simpa using hh
      exact le_antisymm hh' (hr i)
    simp only [hh, Finset.sum_const_zero, lt_self_iff_false] at hrsum
  have hsum : ∑ i, x i * (c - r i / (x i + b)) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => mul_sub _ _ _), Finset.sum_sub_distrib,
      ← Finset.sum_mul, hx.2, one_mul]
    exact sub_self c
  have hz (i : n) : x i * (c - r i / (x i + b)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hx.1 k) (sub_nonneg.mpr (hg k)))).mp hsum i
      (Finset.mem_univ i)
  refine ⟨c, hc, ?_⟩
  intro i
  by_cases hi : x i = 0
  · have hh := (div_le_iff₀ (hxb i)).mp (hg i)
    rw [hi, zero_add] at hh ⊢
    exact (max_eq_left ((div_le_iff₀ hc).mpr (by nlinarith : r i ≤ b * c))).symm
  · have he := sub_eq_zero.mp ((mul_eq_zero.mp (hz i)).resolve_left hi)
    have hp : r i / c = x i + b := by
      apply (div_eq_iff hc.ne').mpr
      have hq := (div_eq_iff (hxb i).ne').mp he.symm
      nlinarith
    rw [hp, max_eq_right (by linarith [hx.1 i])]

end PolynomialPEPS.PinnedEntropy.NestedFilter.Stationarity
namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Analytic

lemma inner_insertion_eq_trace {L q m : ℕ}
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (F : FilterFamily q m X) (Ω : State L q)
    (hdet : ∀ j, IsUnit (F j).matrix.det)
    (hc : ∀ j, Commute (F j).matrix (reducedDensity (output F Ω) (X j)))
    (j : Fin m) (B : Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ) :
    inner ℂ (output F Ω) (insertionMap F Ω j B) =
      (B * (F j).matrix⁻¹ * reducedDensity (output F Ω) (X j)).trace := by
  induction m generalizing Ω with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    induction j using Fin.cases with
    | zero =>
      let C := liftLocal (X 0) (B * (F 0).matrix⁻¹)
      have hrel : liftLocal (X 0) B = C * liftLocal (X 0) (F 0).matrix := by
        rw [← liftLocal_mul]
        congr 1
        simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul (F 0).matrix (hdet 0), Matrix.mul_one]
      rw [insertionMap_succ_zero, hrel, asMap_mul, matrixOutput_propagate
        _ (fun k : Fin m => liftLocal (X k.succ) (F k.succ).matrix⁻¹)]
      · have ho : matrixOutput (fun k : Fin m => liftLocal (X k.succ) (F k.succ).matrix)
            (asMap (liftLocal (X 0) (F 0).matrix) Ω) = output F Ω := (output_succ F Ω).symm
        rw [ho]
        rw [propagate_trace_strip (output F Ω) (fun k => X k.succ)
          (fun _ _ h => hX (Fin.succ_le_succ_iff.mpr h)) (fun k => F k.succ)
          (fun k => hdet k.succ) (fun k => hc k.succ) C
          (fun k => SupportedOn.mono (⟨_, rfl⟩ : SupportedOn C (X 0)) (hX (Fin.zero_le _)))]
        exact inner_asMap_liftLocal (X 0) _ _
      · intro k
        rw [← liftLocal_mul, Matrix.nonsing_inv_mul (F k.succ).matrix (hdet k.succ), liftLocal_one]
    | succ j =>
      rw [insertionMap_succ_succ]
      have hh := ih (fun k => X k.succ)
        (fun _ _ h => hX (Fin.succ_le_succ_iff.mpr h)) (fun k => F k.succ)
        (asMap (liftLocal (X 0) (F 0).matrix) Ω) (fun k => hdet k.succ)
        (by intro k; simpa only [← output_succ F Ω] using hc k.succ) j B
      simpa only [← output_succ F Ω] using hh

end PolynomialPEPS.PinnedEntropy.NestedFilter
namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

def spectralAffineCurve (b a : ℝ) (U : unitary (Matrix n n ℂ))
    (x d : n → ℝ) (t : ℝ) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal fun i => (((x i + t*d i + b) ^ (a/2) : ℝ) : ℂ))

def spectralLogDirection (b : ℝ) (U : unitary (Matrix n n ℂ))
    (x d : n → ℝ) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal fun i => ((d i / (x i + b) : ℝ) : ℂ))

lemma spectralAffineCurve_zero (b a : ℝ) (p : SpectralCoordinate n) (d : n → ℝ) :
    spectralAffineCurve b a p.1 p.2.val d 0 = regularizedCoordinateMatrix b a p := by
  simp only [spectralAffineCurve, regularizedCoordinateMatrix, zero_mul, add_zero]

lemma deriv_spectralAffineCurve (b a : ℝ) (U : unitary (Matrix n n ℂ))
    (x d : n → ℝ) (hxb : ∀ i, 0 < x i + b) :
    HasDerivAt (spectralAffineCurve b a U x d)
      ((a/2 : ℂ) • (spectralLogDirection b U x d * spectralAffineCurve b a U x d 0)) 0 := by
  let Φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  let C := (Φ.toAlgEquiv.toLinearMap.comp (Matrix.diagonalLinearMap n ℂ ℂ)).toContinuousLinearMap
  have hi (i : n) : HasDerivAt (fun t : ℝ => (((x i + t*d i + b) ^ (a/2) : ℝ) : ℂ))
      (((d i * (a/2) * (x i + b) ^ (a/2-1) : ℝ) : ℂ)) 0 := by
    have harg : HasDerivAt (fun t : ℝ => x i + t*d i + b) (d i) 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).mul_const (d i)).const_add (x i)).add_const b using 1 <;> first | rfl | simp
    have hp := harg.rpow_const (p := a/2) (Or.inl (by simpa using (hxb i).ne'))
    have hh := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hp
    convert hh using 1 <;> first | rfl | simp
  have hh := (C.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_pi.mpr hi)
  have he : C (fun i => (((d i * (a/2) * (x i + b) ^ (a/2-1) : ℝ) : ℂ))) =
      (a/2 : ℂ) • (spectralLogDirection b U x d * spectralAffineCurve b a U x d 0) := by
    change Φ (Matrix.diagonal _) = _
    change Φ (Matrix.diagonal _) = (a/2 : ℂ) •
      (Φ (Matrix.diagonal fun i => ((d i / (x i + b) : ℝ) : ℂ)) *
       Φ (Matrix.diagonal fun i => (((x i + 0*d i + b) ^ (a/2) : ℝ) : ℂ)))
    rw [← map_mul, ← map_smul]
    congr 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
    congr 1
    funext i
    dsimp only [Pi.smul_apply]
    simp only [zero_mul, add_zero, smul_eq_mul, Real.rpow_sub (hxb i), Real.rpow_one]
    push_cast
    ring
  change HasDerivAt (spectralAffineCurve b a U x d) (C _) 0 at hh
  rw [he] at hh
  exact hh

end PolynomialPEPS.PinnedEntropy.NestedFilter
namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Analytic

section Diagonal
variable {n : Type*} [Fintype n] [DecidableEq n]

def marginalDiagonal (U : unitary (Matrix n n ℂ)) (ρ : Matrix n n ℂ) (i : n) : ℝ :=
  ((star (U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ)) i i).re

lemma marginalDiagonal_nonneg (U : unitary (Matrix n n ℂ)) {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (i : n) : 0 ≤ marginalDiagonal U ρ i := by
  have hh := (hρ.conjTranspose_mul_mul_same (U : Matrix n n ℂ)).diag_nonneg (i := i)
  exact (Complex.nonneg_iff.mp hh).1

lemma sum_marginalDiagonal (U : unitary (Matrix n n ℂ)) (ρ : Matrix n n ℂ) :
    ∑ i, marginalDiagonal U ρ i = ρ.trace.re := by
  have hu : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := U.property.2
  have he : (star (U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ)).trace = ρ.trace := by
    rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul]
  rw [← he]
  simp [marginalDiagonal, Matrix.trace]

lemma re_trace_spectralLogDirection (b : ℝ) (U : unitary (Matrix n n ℂ))
    (x d : n → ℝ) (ρ : Matrix n n ℂ) :
    (spectralLogDirection b U x d * ρ).trace.re =
      ∑ i, d i / (x i + b) * marginalDiagonal U ρ i := by
  rw [spectralLogDirection, Unitary.conjStarAlgAut_apply]
  rw [Matrix.mul_assoc (U : Matrix n n ℂ), Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp [Matrix.trace, Matrix.diagonal_mul, marginalDiagonal, Complex.mul_re,
    Matrix.mul_assoc, -Complex.ofReal_add, -Complex.ofReal_div]

end Diagonal

lemma regularized_output_update {L q m : ℕ} [NeZero q]
    {X : Fin m → Finset (Vertex L)} {b : ℝ} (hb : 0 ≤ b)
    (a : Fin m → ℝ) (p : CoordinateFamily q X) (Ω : State L q) (j : Fin m)
    (s : SpectralCoordinate (RegionConfiguration q (X j))) :
    output (regularizedFilters hb a (Function.update p j s)) Ω =
      insertionMap (regularizedFilters hb a p) Ω j (regularizedCoordinateMatrix b (a j) s) := by
  classical
  change matrixOutput (fun k => liftLocal (X k)
    (regularizedCoordinateMatrix b (a k) (Function.update p j s k))) Ω =
    matrixOutput (Function.update _ j _) Ω
  congr 1
  funext k
  by_cases hk : k = j
  · subst k; simp; rfl
  · simp only [Function.update_of_ne hk]
    rfl

lemma simplex_affine_vertex {n : Type*} [Fintype n] [DecidableEq n]
    (x : n → ℝ) (hx : (∀ index, 0 ≤ x index) ∧ ∑ index, x index = 1) (i : n) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∀ index, 0 ≤ x index + t * ((Pi.single i (1 : ℝ) : n → ℝ) index - x index)) ∧
      ∑ index, (x index + t * ((Pi.single i (1 : ℝ) : n → ℝ) index - x index)) = 1 := by
  constructor
  · intro index
    have hsingle : 0 ≤ (Pi.single i (1 : ℝ) : n → ℝ) index := by
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (hx.1 index), mul_nonneg ht.1 hsingle]
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hx.2]
    simp

lemma deriv_sq_norm_complex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {y : ℝ → E} {d : E} (hy : HasDerivAt y d 0) :
    HasDerivAt (fun t : ℝ => ‖y t‖ ^ 2) (2 * (inner ℂ (y 0) d).re) 0 := by
  have hn0 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hy.inner ℂ hy)
  convert hn0 using 1 <;> try rfl
  · funext t
    change ‖y t‖ ^ 2 = (inner ℂ (y t) (y t)).re
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (y t)
  · change 2 * (inner ℂ (y 0) d).re =
      (inner ℂ (y 0) d + inner ℂ d (y 0)).re
    rw [Complex.add_re]
    have hs := inner_re_symm (𝕜 := ℂ) d (y 0)
    change (inner ℂ d (y 0)).re = (inner ℂ (y 0) d).re at hs
    rw [hs]
    ring

end PolynomialPEPS.PinnedEntropy.NestedFilter
namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Analytic

variable {L q m : ℕ} [NeZero q] {X : Fin m → Finset (Vertex L)}

omit [NeZero q] in
lemma deriv_regularized_norm_sq {b : ℝ} (hb : 0 < b) (a : Fin m → ℝ)
    (p : CoordinateFamily q X) (Ω : State L q) (hX : Monotone X)
    (hc : ∀ j, Commute (regularizedFilters hb.le a p j).matrix
      (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j)))
    (j : Fin m) (d : RegionConfiguration q (X j) → ℝ) :
    HasDerivAt (fun t : ℝ => ‖insertionMap (regularizedFilters hb.le a p) Ω j
      (spectralAffineCurve b (a j) (p j).1 (p j).2.val d t)‖ ^ 2)
      (a j * ∑ i, d i / ((p j).2.val i + b) *
        marginalDiagonal (p j).1 (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j)) i) 0 := by
  let F := regularizedFilters hb.le a p
  let B := spectralLogDirection b (p j).1 (p j).2.val d
  let I := (insertionMap F Ω j).toContinuousLinearMap
  have hg := deriv_spectralAffineCurve b (a j) (p j).1 (p j).2.val d
    (fun i => add_pos_of_nonneg_of_pos ((p j).2.property.1 i) hb)
  have hy := (I.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hg
  have hn := deriv_sq_norm_complex hy
  have hy0 : insertionMap F Ω j (spectralAffineCurve b (a j) (p j).1 (p j).2.val d 0) = output F Ω := by
    rw [spectralAffineCurve_zero]
    exact insertionMap_self F Ω j
  have hi : inner ℂ (output F Ω) (insertionMap F Ω j (B * (F j).matrix)) =
      (B * reducedDensity (output F Ω) (X j)).trace := by
    rw [inner_insertion_eq_trace X hX F Ω
      (fun k => regularizedCoordinateMatrix_invertible hb (a k) (p k)) hc]
    rw [Matrix.mul_assoc B (F j).matrix, Matrix.mul_nonsing_inv (F j).matrix
      (show IsUnit (F j).matrix.det from regularizedCoordinateMatrix_invertible hb (a j) (p j)), Matrix.mul_one]
  convert hn using 1 <;> try rfl
  change _ = 2 * (inner ℂ
    (insertionMap F Ω j (spectralAffineCurve b (a j) (p j).1 (p j).2.val d 0))
    (insertionMap F Ω j ((a j / 2 : ℂ) •
      (B * spectralAffineCurve b (a j) (p j).1 (p j).2.val d 0)))).re
  rw [hy0, map_smul, inner_smul_right, spectralAffineCurve_zero]
  change _ = 2 * ((a j / 2 : ℂ) * inner ℂ (output F Ω)
    (insertionMap F Ω j (B * (F j).matrix))).re
  rw [hi]
  simp only [Complex.mul_re, Complex.div_ofNat_re, Complex.ofReal_re,
    Complex.div_ofNat_im, Complex.ofReal_im]
  rw [re_trace_spectralLogDirection]
  ring

lemma regularized_maximizer_gradient {b : ℝ} (hb : 0 < b) {a : Fin m → ℝ}
    (ha : ∀ j, 0 < a j) {p : CoordinateFamily q X} {Ω : State L q}
    (hX : Monotone X) (hp : IsRegularizedMaximizer hb.le Ω a p)
    (hc : ∀ j, Commute (regularizedFilters hb.le a p j).matrix
      (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j)))
    (j : Fin m) (i : RegionConfiguration q (X j)) :
    let r := marginalDiagonal (p j).1 (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j))
    r i / ((p j).2.val i + b) ≤ ∑ k, (p j).2.val k * (r k / ((p j).2.val k + b)) := by
  classical
  let x := (p j).2.val
  let d : RegionConfiguration q (X j) → ℝ := fun k => (Pi.single i (1 : ℝ) : _ → ℝ) k - x k
  let r := marginalDiagonal (p j).1 (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j))
  let y := fun t : ℝ => insertionMap (regularizedFilters hb.le a p) Ω j
    (spectralAffineCurve b (a j) (p j).1 x d t)
  have hy0 : y 0 = output (regularizedFilters hb.le a p) Ω := by
    dsimp only [y, x]
    rw [spectralAffineCurve_zero]
    exact insertionMap_self _ _ _
  have hmax (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖y t‖ ^ 2 ≤ ‖y 0‖ ^ 2 := by
    let s : SpectralCoordinate (RegionConfiguration q (X j)) :=
      ((p j).1, ⟨fun k => x k + t * d k, simplex_affine_vertex x (p j).2.property i t ht⟩)
    have hh := hp (Function.update p j s)
    rw [regularized_output_update] at hh
    rw [hy0]
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hn := Stationarity.deriv_nonpos_of_right_max
    (deriv_regularized_norm_sq hb a p Ω hX hc j d) hmax
  have he : (∑ k, d k / (x k + b) * r k) =
      r i / (x i + b) - ∑ k, x k * (r k / (x k + b)) := by
    simp only [d, sub_div, sub_mul, Finset.sum_sub_distrib]
    have hh : ∑ k, (Pi.single i (1 : ℝ) : _ → ℝ) k / (x k + b) * r k = r i / (x i + b) := by
      rw [Finset.sum_eq_single i]
      · simp [div_eq_mul_inv, mul_comm]
      · intro k _ hk; simp [Pi.single_eq_of_ne hk]
      · simp
    rw [hh]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  change a j * (∑ k, d k / (x k + b) * r k) ≤ 0 at hn
  rw [he] at hn
  change r i / (x i + b) ≤ ∑ k, x k * (r k / (x k + b))
  nlinarith [ha j]

end PolynomialPEPS.PinnedEntropy.NestedFilter
namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators Matrix.Norms.L2Operator
open Analytic

lemma output_ne_zero_of_invertible {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (F : FilterFamily q m X) (hdet : ∀ j, IsUnit (F j).matrix.det)
    {Ω : State L q} (hΩ : Ω ≠ 0) : output F Ω ≠ 0 := by
  induction m generalizing Ω with
  | zero => simpa only [output, List.ofFn_zero, List.foldl_nil] using hΩ
  | succ m ih =>
    rw [output_succ]
    apply ih _ (fun j => hdet j.succ)
    intro hz
    apply hΩ
    have hleft : asMap (liftLocal (X 0) (F 0).matrix⁻¹)
        (asMap (liftLocal (X 0) (F 0).matrix) Ω) = Ω := by
      rw [← asMap_mul, ← liftLocal_mul,
        Matrix.nonsing_inv_mul (F 0).matrix (hdet 0), liftLocal_one]
      change (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) 1) Ω = Ω
      rw [map_one]
      rfl
    rw [hz, map_zero] at hleft
    exact hleft.symm

lemma regularized_output_ne_zero {L q m : ℕ} [NeZero q] {X : Fin m → Finset (Vertex L)}
    {b : ℝ} (hb : 0 < b) (a : Fin m → ℝ) (p : CoordinateFamily q X)
    {Ω : State L q} (hΩ : Ω ≠ 0) : output (regularizedFilters hb.le a p) Ω ≠ 0 :=
  output_ne_zero_of_invertible _ (fun j => regularizedCoordinateMatrix_invertible hb (a j) (p j)) hΩ

lemma regularized_maximizer_clip {L q m : ℕ} [NeZero q] {X : Fin m → Finset (Vertex L)}
    {b : ℝ} (hb : 0 < b) {a : Fin m → ℝ} (ha : ∀ j, 0 < a j)
    {p : CoordinateFamily q X} {Ω : State L q} (hΩ : Ω ≠ 0)
    (hX : Monotone X) (hp : IsRegularizedMaximizer hb.le Ω a p)
    (hc : ∀ j, Commute (regularizedFilters hb.le a p j).matrix
      (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j))) (j : Fin m) :
    let r := marginalDiagonal (p j).1 (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j))
    ∃ c : ℝ, 0 < c ∧ ∀ i, (p j).2.val i + b = max b (r i / c) := by
  apply Stationarity.simplex_clip _ _ hb (p j).2.property
  · intro i
    exact marginalDiagonal_nonneg _ (reducedDensity_posSemidef _ _) i
  · rw [sum_marginalDiagonal, trace_reducedDensity, ← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr (regularized_output_ne_zero hb a p hΩ))
  · exact regularized_maximizer_gradient hb ha hX hp hc j

end PolynomialPEPS.PinnedEntropy.NestedFilter

end

end OAI
