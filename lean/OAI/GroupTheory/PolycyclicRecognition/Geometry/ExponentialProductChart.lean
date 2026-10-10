import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteLieSmooth
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! # Local product charts from the finite Dynkin identity

Products of exponentials in a basis have a locally surjective logarithm map.
The proof gets smoothness from the finite Dynkin polynomial and its derivative
from the exact one-coordinate restrictions. No smooth-logarithm or local
product assertion is a separate input.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology ContDiff

/-- An ordered product with just one nonidentity factor equals that factor,
without a commutativity assumption. -/
theorem list_prod_ofFn_eq_single {G : Type*} [Monoid G] {n : ℕ}
    (f : Fin n → G) (i : Fin n) (hf : ∀ j, j ≠ i → f j = 1) :
    (List.ofFn f).prod = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun i => ?_) i hf
    · intro hf
      have ht : (List.ofFn (fun j : Fin n => f j.succ)).prod = 1 := by
        apply List.prod_eq_one
        intro g hg
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
        exact hf j.succ (by simp)
      rw [ht, mul_one]
    · intro hf
      rw [hf 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact ih (fun j => f j.succ) i (fun j hj => hf j.succ (by simpa))

/-- The ordered basis-exponential endpoint map. -/
def basisExponentialProduct {L G : Type*} [AddCommGroup L] [Module ℝ L]
    [Monoid G] {n : ℕ} (Exp : L → G) (b : Basis (Fin n) ℝ L) (t : Fin n → ℝ) : G :=
  (List.ofFn (fun i => Exp (t i • b i))).prod

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance exponentialProductNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance exponentialProductNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

variable {G : Type*} [Group G] {n : ℕ} (Exp : L → G) (b : Basis (Fin n) ℝ L)

/-- Its logarithm in a global exponential bijection. -/
def basisProductLog (hExp : Function.Bijective Exp) (t : Fin n → ℝ) : L :=
  (Equiv.ofBijective Exp hExp).symm (basisExponentialProduct Exp b t)

variable (hExp : Function.Bijective Exp) (hzero : Exp 0 = 1)

include hzero in
@[simp] theorem basisProductLog_zero : basisProductLog Exp b hExp 0 = 0 := by
  apply hExp.injective
  rw [show Exp (basisProductLog Exp b hExp 0) = basisExponentialProduct Exp b 0 from
    (Equiv.ofBijective Exp hExp).apply_symm_apply _]
  simp [basisExponentialProduct, hzero]

include hzero in
@[simp] theorem basisProductLog_single (i : Fin n) (s : ℝ) :
    basisProductLog Exp b hExp (Pi.single i s) = s • b i := by
  apply hExp.injective
  rw [show Exp (basisProductLog Exp b hExp (Pi.single i s)) =
    basisExponentialProduct Exp b (Pi.single i s) from
      (Equiv.ofBijective Exp hExp).apply_symm_apply _]
  unfold basisExponentialProduct
  rw [list_prod_ofFn_eq_single _ i (by
    intro j hj
    simp [Pi.single_eq_of_ne hj, hzero])]
  simp

include hExp in
/-- The exact polynomial identity supplies all differentiability of the
logarithmic endpoint map. -/
theorem contDiff_basisProductLog {c : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → L, (List.ofFn (fun i => Exp (X i))).prod =
      Exp (finiteDynkinPolynomial coeff X)) :
    ContDiff ℝ ∞ (basisProductLog Exp b hExp) := by
  have he : basisProductLog Exp b hExp =
      fun t => finiteDynkinPolynomial coeff (fun i => t i • b i) := by
    funext t
    apply hExp.injective
    exact ((Equiv.ofBijective Exp hExp).apply_symm_apply _).trans (hprod _)
  rw [he]
  exact contDiff_finiteDynkinPolynomial coeff _
    (fun i => (contDiff_apply ℝ ℝ i).smul contDiff_const)

include hzero in
/-- The differential of the logarithmic endpoint map at the origin is the
basis synthesis map, proved from its coordinate-axis restrictions. -/
theorem fderiv_basisProductLog_zero
    (hd : DifferentiableAt ℝ (basisProductLog Exp b hExp) 0) :
    fderiv ℝ (basisProductLog Exp b hExp) 0 = b.equivFun.symm.toContinuousLinearEquiv := by
  apply ContinuousLinearMap.ext
  intro t
  have hcol (i : Fin n) :
      fderiv ℝ (basisProductLog Exp b hExp) 0 (Pi.single i 1) = b i := by
    have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (hasDerivAt_single i (0 : ℝ)) (by simp)
    have he : (fun s : ℝ => basisProductLog Exp b hExp (Pi.single i s)) =
        fun s => s • b i := by funext s; exact basisProductLog_single Exp b hExp hzero i s
    change HasDerivAt (fun s : ℝ => basisProductLog Exp b hExp (Pi.single i s)) _ 0 at h
    rw [he] at h
    exact h.unique (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const (b i))
  calc
    _ = fderiv ℝ (basisProductLog Exp b hExp) 0
        (∑ i, t i • Pi.single i (1 : ℝ)) := congrArg _ (pi_eq_sum_univ' t)
    _ = ∑ i, t i • b i := by simp only [map_sum, map_smul, hcol]
    _ = _ := by
      change (∑ i, t i • b i) = b.equivFun.symm t
      simpa only [LinearEquiv.apply_symm_apply] using b.sum_equivFun (b.equivFun.symm t)

include hzero in
/-- The basis exponential map covers a logarithmic neighborhood using
parameters from any prescribed neighborhood of zero. -/
theorem basisProductLog_map_nhds {c : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → L, (List.ofFn (fun i => Exp (X i))).prod =
      Exp (finiteDynkinPolynomial coeff X)) :
    map (basisProductLog Exp b hExp) (𝓝 0) = 𝓝 (0 : L) := by
  have hc := contDiff_basisProductLog Exp b hExp coeff hprod
  have hf : ContDiffAt ℝ 1 (basisProductLog Exp b hExp) 0 :=
    hc.contDiffAt.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have he := fderiv_basisProductLog_zero Exp b hExp hzero
    (hf.differentiableAt one_ne_zero)
  have hs := (hf.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj
    (by rw [he]; exact LinearMap.range_eq_top.mpr b.equivFun.symm.surjective)
  simpa only [basisProductLog_zero Exp b hExp hzero] using hs

include hzero in
/-- A fixed parameter ball suffices for a nonzero logarithmic ball. -/
theorem exists_ball_subset_basisProductLog_image {c : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → L, (List.ofFn (fun i => Exp (X i))).prod =
      Exp (finiteDynkinPolynomial coeff X)) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : L) ε ⊆
      basisProductLog Exp b hExp '' Metric.ball (0 : Fin n → ℝ) 1 := by
  have hm := basisProductLog_map_nhds Exp b hExp hzero coeff hprod
  have him : basisProductLog Exp b hExp '' Metric.ball (0 : Fin n → ℝ) 1 ∈ 𝓝 (0 : L) := by
    rw [← hm]
    exact Filter.image_mem_map (Metric.ball_mem_nhds _ zero_lt_one)
  exact Metric.mem_nhds_iff.mp him

end PolycyclicRecognition

end

end OAI
