import Mathlib
import OAI.Analysis.BoundedHochschild.CollisionBounds
import OAI.Analysis.BoundedHochschild.HarmonicSums
import OAI.Analysis.BoundedHochschild.MatrixDilation

namespace OAI

/-! Approximate power identities and rigidity for contractions. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildRigidity
noncomputable section
open scoped ComplexOrder BigOperators
open Finset
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)

def unitaryHarmonicError {K : ℕ} [NeZero K] (S : A →L[ℂ] A)
    (u : unitary A) (a b : A) (n : ℕ) (j : ZMod (K^2)) : A :=
  let v : unitary A := rootUnitary (-j) • u
  S (harmonicPolynomial n (v:A) - star (harmonicPolynomial n (v:A))) -
    (a * harmonicPolynomial n (v:A) - b * star (harmonicPolynomial n (v:A)))

theorem unitary_power_approx_multiplier_bound [Nontrivial A]
    (h1 : τ 1 = 1) (htr : ∀ a b : A, τ (a * b) = τ (b * a))
    (S : A →L[ℂ] A) (u : unitary A) (a b : A)
    (n : ℕ) {K : ℕ} [NeZero K] :
    (harmonic n : ℝ) * ‖τ.toPreGNS (a - b)‖ ≤
      (2 * (1 + Real.pi)) * ‖S‖ + (‖a‖ + ‖b‖) * ((2 * n : ℝ) / K) +
      ‖gnsFamily τ (fun j : ZMod (K^2) => unitaryHarmonicError S u a b n j *
        fourierWindow (u:A) j)‖ := by
  let q : ZMod (K ^ 2) → A := fun j => fourierWindow (u : A) j
  let v : ZMod (K ^ 2) → unitary A := fun j => rootUnitary (-j) • u
  have hq : ∑ j, q j * star (q j) = 1 := sum_fourierWindow_mul_star u
  have hv (j) : ‖(v j : A) * q j - q j‖ ≤ 2 / (K : ℝ) ^ 2 := by
    simpa only [q, v, Nat.cast_pow] using norm_unitary_mul_fourierWindow_sub_le u j
  have hvneg (j) : ‖(star (v j) : A) * q j - q j‖ ≤ 2 / (K : ℝ) ^ 2 := by
    rw [norm_star_unitary_mul_sub]
    exact hv j
  let ep := fun j => harmonicPolynomial n (v j : A) * q j - (harmonic n : ℂ) • q j
  let em := fun j => star (harmonicPolynomial n (v j : A)) * q j - (harmonic n : ℂ) • q j
  let F := fun j => S (harmonicPolynomial n (v j : A) - star (harmonicPolynomial n (v j : A)))
  have hep : ‖gnsFamily τ ep‖ ≤ (2 * n : ℝ) / K :=
    norm_gnsFamily_harmonic_error_le τ h1 q v hv n
  have hem : ‖gnsFamily τ em‖ ≤ (2 * n : ℝ) / K := by
    simpa only [em, star_harmonicPolynomial, Unitary.coe_star] using
      norm_gnsFamily_harmonic_error_le τ h1 q (fun j => star (v j)) hvneg n
  let E := fun j : ZMod (K^2) => unitaryHarmonicError S u a b n j
  have hFbound (j) : ‖F j‖ ≤ (2 * (1 + Real.pi)) * ‖S‖ := by
    calc
      _ ≤ ‖S‖ * ‖harmonicPolynomial n (v j : A) - star (harmonicPolynomial n (v j : A))‖ := S.le_opNorm _
      _ ≤ ‖S‖ * (2 * (1 + Real.pi)) := by
        gcongr
        exact norm_unitary_harmonicPolynomial_sub_star_le (v j) n
      _ = _ := mul_comm _ _
  have hqn : ‖gnsFamily τ q‖ = 1 := by
    simpa only [one_mul, preGNS_norm_one τ h1] using norm_gnsFamily_mul τ htr q hq 1
  have hFn : ‖gnsFamily τ (fun j => F j * q j)‖ ≤ (2 * (1 + Real.pi)) * ‖S‖ := by
    simpa only [hqn, mul_one] using
      norm_gnsFamily_leftMul_le τ F q _ (by positivity) hFbound
  have hepn : ‖gnsFamily τ (fun j => a * ep j)‖ ≤ ‖a‖ * ((2 * n : ℝ) / K) :=
    (norm_gnsFamily_leftMul_le τ (fun _ => a) ep ‖a‖ (norm_nonneg _) (fun _ => le_rfl)).trans
      (by gcongr)
  have hemn : ‖gnsFamily τ (fun j => b * em j)‖ ≤ ‖b‖ * ((2 * n : ℝ) / K) :=
    (norm_gnsFamily_leftMul_le τ (fun _ => b) em ‖b‖ (norm_nonneg _) (fun _ => le_rfl)).trans
      (by gcongr)
  have hid (j) : (harmonic n : ℂ) • ((a - b) * q j) =
      F j * q j - a * ep j + b * em j - E j * q j := by
    change (harmonic n : ℂ) • ((a - b) * q j) =
      F j * q j - a * ep j + b * em j -
      (F j - (a * harmonicPolynomial n (v j:A) - b * star (harmonicPolynomial n (v j:A)))) * q j
    simp only [ep, em, sub_mul, mul_sub, smul_sub, mul_smul_comm]
    noncomm_ring
  have hh : 0 ≤ (harmonic n : ℝ) := by unfold harmonic; positivity
  have hhnorm : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_of_nonneg hh]
  calc
    _ = ‖gnsFamily τ (fun j => (harmonic n : ℂ) • ((a - b) * q j))‖ := by
      rw [gnsFamily_smul, norm_smul, hhnorm, norm_gnsFamily_mul τ htr q hq]
    _ = ‖gnsFamily τ (fun j => F j * q j) - gnsFamily τ (fun j => a * ep j) +
        gnsFamily τ (fun j => b * em j) - gnsFamily τ (fun j => E j * q j)‖ := by
      simp only [hid, gnsFamily_add, gnsFamily_sub]
    _ ≤ (‖gnsFamily τ (fun j => F j * q j)‖ + ‖gnsFamily τ (fun j => a * ep j)‖) +
        ‖gnsFamily τ (fun j => b * em j)‖ + ‖gnsFamily τ (fun j => E j * q j)‖ :=
      (norm_sub_le _ _).trans (by
        gcongr
        exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _))
    _ ≤ _ := by nlinarith [hFn, hepn, hemn]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_fourierWindow_le_one [Nontrivial A] {L : ℕ} [NeZero L]
    (u : unitary A) (j : ZMod L) : ‖fourierWindow (u:A) j‖ ≤ 1 := by
  let v : unitary A := rootUnitary (-j) • u
  change ‖fourierWindow (u:A) j‖ ≤ 1
  rw [fourierWindow_eq_geometric, norm_smul, norm_inv, Complex.norm_natCast]
  have hn (k : ℕ) : ‖(ZMod.stdAddChar (-j) • (u:A))^k‖ = 1 := by
    change ‖(v:A)^k‖ = 1
    simpa only [SubmonoidClass.coe_pow] using CStarRing.norm_coe_unitary (v^k)
  calc
    _ ≤ (L:ℝ)⁻¹ * ∑ k ∈ range L, ‖(ZMod.stdAddChar (-j) • (u:A))^k‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = 1 := by simp only [hn, sum_const, card_range, nsmul_eq_mul, mul_one]
                exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne L))

lemma tendsto_smul_power_error (S : A →L[ℂ] A) (u : ℕ → A) (a : A)
    (hp : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S (u r ^ k) - a * u r ^ k)) Filter.atTop (nhds 0))
    (c : ℂ) (k : ℕ) (hk : 0 < k) : Filter.Tendsto
      (fun r => τ.toPreGNS (S ((c • u r)^k) - a * (c • u r)^k))
      Filter.atTop (nhds 0) := by
  have he (r) : τ.toPreGNS (S ((c • u r)^k) - a * (c • u r)^k) =
      c^k • τ.toPreGNS (S (u r^k) - a*u r^k) := by
    simp only [smul_pow, map_smul, mul_smul_comm, ← smul_sub]
  simpa only [he, smul_zero] using (hp k hk).const_smul (c^k)

lemma tendsto_harmonic_power_error (S : A →L[ℂ] A) (u : ℕ → A) (a : A)
    (hp : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S (u r ^ k) - a * u r ^ k)) Filter.atTop (nhds 0))
    (n : ℕ) : Filter.Tendsto
      (fun r => τ.toPreGNS (S (harmonicPolynomial n (u r)) -
        a * harmonicPolynomial n (u r))) Filter.atTop (nhds 0) := by
  have he (r) : τ.toPreGNS (S (harmonicPolynomial n (u r)) -
        a * harmonicPolynomial n (u r)) =
      ∑ i ∈ range n, ((i+1:ℂ)⁻¹) • τ.toPreGNS (S (u r^(i+1))-a*u r^(i+1)) := by
    simp only [harmonicPolynomial, map_sum, map_smul, mul_sum, mul_smul_comm,
      ← sum_sub_distrib, ← smul_sub]
  simp_rw [he]
  simpa only [smul_zero, sum_const_zero] using
    tendsto_finsetSum (range n) (fun i _ => (hp (i+1) (Nat.succ_pos i)).const_smul ((i+1:ℂ)⁻¹))

lemma tendsto_unitaryHarmonicError (S : A →L[ℂ] A) (u : ℕ → unitary A) (a b : A)
    (hp : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S ((u r:A)^k)-a*(u r:A)^k)) Filter.atTop (nhds 0))
    (hm : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S (star (u r:A)^k)-b*star (u r:A)^k)) Filter.atTop (nhds 0))
    (n : ℕ) {K : ℕ} [NeZero K] (j : ZMod (K^2)) : Filter.Tendsto
      (fun r => τ.toPreGNS (unitaryHarmonicError S (u r) a b n j)) Filter.atTop (nhds 0) := by
  let c := ZMod.stdAddChar (-j)
  have hp' := tendsto_harmonic_power_error τ S (fun r => c • (u r:A)) a
    (fun k hk => tendsto_smul_power_error τ S (fun r => (u r:A)) a hp c k hk) n
  have hm' := tendsto_harmonic_power_error τ S (fun r => star c • star (u r:A)) b
    (fun k hk => tendsto_smul_power_error τ S (fun r => star (u r:A)) b hm (star c) k hk) n
  have he (r) : τ.toPreGNS (unitaryHarmonicError S (u r) a b n j) =
      τ.toPreGNS (S (harmonicPolynomial n (c • (u r:A))) - a*harmonicPolynomial n (c • (u r:A))) -
      τ.toPreGNS (S (harmonicPolynomial n (star c • star (u r:A))) -
        b*harmonicPolynomial n (star c • star (u r:A))) := by
    change τ.toPreGNS (S (harmonicPolynomial n (c • (u r:A)) -
      star (harmonicPolynomial n (c • (u r:A)))) -
      (a * harmonicPolynomial n (c • (u r:A)) - b * star (harmonicPolynomial n (c • (u r:A))))) = _
    simp only [star_harmonicPolynomial, star_smul, map_sub]
    abel
  simpa only [he, sub_self] using hp'.sub hm'

lemma tendsto_preGNS_mul_zero_of_contraction
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (f g : ℕ → A)
    (hf : Filter.Tendsto (fun r => τ.toPreGNS (f r)) Filter.atTop (nhds 0))
    (hg : ∀ r, ‖g r‖ ≤ 1) :
    Filter.Tendsto (fun r => τ.toPreGNS (f r * g r)) Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun r =>
    (preGNS_norm_mul_right_le τ htr _ _).trans ((mul_le_mul_of_nonneg_right (hg r)
      (norm_nonneg _)).trans_eq (one_mul _)))
  simpa only [norm_zero] using hf.norm

lemma tendsto_harmonic_errorFamily [Nontrivial A]
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (S : A →L[ℂ] A) (u : ℕ → unitary A) (a b : A)
    (hp : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S ((u r:A)^k)-a*(u r:A)^k)) Filter.atTop (nhds 0))
    (hm : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S (star (u r:A)^k)-b*star (u r:A)^k)) Filter.atTop (nhds 0))
    (n : ℕ) {K : ℕ} [NeZero K] : Filter.Tendsto
      (fun r => ‖gnsFamily τ (fun j : ZMod (K^2) =>
        unitaryHarmonicError S (u r) a b n j * fourierWindow (u r:A) j)‖)
      Filter.atTop (nhds 0) := by
  have he (j : ZMod (K^2)) := tendsto_preGNS_mul_zero_of_contraction τ htr
    (fun r => unitaryHarmonicError S (u r) a b n j)
    (fun r => fourierWindow (u r:A) j)
    (tendsto_unitaryHarmonicError τ S u a b hp hm n j)
    (fun r => norm_fourierWindow_le_one (u r) j)
  have hf := (PiLp.continuous_toLp (p:=2) (β:=fun _ : ZMod (K^2) => τ.PreGNS)).continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr he)
  have hf' : Filter.Tendsto
      (fun r => gnsFamily τ (fun j : ZMod (K^2) =>
        unitaryHarmonicError S (u r) a b n j * fourierWindow (u r:A) j))
      Filter.atTop (nhds 0) := hf
  simpa only [norm_zero] using hf'.norm

 
theorem unitary_power_rigidity_of_tendsto
    (h1 : τ 1 = 1) (htr : ∀ a b : A, τ (a * b) = τ (b * a))
    (hfaithful : ∀ x : A, τ (star x * x) = 0 → x = 0)
    (S : A →L[ℂ] A) (u : ℕ → unitary A) (a b : A)
    (hpos : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S ((u r:A)^k)-a*(u r:A)^k)) Filter.atTop (nhds 0))
    (hneg : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S (star (u r:A)^k)-b*star (u r:A)^k)) Filter.atTop (nhds 0)) :
    a = b := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  let C : ℝ := (2 * (1 + Real.pi)) * ‖S‖
  have happrox (n : ℕ) (K : ℕ) [NeZero K] :
      (harmonic n : ℝ) * ‖τ.toPreGNS (a-b)‖ ≤
      C + (‖a‖+‖b‖)*((2*n:ℝ)/K) := by
    have he := tendsto_harmonic_errorFamily τ htr S u a b hpos hneg n (K:=K)
    have ht := (tendsto_const_nhds (x := C + (‖a‖+‖b‖)*((2*n:ℝ)/K))).add he
    have ht' : Filter.Tendsto
        (fun r => C + (‖a‖+‖b‖)*((2*n:ℝ)/K) +
          ‖gnsFamily τ (fun j : ZMod (K^2) => unitaryHarmonicError S (u r) a b n j *
            fourierWindow (u r:A) j)‖) Filter.atTop
        (nhds (C + (‖a‖+‖b‖)*((2*n:ℝ)/K))) := by simpa only [add_zero] using ht
    apply ge_of_tendsto ht'
    exact Filter.Eventually.of_forall fun r =>
      unitary_power_approx_multiplier_bound τ h1 htr S (u r) a b n (K:=K)
  have hbound (n : ℕ) : (harmonic n : ℝ) * ‖τ.toPreGNS (a - b)‖ ≤ C := by
    have hl : Filter.Tendsto (fun m : ℕ =>
        C + (‖a‖ + ‖b‖) * ((2 * n : ℝ) / ((m : ℝ) + 1)))
        Filter.atTop (nhds C) := by
      simpa only [mul_zero, add_zero, mul_one_div] using
        tendsto_const_nhds.add
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (n : ℝ)) |>.const_mul (‖a‖ + ‖b‖))
    apply ge_of_tendsto hl
    apply Filter.Eventually.of_forall
    intro m
    simpa only [Nat.cast_add, Nat.cast_one] using
      happrox n (m+1)
  have hdiv : Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono log_add_one_le_harmonic
      (Real.tendsto_log_atTop.comp
        ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
          Filter.atTop Filter.atTop).comp (Filter.tendsto_add_atTop_nat 1)))
  have hz : ‖τ.toPreGNS (a - b)‖ = 0 := by
    by_contra hne
    have hp : 0 < ‖τ.toPreGNS (a - b)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨n, hn⟩ := ((hdiv.atTop_mul_const hp).eventually_gt_atTop C).exists
    exact (not_lt_of_ge (hbound n)) hn
  exact sub_eq_zero.mp ((preGNS_norm_eq_zero_iff τ hfaithful (a - b)).mp hz)

end
end HochschildRigidity

namespace HochschildMatrixDilation
noncomputable section
open scoped ComplexOrder
open Filter HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)

local instance powerRigidityMatrixContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ (Mat A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance powerRigidityMatrixNonnegSpectrum : NonnegSpectrumClass ℝ (Mat A) :=
  CStarAlgebra.instNonnegSpectrumClass

lemma matrixTrace_entry_le (M : Mat A) (i j : Fin 2) :
    ‖τ.toPreGNS (M i j)‖ ≤ 2 * ‖(matrixTrace τ).toPreGNS M‖ := by
  have he := matrixTrace_norm_sq τ M
  have h00 := sq_nonneg ‖τ.toPreGNS (M 0 0)‖
  have h10 := sq_nonneg ‖τ.toPreGNS (M 1 0)‖
  have h01 := sq_nonneg ‖τ.toPreGNS (M 0 1)‖
  have h11 := sq_nonneg ‖τ.toPreGNS (M 1 1)‖
  have hM := sq_nonneg ‖(matrixTrace τ).toPreGNS M‖
  have hn00 : ‖τ.toPreGNS (M 0 0)‖^2 ≤ (2*‖(matrixTrace τ).toPreGNS M‖)^2 := by nlinarith
  have hn10 : ‖τ.toPreGNS (M 1 0)‖^2 ≤ (2*‖(matrixTrace τ).toPreGNS M‖)^2 := by nlinarith
  have hn01 : ‖τ.toPreGNS (M 0 1)‖^2 ≤ (2*‖(matrixTrace τ).toPreGNS M‖)^2 := by nlinarith
  have hn11 : ‖τ.toPreGNS (M 1 1)‖^2 ≤ (2*‖(matrixTrace τ).toPreGNS M‖)^2 := by nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  fin_cases i <;> fin_cases j
  · exact hn00
  · exact hn01
  · exact hn10
  · exact hn11

lemma tendsto_matrixTrace_of_entries (M : ℕ → Mat A)
    (hM : ∀ i j, Tendsto (fun r => ‖τ.toPreGNS (M r i j)‖) atTop (nhds 0)) :
    Tendsto (fun r => ‖(matrixTrace τ).toPreGNS (M r)‖) atTop (nhds 0) := by
  have he : Tendsto (fun r => ‖(matrixTrace τ).toPreGNS (M r)‖^2) atTop (nhds 0) := by
    simp_rw [matrixTrace_norm_sq]
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_add, zero_div] using
      ((((hM 0 0).pow 2).add ((hM 1 0).pow 2)).add ((hM 0 1).pow 2) |>.add ((hM 1 1).pow 2) |>.div_const 2)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using he.sqrt

lemma matrixMap_sequential (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (M : ℕ → Mat A) (hM : ∃ C : ℝ, ∀ r, ‖M r‖ ≤ C)
    (ht : Tendsto (fun r => ‖(matrixTrace τ).toPreGNS (M r)‖) atTop (nhds 0)) :
    Tendsto (fun r => ‖(matrixTrace τ).toPreGNS (matrixMap R (M r))‖) atTop (nhds 0) := by
  apply tendsto_matrixTrace_of_entries
  intro i j
  apply hR (fun r => M r i j)
  · obtain ⟨C,hC⟩ := hM
    exact ⟨C,fun r => CStarMatrix.norm_entry_le_norm.trans (hC r)⟩
  · exact squeeze_zero (fun _ => norm_nonneg _) (fun r => matrixTrace_entry_le τ (M r) i j)
      (by simpa only [mul_zero] using ht.const_mul 2)

lemma preGNS_norm_pow_sub_le [Nontrivial A]
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a b : A)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (k : ℕ) :
    ‖τ.toPreGNS (a^k-b^k)‖ ≤ (k:ℝ)*‖τ.toPreGNS (a-b)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : a^(k+1)-b^(k+1) = a*(a^k-b^k)+(a-b)*b^k := by
      rw [pow_succ' a, pow_succ' b]
      noncomm_ring
    rw [he, map_add]
    have hbk : ‖b^k‖ ≤ 1 := (norm_pow_le b k).trans (by simpa using pow_le_pow_left₀ (norm_nonneg b) hb k)
    calc
      _ ≤ ‖τ.toPreGNS (a*(a^k-b^k))‖+‖τ.toPreGNS ((a-b)*b^k)‖ := norm_add_le _ _
      _ ≤ ‖a‖*‖τ.toPreGNS (a^k-b^k)‖+‖b^k‖*‖τ.toPreGNS (a-b)‖ :=
        add_le_add (preGNS_norm_mul_le τ _ _) (preGNS_norm_mul_right_le τ htr _ _)
      _ ≤ 1*((k:ℝ)*‖τ.toPreGNS (a-b)‖)+1*‖τ.toPreGNS (a-b)‖ := by gcongr
      _ = _ := by push_cast; ring

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma diag_pow (a b : A) (k : ℕ) : (diag a b)^k = diag (a^k) (b^k) := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ, ih, diag_mul]

lemma tendsto_multiplier_error_transfer (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (x y : ℕ → A) (c : A)
    (hb : ∃ C : ℝ, ∀ r, ‖x r-y r‖ ≤ C)
    (hd : Tendsto (fun r => ‖τ.toPreGNS (x r-y r)‖) atTop (nhds 0))
    (hy : Tendsto (fun r => ‖τ.toPreGNS (R (y r)-c*y r)‖) atTop (nhds 0)) :
    Tendsto (fun r => ‖τ.toPreGNS (R (x r)-c*x r)‖) atTop (nhds 0) := by
  have hr := hR (fun r => x r-y r) hb hd
  have hmajor := (hr.add (hd.const_mul ‖c‖)).add hy
  simp only [mul_zero, zero_add] at hmajor
  apply squeeze_zero (fun _ => norm_nonneg _) _ hmajor
  intro r
  have he : R (x r)-c*x r = (R (x r-y r)-c*(x r-y r))+(R (y r)-c*y r) := by
    rw [map_sub, mul_sub]; abel
  rw [he]
  simp only [map_add, map_sub]
  have hn := preGNS_norm_mul_le τ c (x r-y r)
  rw [map_sub] at hn
  calc
    _ ≤ ‖τ.toPreGNS (R (x r-y r)) - τ.toPreGNS (c*(x r-y r))‖ +
        ‖τ.toPreGNS (R (y r)-c*y r)‖ := by
      simpa only [map_sub] using (norm_add_le
        (τ.toPreGNS (R (x r-y r)) - τ.toPreGNS (c*(x r-y r)))
        (τ.toPreGNS (R (y r)-c*y r)))
    _ ≤ _ := by
      have h := norm_sub_le (τ.toPreGNS (R (x r-y r))) (τ.toPreGNS (c*(x r-y r)))
      simp only [map_sub] at h ⊢
      linarith

lemma tendsto_preGNS_pow_sub [Nontrivial A]
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (x y : ℕ → A)
    (hx : ∀ r, ‖x r‖ ≤ 1) (hy : ∀ r, ‖y r‖ ≤ 1)
    (hd : Tendsto (fun r => ‖τ.toPreGNS (x r-y r)‖) atTop (nhds 0)) (k : ℕ) :
    Tendsto (fun r => ‖τ.toPreGNS ((x r)^k-(y r)^k)‖) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun r => preGNS_norm_pow_sub_le τ htr (x r) (y r) (hx r) (hy r) k)
  simpa only [mul_zero] using hd.const_mul (k:ℝ)

 

theorem contraction_power_rigidity
    (h1 : τ 1 = 1) (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ x : A, τ (star x*x) = 0 → x = 0)
    (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (q : ℕ → A) (hq : ∀ r, ‖q r‖ ≤ 1)
    (hdef : Tendsto (fun r => (τ (1-star (q r)*q r)).re) atTop (nhds 0))
    (a b : A)
    (hp : ∀ k : ℕ, 0 < k → Tendsto
      (fun r => ‖τ.toPreGNS (R ((q r)^k)-a*(q r)^k)‖) atTop (nhds 0))
    (hm : ∀ k : ℕ, 0 < k → Tendsto
      (fun r => ‖τ.toPreGNS (R (star (q r)^k)-b*star (q r)^k)‖) atTop (nhds 0)) :
    a = b := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  let U : ℕ → unitary (Mat A) := fun r => dilation (q r) (hq r)
  let D : ℕ → Mat A := fun r => diag (q r) (star (q r))
  let T := matrixTrace τ
  have hTtr := matrixTrace_tracial τ htr
  have hD (r : ℕ) : ‖D r‖ ≤ 1 := by
    exact (norm_diag_le _ _).trans (max_le (hq r) (by simpa only [norm_star] using hq r))
  have hU (r : ℕ) : ‖(U r:Mat A)‖ ≤ 1 := by simp
  have hd : Tendsto (fun r => ‖T.toPreGNS ((U r:Mat A)-D r)‖) atTop (nhds 0) := by
    have hs : Tendsto (fun r => ‖T.toPreGNS ((U r:Mat A)-D r)‖^2) atTop (nhds 0) := by
      simpa only [U,D,T,dilation_error_sq τ htr] using hdef
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt
  have hmd : Tendsto (fun r => ‖T.toPreGNS (star (U r:Mat A)-star (D r))‖)
      atTop (nhds 0) := by
    simpa only [← star_sub, preGNS_norm_star T hTtr] using hd
  have hdpos (k : ℕ) := tendsto_preGNS_pow_sub T hTtr (fun r => (U r:Mat A)) D hU hD hd k
  have hdneg (k : ℕ) := tendsto_preGNS_pow_sub T hTtr (fun r => star (U r:Mat A))
    (fun r => star (D r)) (by simpa only [norm_star] using hU)
    (by simpa only [norm_star] using hD) hmd k
  have hbound (x y : ℕ → Mat A) (hx : ∀ r, ‖x r‖ ≤ 1) (hy : ∀ r, ‖y r‖ ≤ 1)
      (k : ℕ) : ∃ C : ℝ, ∀ r, ‖(x r)^k-(y r)^k‖ ≤ C := by
    refine ⟨2,fun r => (norm_sub_le _ _).trans ?_⟩
    have hxk : ‖(x r)^k‖ ≤ 1 := (norm_pow_le _ _).trans (by simpa using pow_le_pow_left₀ (norm_nonneg (x r)) (hx r) k)
    have hyk : ‖(y r)^k‖ ≤ 1 := (norm_pow_le _ _).trans (by simpa using pow_le_pow_left₀ (norm_nonneg (y r)) (hy r) k)
    linarith
  have hdp (k : ℕ) (hk : 0 < k) : Tendsto
      (fun r => ‖T.toPreGNS (matrixMap R ((D r)^k)-diag a b*(D r)^k)‖) atTop (nhds 0) := by
    apply tendsto_matrixTrace_of_entries
    intro i j
    simp only [D,diag_pow,matrixMap_diag,diag_mul]
    fin_cases i <;> fin_cases j
    · simpa [diag] using hp k hk
    · simp [diag]
    · simp [diag]
    · simpa [diag] using hm k hk
  have hdm (k : ℕ) (hk : 0 < k) : Tendsto
      (fun r => ‖T.toPreGNS (matrixMap R (star (D r)^k)-diag b a*star (D r)^k)‖) atTop (nhds 0) := by
    apply tendsto_matrixTrace_of_entries
    intro i j
    simp only [D,star_diag,star_star,diag_pow,matrixMap_diag,diag_mul]
    fin_cases i <;> fin_cases j
    · simpa [diag] using hm k hk
    · simp [diag]
    · simp [diag]
    · simpa [diag] using hp k hk
  have he : diag a b = diag b a := unitary_power_rigidity_of_tendsto T
    (matrixTrace_one τ h1) hTtr (matrixTrace_faithful τ hf) (matrixMap R) U (diag a b) (diag b a)
    (fun k hk => tendsto_zero_iff_norm_tendsto_zero.mpr
      (tendsto_multiplier_error_transfer T (matrixMap R) (matrixMap_sequential τ R hR)
        (fun r => (U r:Mat A)^k) (fun r => (D r)^k) (diag a b)
        (hbound _ _ hU hD k) (hdpos k) (hdp k hk)))
    (fun k hk => tendsto_zero_iff_norm_tendsto_zero.mpr
      (tendsto_multiplier_error_transfer T (matrixMap R) (matrixMap_sequential τ R hR)
        (fun r => star (U r:Mat A)^k) (fun r => star (D r)^k) (diag b a)
        (hbound _ _ (by simpa only [norm_star] using hU)
          (by simpa only [norm_star] using hD) k) (hdneg k) (hdm k hk)))
  exact congrArg (fun M : Mat A => M 0 0) he

end
end HochschildMatrixDilation
end

end OAI
