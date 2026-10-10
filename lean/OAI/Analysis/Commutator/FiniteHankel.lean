import Mathlib
import OAI.Analysis.Commutator.FejerTest

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.FreeCorner

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def compress (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) : K →L[ℂ] K :=
  (V.toContinuousLinearMap.adjoint.comp T).comp V.toContinuousLinearMap

lemma norm_compress_le (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    ‖compress V T‖ ≤ ‖T‖ := by
  have hv : ‖V.toContinuousLinearMap‖ ≤ 1 := V.norm_toContinuousLinearMap_le
  have hv' : ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by rw [adjoint.norm_map]; exact hv
  calc
    ‖compress V T‖ ≤ ‖V.toContinuousLinearMap.adjoint‖ * ‖T‖ *
        ‖V.toContinuousLinearMap‖ := (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖T‖ * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hv' (norm_nonneg _)) hv (norm_nonneg _)
      (by positivity)
    _ = ‖T‖ := by ring

lemma compression_commutator_identity (V : K →ₗᵢ[ℂ] H)
    (G L : H →L[ℂ] H) (J : K →L[ℂ] K) :
    compress V (G * L - L * G) =
      J * compress V L - compress V L * J +
      (G.adjoint.comp V.toContinuousLinearMap -
        V.toContinuousLinearMap.comp J.adjoint).adjoint.comp
        (L.comp V.toContinuousLinearMap) -
      V.toContinuousLinearMap.adjoint.comp
        (L.comp (G.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp J)) := by
  simp only [compress, mul_def, comp_sub, sub_comp, map_sub,
    adjoint_comp, adjoint_adjoint, comp_assoc]
  abel

lemma norm_compression_commutator_le (V : K →ₗᵢ[ℂ] H)
    (G L : H →L[ℂ] H) (J : K →L[ℂ] K) {d d' : ℝ}
    (hd : ‖G.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp J‖ ≤ d)
    (hd' : ‖G.adjoint.comp V.toContinuousLinearMap -
      V.toContinuousLinearMap.comp J.adjoint‖ ≤ d') :
    ‖J * compress V L - compress V L * J‖ ≤
      ‖G * L - L * G‖ + (d + d') * ‖L‖ := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hd0' : 0 ≤ d' := (norm_nonneg _).trans hd'
  let R := G.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp J
  let R' := G.adjoint.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp J.adjoint
  have hv : ‖V.toContinuousLinearMap‖ ≤ 1 := V.norm_toContinuousLinearMap_le
  have hv' : ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by rw [adjoint.norm_map]; exact hv
  have h1 : ‖R'.adjoint.comp (L.comp V.toContinuousLinearMap)‖ ≤ d' * ‖L‖ := by
    calc
      _ ≤ ‖R'.adjoint‖ * (‖L‖ * ‖V.toContinuousLinearMap‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ d' * (‖L‖ * 1) := mul_le_mul
        (by simpa only [adjoint.norm_map, R'] using hd')
        (mul_le_mul_of_nonneg_left hv (norm_nonneg _)) (by positivity) hd0'
      _ = d' * ‖L‖ := by ring
  have h2 : ‖V.toContinuousLinearMap.adjoint.comp (L.comp R)‖ ≤ d * ‖L‖ := by
    calc
      _ ≤ ‖V.toContinuousLinearMap.adjoint‖ * (‖L‖ * ‖R‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖L‖ * d) := mul_le_mul hv'
        (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) (by positivity) (by positivity)
      _ = d * ‖L‖ := by ring
  have heq : J * compress V L - compress V L * J =
      compress V (G * L - L * G) - R'.adjoint.comp (L.comp V.toContinuousLinearMap) +
        V.toContinuousLinearMap.adjoint.comp (L.comp R) := by
    rw [compression_commutator_identity]
    dsimp [R, R']
    abel
  rw [heq]
  calc
    _ ≤ ‖compress V (G * L - L * G)‖ +
        ‖R'.adjoint.comp (L.comp V.toContinuousLinearMap)‖ +
        ‖V.toContinuousLinearMap.adjoint.comp (L.comp R)‖ := (norm_add_le _ _).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖G * L - L * G‖ + d' * ‖L‖ + d * ‖L‖ :=
      add_le_add (add_le_add (norm_compress_le V _) h1) h2
    _ = _ := by ring

lemma compressed_commutator_bound (V : K →ₗᵢ[ℂ] H)
    (G L : H →L[ℂ] H) (J : K →L[ℂ] K) {c ε : ℝ}
    (hG : ‖G * L - L * G‖ ≤ ε * ‖L‖)
    (hR : ‖G.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp J‖ ≤ 2*c*ε)
    (hR' : ‖G.adjoint.comp V.toContinuousLinearMap -
      V.toContinuousLinearMap.comp J.adjoint‖ ≤ 2*c*ε) :
    ‖J * compress V L - compress V L * J‖ ≤ (1+4*c)*ε*‖L‖ := by
  calc
    _ ≤ ‖G * L - L * G‖ + (2*c*ε + 2*c*ε)*‖L‖ :=
      norm_compression_commutator_le V G L J hR hR'
    _ ≤ ε*‖L‖ + (2*c*ε + 2*c*ε)*‖L‖ := add_le_add hG le_rfl
    _ = _ := by ring

end Kadison.FreeCorner

namespace Kadison.FiniteCompression

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [CompleteSpace H] [DecidableEq I] in
lemma inner_sum_diagonal (x y : I → H)
    (h : ∀ i j, i ≠ j → inner ℂ (x i) (y j) = 0) :
    inner ℂ (∑ i, x i) (∑ i, y i) = ∑ i, inner ℂ (x i) (y i) := by
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_eq_single i (fun j _ hji => h j i hji) (by simp)

omit [CompleteSpace H] [DecidableEq I] in
lemma norm_sum_sq (x : I → H) (h : ∀ i j, i ≠ j → inner ℂ (x i) (x j) = 0) :
    ‖∑ i, x i‖^2 = ∑ i, ‖x i‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_sum_diagonal x x h, map_sum]
  exact Finset.sum_congr rfl (fun i _ => (norm_sq_eq_re_inner (𝕜 := ℂ) (x i)).symm)

def average (c : ℝ) (U : I → K →L[ℂ] H) : K →L[ℂ] H :=
  (c : ℂ) • ∑ i, U i

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
@[simp] lemma average_apply (c : ℝ) (U : I → K →L[ℂ] H) (x : K) :
    average c U x = (c : ℂ) • ∑ i, U i x := by simp [average]

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
lemma average_inner (c : ℝ) (U : I → K →ₗᵢ[ℂ] H)
    (horth : ∀ i j, i ≠ j → ∀ x y : K, inner ℂ (U i x) (U j y) = 0)
    (hscale : c^2 * Fintype.card I = 1) (x y : K) :
    inner ℂ (average c (fun i => (U i).toContinuousLinearMap) x)
      (average c (fun i => (U i).toContinuousLinearMap) y) = inner ℂ x y := by
  simp only [average_apply, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, LinearIsometry.coe_toContinuousLinearMap]
  rw [inner_sum_diagonal (fun i => U i x) (fun i => U i y)
    (fun i j hij => horth i j hij x y)]
  simp only [LinearIsometry.inner_map_map, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hs : (c : ℂ)^2 * (Fintype.card I : ℂ) = 1 := by exact_mod_cast hscale
  calc
    _ = ((c : ℂ)^2 * (Fintype.card I : ℂ)) * inner ℂ x y := by ring
    _ = _ := by rw [hs, one_mul]

def averageIsometry (c : ℝ) (U : I → K →ₗᵢ[ℂ] H)
    (horth : ∀ i j, i ≠ j → ∀ x y : K, inner ℂ (U i x) (U j y) = 0)
    (hscale : c^2 * Fintype.card I = 1) : K →ₗᵢ[ℂ] H where
  toLinearMap := (average c (fun i => (U i).toContinuousLinearMap)).toLinearMap
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re (average_inner c U horth hscale x x)

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
@[simp] lemma averageIsometry_toCLM (c : ℝ) (U : I → K →ₗᵢ[ℂ] H) horth hscale :
    (averageIsometry c U horth hscale).toContinuousLinearMap =
      average c (fun i => (U i).toContinuousLinearMap) := rfl

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
lemma norm_average_le (c : ℝ) (U : I → K →L[ℂ] H)
    (horth : ∀ i j, i ≠ j → ∀ x : K, inner ℂ (U i x) (U j x) = 0)
    (hscale : c^2 * Fintype.card I = 1) {d : ℝ} (hd : 0 ≤ d)
    (hU : ∀ i, ‖U i‖ ≤ d) : ‖average c U‖ ≤ d := by
  apply (average c U).opNorm_le_bound hd
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (norm_nonneg x))).mp
  rw [average_apply, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, norm_sum_sq _ (fun i j hij => horth i j hij x)]
  calc
    c^2 * ∑ i, ‖U i x‖^2 ≤ c^2 * ∑ _i : I, (d*‖x‖)^2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (norm_nonneg x))).mpr
      exact ((U i).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hU i) (norm_nonneg x))
    _ = (d*‖x‖)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, hscale, one_mul]

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
lemma comp_sum' (U : I → K →L[ℂ] H) (G : H →L[ℂ] H) :
    G.comp (∑ i, U i) = ∑ i, G.comp (U i) := by
  ext x
  simp

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
lemma sum_comp' (U : I → K →L[ℂ] H) (B : K →L[ℂ] K) :
    (∑ i, U i).comp B = ∑ i, (U i).comp B := by
  ext x
  simp

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
lemma average_error (c : ℝ) (U : I → K →L[ℂ] H) (G : H →L[ℂ] H) (B : K →L[ℂ] K) :
    G.comp (average c U) - (average c U).comp B =
      average c (fun i => G.comp (U i) - (U i).comp B) := by
  simp only [average, comp_smul, smul_comp, comp_sum', sum_comp',
    Finset.sum_sub_distrib, smul_sub]

omit [DecidableEq I] in
lemma average_compression (c : ℝ) (U : I → K →L[ℂ] H) (T : H →L[ℂ] H) :
    ((average c U).adjoint.comp T).comp (average c U) =
      ((c : ℂ)^2) • ∑ i, ∑ j, ((U i).adjoint.comp T).comp (U j) := by
  unfold average
  rw [map_smulₛₗ, map_sum]
  have hc : starRingEnd ℂ (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
  rw [hc]
  ext x
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    sum_apply, map_smul, map_sum]
  simp only [Finset.smul_sum, smul_smul, pow_two]
  rw [Finset.sum_comm]

omit [DecidableEq I] in
lemma average_compression_entries (c : ℝ) (U : I → K →ₗᵢ[ℂ] H)
    (horth : ∀ i j, i ≠ j → ∀ x y : K, inner ℂ (U i x) (U j y) = 0)
    (hscale : c^2 * Fintype.card I = 1)
    (T : H →L[ℂ] H) (S : K →L[ℂ] K) (u : ℂ) (a b : I → I → ℂ)
    (hentry : ∀ i j, ((U i).toContinuousLinearMap.adjoint.comp T).comp
      (U j).toContinuousLinearMap = u • (a i j • 1 + b i j • S)) :
    FreeCorner.compress (averageIsometry c U horth hscale) T =
      u • (((c : ℂ)^2 * ∑ i, ∑ j, a i j) • 1 +
          ((c : ℂ)^2 * ∑ i, ∑ j, b i j) • S) := by
  rw [FreeCorner.compress, averageIsometry_toCLM, average_compression]
  simp only [hentry, smul_add, smul_smul, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Finset.mul_sum]
  module

end Kadison.FiniteCompression

namespace Kadison.FiniteHankel

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap FiniteCompression

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_commutator_le_of_finite_entries
    (N : ℕ) (hN : 0 < N) (U : Fin N → K →ₗᵢ[ℂ] H)
    (horth : ∀ i j, i ≠ j → ∀ x y : K, inner ℂ (U i x) (U j y) = 0)
    (G L : H →L[ℂ] H) (B S : K →L[ℂ] K) (u c ε : ℝ)
    (hu : 0 < u) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hL : ‖L‖ ≤ 4*u)
    (hG : ‖G*L-L*G‖ ≤ ε*‖L‖)
    (hR : ∀ i, ‖G.comp (U i).toContinuousLinearMap -
      (U i).toContinuousLinearMap.comp B‖ ≤ 2*c*ε)
    (hR' : ∀ i, ‖G.adjoint.comp (U i).toContinuousLinearMap -
      (U i).toContinuousLinearMap.comp B.adjoint‖ ≤ 2*c*ε)
    (hRorth : ∀ i j, i ≠ j → ∀ x : K,
      inner ℂ (G (U i x) - U i (B x)) (G (U j x) - U j (B x)) = 0)
    (hRorth' : ∀ i j, i ≠ j → ∀ x : K,
      inner ℂ (G.adjoint (U i x) - U i (B.adjoint x))
        (G.adjoint (U j x) - U j (B.adjoint x)) = 0)
    (a : Fin N → Fin N → ℂ)
    (hentry : ∀ i j, ((U i).toContinuousLinearMap.adjoint.comp L).comp
      (U j).toContinuousLinearMap = (u : ℂ) • (a i j • 1 +
        (Complex.ofReal (((2*N : ℝ) - i.val - j.val - 1)/(2*N : ℝ)^2)) • S)) :
    ‖B*S-S*B‖ ≤ 16*(1+4*c)*ε := by
  let v : ℝ := (Real.sqrt (N : ℝ))⁻¹
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hv2 : v^2 = (N : ℝ)⁻¹ := by
    dsimp [v]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hscale : v^2 * Fintype.card (Fin N) = 1 := by
    rw [hv2, Fintype.card_fin, inv_mul_cancel₀ hn]
  let V := averageIsometry v U horth hscale
  have hRV : ‖G.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp B‖ ≤ 2*c*ε := by
    rw [averageIsometry_toCLM, average_error]
    exact norm_average_le v _ (fun i j hij x => hRorth i j hij x) hscale (by positivity) hR
  have hRV' : ‖G.adjoint.comp V.toContinuousLinearMap -
      V.toContinuousLinearMap.comp B.adjoint‖ ≤ 2*c*ε := by
    rw [averageIsometry_toCLM, average_error]
    exact norm_average_le v _ (fun i j hij x => hRorth' i j hij x) hscale (by positivity) hR'
  have hb : (v : ℂ)^2 * ∑ i : Fin N, ∑ j : Fin N,
      (Complex.ofReal (((2*N : ℝ) - i.val - j.val - 1)/(2*N : ℝ)^2)) = 1/4 := by
    have h : v^2 * ∑ i : Fin N, ∑ j : Fin N,
        (((2*N : ℝ) - i.val - j.val - 1)/(2*N : ℝ)^2) = 1/4 := by
      rw [hv2]
      exact FejerTest.hankel_average N hN
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sum,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      congrArg Complex.ofReal h
  have hcomp : FreeCorner.compress V L = (u : ℂ) •
      (((v : ℂ)^2 * ∑ i, ∑ j, a i j) • 1 + (1/4 : ℂ) • S) := by
    have h := average_compression_entries v U horth hscale L S (u : ℂ) a
      (fun i j => (Complex.ofReal (((2*N : ℝ) - i.val - j.val - 1)/(2*N : ℝ)^2))) hentry
    rw [hb] at h
    exact h
  have heq : B * FreeCorner.compress V L - FreeCorner.compress V L * B =
      ((u/4 : ℝ) : ℂ) • (B*S-S*B) := by
    rw [hcomp]
    simp only [smul_add, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one,
      one_mul, smul_sub, smul_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
    module
  have hbound := FreeCorner.compressed_commutator_bound V G L B hG hRV hRV'
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos hu (by norm_num))] at hbound
  have hbound' : (u/4)*‖B*S-S*B‖ ≤ (1+4*c)*ε*(4*u) :=
    hbound.trans (mul_le_mul_of_nonneg_left hL (by positivity))
  apply (mul_le_mul_iff_right₀ (div_pos hu (by norm_num : (0 : ℝ) < 4))).mp
  calc
    _ ≤ (1+4*c)*ε*(4*u) := hbound'
    _ = (u/4)*(16*(1+4*c)*ε) := by ring

end Kadison.FiniteHankel

end

end
end

end OAI
