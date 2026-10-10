import OAI.Geometry.ConjugatePoints.Neck

namespace OAI

noncomputable section

/-!
# Returning neck geodesics, passage dynamics, and index bounds.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Neck
open Matrix
open scoped Matrix.Norms.Elementwise

lemma metric_smul_left (Q : TMat) (r : ℝ) (U V : Vec) :
    metric Q (r • U) V = r * metric Q U V := by
  simp only [metric, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, pairing_smul_left]
  ring

lemma gamma_add_right (P A : TMat) (T U V : Vec) :
    gamma P A T (U + V) = gamma P A T U + gamma P A T V := by
  apply Prod.ext
  · simp only [gamma, Prod.fst_add, Prod.snd_add, pairing_add_right]
    ring
  · simp only [gamma, Prod.fst_add, Prod.snd_add, Matrix.mulVec_add,
      smul_add, add_smul]
    module

lemma gamma_smul_right (P A : TMat) (r : ℝ) (T V : Vec) :
    gamma P A T (r • V) = r • gamma P A T V := by
  apply Prod.ext
  · simp only [gamma, Prod.smul_fst, Prod.smul_snd, pairing_smul_right, smul_eq_mul]
    ring
  · simp only [gamma, Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul]
    module

lemma covariant_gauge (P A : TMat) (T V D : Vec) (h h' : ℝ) :
    (D + h' • T - h • gamma P A T T) + gamma P A T (V + h • T) =
      (D + gamma P A T V) + h' • T := by
  rw [gamma_add_right, gamma_smul_right]
  module

lemma curvature_contraction_gauge {P Q A B : TMat} (hQP : Q * P = 1)
    (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B) (V T : Vec) (h : ℝ) :
    metric Q (V + h • T) (curvatureJet P A B (V + h • T) T T) =
      metric Q V (curvatureJet P A B V T T) := by
  rw [curvature_contraction hQP hP hA hB, curvature_contraction hQP hP hA hB]
  have hw : (V + h • T).1 • T.2 - T.1 • (V + h • T).2 = V.1 • T.2 - T.1 • V.2 := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
    module
  rw [hw]
  simp only [Prod.snd_add, Prod.smul_snd, pairing_add_left, pairing_add_right,
    pairing_smul_left, pairing_smul_right, pairing_symm hA T.2 V.2]
  ring

def normalDensity (P Q A B : TMat) (T V D : Vec) : ℝ :=
  metric Q (D + gamma P A T V) (D + gamma P A T V) -
    metric Q V (curvatureJet P A B V T T) -
    (metric Q (D + gamma P A T V) T) ^ 2

lemma normalDensity_gauge {P Q A B : TMat} (hQP : Q * P = 1)
    (hQ : Qᵀ = Q) (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (T V D : Vec) (hunit : metric Q T T = 1) (h h' : ℝ) :
    normalDensity P Q A B T (V + h • T) (D + h' • T - h • gamma P A T T) =
      normalDensity P Q A B T V D := by
  simp only [normalDensity, covariant_gauge,
    curvature_contraction_gauge hQP hP hA hB, metric_add_left, metric_add_right,
    metric_smul_left, metric_smul_right, metric_symm hQ T D,
    metric_symm hQ T (gamma P A T V), hunit]
  ring

lemma metric_compatibility_jet {P Q A : TMat} (hQP : Q * P = 1) (hA : Aᵀ = A)
    (T V W : Vec) : T.1 * pairing A V.2 W.2 =
      metric Q V (gamma P A T W) + metric Q W (gamma P A T V) := by
  simp only [metric_gamma hQP, pairing_symm hA W.2 V.2,
    pairing_symm hA W.2 T.2,
    pairing_symm hA T.2 V.2]
  ring

lemma metric_hasDerivAt {Q : ℝ → TMat} {A : TMat} {t : ℝ → ℝ}
    {V W : ℝ → Vec} {V' W' : Vec} {v s : ℝ}
    (hQ : HasDerivAt Q A (t s)) (ht : HasDerivAt t v s)
    (hV : HasDerivAt V V' s) (hW : HasDerivAt W W' s) :
    HasDerivAt (fun r => metric (Q (t r)) (V r) (W r))
      (metric (Q (t s)) V' (W s) + metric (v • A) (0, (V s).2) (0, (W s).2) +
        metric (Q (t s)) (V s) W') s := by
  have hv1 := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hV
  have hv2 := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hV
  have hw1 := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hW
  have hw2 := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hW
  have hp := pairing_hasDerivAt (hQ.scomp s ht) hv2 hw2
  convert! (hv1.mul hw1).add hp using 1
  simp only [metric, zero_mul, zero_add, Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  ring

lemma pairing_neg_right (Q : TMat) (x y : TVec) :
    pairing Q x (-y) = -pairing Q x y := by
  simp only [pairing, Matrix.mulVec_neg, dotProduct_neg]

lemma tangential_hasDerivAt {P A : TMat} {Q : ℝ → TMat} {t : ℝ → ℝ}
    {T V : ℝ → Vec} {D : Vec} {s : ℝ}
    (hQP : Q (t s) * P = 1) (hQs : (Q (t s))ᵀ = Q (t s)) (hA : Aᵀ = A)
    (hQ : HasDerivAt Q A (t s)) (ht : HasDerivAt t (T s).1 s)
    (hT : HasDerivAt T (-gamma P A (T s) (T s)) s)
    (hV : HasDerivAt V D s) :
    HasDerivAt (fun r => metric (Q (t r)) (V r) (T r))
      (metric (Q (t s)) (D + gamma P A (T s) (V s)) (T s)) s := by
  apply (metric_hasDerivAt hQ ht hV hT).congr_deriv
  have hc := metric_compatibility_jet hQP hA (T s) (V s) (T s)
  simp only [metric, zero_mul, zero_add, pairing_matrix_smul] at hc ⊢
  dsimp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  simp only [pairing_add_left, pairing_neg_right]
  have hg := metric_symm hQs (T s) (gamma P A (T s) (V s))
  unfold metric at hg
  linarith

end ThreeManifold.Neck

namespace ThreeManifold.Turning

def beta : ℝ := (1 + Real.exp (-(9 : ℝ) / 26)) / 2

def aZero : ℝ := Real.exp (-(3 : ℝ) / 2)

lemma beta_pos : 0 < beta := by
  have h := Real.exp_pos (-(9 : ℝ) / 26)
  unfold beta
  linarith

lemma beta_lt_one : beta < 1 := by
  have h : Real.exp (-(9 : ℝ) / 26) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  unfold beta
  linarith

lemma aZero_pos : 0 < aZero := Real.exp_pos _

def SmallParameter (Ce Cm δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 ∧ δ ≤ 1 / (2 * Cm) ∧
    δ ≤ (1 - beta) / (2 * Cm + Ce * aZero)

lemma small_half {Ce Cm δ : ℝ} ( _he : 0 < Ce) (hm : 0 < Cm)
    (hδ : SmallParameter Ce Cm δ) : Cm * δ ≤ 1 / 2 := by
  have h : δ * (2 * Cm) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * Cm)).mp hδ.2.2.1
  nlinarith

lemma small_gain {Ce Cm δ : ℝ} ( _he : 0 < Ce) (hm : 0 < Cm)
    (hδ : SmallParameter Ce Cm δ) : beta + Ce * aZero * δ ≤ (1 - Cm * δ) ^ 2 := by
  have hd : 0 < 2 * Cm + Ce * aZero := by have := aZero_pos; positivity
  have h := (le_div_iff₀ hd).mp hδ.2.2.2
  nlinarith [sq_nonneg (Cm * δ)]

lemma mixed_square_lower {L p1 c spe : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ 1 - c)
    (h : |spe - L * p1| ≤ c * L * |p1|) :
    (L * p1) ^ 2 * (1 - c) ^ 2 ≤ spe ^ 2 := by
  have habs : |L * p1| ≤ |spe| + |spe - L * p1| := by
    calc
      |L * p1| = |spe - (spe - L * p1)| := by congr 1; ring
      _ ≤ |spe| + |spe - L * p1| := abs_sub _ _
  rw [abs_mul, abs_of_nonneg hL] at habs
  have hlo : L * |p1| * (1 - c) ≤ |spe| := by nlinarith
  have hn : 0 ≤ L * |p1| * (1 - c) := by positivity
  have hs := sq_le_sq₀ hn (abs_nonneg spe) |>.mpr hlo
  simpa only [mul_pow, sq_abs] using hs

lemma endpoint_gain
    {Ce Cm δ L v0 p1 κ μ see spe : ℝ}
    (he : 0 < Ce) (hm : 0 < Cm) (hδ : SmallParameter Ce Cm δ)
    (hL : 0 < L) (hv : 0 < v0) (hμ : 0 < μ)
    (hκ : κ = δ * aZero) (hμdef : μ = κ * v0 / 4)
    (hinc : v0 ^ 2 ≤ κ * p1 ^ 2)
    (htime : 4 * v0 ≤ beta * κ * p1 ^ 2 * L)
    (hsee : 0 ≤ see) (hsee_upper : see ≤ Ce * L)
    (hmixed : |spe - L * p1| ≤ Cm * δ * L * |p1|) :
    L * v0 ^ 2 ≤ spe ^ 2 / (see + μ⁻¹) := by
  have hhalf := small_half he hm hδ
  have hsquare := mixed_square_lower hL.le (by linarith : 0 ≤ 1 - Cm * δ) hmixed
  have ht := mul_le_mul_of_nonneg_right htime hv.le
  have ht' : v0 ^ 2 ≤ beta * L * p1 ^ 2 * μ := by
    rw [hμdef]
    nlinarith
  have hspeed : v0 ^ 2 * μ⁻¹ ≤ beta * L * p1 ^ 2 := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hμ).mpr ht'
  have hinc' : v0 ^ 2 ≤ δ * aZero * p1 ^ 2 := by simpa [hκ] using hinc
  have hden : 0 < see + μ⁻¹ := add_pos_of_nonneg_of_pos hsee (inv_pos.mpr hμ)
  apply (le_div_iff₀ hden).mpr
  calc
    L * v0 ^ 2 * (see + μ⁻¹) ≤ L * v0 ^ 2 * (Ce * L + μ⁻¹) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hsee_upper le_rfl) (by positivity)
    _ = Ce * L ^ 2 * v0 ^ 2 + L * (v0 ^ 2 * μ⁻¹) := by ring
    _ ≤ Ce * L ^ 2 * (δ * aZero * p1 ^ 2) + L * (beta * L * p1 ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hinc' (by positivity))
        (mul_le_mul_of_nonneg_left hspeed hL.le)
    _ = (L * p1) ^ 2 * (beta + Ce * aZero * δ) := by ring
    _ ≤ (L * p1) ^ 2 * (1 - Cm * δ) ^ 2 :=
      mul_le_mul_of_nonneg_left (small_gain he hm hδ) (sq_nonneg _)
    _ ≤ spe ^ 2 := hsquare

lemma minimize_quadratic (spp spe D α : ℝ) (hD : 0 < D) :
    spp - spe ^ 2 / D ≤ spp - 2 * α * spe + α ^ 2 * D := by
  have h : 0 ≤ (α * D - spe) ^ 2 / D := div_nonneg (sq_nonneg _) hD.le
  have heq : (spp - 2 * α * spe + α ^ 2 * D) - (spp - spe ^ 2 / D) =
      (α * D - spe) ^ 2 / D := by
    field_simp
    ring
  rw [← heq] at h
  linarith

theorem returning_quadratic_bound
    {Ce Cm δ L v0 p1 κ μ spp see spe : ℝ}
    (he : 0 < Ce) (hm : 0 < Cm) (hδ : SmallParameter Ce Cm δ)
    (hL : 0 < L) (hv : 0 < v0) (hμ : 0 < μ)
    (hκ : κ = δ * aZero) (hμdef : μ = κ * v0 / 4)
    (hinc : v0 ^ 2 ≤ κ * p1 ^ 2)
    (htime : 4 * v0 ≤ beta * κ * p1 ^ 2 * L)
    (hspp : spp ≤ L * (1 + v0 ^ 2))
    (hsee : 0 ≤ see) (hsee_upper : see ≤ Ce * L)
    (hmixed : |spe - L * p1| ≤ Cm * δ * L * |p1|) :
    ∃ α : ℝ, spp - 2 * α * spe + α ^ 2 * (see + μ⁻¹) ≤ L := by
  have hgain := endpoint_gain he hm hδ hL hv hμ hκ hμdef hinc htime
    hsee hsee_upper hmixed
  have hden : 0 < see + μ⁻¹ := add_pos_of_nonneg_of_pos hsee (inv_pos.mpr hμ)
  refine ⟨spe / (see + μ⁻¹), ?_⟩
  have heq : spp - 2 * (spe / (see + μ⁻¹)) * spe +
      (spe / (see + μ⁻¹)) ^ 2 * (see + μ⁻¹) = spp - spe ^ 2 / (see + μ⁻¹) := by
    field_simp
    ring
  rw [heq]
  nlinarith

end ThreeManifold.Turning

namespace ThreeManifold.DirectTurning

section
open Set MeasureTheory Neck Matrix
open scoped Interval Topology

lemma two_energy_nonneg {A B C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : B ^ 2 ≤ A * C) (x y : ℝ) :
    0 ≤ A * x ^ 2 + 2 * B * x * y + C * y ^ 2 := by
  by_cases ha : A = 0
  · have hb : B = 0 := by nlinarith [sq_nonneg B]
    simp only [ha, hb, zero_mul, mul_zero, zero_add]
    exact mul_nonneg hC (sq_nonneg y)
  · have hp : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
    have hh := mul_nonneg (sub_nonneg.mpr hB) (sq_nonneg y)
    nlinarith [sq_nonneg (A * x + B * y)]

lemma dual_pairing {P Q : TMat} (hQP : Q * P = 1) (hP : Pᵀ = P)
    (q ξ : TVec) : pairing Q (P *ᵥ q) ξ = q ⬝ᵥ ξ := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  rw [pairing_mulVec_left, hP, hPQ]
  simp [pairing]

lemma dual_pairing_self {P Q : TMat} (hQP : Q * P = 1) (hP : Pᵀ = P)
    (q : TVec) : pairing Q (P *ᵥ q) (P *ᵥ q) = pairing P q q := by
  rw [dual_pairing hQP hP]
  rfl

lemma direct_pointwise_quadratic {P Q : TMat} (hQP : Q * P = 1)
    (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hpos : ∀ ξ, 0 ≤ pairing Q ξ ξ)
    {K h g : ℝ} (hK : 0 ≤ K) (hh : 0 ≤ h) (hg : g ^ 2 ≤ h * K)
    (q ξ : TVec) (v w w' α r : ℝ) :
    0 ≤ (pairing Q ξ ξ + w' ^ 2 + h * w ^ 2) -
      2 * r * (q ⬝ᵥ ξ + 2 * v * w' - α * g * w) +
      r ^ 2 * (pairing P q q + 4 * v ^ 2 + α ^ 2 * K) := by
  have hp := hpos (ξ - r • (P *ᵥ q))
  have hs := two_energy_nonneg hh hK hg w (r * α)
  have hcross : pairing Q ξ (P *ᵥ q) = q ⬝ᵥ ξ := by
    rw [pairing_symm hQ, dual_pairing hQP hP]
  have hnorm : pairing Q (ξ - r • (P *ᵥ q)) (ξ - r • (P *ᵥ q)) =
      pairing Q ξ ξ - 2 * r * (q ⬝ᵥ ξ) + r ^ 2 * pairing P q q := by
    simp only [pairing_sub_left, pairing_sub_right, pairing_smul_left,
      pairing_smul_right, dual_pairing hQP hP, hcross]
    unfold pairing
    ring
  rw [hnorm] at hp
  nlinarith [sq_nonneg (w' - 2 * r * v)]

lemma interval_cauchy_of_quadratic {a b : ℝ} (hab : a ≤ b)
    {E F A : ℝ → ℝ} (hE : ContinuousOn E (Icc a b))
    (hF : ContinuousOn F (Icc a b)) (hA : ContinuousOn A (Icc a b))
    (hq : ∀ s ∈ Icc a b, ∀ r : ℝ, 0 ≤ E s - 2 * r * F s + r ^ 2 * A s) :
    (∫ s in a..b, F s) ^ 2 ≤ (∫ s in a..b, A s) * (∫ s in a..b, E s) := by
  have hEi : IntervalIntegrable E volume a b := (by simpa [uIcc_of_le hab] using hE :
    ContinuousOn E (uIcc a b)).intervalIntegrable
  have hFi : IntervalIntegrable F volume a b := (by simpa [uIcc_of_le hab] using hF :
    ContinuousOn F (uIcc a b)).intervalIntegrable
  have hAi : IntervalIntegrable A volume a b := (by simpa [uIcc_of_le hab] using hA :
    ContinuousOn A (uIcc a b)).intervalIntegrable
  have hi : ∀ r : ℝ, 0 ≤ (∫ s in a..b, E s) - 2 * r * (∫ s in a..b, F s) +
      r ^ 2 * (∫ s in a..b, A s) := by
    intro r
    have h := intervalIntegral.integral_nonneg (μ := volume) hab (fun s hs => hq s hs r)
    rw [intervalIntegral.integral_add (hEi.sub (hFi.const_mul (2 * r))) (hAi.const_mul (r ^ 2)),
      intervalIntegral.integral_sub hEi (hFi.const_mul (2 * r)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    exact h
  have hd := discrim_le_zero (a := ∫ s in a..b, A s)
    (b := -2 * ∫ s in a..b, F s) (c := ∫ s in a..b, E s) (fun r => by
      nlinarith [hi r])
  simp only [discrim] at hd
  nlinarith

lemma pairing_quadratic {P : TMat} (hP : Pᵀ = P) (p e : TVec) (α : ℝ) :
    pairing P (p - α • e) (p - α • e) =
      pairing P p p - 2 * α * pairing P p e + α ^ 2 * pairing P e e := by
  simp only [pairing_sub_left, pairing_sub_right, pairing_smul_left, pairing_smul_right,
    pairing_symm hP e p]
  ring

lemma add_boundary_cauchy {S E μ f y α : ℝ} (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hμ : 0 < μ) (hcs : f ^ 2 ≤ S * E) :
    (f + α * y) ^ 2 ≤ (S + α ^ 2 * μ⁻¹) * (E + μ * y ^ 2) := by
  have hh : (-f) ^ 2 ≤ (μ * S) * (E / μ) := by
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hcs hμ.le]
  have h := two_energy_nonneg (mul_nonneg hμ.le hS) (div_nonneg hE hμ.le) hh y α
  have heq : (S + α ^ 2 * μ⁻¹) * (E + μ * y ^ 2) - (f + α * y) ^ 2 =
      (S * E - f ^ 2) + (μ * S * y ^ 2 + 2 * (-f) * y * α + E / μ * α ^ 2) := by
    field_simp
    ring
  rw [← sub_nonneg, heq]
  linarith

lemma dotProduct_hasDerivAt {z z' : ℝ → TVec} {s : ℝ} (hz : HasDerivAt z (z' s) s)
    (q : TVec) : HasDerivAt (fun r => q ⬝ᵥ z r) (q ⬝ᵥ z' s) s := by
  let f : TVec →L[ℝ] ℝ := q 0 • ContinuousLinearMap.proj 0 +
    q 1 • ContinuousLinearMap.proj 1
  have h := f.hasFDerivAt.comp_hasDerivAt s hz
  simpa only [f, Function.comp_def, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct, Fin.sum_univ_two] using h

lemma direct_endpoint_functional {a b : ℝ} {p e : TVec} {α : ℝ}
    {z z' k : ℝ → TVec} {v v' w w' : ℝ → ℝ}
    (hz : ∀ s ∈ uIcc a b, HasDerivAt z (z' s) s)
    (hv : ∀ s ∈ uIcc a b, HasDerivAt v (v' s) s)
    (hw : ∀ s ∈ uIcc a b, HasDerivAt w (w' s) s)
    (hode : ∀ s ∈ uIcc a b, p ⬝ᵥ k s = -2 * v' s)
    (hwa : w a = 0) (hwb : w b = 0)
    (hF : IntervalIntegrable (fun s => (p - α • e) ⬝ᵥ (z' s - w s • k s) +
      2 * v s * w' s - α * (e ⬝ᵥ k s) * w s) volume a b) :
    (∫ s in a..b, (p - α • e) ⬝ᵥ (z' s - w s • k s) +
      2 * v s * w' s - α * (e ⬝ᵥ k s) * w s) = (p - α • e) ⬝ᵥ (z b - z a) := by
  have hd : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r => (p - α • e) ⬝ᵥ z r + 2 * v r * w r)
        ((p - α • e) ⬝ᵥ (z' s - w s • k s) + 2 * v s * w' s -
          α * (e ⬝ᵥ k s) * w s) s := by
    intro s hs
    apply ((dotProduct_hasDerivAt (hz s hs) (p - α • e)).add
      (((hv s hs).const_mul 2).mul (hw s hs))).congr_deriv
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    rw [hode s hs]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hF
  simpa only [hwa, hwb, mul_zero, add_zero, dotProduct_sub] using hi

lemma integral_direct_coefficient {a b : ℝ} {P : ℝ → TMat} {v : ℝ → ℝ}
    (hP : ∀ s, (P s)ᵀ = P s) (p e : TVec) (K α : ℝ)
    (hpp : IntervalIntegrable (fun s => pairing (P s) p p) volume a b)
    (hpe : IntervalIntegrable (fun s => pairing (P s) p e) volume a b)
    (hee : IntervalIntegrable (fun s => pairing (P s) e e) volume a b)
    (hvv : IntervalIntegrable (fun s => v s ^ 2) volume a b) :
    (∫ s in a..b, pairing (P s) (p - α • e) (p - α • e) + 4 * v s ^ 2 + α ^ 2 * K) =
      (∫ s in a..b, pairing (P s) p p + 4 * v s ^ 2) -
      2 * α * (∫ s in a..b, pairing (P s) p e) +
      α ^ 2 * (∫ s in a..b, pairing (P s) e e + K) := by
  calc
    _ = ∫ s in a..b, (pairing (P s) p p + 4 * v s ^ 2) -
        (2 * α) * pairing (P s) p e + α ^ 2 * (pairing (P s) e e + K) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [pairing_quadratic (hP s)]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add ((hpp.add (hvv.const_mul 4)).sub
        (hpe.const_mul (2 * α))) ((hee.add intervalIntegrable_const).const_mul (α ^ 2)),
        intervalIntegral.integral_sub (hpp.add (hvv.const_mul 4)) (hpe.const_mul (2 * α)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end

open Neck Matrix Set MeasureTheory Turning
open scoped Interval Topology Matrix.Norms.Elementwise

lemma continuousOn_dot_left {f : ℝ → TVec} {S : Set ℝ}
    (hf : ContinuousOn f S) (q : TVec) : ContinuousOn (fun s => q ⬝ᵥ f s) S := by
  simp only [dotProduct, Fin.sum_univ_two]
  exact ((continuous_apply 0).comp_continuousOn hf).const_mul (q 0) |>.add
    (((continuous_apply 1).comp_continuousOn hf).const_mul (q 1))

def energyDensity (Q : ℝ → TMat) (k : ℝ → TVec) (h : ℝ → ℝ)
    (z' : ℝ → TVec) (w w' : ℝ → ℝ) (s : ℝ) : ℝ :=
  pairing (Q s) (z' s - w s • k s) (z' s - w s • k s) + w' s ^ 2 + h s * w s ^ 2

lemma direct_endpoint_cauchy {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    {P Q : ℝ → TMat} {k z z' : ℝ → TVec} {h v v' w w' : ℝ → ℝ} (p e : TVec)
    (hPc : ContinuousOn P (Icc 0 L)) (hQc : ContinuousOn Q (Icc 0 L))
    (hkc : ContinuousOn k (Icc 0 L)) (hhc : ContinuousOn h (Icc 0 L))
    (hvc : ContinuousOn v (Icc 0 L)) (hzc : ContinuousOn z' (Icc 0 L))
    (hwc : ContinuousOn w (Icc 0 L)) (hw'c : ContinuousOn w' (Icc 0 L))
    (hQP : ∀ s ∈ Icc 0 L, Q s * P s = 1)
    (hPs : ∀ s ∈ Icc 0 L, (P s)ᵀ = P s)
    (hQs : ∀ s ∈ Icc 0 L, (Q s)ᵀ = Q s)
    (hpos : ∀ s ∈ Icc 0 L, ∀ ξ, 0 ≤ pairing (Q s) ξ ξ)
    (hh : ∀ s ∈ Icc 0 L, 0 ≤ h s)
    (hdom : ∀ s ∈ Icc 0 L, (e ⬝ᵥ k s) ^ 2 ≤ h s * K)
    (hz : ∀ s ∈ Icc 0 L, HasDerivAt z (z' s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (v' s) s)
    (hw : ∀ s ∈ Icc 0 L, HasDerivAt w (w' s) s)
    (hode : ∀ s ∈ Icc 0 L, p ⬝ᵥ k s = -2 * v' s)
    (hwa : w 0 = 0) (hwb : w L = 0) (α : ℝ) :
    ((p - α • e) ⬝ᵥ (z L - z 0)) ^ 2 ≤
      (∫ s in (0 : ℝ)..L, pairing (P s) (p - α • e) (p - α • e) +
        4 * v s ^ 2 + α ^ 2 * K) *
      (∫ s in (0 : ℝ)..L, energyDensity Q k h z' w w' s) := by
  let q := p - α • e
  let ξ := fun s => z' s - w s • k s
  let F := fun s => q ⬝ᵥ ξ s + 2 * v s * w' s - α * (e ⬝ᵥ k s) * w s
  let A := fun s => pairing (P s) q q + 4 * v s ^ 2 + α ^ 2 * K
  have hξ : ContinuousOn ξ (Icc 0 L) := hzc.sub (hwc.smul hkc)
  have hE : ContinuousOn (energyDensity Q k h z' w w') (Icc 0 L) :=
    ((continuousOn_pairing hQc hξ hξ).add (hw'c.pow 2)).add (hhc.mul (hwc.pow 2))
  have hF : ContinuousOn F (Icc 0 L) := by
    apply ContinuousOn.sub
    · exact (continuousOn_dot_left hξ q).add ((hvc.const_mul 2).mul hw'c)
    · exact ((continuousOn_dot_left hkc e).const_mul α).mul hwc
  have hA : ContinuousOn A (Icc 0 L) :=
    ((continuousOn_pairing hPc continuousOn_const continuousOn_const).add
      ((hvc.pow 2).const_mul 4)).add continuousOn_const
  have hcs := interval_cauchy_of_quadratic hL hE hF hA (fun s hs r =>
    direct_pointwise_quadratic (hQP s hs) (hPs s hs) (hQs s hs) (hpos s hs)
      hK (hh s hs) (hdom s hs) q (ξ s) (v s) (w s) (w' s) α r)
  have hf : (∫ s in (0 : ℝ)..L, F s) = q ⬝ᵥ (z L - z 0) := by
    apply direct_endpoint_functional
    · simpa only [uIcc_of_le hL] using hz
    · simpa only [uIcc_of_le hL] using hv
    · simpa only [uIcc_of_le hL] using hw
    · simpa only [uIcc_of_le hL] using hode
    · exact hwa
    · exact hwb
    · exact (by simpa only [uIcc_of_le hL] using hF : ContinuousOn F (uIcc 0 L)).intervalIntegrable
  rw [hf] at hcs
  exact hcs

theorem returning_endpoint_bound
    {Ce Cm δ L v0 κ μ spp see spe E : ℝ} {p e X : TVec}
    (he : 0 < Ce) (hm : 0 < Cm) (hδ : SmallParameter Ce Cm δ)
    (hL : 0 < L) (hv : 0 < v0) (hμ : 0 < μ)
    (hκ : κ = δ * aZero) (hμdef : μ = κ * v0 / 4)
    (hinc : v0 ^ 2 ≤ κ * (p ⬝ᵥ e) ^ 2)
    (htime : 4 * v0 ≤ beta * κ * (p ⬝ᵥ e) ^ 2 * L)
    (hspp : spp ≤ L * (1 + v0 ^ 2))
    (hsee : 0 ≤ see) (hsee_upper : see ≤ Ce * L)
    (hmixed : |spe - L * (p ⬝ᵥ e)| ≤ Cm * δ * L * |p ⬝ᵥ e|)
    (hE : 0 ≤ E)
    (hS : ∀ α : ℝ, 0 ≤ spp - 2 * α * spe + α ^ 2 * see)
    (hcs : ∀ α : ℝ, ((p - α • e) ⬝ᵥ X) ^ 2 ≤
      (spp - 2 * α * spe + α ^ 2 * see) * E) :
    0 ≤ E + μ * (e ⬝ᵥ X) ^ 2 - (p ⬝ᵥ X) ^ 2 / L := by
  obtain ⟨α, hα⟩ := returning_quadratic_bound he hm hδ hL hv hμ hκ hμdef
    hinc htime hspp hsee hsee_upper hmixed
  have hb := add_boundary_cauchy (hS α) hE hμ (hcs α) (y := e ⬝ᵥ X) (α := α)
  have heq : (p - α • e) ⬝ᵥ X + α * (e ⬝ᵥ X) = p ⬝ᵥ X := by
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  rw [heq] at hb
  have hnon : 0 ≤ E + μ * (e ⬝ᵥ X) ^ 2 := by positivity
  have ht := mul_le_mul_of_nonneg_right hα hnon
  have htop : (p ⬝ᵥ X) ^ 2 ≤ L * (E + μ * (e ⬝ᵥ X) ^ 2) := by
    nlinarith [hb, ht]
  have hdiv := (div_le_iff₀ hL).mpr (by nlinarith [htop] :
    (p ⬝ᵥ X) ^ 2 ≤ (E + μ * (e ⬝ᵥ X) ^ 2) * L)
  linarith

end ThreeManifold.DirectTurning

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningTime

lemma convex_chord {H v₀ : ℝ} (hH : 0 < H) {v : ℝ → ℝ}
    (hv : ConvexOn ℝ (Icc 0 H) v) (h0 : v 0 = v₀) (h1 : v H = 0)
    {s : ℝ} (hs : s ∈ Icc 0 H) : v s ≤ v₀ * (1 - s / H) := by
  have hw0 : 0 ≤ 1 - s / H := sub_nonneg.mpr ((div_le_one hH).mpr hs.2)
  have hw1 : 0 ≤ s / H := div_nonneg hs.1 hH.le
  have hh := hv.2 (show (0 : ℝ) ∈ Icc 0 H from ⟨le_rfl, hH.le⟩)
    (show H ∈ Icc 0 H from ⟨hH.le, le_rfl⟩) hw0 hw1 (by ring : 1 - s / H + s / H = 1)
  simp only [smul_eq_mul, h0, h1, mul_zero, zero_add, add_zero, div_mul_cancel₀ _ hH.ne'] at hh
  nlinarith [hh]

lemma concave_chord {H t₀ : ℝ} (hH : 0 < H) {t : ℝ → ℝ}
    (ht : ConcaveOn ℝ (Icc 0 H) t) (h0 : t 0 = 0) (h1 : t H = t₀)
    {s : ℝ} (hs : s ∈ Icc 0 H) : s / H * t₀ ≤ t s := by
  have hw0 : 0 ≤ 1 - s / H := sub_nonneg.mpr ((div_le_one hH).mpr hs.2)
  have hw1 : 0 ≤ s / H := div_nonneg hs.1 hH.le
  have hh := ht.2 (show (0 : ℝ) ∈ Icc 0 H from ⟨le_rfl, hH.le⟩)
    (show H ∈ Icc 0 H from ⟨hH.le, le_rfl⟩) hw0 hw1 (by ring : 1 - s / H + s / H = 1)
  simpa only [smul_eq_mul, h0, h1, mul_zero, zero_add, div_mul_cancel₀ _ hH.ne'] using hh

lemma integral_chord_square {H v₀ : ℝ} (hH : 0 < H) :
    (∫ s in (0 : ℝ)..H, (v₀ * (1 - s / H)) ^ 2) = H * v₀ ^ 2 / 3 := by
  let f : ℝ → ℝ := fun s => v₀ ^ 2 * (s - s ^ 2 / H + s ^ 3 / (3 * H ^ 2))
  have hd (s : ℝ) : HasDerivAt f ((v₀ * (1 - s / H)) ^ 2) s := by
    have hh := (((hasDerivAt_id s).sub (((hasDerivAt_id s).pow 2).div_const H)).add
      (((hasDerivAt_id s).pow 3).div_const (3 * H ^ 2))).const_mul (v₀ ^ 2)
    convert hh using 1 <;> (first | rfl | (dsimp only [id]; field_simp; ring))
  have hc : Continuous (fun s : ℝ => (v₀ * (1 - s / H)) ^ 2) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable 0 H)]
  dsimp [f]
  field_simp
  ring

lemma half_chord_integral {H v₀ : ℝ} (hH : 0 < H) (hv₀ : 0 ≤ v₀) {v : ℝ → ℝ}
    (hc : ContinuousOn v (Icc 0 H)) (hv : ConvexOn ℝ (Icc 0 H) v)
    (hn : ∀ s ∈ Icc 0 H, 0 ≤ v s) (h0 : v 0 = v₀) (h1 : v H = 0) :
    (∫ s in (0 : ℝ)..H, v s ^ 2) ≤ H * v₀ ^ 2 / 3 := by
  rw [← integral_chord_square hH]
  apply intervalIntegral.integral_mono_on hH.le
  · exact (hc.pow 2).intervalIntegrable_of_Icc hH.le
  · exact (show Continuous (fun s : ℝ => (v₀ * (1 - s / H)) ^ 2) from by
      fun_prop).intervalIntegrable 0 H
  · intro s hs
    have hh := convex_chord hH hv h0 h1 hs
    have hr : 0 ≤ v₀ * (1 - s / H) := mul_nonneg hv₀
      (sub_nonneg.mpr ((div_le_one hH).mpr hs.2))
    nlinarith [hn s hs, mul_nonneg (sub_nonneg.mpr hh) (add_nonneg (hn s hs) hr)]

lemma full_chord_integral {L v₀ : ℝ} (hL : 0 < L) (hv₀ : 0 ≤ v₀) {v : ℝ → ℝ}
    (hc : ContinuousOn v (Icc 0 L)) (hv : ConvexOn ℝ (Icc 0 (L / 2)) v)
    (hn : ∀ s ∈ Icc 0 (L / 2), 0 ≤ v s) (h0 : v 0 = v₀) (h1 : v (L / 2) = 0)
    (hsym : ∀ s ∈ Icc 0 L, v (L - s) = -v s) :
    (∫ s in (0 : ℝ)..L, v s ^ 2) ≤ L * v₀ ^ 2 / 3 := by
  have hH : 0 < L / 2 := half_pos hL
  have hsub : Icc (0 : ℝ) (L / 2) ⊆ Icc 0 L := Icc_subset_Icc le_rfl (by linarith)
  have hi : IntervalIntegrable (fun s => v s ^ 2) volume 0 L :=
    (hc.pow 2).intervalIntegrable_of_Icc hL.le
  have hi0 := hi.mono_set (show uIcc (0 : ℝ) (L / 2) ⊆ uIcc 0 L from by
    simpa only [uIcc_of_le hL.le, uIcc_of_le hH.le] using hsub)
  have hi1 := hi.mono_set (show uIcc (L / 2) L ⊆ uIcc 0 L from by
    simp only [uIcc_of_le hL.le, uIcc_of_le (show L / 2 ≤ L by linarith)]
    exact Icc_subset_Icc hH.le le_rfl)
  have heq : (∫ s in L / 2..L, v s ^ 2) = ∫ s in (0 : ℝ)..L / 2, v s ^ 2 := by
    have hh := intervalIntegral.integral_comp_sub_left (a := 0) (b := L / 2)
      (fun s => v s ^ 2) L
    have hminus : L - L / 2 = L / 2 := by ring
    simp only [sub_zero, hminus] at hh
    rw [← hh]
    apply intervalIntegral.integral_congr
    intro s hs
    have hss : s ∈ Icc 0 L := hsub (by simpa only [uIcc_of_le hH.le] using hs)
    change v (L - s) ^ 2 = v s ^ 2
    rw [hsym s hss]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1, heq]
  have hb := half_chord_integral hH hv₀ (hc.mono hsub) hv hn h0 h1
  linarith

lemma velocity_convex {H : ℝ} {t v F₁ F₂ : ℝ → ℝ}
    (ht : ∀ s ∈ Icc 0 H, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 H, HasDerivAt v (-F₁ (t s) / 2) s)
    (hF : ∀ s ∈ Icc 0 H, HasDerivAt F₁ (F₂ (t s)) (t s))
    (hn : ∀ s ∈ Icc 0 H, 0 ≤ v s)
    (hFn : ∀ s ∈ Icc 0 H, F₂ (t s) ≤ 0) : ConvexOn ℝ (Icc 0 H) v := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 H)
    (fun s hs => (hv s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hv s (interior_subset hs)).hasDerivWithinAt)
    (f'' := fun s => -F₂ (t s) * v s / 2)
  · intro s hs
    have h := ((hF s (interior_subset hs)).comp s (ht s (interior_subset hs))).neg.div_const 2
    convert h.hasDerivWithinAt using 1 <;> (first | rfl | ring)
  · intro s hs
    exact div_nonneg (mul_nonneg (neg_nonneg.mpr (hFn s (interior_subset hs)))
      (hn s (interior_subset hs))) (by norm_num)

lemma height_concave {H : ℝ} {t v F₁ : ℝ → ℝ}
    (ht : ∀ s ∈ Icc 0 H, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 H, HasDerivAt v (-F₁ (t s) / 2) s)
    (hFn : ∀ s ∈ Icc 0 H, 0 ≤ F₁ (t s)) : ConcaveOn ℝ (Icc 0 H) t := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 H)
    (fun s hs => (ht s hs).continuousAt.continuousWithinAt)
    (fun s hs => (ht s (interior_subset hs)).hasDerivWithinAt)
    (fun s hs => (hv s (interior_subset hs)).hasDerivWithinAt)
  intro s hs
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hFn s (interior_subset hs)))
    (by norm_num)

lemma middle_height {L tstar : ℝ} (hL : 0 < L) (hstar : 1 / 4 < tstar)
    {t : ℝ → ℝ} (ht : ConcaveOn ℝ (Icc 0 (L / 2)) t)
    (h0 : t 0 = 0) (h1 : t (L / 2) = tstar)
    (hsym : ∀ s ∈ Icc 0 L, t (L - s) = t s) :
    ∀ s ∈ Icc (L / 4) (3 * L / 4), 1 / 8 ≤ t s := by
  have hH : 0 < L / 2 := half_pos hL
  have hhalf : ∀ s ∈ Icc (L / 4) (L / 2), 1 / 8 ≤ t s := by
    intro s hs
    have hs0 : s ∈ Icc 0 (L / 2) := ⟨by linarith [hs.1], hs.2⟩
    have hh := concave_chord hH ht h0 h1 hs0
    have hr : 1 / 2 ≤ s / (L / 2) := (le_div_iff₀ hH).mpr (by linarith [hs.1])
    nlinarith [mul_nonneg (by linarith : 0 ≤ tstar) (sub_nonneg.mpr hr)]
  intro s hs
  by_cases hfirst : s ≤ L / 2
  · exact hhalf s ⟨hs.1, hfirst⟩
  · have hss : L - s ∈ Icc (L / 4) (L / 2) := ⟨by linarith [hs.2], by linarith⟩
    have h := hhalf (L - s) hss
    rwa [hsym s ⟨by linarith [hs.1], by linarith [hs.2]⟩] at h

lemma integral_le_const {a b K : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc a b)) (hb : ∀ s ∈ Icc a b, f s ≤ K) :
    (∫ s in a..b, f s) ≤ (b - a) * K := by
  have h := intervalIntegral.integral_mono_on hab (hc.intervalIntegrable_of_Icc hab)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => K) volume a b) hb
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

lemma integral_quarter_bound {L A B : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 L))
    (hout : ∀ s ∈ Icc 0 L, f s ≤ A)
    (hmid : ∀ s ∈ Icc (L / 4) (3 * L / 4), f s ≤ B) :
    (∫ s in (0 : ℝ)..L, f s) ≤ L * (A + B) / 2 := by
  have h0 : (0 : ℝ) ≤ L / 4 := by linarith
  have h1 : L / 4 ≤ 3 * L / 4 := by linarith
  have h2 : 3 * L / 4 ≤ L := by linarith
  have hc0 := hc.mono (Icc_subset_Icc le_rfl (show L / 4 ≤ L by linarith))
  have hc1 := hc.mono (Icc_subset_Icc h0 h2)
  have hc2 := hc.mono (Icc_subset_Icc (show 0 ≤ 3 * L / 4 by linarith) le_rfl)
  have hb0 := integral_le_const h0 hc0 (fun s hs => hout s ⟨hs.1, by linarith [hs.2]⟩)
  have hb1 := integral_le_const h1 hc1 hmid
  have hb2 := integral_le_const h2 hc2 (fun s hs => hout s ⟨by linarith [hs.1], hs.2⟩)
  have hi0 : IntervalIntegrable f volume 0 (L / 4) := hc0.intervalIntegrable_of_Icc h0
  have hi1 : IntervalIntegrable f volume (L / 4) (3 * L / 4) := hc1.intervalIntegrable_of_Icc h1
  have hi2 : IntervalIntegrable f volume (3 * L / 4) L := hc2.intervalIntegrable_of_Icc h2
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi0.trans hi1) hi2,
    ← intervalIntegral.integral_add_adjacent_intervals hi0 hi1]
  linarith

lemma turning_time_margin {L tstar v₀ : ℝ} (hL : 0 < L) (hstar : 1 / 4 < tstar)
    {t v F₁ : ℝ → ℝ}
    (htc : ContinuousOn t (Icc 0 L))
    (hFc : ContinuousOn F₁ (Icc 0 tstar))
    (hrange : MapsTo t (Icc 0 L) (Icc 0 tstar))
    (hanti : AntitoneOn F₁ (Icc 0 tstar))
    (ht : ConcaveOn ℝ (Icc 0 (L / 2)) t)
    (h0 : t 0 = 0) (h1 : t (L / 2) = tstar)
    (hsym : ∀ s ∈ Icc 0 L, t (L - s) = t s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (hv0 : v 0 = v₀) (hv1 : v L = -v₀) :
    4 * v₀ ≤ L * (F₁ 0 + F₁ (1 / 8)) / 2 := by
  have hforce : ContinuousOn (fun s => F₁ (t s)) (Icc 0 L) := hFc.comp htc hrange
  have hint : (∫ s in (0 : ℝ)..L, F₁ (t s)) = 4 * v₀ := by
    have hd : ∀ s ∈ uIcc 0 L, HasDerivAt (fun s => -2 * v s) (F₁ (t s)) s := by
      intro s hs
      have hh := (hv s (by simpa only [uIcc_of_le hL.le] using hs)).const_mul (-2)
      convert hh using 1 ; (first | rfl | ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hforce.intervalIntegrable_of_Icc hL.le), hv0, hv1]
    ring
  rw [← hint]
  apply integral_quarter_bound hL.le hforce
  · intro s hs
    exact hanti ⟨le_rfl, by linarith⟩ (hrange hs) (hrange hs).1
  · intro s hs
    have hss : s ∈ Icc 0 L := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact hanti ⟨by norm_num, by linarith⟩ (hrange hss)
      (middle_height hL hstar ht h0 h1 hsym s hs)

end ThreeManifold.ReturningTime

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningCoefficients
open Neck Matrix

lemma constant_pairing_deriv {P : ℝ → TMat} {D : TMat} {u : ℝ}
    (hP : HasDerivAt P D u) (p q : TVec) :
    HasDerivAt (fun t => pairing (P t) p q) (pairing D p q) u := by
  simpa only [pairing, zero_dotProduct, Matrix.mulVec_zero, dotProduct_zero,
    zero_add, add_zero] using
    (pairing_hasDerivAt hP (hasDerivAt_const u p) (hasDerivAt_const u q))

lemma psd_cauchy {D : TMat} (hD : Dᵀ = D)
    (hpos : ∀ q, 0 ≤ pairing D q q) (p q : TVec) :
    pairing D p q ^ 2 ≤ pairing D p p * pairing D q q := by
  have hquad : ∀ r : ℝ, 0 ≤ pairing D p p * r ^ 2 +
      (2 * pairing D p q) * r + pairing D q q := by
    intro r
    have hh := hpos (r • p + q)
    simp only [pairing_add_left, pairing_add_right, pairing_smul_left,
      pairing_smul_right, pairing_symm hD q p] at hh
    nlinarith [hh]
  have hh := discrim_le_zero (a := pairing D p p) (b := 2 * pairing D p q)
    (c := pairing D q q) (fun r => by simpa only [pow_two] using hquad r)
  simp only [discrim] at hh
  nlinarith

lemma derivative_antitone {P₁ P₂ : ℝ → TMat} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt P₁ (P₂ t) t)
    (hc : ∀ t ∈ Icc 0 T, ∀ p, pairing (P₂ t) p p ≤ 0) (p : TVec) :
    AntitoneOn (fun t => pairing (P₁ t) p p) (Icc 0 T) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
  · exact fun t ht => (constant_pairing_deriv (hd t ht) p p).continuousAt.continuousWithinAt
  · intro t ht
    exact (constant_pairing_deriv (hd t (interior_subset ht)) p p).hasDerivWithinAt
  · intro t ht
    exact hc t (interior_subset ht) p

lemma derivative_difference_psd {P₁ P₂ : ℝ → TMat} {T t : ℝ}
    (ht : t ∈ Icc 0 T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt P₁ (P₂ t) t)
    (hc : ∀ t ∈ Icc 0 T, ∀ p, pairing (P₂ t) p p ≤ 0) (p : TVec) :
    0 ≤ pairing (P₁ 0 - P₁ t) p p := by
  rw [pairing_matrix_sub]
  exact sub_nonneg.mpr (derivative_antitone hd hc p ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1)

lemma mixed_derivative_bound {D U : TMat} {a C δ p₁ : ℝ} {p e : TVec}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hD : Dᵀ = D) (hpos : ∀ q, 0 ≤ pairing D q q)
    (hee : pairing D e e ≤ 2 * C * δ)
    (hpp : pairing D p p ≤ δ * a * p₁ ^ 2)
    (hfirst : pairing (D + U) e p = δ * a * p₁) :
    |pairing U e p| ≤ (a + Real.sqrt (2 * C * a)) * δ * |p₁| := by
  have hcs := psd_cauchy hD hpos e p
  have hmul := mul_le_mul hee hpp (hpos p) (by positivity : 0 ≤ 2 * C * δ)
  have hs : (Real.sqrt (2 * C * a)) ^ 2 = 2 * C * a := Real.sq_sqrt (by positivity)
  have hsq : pairing D e p ^ 2 ≤ (Real.sqrt (2 * C * a) * δ * |p₁|) ^ 2 := by
    rw [mul_pow, mul_pow, hs, sq_abs]
    nlinarith [hcs, hmul]
  have hnorm : |pairing D e p| ≤ Real.sqrt (2 * C * a) * δ * |p₁| :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)
  have heq : pairing U e p = δ * a * p₁ - pairing D e p := by
    rw [pairing_matrix_add] at hfirst
    linarith
  rw [heq]
  calc
    |δ * a * p₁ - pairing D e p| ≤ |δ * a * p₁| + |pairing D e p| := abs_sub _ _
    _ ≤ δ * a * |p₁| + Real.sqrt (2 * C * a) * δ * |p₁| := by
      simpa only [abs_mul, abs_of_nonneg hδ, abs_of_nonneg ha] using
        add_le_add_right hnorm |δ * a * p₁|
    _ = _ := by ring

lemma mixed_variation_bound {P P₁ : ℝ → TMat} {T t K p₁ : ℝ} {p e : TVec}
    (hT : T ≤ 1) (hK : 0 ≤ K) (ht : t ∈ Icc 0 T)
    (hd : ∀ u ∈ Icc 0 T, HasDerivAt P (P₁ u) u)
    (hb : ∀ u ∈ Icc 0 T, |pairing (P₁ u) e p| ≤ K)
    (hp0 : pairing (P 0) e p = p₁) : |pairing (P t) e p - p₁| ≤ K := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (constant_pairing_deriv (hd u hu) e p).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using hb u hu)
    (convex_Icc 0 T) (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, ht.1.trans ht.2⟩) ht
  rw [hp0, Real.norm_eq_abs, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] at hh
  exact hh.trans (mul_le_of_le_one_right hK (ht.2.trans hT))

lemma mixed_integral_bound {L C δ p₁ : ℝ} {f : ℝ → ℝ}
    (hL : 0 ≤ L) (hc : ContinuousOn f (Icc 0 L))
    (hb : ∀ s ∈ Icc 0 L, |f s - p₁| ≤ C * δ * |p₁|) :
    |(∫ s in (0 : ℝ)..L, f s) - L * p₁| ≤ C * δ * L * |p₁| := by
  have hf : IntervalIntegrable f volume 0 L := hc.intervalIntegrable_of_Icc hL
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := L) (C := C * δ * |p₁|) (f := fun s => f s - p₁)
    (fun s hs => by
      simpa only [Real.norm_eq_abs] using hb s (by simpa only [uIcc_of_le hL] using (uIoc_subset_uIcc hs)))
  rw [intervalIntegral.integral_sub hf intervalIntegrable_const,
    intervalIntegral.integral_const, Real.norm_eq_abs, sub_zero, abs_of_nonneg hL,
    smul_eq_mul] at hn
  nlinarith [hn]

lemma first_coefficient_bound {L v₀ : ℝ} {F v : ℝ → ℝ}
    (hL : 0 ≤ L) (hFc : ContinuousOn F (Icc 0 L)) (hvc : ContinuousOn v (Icc 0 L))
    (henergy : ∀ s ∈ Icc 0 L, F s + v s ^ 2 = 1)
    (hchord : (∫ s in (0 : ℝ)..L, v s ^ 2) ≤ L * v₀ ^ 2 / 3) :
    (∫ s in (0 : ℝ)..L, F s) + 4 * (∫ s in (0 : ℝ)..L, v s ^ 2) ≤ L * (1 + v₀ ^ 2) := by
  have hvi : IntervalIntegrable (fun s => v s ^ 2) volume 0 L :=
    (hvc.pow 2).intervalIntegrable_of_Icc hL
  have hfi : IntervalIntegrable F volume 0 L := hFc.intervalIntegrable_of_Icc hL
  have hh : (∫ s in (0 : ℝ)..L, F s) + (∫ s in (0 : ℝ)..L, v s ^ 2) = L := by
    rw [← intervalIntegral.integral_add hfi hvi]
    have hc : (∫ s in (0 : ℝ)..L, F s + v s ^ 2) = (∫ _s in (0 : ℝ)..L, (1 : ℝ)) :=
      intervalIntegral.integral_congr (fun s hs => henergy s (by simpa only [uIcc_of_le hL] using hs))
    rw [hc]
    simp
  nlinarith

lemma second_coefficient_bound {L C δ : ℝ} {f : ℝ → ℝ}
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hδ : δ ∈ Icc 0 1)
    (hc : ContinuousOn f (Icc 0 L)) (hb : ∀ s ∈ Icc 0 L, f s ≤ C) :
    (∫ s in (0 : ℝ)..L, f s) + 2 * C * δ * L ≤ 3 * C * L := by
  have hi := ReturningTime.integral_le_const hL hc hb
  have hd := mul_le_mul_of_nonneg_left hδ.2 (show 0 ≤ 2 * C * L by positivity)
  nlinarith

end ThreeManifold.ReturningCoefficients

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck Matrix

lemma coordinateCometric_smooth (right : Bool) (δ : ℝ) :
    ContDiff ℝ ∞ (coordinateCometric right δ) := by
  cases right
  · exact P_smooth δ
  · exact (congruenceCLM (C₂ δ)).contDiff.comp
      ((P_smooth δ).comp (contDiff_const.sub contDiff_id))

lemma coordinateCometric_transpose (right : Bool) (δ t : ℝ) :
    (coordinateCometric right δ t)ᵀ = coordinateCometric right δ t := by
  cases right
  · exact Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ t)
  · change (C₂ δ * P δ (1 - t) * (C₂ δ)ᵀ)ᵀ = C₂ δ * P δ (1 - t) * (C₂ δ)ᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ (1 - t)), Matrix.mul_assoc]

lemma symmetric_derivative {R : ℝ → Mat2} {D : Mat2} {t : ℝ}
    (hR : ∀ u, (R u)ᵀ = R u) (hd : HasDerivAt R D t) : Dᵀ = D := by
  ext i j
  have hdi := hasDerivAt_pi.mp (hasDerivAt_pi.mp hd j) i
  have hdj := hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j
  have he : (fun u => R u j i) = (fun u => R u i j) := by
    funext u
    exact congrFun (congrFun (hR u) i) j
  rw [he] at hdi
  exact hdi.unique hdj

lemma coordinateCometric_deriv_transpose (right : Bool) (δ t : ℝ) :
    (deriv (coordinateCometric right δ) t)ᵀ = deriv (coordinateCometric right δ) t :=
  symmetric_derivative (coordinateCometric_transpose right δ)
    (((coordinateCometric_smooth right δ).differentiable (by simp)).differentiableAt.hasDerivAt)

lemma coordinateCometric_end {right : Bool} {δ t : ℝ} (ht : t ≤ 1 / 4) :
    coordinateCometric right δ t = !![1 + δ * A t, 0; 0, 1 + δ * A 1] := by
  cases right
  · exact P_left_endpoint ht
  · exact P_right_endpoint ht

lemma coordinateCometric_end_deriv {right : Bool} {δ t : ℝ} (ht : t < 1 / 4) :
    deriv (coordinateCometric right δ) t = !![δ * a t, 0; 0, 0] := by
  have he : coordinateCometric right δ =ᶠ[𝓝 t]
      (fun u => !![1 + δ * A u, 0; 0, 1 + δ * A 1]) := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact coordinateCometric_end hu.le
  have hd : HasDerivAt (fun u => !![1 + δ * A u, 0; 0, 1 + δ * A 1])
      !![δ * a t, 0; 0, 0] t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> dsimp
    · exact ((A_hasDerivAt t).const_mul δ).const_add 1
    all_goals exact hasDerivAt_const _ _
  exact (hd.congr_of_eventuallyEq he).deriv

lemma endpoint_pairing (right : Bool) (δ : ℝ) (p : TVec) :
    pairing (coordinateCometric right δ 0) ![1, 0] p = p 0 := by
  rw [coordinateCometric_end (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  simp [pairing, Matrix.mulVec, dotProduct, Fin.sum_univ_two, A]

lemma endpoint_derivative_pairing (right : Bool) (δ : ℝ) (p : TVec) :
    pairing (deriv (coordinateCometric right δ) 0) ![1, 0] p = δ * a 0 * p 0 := by
  rw [coordinateCometric_end_deriv (by norm_num : (0 : ℝ) < 1 / 4)]
  simp [pairing, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma endpoint_derivative_qform (right : Bool) (δ : ℝ) (p : TVec) :
    pairing (deriv (coordinateCometric right δ) 0) p p = δ * a 0 * p 0 ^ 2 := by
  rw [coordinateCometric_end_deriv (by norm_num : (0 : ℝ) < 1 / 4)]
  simp only [pairing, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_zero, zero_mul, add_zero]
  ring

lemma a_eighth : a (1 / 8) = a 0 * Real.exp (-(9 : ℝ) / 26) := by
  have hh := a_eighth_ratio
  have ha := a_pos (u := 0) (by norm_num)
  exact (div_eq_iff ha.ne').mp hh |>.trans (mul_comm _ _)

lemma exact_timing_constant (δ L p₁ : ℝ) :
    L * (δ * a 0 * p₁ ^ 2 + δ * a (1 / 8) * p₁ ^ 2) / 2 =
      Turning.beta * (δ * Turning.aZero) * p₁ ^ 2 * L := by
  rw [a_eighth, a_zero]
  dsimp [Turning.beta, Turning.aZero]
  ring

end ThreeManifold.Cometric

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningCoefficients
open Neck Cometric Matrix

def e : TVec := ![1, 0]

lemma sqnorm_e : sqnorm e = 1 := by norm_num [e, sqnorm]

lemma pairing_e_bound (D : TMat) {C : ℝ} (hC : 0 ≤ C)
    (hD : sqnorm (D *ᵥ e) ≤ C ^ 2) : |pairing D e e| ≤ C := by
  have hs : pairing D e e ^ 2 ≤ sqnorm (D *ᵥ e) := by
    simp only [pairing, dotProduct, Fin.sum_univ_two, e, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, zero_mul, add_zero, sqnorm]
    nlinarith [sq_nonneg ((D *ᵥ ![1, 0]) 1)]
  exact (sq_le_sq₀ (abs_nonneg _) hC).mp (by simpa only [sq_abs] using hs.trans hD)

lemma actual_mixed_bound {right : Bool} {δ T C : ℝ} {p : TVec}
    (hδ : 0 ≤ δ) (hC : 0 < C) (hT : T ∈ Icc 0 1)
    (hconc : ∀ t ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) t) q)
    (hder : ∀ t ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) t *ᵥ e) ≤ C ^ 2 * δ ^ 2)
    (hforce : ∀ t ∈ Icc 0 T, 0 ≤ pairing (deriv (coordinateCometric right δ) t) p p) :
    ∀ t ∈ Icc 0 T,
      |pairing (coordinateCometric right δ t) e p - p 0| ≤
        (a 0 + Real.sqrt (2 * C * a 0)) * δ * |p 0| := by
  let R := coordinateCometric right δ
  have hsm : ContDiff ℝ ∞ R := coordinateCometric_smooth right δ
  have hsm1 := (contDiff_infty_iff_deriv.mp hsm).2
  have hdr (u : ℝ) : HasDerivAt R (deriv R u) u :=
    (hsm.differentiable (by simp)).differentiableAt.hasDerivAt
  have hdr1 (u : ℝ) : HasDerivAt (deriv R) (deriv (deriv R) u) u :=
    (hsm1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hc : ∀ u ∈ Icc 0 T, ∀ q, pairing (deriv (deriv R) u) q q ≤ 0 := by
    intro u hu q
    have hh := hconc u ⟨hu.1, hu.2.trans hT.2⟩ q
    change 0 ≤ pairing (-deriv (deriv R) u) q q at hh
    rw [pairing_matrix_neg] at hh
    linarith
  have hbound : ∀ u ∈ Icc 0 T, |pairing (deriv R u) e p| ≤
      (a 0 + Real.sqrt (2 * C * a 0)) * δ * |p 0| := by
    intro u hu
    let D := deriv R 0 - deriv R u
    have hpos (q : TVec) : 0 ≤ pairing D q q :=
      derivative_difference_psd hu (fun u _ => hdr1 u) hc q
    have hDs : Dᵀ = D := by
      dsimp only [D]
      rw [Matrix.transpose_sub, coordinateCometric_deriv_transpose,
        coordinateCometric_deriv_transpose]
    have hD0 : |pairing (deriv R 0) e e| ≤ C * δ :=
      pairing_e_bound _ (by positivity) (by
        simpa only [mul_pow] using hder 0 ⟨le_rfl, by norm_num⟩)
    have hDu : |pairing (deriv R u) e e| ≤ C * δ :=
      pairing_e_bound _ (by positivity) (by
        simpa only [mul_pow] using hder u ⟨hu.1, hu.2.trans hT.2⟩)
    have hee : pairing D e e ≤ 2 * C * δ := by
      dsimp only [D]
      rw [pairing_matrix_sub]
      have h0 := (abs_le.mp hD0).2
      have hu' := (abs_le.mp hDu).1
      linarith
    have hpp : pairing D p p ≤ δ * a 0 * p 0 ^ 2 := by
      dsimp only [D]
      rw [pairing_matrix_sub, endpoint_derivative_qform]
      linarith [hforce u hu]
    have hfirst : pairing (D + deriv R u) e p = δ * a 0 * p 0 := by
      dsimp only [D]
      rw [sub_add_cancel]
      exact endpoint_derivative_pairing right δ p
    exact mixed_derivative_bound (a_nonneg 0) hC.le hδ hDs hpos hee hpp hfirst
  intro t ht
  exact mixed_variation_bound hT.2
    (mul_nonneg (mul_nonneg (add_nonneg (a_nonneg 0) (Real.sqrt_nonneg _)) hδ) (abs_nonneg _)) ht (fun u _ => hdr u) hbound
    (endpoint_pairing right δ p)

lemma actual_force_end_values (right : Bool) (δ : ℝ) (p : TVec) :
    pairing (deriv (coordinateCometric right δ) 0) p p = δ * a 0 * p 0 ^ 2 ∧
    pairing (deriv (coordinateCometric right δ) (1 / 8)) p p = δ * a (1 / 8) * p 0 ^ 2 := by
  refine ⟨endpoint_derivative_qform right δ p, ?_⟩
  rw [coordinateCometric_end_deriv (by norm_num : (1 / 8 : ℝ) < 1 / 4)]
  simp only [pairing, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_mul, add_zero]
  ring

end ThreeManifold.ReturningCoefficients

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.PassageDynamics

lemma smooth_autonomous_unique {V : (ℝ × ℝ) → (ℝ × ℝ)}
    (hV : ContDiff ℝ ∞ V) {f g : ℝ → ℝ × ℝ} {a b c : ℝ}
    (hc : c ∈ Ioo a b) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfd : ∀ s ∈ Ioo a b, HasDerivAt f (V (f s)) s)
    (hgd : ∀ s ∈ Ioo a b, HasDerivAt g (V (g s)) s)
    (heq : f c = g c) : EqOn f g (Icc a b) := by
  have hcomp := (isCompact_Icc.image_of_continuousOn hf).union (isCompact_Icc.image_of_continuousOn hg)
  obtain ⟨R, hR⟩ := hcomp.isBounded.subset_closedBall (0 : ℝ × ℝ)
  obtain ⟨K, hK⟩ := hV.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : ℝ × ℝ) R) (isCompact_closedBall (0 : ℝ × ℝ) R)
  exact ODE_solution_unique_of_mem_Icc (v := fun _ => V)
    (s := fun _ => Metric.closedBall (0 : ℝ × ℝ) R) (fun _ _ => hK) hc hf hfd
    (fun s hs => hR (Or.inl ⟨s, Ioo_subset_Icc_self hs, rfl⟩)) hg hgd
    (fun s hs => hR (Or.inr ⟨s, Ioo_subset_Icc_self hs, rfl⟩)) heq

def scalarVectorField (F₁ : ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, -F₁ x.1 / 2)

lemma scalarVectorField_smooth {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁) :
    ContDiff ℝ ∞ (scalarVectorField F₁) :=
  contDiff_snd.prodMk ((hF.comp contDiff_fst).neg.div_const 2)

lemma scalar_equations_unique {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v u w : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F₁ (t s) / 2) s)
    (hu : ∀ s ∈ Icc a b, HasDerivAt u (w s) s)
    (hw : ∀ s ∈ Icc a b, HasDerivAt w (-F₁ (u s) / 2) s)
    (htc : t c = u c) (hvc : v c = w c) :
    EqOn t u (Icc a b) ∧ EqOn v w (Icc a b) := by
  have hh := smooth_autonomous_unique (scalarVectorField_smooth hF) hc
    ((HasDerivAt.continuousOn ht).prodMk (HasDerivAt.continuousOn hv))
    ((HasDerivAt.continuousOn hu).prodMk (HasDerivAt.continuousOn hw))
    (fun s hs => (ht s (Ioo_subset_Icc_self hs)).prodMk (hv s (Ioo_subset_Icc_self hs)))
    (fun s hs => (hu s (Ioo_subset_Icc_self hs)).prodMk (hw s (Ioo_subset_Icc_self hs)))
    (Prod.ext htc hvc)
  exact ⟨fun s hs => congrArg Prod.fst (hh hs), fun s hs => congrArg Prod.snd (hh hs)⟩

lemma cannot_reach_equilibrium {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F₁ (t s) / 2) s)
    (hvc : v c = 0) (hFc : F₁ (t c) = 0) :
    ∀ s ∈ Icc a b, t s = t c ∧ v s = 0 := by
  have huc (s : ℝ) : HasDerivAt (fun _ : ℝ => t c) (0 : ℝ) s := hasDerivAt_const s (t c)
  have hwc (s : ℝ) : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (-F₁ (t c) / 2) s := by
    simpa only [hFc, neg_zero, zero_div] using (hasDerivAt_const s (0 : ℝ))
  obtain ⟨hu, hw⟩ := scalar_equations_unique hF hc ht hv
    (fun s _ => huc s) (fun s _ => hwc s) rfl hvc
  exact fun s hs => ⟨hu hs, hw hs⟩

lemma scalar_reflection {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b) (hab : a + b = 2 * c)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F₁ (t s) / 2) s)
    (hvc : v c = 0) :
    ∀ s ∈ Icc a b, t (2 * c - s) = t s ∧ v (2 * c - s) = -v s := by
  have hr (s : ℝ) (hs : s ∈ Icc a b) : 2 * c - s ∈ Icc a b :=
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have htd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun u => t (2 * c - u)) (-v (2 * c - s)) s := by
    convert (ht _ (hr s hs)).comp s ((hasDerivAt_id s).const_sub (2 * c)) using 1 <;>
      (first | rfl | simp)
  have hvd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun u => -v (2 * c - u)) (-F₁ (t (2 * c - s)) / 2) s := by
    convert ((hv _ (hr s hs)).comp s ((hasDerivAt_id s).const_sub (2 * c))).neg using 1 <;>
      (first | rfl | ring)
  obtain ⟨htu, hvw⟩ := scalar_equations_unique hF hc ht hv htd hvd
    (by congr 1; ring) (by rw [show 2 * c - c = c by ring, hvc, neg_zero])
  intro s hs
  exact ⟨(htu hs).symm, by linarith [hvw hs]⟩

lemma positive_return_has_stationary_maximum {t v : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (h0 : t 0 = 0) (hL0 : t L = 0) (hpos : ∀ s ∈ Ioo 0 L, 0 < t s) :
    ∃ c ∈ Ioo 0 L, 0 < t c ∧ v c = 0 ∧ IsMaxOn t (Icc 0 L) c := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hL.le) (HasDerivAt.continuousOn ht)
  have hp := hpos (L / 2) ⟨by linarith, by linarith⟩
  have hcm : 0 < t c := lt_of_lt_of_le hp (hmax ⟨by linarith, by linarith⟩)
  have hc' : c ∈ Ioo 0 L := by
    constructor
    · by_contra hn
      have he : c = 0 := by linarith [hc.1]
      rw [he, h0] at hcm
      exact lt_irrefl _ hcm
    · by_contra hn
      have he : c = L := by linarith [hc.2]
      rw [he, hL0] at hcm
      exact lt_irrefl _ hcm
  refine ⟨c, hc', hcm, ?_, hmax⟩
  exact (hmax.isLocalMax (Icc_mem_nhds hc'.1 hc'.2)).hasDerivAt_eq_zero (ht c hc)

lemma return_midpoint {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {L c : ℝ} (hc : c ∈ Ioo 0 L)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (h0 : t 0 = 0) (hL0 : t L = 0) (hpos : ∀ s ∈ Ioo 0 L, 0 < t s)
    (hvc : v c = 0) : c = L / 2 := by
  rcases lt_trichotomy c (L / 2) with h | h | h
  · have hsub : Icc (0 : ℝ) (2 * c) ⊆ Icc 0 L := Icc_subset_Icc le_rfl (by linarith)
    have hh := scalar_reflection hF (show c ∈ Ioo (0 : ℝ) (2 * c) from
      ⟨hc.1, by linarith [hc.1]⟩) (by ring : 0 + 2 * c = 2 * c)
      (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs)) hvc
    have he := (hh 0 ⟨le_rfl, by linarith [hc.1]⟩).1
    simp only [sub_zero, h0] at he
    have hp := hpos (2 * c) ⟨by linarith [hc.1], by linarith⟩
    exact False.elim (by linarith)
  · exact h
  · have hsub : Icc (2 * c - L) L ⊆ Icc 0 L := Icc_subset_Icc (by linarith) le_rfl
    have hh := scalar_reflection hF (show c ∈ Ioo (2 * c - L) L from
      ⟨by linarith [hc.2], hc.2⟩) (by ring : 2 * c - L + L = 2 * c)
      (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs)) hvc
    have he := (hh L ⟨by linarith [hc.2], le_rfl⟩).1
    rw [hL0] at he
    have hp := hpos (2 * c - L) ⟨by linarith, by linarith [hc.2]⟩
    exact False.elim (by linarith)

lemma actual_return_symmetry {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (h0 : t 0 = 0) (hL0 : t L = 0) (hpos : ∀ s ∈ Ioo 0 L, 0 < t s) :
    v (L / 2) = 0 ∧ IsMaxOn t (Icc 0 L) (L / 2) ∧
      ∀ s ∈ Icc 0 L, t (L - s) = t s ∧ v (L - s) = -v s := by
  obtain ⟨c, hc, _, hvc, hm⟩ := positive_return_has_stationary_maximum hL ht h0 hL0 hpos
  have he := return_midpoint hF hc ht hv h0 hL0 hpos hvc
  subst c
  refine ⟨hvc, hm, ?_⟩
  have hh := scalar_reflection hF (show L / 2 ∈ Ioo (0 : ℝ) L from
    ⟨by linarith, by linarith⟩) (by ring : 0 + L = 2 * (L / 2)) ht hv hvc
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh

lemma force_nonneg_at_top {t v F F₁ : ℝ → ℝ} {L c energy : ℝ}
    (hc : c ∈ Icc 0 L) (htop : 0 < t c)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (h0 : t 0 = 0) (hvc : v c = 0)
    (henergy : ∀ s ∈ Icc 0 L, F (t s) + v s ^ 2 = energy)
    (hFd : HasDerivAt F (F₁ (t c)) (t c)) : 0 ≤ F₁ (t c) := by
  have hsub : Icc (0 : ℝ) c ⊆ Icc 0 L := Icc_subset_Icc le_rfl hc.2
  have hIVT := intermediate_value_Icc hc.1 ((HasDerivAt.continuousOn ht).mono hsub)
  rw [h0] at hIVT
  have hmax : IsMaxOn F (Icc 0 (t c)) (t c) := by
    intro u hu
    obtain ⟨s, hs, hsu⟩ := hIVT hu
    have hh := henergy s (hsub hs)
    have htopE := henergy c hc
    rw [hvc, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at htopE
    rw [hsu] at hh
    change F u ≤ F (t c)
    calc
      F u ≤ F u + v s ^ 2 := le_add_of_nonneg_right (sq_nonneg (v s))
      _ = energy := hh
      _ = F (t c) := htopE.symm
  have hy : 0 - t c ∈ posTangentConeAt (Icc 0 (t c)) (t c) :=
    sub_mem_posTangentConeAt_of_segment_subset ((convex_Icc (0 : ℝ) (t c)).segment_subset
      ⟨htop.le, le_rfl⟩ ⟨le_rfl, htop.le⟩)
  have hh := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hFd.hasFDerivAt.hasFDerivWithinAt hy
  have he : -(t c) * F₁ (t c) ≤ 0 := by simpa using hh
  nlinarith

lemma force_pos_at_top {F F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {L c energy : ℝ} (hc : c ∈ Ioo 0 L) (htop : 0 < t c)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (h0 : t 0 = 0) (hvc : v c = 0)
    (henergy : ∀ s ∈ Icc 0 L, F (t s) + v s ^ 2 = energy)
    (hFd : HasDerivAt F (F₁ (t c)) (t c)) : 0 < F₁ (t c) := by
  have hnon := force_nonneg_at_top (Ioo_subset_Icc_self hc) htop ht h0 hvc henergy hFd
  apply lt_of_le_of_ne hnon
  intro he
  have heq := cannot_reach_equilibrium hF hc ht hv hvc he.symm
  have hh := (heq 0 ⟨le_rfl, le_trans hc.1.le hc.2.le⟩).1
  rw [h0] at hh
  linarith

lemma return_velocity_strictAnti {F₁ : ℝ → ℝ} {t v : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (ht : MapsTo t (Icc 0 L) (Icc 0 (t (L / 2))))
    (hanti : AntitoneOn F₁ (Icc 0 (t (L / 2))))
    (hforce : 0 < F₁ (t (L / 2))) (hvc : v (L / 2) = 0) :
    StrictAntiOn v (Icc 0 L) ∧ 0 < v 0 ∧
      (∀ s ∈ Icc 0 (L / 2), 0 ≤ v s) := by
  have hF (s : ℝ) (hs : s ∈ Icc 0 L) : 0 < F₁ (t s) :=
    lt_of_lt_of_le hforce (hanti (ht hs)
      (ht ⟨by linarith, by linarith⟩) (ht hs).2)
  have hsa : StrictAntiOn v (Icc 0 L) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 L)
      (HasDerivAt.continuousOn hv)
      (fun s hs => (hv s (interior_subset hs)).hasDerivWithinAt)
    intro s hs
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (hF s (interior_subset hs))) (by norm_num)
  refine ⟨hsa, ?_, ?_⟩
  · have hh := hsa ⟨le_rfl, hL.le⟩ ⟨by linarith, by linarith⟩ (by linarith : 0 < L / 2)
    rwa [hvc] at hh
  · intro s hs
    have hh := hsa.antitoneOn ⟨hs.1, by linarith [hs.2]⟩ ⟨by linarith, by linarith⟩ hs.2
    rwa [hvc] at hh

end ThreeManifold.PassageDynamics

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage

section
open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix

def potential (right : Bool) (δ : ℝ) (p : TVec) (u : ℝ) : ℝ :=
  pairing (coordinateCometric right δ u) p p

def force (right : Bool) (δ : ℝ) (p : TVec) (u : ℝ) : ℝ :=
  pairing (deriv (coordinateCometric right δ) u) p p

def forceDerivative (right : Bool) (δ : ℝ) (p : TVec) (u : ℝ) : ℝ :=
  pairing (deriv (deriv (coordinateCometric right δ)) u) p p

lemma contDiff_pairing_const {R : ℝ → TMat} {n : WithTop ℕ∞}
    (hR : ContDiff ℝ n R) (p q : TVec) : ContDiff ℝ n (fun u => pairing (R u) p q) := by
  simp only [pairing, Matrix.mulVec, dotProduct]
  fun_prop

lemma potential_smooth (right : Bool) (δ : ℝ) (p : TVec) :
    ContDiff ℝ ∞ (potential right δ p) :=
  contDiff_pairing_const (coordinateCometric_smooth right δ) p p

lemma force_smooth (right : Bool) (δ : ℝ) (p : TVec) :
    ContDiff ℝ ∞ (force right δ p) :=
  contDiff_pairing_const (contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2 p p

lemma potential_hasDerivAt (right : Bool) (δ : ℝ) (p : TVec) (u : ℝ) :
    HasDerivAt (potential right δ p) (force right δ p u) u :=
  constant_pairing_deriv ((coordinateCometric_smooth right δ).differentiable
    (by simp)).differentiableAt.hasDerivAt p p

lemma force_hasDerivAt (right : Bool) (δ : ℝ) (p : TVec) (u : ℝ) :
    HasDerivAt (force right δ p) (forceDerivative right δ p u) u :=
  constant_pairing_deriv ((contDiff_infty_iff_deriv.mp
    (coordinateCometric_smooth right δ)).2.differentiable (by simp)).differentiableAt.hasDerivAt p p

lemma force_antitone {right : Bool} {δ T : ℝ} {p : TVec}
    (hT : T ≤ 1)
    (hc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q) :
    AntitoneOn (force right δ p) (Icc 0 T) := by
  apply derivative_antitone (P₂ := deriv (deriv (coordinateCometric right δ)))
    (fun u _ => ((contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2.differentiable
      (by simp)).differentiableAt.hasDerivAt)
  intro u hu q
  have hh := hc u ⟨hu.1, hu.2.trans hT⟩ q
  change 0 ≤ pairing (-deriv (deriv (coordinateCometric right δ)) u) q q at hh
  rw [pairing_matrix_neg] at hh
  linarith

theorem returning_dynamics {right : Bool} {δ L : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hL : 0 < L)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1) :
    let T := t (L / 2)
    0 < v 0 ∧ v (L / 2) = 0 ∧ T ∈ Ioo 0 1 ∧
    MapsTo t (Icc 0 L) (Icc 0 T) ∧
    (∀ s ∈ Icc 0 L, t (L - s) = t s ∧ v (L - s) = -v s) ∧
    (∀ u ∈ Icc 0 T, 0 < force right δ p u) ∧
    ConvexOn ℝ (Icc 0 (L / 2)) v ∧
    ConcaveOn ℝ (Icc 0 (L / 2)) t ∧
      (∫ s in (0 : ℝ)..L, v s ^ 2) ≤ L * v 0 ^ 2 / 3 := by
  have hc : L / 2 ∈ Ioo (0 : ℝ) L := ⟨by linarith, by linarith⟩
  have hpos := fun s hs => (hrange s hs).1
  obtain ⟨hvc, hmax, hsym⟩ := actual_return_symmetry (force_smooth right δ p) hL ht hv h0 h1 hpos
  have hmaps : MapsTo t (Icc 0 L) (Icc 0 (t (L / 2))) := by
    intro s hs
    refine ⟨?_, hmax hs⟩
    rcases eq_or_lt_of_le hs.1 with he | he
    · rw [← he, h0]
    · rcases eq_or_lt_of_le hs.2 with he' | he'
      · rw [he', h1]
      · exact (hpos s ⟨he, he'⟩).le
  have htop := force_pos_at_top (force_smooth right δ p) hc (hpos _ hc) ht hv h0 hvc henergy
    (potential_hasDerivAt right δ p _)
  have hanti := force_antitone (hrange _ hc).2.le hconc (p := p)
  have hforce (u : ℝ) (hu : u ∈ Icc 0 (t (L / 2))) : 0 < force right δ p u :=
    lt_of_lt_of_le htop (hanti hu ⟨(hrange _ hc).1.le, le_rfl⟩ hu.2)
  obtain ⟨_, hv0, hvnon⟩ := return_velocity_strictAnti hL hv hmaps hanti htop hvc
  have hsub : Icc (0 : ℝ) (L / 2) ⊆ Icc 0 L := Icc_subset_Icc le_rfl (by linarith)
  have hvconv : ConvexOn ℝ (Icc 0 (L / 2)) v := by
    apply velocity_convex (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs))
      (fun s _ => force_hasDerivAt right δ p (t s)) hvnon
    intro s hs
    have hu := hmaps (hsub hs)
    have hh := hconc (t s) ⟨hu.1, hu.2.trans (hrange _ hc).2.le⟩ p
    change 0 ≤ pairing (-deriv (deriv (coordinateCometric right δ)) (t s)) p p at hh
    rw [pairing_matrix_neg] at hh
    exact neg_nonneg.mp hh
  have htconc : ConcaveOn ℝ (Icc 0 (L / 2)) t :=
    height_concave (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs))
      (fun s hs => (hforce _ (hmaps (hsub hs))).le)
  refine ⟨hv0, hvc, hrange _ hc, hmaps, hsym, hforce, hvconv, htconc, ?_⟩
  exact full_chord_integral hL hv0.le (HasDerivAt.continuousOn hv) hvconv hvnon rfl hvc
    (fun s hs => (hsym s hs).2)

lemma incidence_bound {right : Bool} {δ L : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hδ : 0 ≤ δ) (hT : t (L / 2) ∈ Ioo 0 1)
    (hc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hf : ∀ u ∈ Icc 0 (t (L / 2)), 0 < force right δ p u)
    (h0 : t 0 = 0) (hvc : v (L / 2) = 0)
    (he0 : potential right δ p (t 0) + v 0 ^ 2 = 1)
    (hec : potential right δ p (t (L / 2)) + v (L / 2) ^ 2 = 1) :
    v 0 ^ 2 ≤ δ * Turning.aZero * p 0 ^ 2 := by
  have ha := force_antitone hT.2.le hc (p := p)
  have hbound : ∀ u ∈ Icc 0 (t (L / 2)),
      |force right δ p u| ≤ δ * a 0 * p 0 ^ 2 := by
    intro u hu
    rw [abs_of_pos (hf u hu)]
    have hh := ha ⟨le_rfl, hT.1.le⟩ hu hu.1
    simpa only [force, endpoint_derivative_qform] using hh
  have hh := mixed_variation_bound hT.2.le
    (mul_nonneg (mul_nonneg hδ (a_nonneg 0)) (sq_nonneg (p 0)))
    (show t (L / 2) ∈ Icc 0 (t (L / 2)) from ⟨hT.1.le, le_rfl⟩)
    (fun u _ => ((coordinateCometric_smooth right δ).differentiable (by simp)).differentiableAt.hasDerivAt)
    hbound (show pairing (coordinateCometric right δ 0) p p = potential right δ p 0 from rfl)
  rw [h0] at he0
  rw [hvc] at hec
  change |potential right δ p (t (L / 2)) - potential right δ p 0| ≤ _ at hh
  rw [a_zero] at hh
  dsimp only [Turning.aZero]
  linarith [(abs_le.mp hh).2]

lemma actual_timing_margin {right : Bool} {δ L : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hL : 0 < L) (hstar : 1 / 4 < t (L / 2)) (hT : t (L / 2) < 1)
    (hc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (hrange : MapsTo t (Icc 0 L) (Icc 0 (t (L / 2))))
    (htconc : ConcaveOn ℝ (Icc 0 (L / 2)) t) (h0 : t 0 = 0)
    (hsym : ∀ s ∈ Icc 0 L, t (L - s) = t s ∧ v (L - s) = -v s) :
    4 * v 0 ≤ Turning.beta * (δ * Turning.aZero) * p 0 ^ 2 * L := by
  have he := hsym 0 ⟨le_rfl, hL.le⟩
  simp only [sub_zero] at he
  have hh := turning_time_margin hL hstar (HasDerivAt.continuousOn ht)
    (force_smooth right δ p).continuous.continuousOn hrange (force_antitone hT.le hc)
    htconc h0 rfl (fun s hs => (hsym s hs).1) hv rfl he.2
  dsimp only [force] at hh
  rw [(actual_force_end_values right δ p).1, (actual_force_end_values right δ p).2,
    exact_timing_constant] at hh
  exact hh

end

open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix DirectTurning Turning

lemma coordinateCometric_posDef {right : Bool} {δ u : ℝ}
    (hbound : ∀ q, sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q) :
    (coordinateCometric right δ u).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr (coordinateCometric_transpose right δ u))
  intro q hq
  change 0 < qform (coordinateCometric right δ u) q
  have hs := sqnorm_pos hq
  have hh := hbound q
  linarith

lemma coordinateCometric_inv_continuousAt {right : Bool} {δ u : ℝ}
    (hbound : ∀ q, sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q) :
    ContinuousAt (fun t => (coordinateCometric right δ t)⁻¹) u := by
  have hd : (coordinateCometric right δ u).det ≠ 0 :=
    (coordinateCometric_posDef hbound).det_pos.ne'
  apply (continuousAt_matrix_inv (coordinateCometric right δ u) ?_).comp
    (coordinateCometric_smooth right δ).continuous.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hd

lemma coefficient_expansion {L K : ℝ} (hL : 0 ≤ L) {R : ℝ → TMat} {v : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hs : ∀ s ∈ Icc 0 L, (R s)ᵀ = R s) (p e : TVec) (α : ℝ) :
    (∫ s in (0 : ℝ)..L, pairing (R s) (p - α • e) (p - α • e) +
      4 * v s ^ 2 + α ^ 2 * K) =
    ((∫ s in (0 : ℝ)..L, pairing (R s) p p) + 4 * (∫ s in (0 : ℝ)..L, v s ^ 2)) -
      2 * α * (∫ s in (0 : ℝ)..L, pairing (R s) e p) +
      α ^ 2 * ((∫ s in (0 : ℝ)..L, pairing (R s) e e) + K * L) := by
  have hpp : IntervalIntegrable (fun s => pairing (R s) p p) volume 0 L := (continuousOn_pairing hR continuousOn_const continuousOn_const
    (u := fun _ => p) (v := fun _ => p)).intervalIntegrable_of_Icc hL
  have hep : IntervalIntegrable (fun s => pairing (R s) e p) volume 0 L := (continuousOn_pairing hR continuousOn_const continuousOn_const
    (u := fun _ => e) (v := fun _ => p)).intervalIntegrable_of_Icc hL
  have hee : IntervalIntegrable (fun s => pairing (R s) e e) volume 0 L := (continuousOn_pairing hR continuousOn_const continuousOn_const
    (u := fun _ => e) (v := fun _ => e)).intervalIntegrable_of_Icc hL
  have hvv : IntervalIntegrable (fun s => v s ^ 2) volume 0 L := (hv.pow 2).intervalIntegrable_of_Icc hL
  have heq : (∫ s in (0 : ℝ)..L, pairing (R s) (p - α • e) (p - α • e) +
      4 * v s ^ 2 + α ^ 2 * K) =
      (∫ s in (0 : ℝ)..L, (pairing (R s) p p + 4 * v s ^ 2) -
        2 * α * pairing (R s) e p + α ^ 2 * (pairing (R s) e e + K)) := by
    apply intervalIntegral.integral_congr
    intro s hs'
    have hss : s ∈ Icc 0 L := by simpa only [uIcc_of_le hL] using hs'
    simp only [pairing_sub_left, pairing_sub_right, pairing_smul_left, pairing_smul_right,
      pairing_symm (hs s hss) p e]
    ring
  rw [heq, intervalIntegral.integral_add ((hpp.add (hvv.const_mul 4)).sub
      (hep.const_mul (2 * α))) ((hee.add intervalIntegrable_const).const_mul (α ^ 2)),
    intervalIntegral.integral_sub (hpp.add (hvv.const_mul 4)) (hep.const_mul (2 * α)),
    intervalIntegral.integral_add hpp (hvv.const_mul 4),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hee intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

lemma direct_coefficient_nonneg {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    {R : ℝ → TMat} {v : ℝ → ℝ}
    (hp : ∀ s ∈ Icc 0 L, ∀ q, 0 ≤ pairing (R s) q q) (p e : TVec) (α : ℝ) :
    0 ≤ (∫ s in (0 : ℝ)..L, pairing (R s) (p - α • e) (p - α • e) +
      4 * v s ^ 2 + α ^ 2 * K) := by
  apply intervalIntegral.integral_nonneg hL
  intro s hs
  have hh := hp s hs (p - α • e)
  positivity

lemma energy_nonnegative {L : ℝ} (hL : 0 ≤ L)
    {Q : ℝ → TMat} {k z' : ℝ → TVec} {h w w' : ℝ → ℝ}
    (hp : ∀ s ∈ Icc 0 L, ∀ q, 0 ≤ pairing (Q s) q q)
    (hh : ∀ s ∈ Icc 0 L, 0 ≤ h s) :
    0 ≤ (∫ s in (0 : ℝ)..L, energyDensity Q k h z' w w' s) := by
  apply intervalIntegral.integral_nonneg hL
  intro s hs
  dsimp only [energyDensity]
  have hh' := hh s hs
  have hp' := hp s hs (z' s - w s • k s)
  positivity

def sourceMixed (C : ℝ) : ℝ := a 0 + Real.sqrt (2 * C * a 0) + 2 * Real.sqrt (2 * C * a 0 / 3)

lemma sourceMixed_pos (C : ℝ) : 0 < sourceMixed C := by
  have hp := a_pos (u := 0) (by norm_num)
  dsimp only [sourceMixed]
  positivity

lemma e_dot (p : TVec) : p ⬝ᵥ e = p 0 := by
  simp [e, dotProduct, Fin.sum_univ_two]

theorem actual_returning_energy_bound {right : Bool} {δ C L : ℝ} {p : TVec}
    {t v : ℝ → ℝ} (hC : 18 ≤ C)
    (hδ : SmallParameter (3 * C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q,
      sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18 * sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C ^ 2 * δ ^ 2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hL : 0 < L) (hstar : 1 / 4 < t (L / 2))
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1)
    {z z' : ℝ → TVec} {w w' : ℝ → ℝ}
    (hzc : ContinuousOn z' (Icc 0 L)) (hw'c : ContinuousOn w' (Icc 0 L))
    (hz : ∀ s ∈ Icc 0 L, HasDerivAt z (z' s) s)
    (hw : ∀ s ∈ Icc 0 L, HasDerivAt w (w' s) s)
    (hwa : w 0 = 0) (hwb : w L = 0) :
    0 ≤ (∫ s in (0 : ℝ)..L,
      energyDensity (fun s => (coordinateCometric right δ (t s))⁻¹)
        (fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p)
        (fun s => -forceDerivative right δ p (t s) / 2) z' w w' s) +
      (δ * aZero * v 0 / 4) * (e ⬝ᵥ (z L - z 0)) ^ 2 - (p ⬝ᵥ (z L - z 0)) ^ 2 / L := by
  have hCp : 0 < C := by linarith
  have hδp := hδ.1
  have hap := aZero_pos
  obtain ⟨hv0, hvc, hT, hmaps, hsym, hforce, _, htconc, hchord⟩ :=
    returning_dynamics hL hconc ht hv h0 h1 hrange henergy
  have hmap : MapsTo t (Icc 0 L) (Icc 0 1) := by
    intro s hs
    exact ⟨(hmaps hs).1, (hmaps hs).2.trans hT.2.le⟩
  have hinc := incidence_bound hδ.1.le hT hconc hforce h0 hvc
    (henergy 0 ⟨le_rfl, hL.le⟩) (henergy (L / 2) ⟨by linarith, by linarith⟩)
  have htime := actual_timing_margin hL hstar hT.2 hconc ht hv hmaps htconc h0 hsym
  let R := fun s => coordinateCometric right δ (t s)
  let Q := fun s => (R s)⁻¹
  let k := fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p
  let h := fun s => -forceDerivative right δ p (t s) / 2
  let K := 2 * C * δ
  let spp := (∫ s in (0 : ℝ)..L, pairing (R s) p p) + 4 * (∫ s in (0 : ℝ)..L, v s ^ 2)
  let see := (∫ s in (0 : ℝ)..L, pairing (R s) e e) + K * L
  let spe := (∫ s in (0 : ℝ)..L, pairing (R s) e p)
  have htc := HasDerivAt.continuousOn ht
  have hRc : ContinuousOn R (Icc 0 L) :=
    (coordinateCometric_smooth right δ).continuous.comp_continuousOn htc
  have hQc : ContinuousOn Q (Icc 0 L) := by
    intro s hs
    exact (coordinateCometric_inv_continuousAt (fun q => (hbound (t s) (hmap hs) q).1)).comp_continuousWithinAt (htc s hs)
  have hkc : ContinuousOn k (Icc 0 L) :=
    ((contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2.continuous.matrix_mulVec
      continuous_const).comp_continuousOn htc
  have hhc : ContinuousOn h (Icc 0 L) := by
    have hc : Continuous (forceDerivative right δ p) :=
      (contDiff_pairing_const (contDiff_infty_iff_deriv.mp
        (contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2).2 p p).continuous
    exact (hc.comp_continuousOn htc).neg.div_const 2
  have hPs (s : ℝ) : (R s)ᵀ = R s := coordinateCometric_transpose right δ (t s)
  have hQs (s : ℝ) : (Q s)ᵀ = Q s := by
    dsimp only [Q]
    rw [Matrix.transpose_nonsing_inv, hPs]
  have hPd (s : ℝ) (hs : s ∈ Icc 0 L) : (R s).PosDef :=
    coordinateCometric_posDef (fun q => (hbound (t s) (hmap hs) q).1)
  have hQP (s : ℝ) (hs : s ∈ Icc 0 L) : Q s * R s = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hPd s hs).det_pos.ne')
  have hPnon (s : ℝ) (hs : s ∈ Icc 0 L) (q : TVec) : 0 ≤ pairing (R s) q q := by
    have hh := (hbound (t s) (hmap hs) q).1
    have hn := sqnorm_nonneg q
    change sqnorm q / 9 ≤ pairing (R s) q q at hh
    linarith
  have hQnon (s : ℝ) (hs : s ∈ Icc 0 L) (q : TVec) : 0 ≤ pairing (Q s) q q := by
    exact (hPd s hs).inv.posSemidef.dotProduct_mulVec_nonneg q
  have hh (s : ℝ) (hs : s ∈ Icc 0 L) : 0 ≤ h s := by
    have hc := hconc (t s) (hmap hs) p
    change 0 ≤ pairing (-deriv (deriv (coordinateCometric right δ)) (t s)) p p at hc
    rw [pairing_matrix_neg] at hc
    exact div_nonneg hc (by norm_num)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hdom' (s : ℝ) (hs : s ∈ Icc 0 L) : (e ⬝ᵥ k s) ^ 2 ≤ h s * K := by
    have hd := hdom (t s) (hmap hs)
    have hk : (e ⬝ᵥ k s) ^ 2 ≤ sqnorm (k s) := by
      rw [dotProduct_comm, e_dot]
      dsimp only [sqnorm]
      nlinarith [sq_nonneg (k s 1)]
    have he : C * δ * qform (-deriv (deriv (coordinateCometric right δ)) (t s)) p = h s * K := by
      change C * δ * pairing (-deriv (deriv (coordinateCometric right δ)) (t s)) p p = _
      rw [pairing_matrix_neg]
      dsimp only [h, K, forceDerivative]
      ring
    exact hk.trans (he ▸ hd)
  have hvc' := HasDerivAt.continuousOn hv
  have hspp : spp ≤ L * (1 + v 0 ^ 2) :=
    first_coefficient_bound hL.le (continuousOn_pairing hRc continuousOn_const continuousOn_const)
      hvc' henergy hchord
  have hsee : 0 ≤ see := by
    have hi : 0 ≤ (∫ s in (0 : ℝ)..L, pairing (R s) e e) :=
      intervalIntegral.integral_nonneg hL.le (fun s hs => hPnon s hs e)
    dsimp only [see]
    positivity
  have hsee_upper : see ≤ (3 * C) * L := by
    apply second_coefficient_bound hL.le hCp.le ⟨hδ.1.le, hδ.2.1⟩
      (continuousOn_pairing hRc continuousOn_const continuousOn_const)
    intro s hs
    have hh := (hbound (t s) (hmap hs) e).2
    rw [sqnorm_e, mul_one] at hh
    exact hh.trans hC
  have hmixed : |spe - L * p 0| ≤ sourceMixed C * δ * L * |p 0| := by
    have hamb := actual_mixed_bound hδ.1.le hCp ⟨hT.1.le, hT.2.le⟩ hconc hder
      (fun u hu => (hforce u hu).le)
    have hi := mixed_integral_bound hL.le
      (continuousOn_pairing hRc continuousOn_const continuousOn_const)
      (fun s hs => hamb (t s) (hmaps hs))
    apply hi.trans
    have hm : a 0 + Real.sqrt (2 * C * a 0) ≤ sourceMixed C := by
      dsimp only [sourceMixed]
      linarith [Real.sqrt_nonneg (2 * C * a 0 / 3)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hδ.1.le) hL.le) (abs_nonneg _)
  have hcs (α : ℝ) : ((p - α • e) ⬝ᵥ (z L - z 0)) ^ 2 ≤
      (spp - 2 * α * spe + α ^ 2 * see) *
        (∫ s in (0 : ℝ)..L, energyDensity Q k h z' w w' s) := by
    have hh := direct_endpoint_cauchy hL.le hK p e hRc hQc hkc hhc hvc' hzc
      (HasDerivAt.continuousOn hw) hw'c hQP (fun s _ => hPs s) (fun s _ => hQs s)
      hQnon hh hdom' hz hv hw (fun s _ => by dsimp only [k, force, pairing]; ring) hwa hwb α
    rw [coefficient_expansion hL.le hRc hvc' (fun s _ => hPs s)] at hh
    exact hh
  apply returning_endpoint_bound (by positivity : 0 < 3 * C) (sourceMixed_pos C) hδ hL hv0
    (by positivity : 0 < δ * aZero * v 0 / 4) rfl rfl
    (by simpa only [e_dot] using hinc) (by simpa only [e_dot] using htime)
    hspp hsee hsee_upper (by simpa only [e_dot] using hmixed)
    (energy_nonnegative hL.le hQnon hh) ?_ hcs
  intro α
  rw [← coefficient_expansion hL.le hRc hvc' (fun s _ => hPs s)]
  exact direct_coefficient_nonneg hL.le hK hPnon p e α

theorem uniform_turning_parameters : ∃ δ₀ C : ℝ,
    0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ 18 ≤ C ∧
    ∀ δ ∈ Ioc (0 : ℝ) δ₀,
      SmallParameter (3 * C) (sourceMixed C) δ ∧
      ∀ right : Bool, ∀ u ∈ Icc (0 : ℝ) 1, ∀ q : TVec,
        (sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q ∧
          qform (coordinateCometric right δ u) q ≤ 18 * sqnorm q) ∧
        sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
        0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
        sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤
          C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q := by
  obtain ⟨ε, D, hε, hhalf, hD, hb⟩ := uniform_cometric_bounds
  let C := 18 + D
  have hC : 18 ≤ C := by dsimp only [C]; linarith
  have hCp : 0 < C := by linarith
  have hDC : D ≤ C := by dsimp only [C]; linarith
  have hDCsq : D ^ 2 ≤ C ^ 2 := by nlinarith
  have hm := sourceMixed_pos C
  have ha := aZero_pos
  have hβ := beta_lt_one
  let ε' := min ε (min 1 (min (1 / (2 * sourceMixed C))
    ((1 - beta) / (2 * sourceMixed C + (3 * C) * aZero))))
  have hep : 0 < ε' := by dsimp only [ε']; positivity
  have hea : ε' ≤ ε := min_le_left _ _
  refine ⟨ε', C, hep, hea.trans hhalf, hC, ?_⟩
  intro δ hδ
  have hδ' : δ ∈ Ioc (0 : ℝ) ε := ⟨hδ.1, hδ.2.trans hea⟩
  have hs : SmallParameter (3 * C) (sourceMixed C) δ := by
    have hh := hδ.2.trans (min_le_right ε _)
    refine ⟨hδ.1, hh.trans (min_le_left _ _),
      (hh.trans (min_le_right _ _)).trans (min_le_left _ _),
      (hh.trans (min_le_right _ _)).trans (min_le_right _ _)⟩
  refine ⟨hs, ?_⟩
  intro right u hu q
  obtain ⟨hq, _, hd, hc, hdom⟩ := hb δ hδ' right u hu q
  refine ⟨hq, ?_, hc, ?_⟩
  · exact hd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDCsq (sq_nonneg _)) (sqnorm_nonneg q))
  · exact hdom.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDC hδ.1.le) hc)

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck

section
open Set Matrix MeasureTheory
open scoped ContDiff Interval Topology Matrix.Norms.Elementwise

lemma contDiffOn_pairing {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : X → TMat} {u v : X → TVec} {S : Set X} {n : WithTop ℕ∞}
    (hA : ContDiffOn ℝ n A S) (hu : ContDiffOn ℝ n u S) (hv : ContDiffOn ℝ n v S) :
    ContDiffOn ℝ n (fun s => pairing (A s) (u s) (v s)) S := by
  unfold pairing Matrix.mulVec dotProduct
  apply ContDiffOn.sum
  intro i _
  exact ((contDiffOn_pi.mp hu i).mul (ContDiffOn.sum fun j _ =>
    (contDiffOn_pi.mp (contDiffOn_pi.mp hA i) j).mul (contDiffOn_pi.mp hv j)))

lemma contDiffOn_metric {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Q : X → TMat} {V T : X → Vec} {S : Set X} {n : WithTop ℕ∞}
    (hQ : ContDiffOn ℝ n Q S) (hV : ContDiffOn ℝ n V S) (hT : ContDiffOn ℝ n T S) :
    ContDiffOn ℝ n (fun s => metric (Q s) (V s) (T s)) S :=
  (hV.fst.mul hT.fst).add (contDiffOn_pairing hQ hV.snd hT.snd)

def turningAffine (L v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) (s : ℝ) : ℝ :=
  let q := fun r => metric (Q r) (V r) (T r)
  q 0 - (V 0).1 / v₀ + s / L *
    ((q L + (V L).1 / v₀) - (q 0 - (V 0).1 / v₀))

def turningChange (L v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) (s : ℝ) : ℝ :=
  turningAffine L v₀ V T Q s - metric (Q s) (V s) (T s)

def turningField (L v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) (s : ℝ) : Vec :=
  V s + turningChange L v₀ V T Q s • T s

lemma turningAffine_zero (L v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) :
    turningAffine L v₀ V T Q 0 = metric (Q 0) (V 0) (T 0) - (V 0).1 / v₀ := by
  simp [turningAffine]

lemma turningAffine_end {L : ℝ} (hL : L ≠ 0) (v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) :
    turningAffine L v₀ V T Q L = metric (Q L) (V L) (T L) + (V L).1 / v₀ := by
  simp [turningAffine, hL]

lemma turningField_zero {L v₀ : ℝ} (hv₀ : v₀ ≠ 0) (V T : ℝ → Vec)
    (Q : ℝ → TMat) (hT : (T 0).1 = v₀) :
    (turningField L v₀ V T Q 0).1 = 0 := by
  simp only [turningField, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
    turningChange, turningAffine_zero, hT]
  field_simp
  ring

lemma turningField_end {L v₀ : ℝ} (hL : L ≠ 0) (hv₀ : v₀ ≠ 0) (V T : ℝ → Vec)
    (Q : ℝ → TMat) (hT : (T L).1 = -v₀) :
    (turningField L v₀ V T Q L).1 = 0 := by
  simp only [turningField, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
    turningChange, turningAffine_end hL, hT]
  field_simp
  ring

lemma turningField_tangential {L v₀ s : ℝ} (V T : ℝ → Vec) (Q : ℝ → TMat)
    (hunit : metric (Q s) (T s) (T s) = 1) :
    metric (Q s) (turningField L v₀ V T Q s) (T s) = turningAffine L v₀ V T Q s := by
  simp only [turningField, turningChange, metric_add_left, metric_smul_left, hunit]
  ring

lemma turningField_smooth {L v₀ : ℝ} {V T : ℝ → Vec} {Q : ℝ → TMat} {U : Set ℝ}
    (hQ : ContDiffOn ℝ ∞ Q U) (hV : ContDiffOn ℝ ∞ V U) (hT : ContDiffOn ℝ ∞ T U) :
    ContDiffOn ℝ ∞ (turningField L v₀ V T Q) U := by
  apply hV.add
  change ContDiffOn ℝ ∞ ((turningChange L v₀ V T Q) • T) U
  apply ContDiffOn.smul _ hT
  exact ((contDiffOn_const.add ((contDiffOn_id.div_const L).mul contDiffOn_const))).sub
    (contDiffOn_metric hQ hV hT)

lemma turningAffine_hasDerivAt (L v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) (s : ℝ) :
    HasDerivAt (turningAffine L v₀ V T Q)
      (((metric (Q L) (V L) (T L) + (V L).1 / v₀) -
        (metric (Q 0) (V 0) (T 0) - (V 0).1 / v₀)) / L) s := by
  convert! (((hasDerivAt_id s).div_const L).mul_const
    ((metric (Q L) (V L) (T L) + (V L).1 / v₀) -
      (metric (Q 0) (V 0) (T 0) - (V 0).1 / v₀))).const_add
      (metric (Q 0) (V 0) (T 0) - (V 0).1 / v₀) using 1
  ring

lemma gauge_hasDerivAt {P A : TMat} {V T : ℝ → Vec} {h : ℝ → ℝ}
    {D : Vec} {h' s : ℝ} (hV : HasDerivAt V D s)
    (hT : HasDerivAt T (-gamma P A (T s) (T s)) s) (hh : HasDerivAt h h' s) :
    HasDerivAt (fun r => V r + h r • T r)
      (D + h' • T s - h s • gamma P A (T s) (T s)) s := by
  apply (hV.add (hh.smul hT)).congr_deriv
  module

lemma normalDensity_deriv_gauge {P Q A B : TMat} (hQP : Q * P = 1)
    (hQ : Qᵀ = Q) (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B)
    {V T : ℝ → Vec} {h : ℝ → ℝ} {D : Vec} {h' s : ℝ}
    (hunit : metric Q (T s) (T s) = 1) (hV : HasDerivAt V D s)
    (hT : HasDerivAt T (-gamma P A (T s) (T s)) s) (hh : HasDerivAt h h' s) :
    normalDensity P Q A B (T s) (V s + h s • T s)
      (deriv (fun r => V r + h r • T r) s) = normalDensity P Q A B (T s) (V s) D := by
  rw [(gauge_hasDerivAt hV hT hh).deriv]
  exact normalDensity_gauge hQP hQ hP hA hB (T s) (V s) D hunit (h s) h'

lemma turning_boundary_term (κ v : ℝ) (u z : TVec) :
    boundaryTerm !![-κ, 0; 0, 0] (v, u) (0, z) = κ * v * (z 0) ^ 2 / 2 := by
  simp only [boundaryTerm, zero_mul, add_zero, pairing, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_zero, zero_mul, add_zero]
  ring

lemma turning_boundary_reduction {κ v : ℝ} (hκ : 0 ≤ κ) (hv : 0 ≤ v) (z₀ zL : TVec) :
    κ * v / 4 * ((zL - z₀) 0) ^ 2 ≤ κ * v / 2 * ((z₀ 0) ^ 2 + (zL 0) ^ 2) := by
  have hh := mul_nonneg (mul_nonneg hκ hv) (sq_nonneg (zL 0 + z₀ 0))
  change κ * v / 4 * (zL 0 - z₀ 0) ^ 2 ≤ _
  nlinarith

end

section
open Set Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma contDiffAt_det_two {R : ℝ → TMat} {s : ℝ} (hR : ContDiffAt ℝ ∞ R s) :
    ContDiffAt ℝ ∞ (fun u => (R u).det) s := by
  simp only [Matrix.det_fin_two]
  exact ((contDiffAt_pi.mp (contDiffAt_pi.mp hR 0) 0).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hR 1) 1)).sub
    ((contDiffAt_pi.mp (contDiffAt_pi.mp hR 0) 1).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp hR 1) 0))

lemma matrix_inverse_smoothAt {R : ℝ → TMat} {s : ℝ}
    (hR : ContDiffAt ℝ ∞ R s) (hdet : (R s).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun u => (R u)⁻¹) s := by
  have hscalar := (contDiffAt_det_two hR).inv hdet
  have he (u : ℝ) : (R u)⁻¹ = (R u).det⁻¹ •
      !![R u 1 1, -R u 0 1; -R u 1 0, R u 0 0] := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
  simp_rw [he]
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hscalar.mul (contDiffAt_pi.mp (contDiffAt_pi.mp hR 1) 1)
  · exact hscalar.mul (contDiffAt_pi.mp (contDiffAt_pi.mp hR 0) 1).neg
  · exact hscalar.mul (contDiffAt_pi.mp (contDiffAt_pi.mp hR 1) 0).neg
  · exact hscalar.mul (contDiffAt_pi.mp (contDiffAt_pi.mp hR 0) 0)

lemma matrix_inverse_first_deriv {R : ℝ → TMat} {s : ℝ}
    (hR : ContDiff ℝ ∞ R) (hdet : (R s).det ≠ 0) :
    deriv (fun u => (R u)⁻¹) s = -(R s)⁻¹ * deriv R s * (R s)⁻¹ := by
  apply inverse_first_jet ((hR.differentiable (by simp)).differentiableAt.hasDerivAt)
    ((matrix_inverse_smoothAt hR.contDiffAt hdet).differentiableAt (by simp)).hasDerivAt
  · filter_upwards [(contDiffAt_det_two hR.contDiffAt).continuousAt.eventually_ne hdet] with u hu
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu)
  · exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)

lemma matrix_inverse_second_deriv {R : ℝ → TMat} {s : ℝ}
    (hR : ContDiff ℝ ∞ R) (hdet : (R s).det ≠ 0) :
    deriv (deriv (fun u => (R u)⁻¹)) s =
      (2 : ℝ) • ((R s)⁻¹ * deriv R s * (R s)⁻¹ * deriv R s * (R s)⁻¹) -
        (R s)⁻¹ * deriv (deriv R) s * (R s)⁻¹ := by
  have hQ := ((matrix_inverse_smoothAt hR.contDiffAt hdet).differentiableAt (by simp)).hasDerivAt
  have hRd : HasDerivAt (deriv R) (deriv (deriv R) s) s := ((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp)).differentiableAt.hasDerivAt
  have h := matrix_mul_hasDerivAt (matrix_mul_hasDerivAt hQ.neg hRd) hQ
  have he : deriv (fun u => (R u)⁻¹) =ᶠ[nhds s]
      (fun u => -(R u)⁻¹ * deriv R u * (R u)⁻¹) := by
    filter_upwards [(contDiffAt_det_two hR.contDiffAt).continuousAt.eventually_ne hdet] with u hu
    exact matrix_inverse_first_deriv hR hu
  have hh : deriv (deriv (fun u => (R u)⁻¹)) s =
      ((-deriv (fun u => (R u)⁻¹) s * deriv R s + (- (R s)⁻¹) * deriv (deriv R) s) * (R s)⁻¹ +
        (-(R s)⁻¹) * deriv R s * deriv (fun u => (R u)⁻¹) s) :=
    (h.congr_of_eventuallyEq he).deriv
  rw [hh, matrix_inverse_first_deriv hR hdet]
  simp only [neg_mul, mul_neg, neg_neg, add_mul, ← Matrix.mul_assoc]
  module

end

open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma continuousOn_metric {X : Type*} [TopologicalSpace X] {S : Set X}
    {Q : X → TMat} {V W : X → Vec} (hQ : ContinuousOn Q S)
    (hV : ContinuousOn V S) (hW : ContinuousOn W S) :
    ContinuousOn (fun s => metric (Q s) (V s) (W s)) S :=
  (hV.fst.mul hW.fst).add (continuousOn_pairing hQ hV.snd hW.snd)

lemma derivative_transpose {R : ℝ → TMat} (hs : ∀ u, (R u)ᵀ = R u)
    {s : ℝ} (hR : DifferentiableAt ℝ R s) : (deriv R s)ᵀ = deriv R s := by
  ext i j
  have hij : (fun u => R u j i) = (fun u => R u i j) := by
    funext u
    exact congrArg (fun m : TMat => m i j) (hs u)
  have hd := congrArg (fun f : ℝ → ℝ => deriv f s) hij
  rw [(hasDerivAt_pi.mp (hasDerivAt_pi.mp hR.hasDerivAt j) i).deriv,
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hR.hasDerivAt i) j).deriv] at hd
  exact hd

lemma gamma_momentum {P Q H : TMat} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hP : Pᵀ = P) (v : ℝ) (p : TVec) :
    gamma P (-Q * H * Q) (v, P *ᵥ p) (v, P *ᵥ p) =
      (pairing H p p / 2, -v • (H *ᵥ p)) := by
  have hp : (-Q * H * Q) *ᵥ (P *ᵥ p) = -(Q *ᵥ (H *ᵥ p)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hQP, Matrix.mul_one,
      Matrix.neg_mulVec, neg_mul]
  have hleft : pairing (-Q * H * Q) (P *ᵥ p) (P *ᵥ p) = -pairing H p p := by
    rw [pairing_mulVec_left, pairing_mulVec_right, hP]
    have hmat : P * (-Q * H * Q) * P = -H := by
      simp only [mul_neg, neg_mul, Matrix.mul_assoc, hQP, Matrix.mul_one]
      simp only [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    rw [hmat, pairing_matrix_neg]
  apply Prod.ext
  · simp only [gamma, hleft]
    ring
  · simp only [gamma, hp, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    module

lemma normal_index_integral
    {P Q A B : ℝ → TMat} {t v w : ℝ → ℝ} {u z : ℝ → TVec}
    {wd : ℝ → ℝ} {zd : ℝ → TVec} {a c m : ℝ}
    (hP : ContinuousOn (P ∘ t) (uIcc a c))
    (hQ : ContinuousOn (Q ∘ t) (uIcc a c))
    (hA : ContinuousOn (A ∘ t) (uIcc a c))
    (hB : ContinuousOn (B ∘ t) (uIcc a c))
    (hv : ContinuousOn v (uIcc a c)) (hu : ContinuousOn u (uIcc a c))
    (hw : ContinuousOn w (uIcc a c)) (hz : ContinuousOn z (uIcc a c))
    (hwd : ContinuousOn wd (uIcc a c)) (hzd : ContinuousOn zd (uIcc a c))
    (hQP : ∀ s ∈ uIcc a c, Q (t s) * P (t s) = 1)
    (hQs : ∀ s ∈ uIcc a c, (Q (t s))ᵀ = Q (t s))
    (hPs : ∀ s ∈ uIcc a c, (P (t s))ᵀ = P (t s))
    (hAs : ∀ s ∈ uIcc a c, (A (t s))ᵀ = A (t s))
    (hBs : ∀ s ∈ uIcc a c, (B (t s))ᵀ = B (t s))
    (ht : ∀ s ∈ uIcc a c, HasDerivAt t (v s) s)
    (hv' : ∀ s ∈ uIcc a c,
      HasDerivAt v ((1 / 2 : ℝ) * pairing (A (t s)) (u s) (u s)) s)
    (hu' : ∀ s ∈ uIcc a c,
      HasDerivAt u (-v s • (P (t s) *ᵥ (A (t s) *ᵥ u s))) s)
    (hQ' : ∀ s ∈ uIcc a c, HasDerivAt Q (A (t s)) (t s))
    (hA' : ∀ s ∈ uIcc a c, HasDerivAt A (B (t s)) (t s))
    (hw' : ∀ s ∈ uIcc a c, HasDerivAt w (wd s) s)
    (hz' : ∀ s ∈ uIcc a c, HasDerivAt z (zd s) s)
    (hlin : ∀ s ∈ uIcc a c,
      HasDerivAt (fun r => metric (Q (t r)) (w r, z r) (v r, u r)) m s) :
    (∫ s in a..c, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s, u s) (w s, z s) (wd s, zd s)) =
      (∫ s in a..c, coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
        (v s, u s) (w s, z s) (wd s, zd s)) -
      (boundaryTerm (A (t c)) (v c, u c) (w c, z c) -
        boundaryTerm (A (t a)) (v a, u a) (w a, z a)) - (c - a) * m ^ 2 := by
  have hTi (s : ℝ) (hs : s ∈ uIcc a c) : HasDerivAt (fun r => (v r, u r))
      (-gamma (P (t s)) (A (t s)) (v s, u s) (v s, u s)) s := by
    apply ((hv' s hs).prodMk (hu' s hs)).congr_deriv
    apply Prod.ext
    · simp only [gamma, Prod.fst_neg, neg_mul, neg_neg]
    · simp only [gamma, Prod.snd_neg]
      module
  have hm (s : ℝ) (hs : s ∈ uIcc a c) :
      metric (Q (t s)) ((wd s, zd s) + gamma (P (t s)) (A (t s))
        (v s, u s) (w s, z s)) (v s, u s) = m := by
    exact (tangential_hasDerivAt (hQP s hs) (hQs s hs) (hAs s hs) (hQ' s hs)
      (ht s hs) (hTi s hs) ((hw' s hs).prodMk (hz' s hs))).unique (hlin s hs)
  let E := fun s => coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
    (v s, u s) (w s, z s) (wd s, zd s)
  let D := fun s => boundaryJet (P (t s)) (A (t s)) (B (t s))
    (v s, u s) (w s, z s) (wd s, zd s)
  have hEc : ContinuousOn E (uIcc a c) :=
    continuousOn_energy hQ hA hB (hv.prodMk hu) (hw.prodMk hz) (hwd.prodMk hzd)
  have hDc : ContinuousOn D (uIcc a c) :=
    continuousOn_boundaryJet hP hA hB (hv.prodMk hu) (hw.prodMk hz) (hwd.prodMk hzd)
  have hI := coordinate_index_integral hP hQ hA hB hv hu hw hz hwd hzd hQP
    hQs hPs hAs hBs ht hv' hu' hA' hw' hz'
  have heq : (∫ s in a..c, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s, u s) (w s, z s) (wd s, zd s)) = (∫ s in a..c, E s - D s - m ^ 2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    change normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s, u s) (w s, z s) (wd s, zd s) = E s - D s - m ^ 2
    unfold normalDensity
    rw [index_density_identity (hQP s hs) (hQs s hs) (hPs s hs)
      (hAs s hs) (hBs s hs), hm s hs]
  have hsub : (∫ s in a..c, E s - D s - m ^ 2) =
      (∫ s in a..c, E s - D s) - (∫ _s in a..c, m ^ 2) :=
    intervalIntegral.integral_sub ((hEc.sub hDc).intervalIntegrable) intervalIntegrable_const
  rw [heq, hsub, intervalIntegral.integral_const, smul_eq_mul]
  have hED : (∫ s in a..c, E s - D s) =
      (∫ s in a..c, coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
        (v s, u s) (w s, z s) (wd s, zd s)) -
      (boundaryTerm (A (t c)) (v c, u c) (w c, z c) -
        boundaryTerm (A (t a)) (v a, u a) (w a, z a)) := by
    rw [← hI]
    apply intervalIntegral.integral_congr
    intro s hs
    exact (index_density_identity (hQP s hs) (hQs s hs) (hPs s hs)
      (hAs s hs) (hBs s hs) (v s, u s) (w s, z s) (wd s, zd s)).symm
  rw [hED]

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

def metricInverse (right : Bool) (δ u : ℝ) : TMat := (coordinateCometric right δ u)⁻¹

lemma metricInverse_transpose (right : Bool) (δ u : ℝ) :
    (metricInverse right δ u)ᵀ = metricInverse right δ u := by
  simp only [metricInverse, Matrix.transpose_nonsing_inv,
    coordinateCometric_transpose]

lemma symmetric_total_deriv {Q : ℝ → TMat} (hs : ∀ u, (Q u)ᵀ = Q u) (u : ℝ) :
    (deriv Q u)ᵀ = deriv Q u := by
  by_cases hQ : DifferentiableAt ℝ Q u
  · exact derivative_transpose hs hQ
  · have hd : deriv Q u = 0 := deriv_zero_of_not_differentiableAt hQ
    rw [hd]
    rfl

lemma metricInverse_deriv_transpose (right : Bool) (δ u : ℝ) :
    (deriv (metricInverse right δ) u)ᵀ = deriv (metricInverse right δ) u :=
  symmetric_total_deriv (metricInverse_transpose right δ) u

lemma metricInverse_second_transpose (right : Bool) (δ u : ℝ) :
    (deriv (deriv (metricInverse right δ)) u)ᵀ = deriv (deriv (metricInverse right δ)) u :=
  symmetric_total_deriv (metricInverse_deriv_transpose right δ) u

lemma metricInverse_smoothAt {right : Bool} {δ u : ℝ}
    (hdet : (coordinateCometric right δ u).det ≠ 0) :
    ContDiffAt ℝ ∞ (metricInverse right δ) u :=
  matrix_inverse_smoothAt (coordinateCometric_smooth right δ).contDiffAt hdet

lemma metricInverse_first {right : Bool} {δ u : ℝ}
    (hdet : (coordinateCometric right δ u).det ≠ 0) :
    deriv (metricInverse right δ) u =
      -metricInverse right δ u * deriv (coordinateCometric right δ) u * metricInverse right δ u :=
  matrix_inverse_first_deriv (coordinateCometric_smooth right δ) hdet

lemma metricInverse_second {right : Bool} {δ u : ℝ}
    (hdet : (coordinateCometric right δ u).det ≠ 0) :
    deriv (deriv (metricInverse right δ)) u =
      (2 : ℝ) • (metricInverse right δ u * deriv (coordinateCometric right δ) u *
        metricInverse right δ u * deriv (coordinateCometric right δ) u * metricInverse right δ u) -
      metricInverse right δ u * deriv (deriv (coordinateCometric right δ)) u * metricInverse right δ u :=
  matrix_inverse_second_deriv (coordinateCometric_smooth right δ) hdet

lemma metricInverse_endpoint {right : Bool} {δ : ℝ}
    (hdet : (coordinateCometric right δ 0).det ≠ 0) :
    metricInverse right δ 0 = !![1, 0; 0, (1 + δ * A 1)⁻¹] := by
  have hd : 1 + δ * A 1 ≠ 0 := by
    rw [coordinateCometric_end (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hdet
    simpa [Matrix.det_fin_two, A] using hdet
  unfold metricInverse
  apply Matrix.inv_eq_left_inv
  rw [coordinateCometric_end (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have ha : A 0 = 0 := by simp [A]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd]

lemma metricInverse_endpoint_deriv {right : Bool} {δ : ℝ}
    (hdet : (coordinateCometric right δ 0).det ≠ 0) :
    deriv (metricInverse right δ) 0 = !![-(δ * a 0), 0; 0, 0] := by
  rw [metricInverse_first hdet, metricInverse_endpoint hdet,
    coordinateCometric_end_deriv (by norm_num : (0 : ℝ) < 1 / 4)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def momentumVelocity (right : Bool) (δ : ℝ) (p : TVec) (t v : ℝ → ℝ) (s : ℝ) : Vec :=
  (v s, coordinateCometric right δ (t s) *ᵥ p)

lemma momentumVelocity_hasDerivAt {right : Bool} {δ s : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hdet : (coordinateCometric right δ (t s)).det ≠ 0)
    (ht : HasDerivAt t (v s) s) (hv : HasDerivAt v (-force right δ p (t s) / 2) s) :
    HasDerivAt (momentumVelocity right δ p t v)
      (-gamma (coordinateCometric right δ (t s)) (deriv (metricInverse right δ) (t s))
        (momentumVelocity right δ p t v s) (momentumVelocity right δ p t v s)) s := by
  have hR : HasDerivAt (coordinateCometric right δ) (deriv (coordinateCometric right δ) (t s)) (t s) :=
    ((coordinateCometric_smooth right δ).differentiable (by simp)).differentiableAt.hasDerivAt
  have hu := mulVec_hasDerivAt (hR.scomp s ht) (hasDerivAt_const s p)
  have hPQ : coordinateCometric right δ (t s) * metricInverse right δ (t s) = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hQP : metricInverse right δ (t s) * coordinateCometric right δ (t s) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  apply (hv.prodMk hu).congr_deriv
  rw [metricInverse_first hdet]
  change (-force right δ p (t s) / 2,
      ((v s • deriv (coordinateCometric right δ) (t s)) *ᵥ p +
        coordinateCometric right δ (t s) *ᵥ 0)) = _
  simp only [momentumVelocity]
  rw [gamma_momentum hPQ hQP (coordinateCometric_transpose right δ (t s))]
  apply Prod.ext
  · simp only [force, Prod.fst_neg]
    ring
  · simp only [Matrix.smul_mulVec, Matrix.mulVec_zero, add_zero, Prod.snd_neg,
      neg_smul, neg_neg]

lemma momentumVelocity_unit {right : Bool} {δ s : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hdet : (coordinateCometric right δ (t s)).det ≠ 0)
    (he : potential right δ p (t s) + v s ^ 2 = 1) :
    metric (metricInverse right δ (t s)) (momentumVelocity right δ p t v s)
      (momentumVelocity right δ p t v s) = 1 := by
  have hQP : metricInverse right δ (t s) * coordinateCometric right δ (t s) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  simp only [momentumVelocity, metric, pairing_inverse hQP]
  rw [dotProduct_comm]
  dsimp only [potential, pairing] at he
  nlinarith

lemma momentumVelocity_pairing {right : Bool} {δ s : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hdet : (coordinateCometric right δ (t s)).det ≠ 0) (W : Vec) :
    metric (metricInverse right δ (t s)) W (momentumVelocity right δ p t v s) =
      W.1 * v s + p ⬝ᵥ W.2 := by
  have hQP : metricInverse right δ (t s) * coordinateCometric right δ (t s) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  simp only [momentumVelocity, metric, pairing_inverse hQP, dotProduct_comm]

end

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise

def returnNormalDensity (right : Bool) (δ : ℝ) (p : TVec) (t v : ℝ → ℝ)
    (V D : ℝ → Vec) (s : ℝ) : ℝ :=
  normalDensity (coordinateCometric right δ (t s)) (metricInverse right δ (t s))
    (deriv (metricInverse right δ) (t s)) (deriv (deriv (metricInverse right δ)) (t s))
    (momentumVelocity right δ p t v s) (V s) (D s)

lemma returning_normal_identity {right : Bool} {δ L m : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hL : 0 < L)
    (hdet : ∀ s ∈ Icc 0 L, (coordinateCometric right δ (t s)).det ≠ 0)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (h0 : t 0 = 0) (h1 : t L = 0) (hvL : v L = -v 0)
    {z z' : ℝ → TVec} {w w' : ℝ → ℝ}
    (hzc : ContinuousOn z' (Icc 0 L)) (hwc : ContinuousOn w' (Icc 0 L))
    (hz : ∀ s ∈ Icc 0 L, HasDerivAt z (z' s) s)
    (hw : ∀ s ∈ Icc 0 L, HasDerivAt w (w' s) s)
    (hwa : w 0 = 0) (hwb : w L = 0)
    (hlin : ∀ s ∈ Icc 0 L, HasDerivAt
      (fun r => metric (metricInverse right δ (t r)) (w r, z r)
        (momentumVelocity right δ p t v r)) m s) :
    (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v
      (fun r => (w r, z r)) (fun r => (w' r, z' r)) s) =
    (∫ s in (0 : ℝ)..L,
      energyDensity (fun s => (coordinateCometric right δ (t s))⁻¹)
        (fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p)
        (fun s => -forceDerivative right δ p (t s) / 2) z' w w' s) +
      δ * a 0 * v 0 / 2 * ((z 0 0) ^ 2 + (z L 0) ^ 2) -
        (p ⬝ᵥ (z L - z 0)) ^ 2 / L := by
  let R := coordinateCometric right δ
  let Q := metricInverse right δ
  let u := fun s => R (t s) *ᵥ p
  have htc := HasDerivAt.continuousOn ht
  have hvc := HasDerivAt.continuousOn hv
  have huc : ContinuousOn u (Icc 0 L) :=
    ((coordinateCometric_smooth right δ).continuous.matrix_mulVec continuous_const).comp_continuousOn htc
  have hRc : ContinuousOn (R ∘ t) (Icc 0 L) :=
    (coordinateCometric_smooth right δ).continuous.comp_continuousOn htc
  have hQa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ Q (t s) :=
    metricInverse_smoothAt (hdet s hs)
  have hQc : ContinuousOn (Q ∘ t) (Icc 0 L) := fun s hs =>
    (hQa s hs).continuousAt.comp_continuousWithinAt (htc s hs)
  have hAc : ContinuousOn (deriv Q ∘ t) (Icc 0 L) := fun s hs =>
    ((hQa s hs).derivWithin (m := ∞) (by simp)).continuousAt.comp_continuousWithinAt (htc s hs)
  have hBc : ContinuousOn (deriv (deriv Q) ∘ t) (Icc 0 L) := fun s hs =>
    (((hQa s hs).derivWithin (m := ∞) (by simp)).derivWithin (m := ∞) (by simp)).continuousAt.comp_continuousWithinAt (htc s hs)
  have hQP (s : ℝ) (hs : s ∈ Icc 0 L) : Q (t s) * R (t s) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet s hs))
  have hQs (s : ℝ) (_hs : s ∈ Icc 0 L) : (Q (t s))ᵀ = Q (t s) := metricInverse_transpose right δ (t s)
  have hPs (s : ℝ) (_hs : s ∈ Icc 0 L) : (R (t s))ᵀ = R (t s) := coordinateCometric_transpose right δ (t s)
  have hAs (s : ℝ) (_hs : s ∈ Icc 0 L) : (deriv Q (t s))ᵀ = deriv Q (t s) := metricInverse_deriv_transpose right δ (t s)
  have hBs (s : ℝ) (_hs : s ∈ Icc 0 L) : (deriv (deriv Q) (t s))ᵀ = deriv (deriv Q) (t s) := metricInverse_second_transpose right δ (t s)
  have hQd (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt Q (deriv Q (t s)) (t s) :=
    ((hQa s hs).differentiableAt (by simp)).hasDerivAt
  have hAd (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt (deriv Q) (deriv (deriv Q) (t s)) (t s) :=
    (((hQa s hs).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hTv (s : ℝ) (hs : s ∈ Icc 0 L) :
      HasDerivAt v ((1 / 2 : ℝ) * pairing (deriv Q (t s)) (u s) (u s)) s := by
    have hh := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
      (momentumVelocity_hasDerivAt (hdet s hs) (ht s hs) (hv s hs))
    simpa only [momentumVelocity, Function.comp_def, ContinuousLinearMap.coe_fst', gamma,
      Prod.fst_neg, neg_mul, neg_neg] using hh
  have hTu (s : ℝ) (hs : s ∈ Icc 0 L) :
      HasDerivAt u (-v s • (R (t s) *ᵥ (deriv Q (t s) *ᵥ u s))) s := by
    have hh := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
      (momentumVelocity_hasDerivAt (hdet s hs) (ht s hs) (hv s hs))
    apply hh.congr_deriv
    simp only [momentumVelocity, gamma, ContinuousLinearMap.coe_snd', Prod.snd_neg, neg_smul]
    dsimp only [u, R, Q]
    module
  have hnorm := normal_index_integral (a := 0) (c := L) (m := m)
    (by simpa only [uIcc_of_le hL.le] using hRc)
    (by simpa only [uIcc_of_le hL.le] using hQc)
    (by simpa only [uIcc_of_le hL.le] using hAc)
    (by simpa only [uIcc_of_le hL.le] using hBc)
    (by simpa only [uIcc_of_le hL.le] using hvc)
    (by simpa only [uIcc_of_le hL.le] using huc)
    (by simpa only [uIcc_of_le hL.le] using HasDerivAt.continuousOn hw)
    (by simpa only [uIcc_of_le hL.le] using HasDerivAt.continuousOn hz)
    (by simpa only [uIcc_of_le hL.le] using hwc)
    (by simpa only [uIcc_of_le hL.le] using hzc)
    (by simpa only [uIcc_of_le hL.le] using hQP)
    (by simpa only [uIcc_of_le hL.le] using hQs)
    (by simpa only [uIcc_of_le hL.le] using hPs)
    (by simpa only [uIcc_of_le hL.le] using hAs)
    (by simpa only [uIcc_of_le hL.le] using hBs)
    (by simpa only [uIcc_of_le hL.le] using ht)
    (by simpa only [uIcc_of_le hL.le] using hTv)
    (by simpa only [uIcc_of_le hL.le] using hTu)
    (by simpa only [uIcc_of_le hL.le] using hQd)
    (by simpa only [uIcc_of_le hL.le] using hAd)
    (by simpa only [uIcc_of_le hL.le] using hw)
    (by simpa only [uIcc_of_le hL.le] using hz)
    (by simpa only [uIcc_of_le hL.le, momentumVelocity, Q, u, R] using hlin)
  have hE (s : ℝ) (hs : s ∈ Icc 0 L) :
      coordinateEnergyDensity (Q (t s)) (deriv Q (t s)) (deriv (deriv Q) (t s))
        (v s, u s) (w s, z s) (w' s, z' s) =
      energyDensity (fun s => (coordinateCometric right δ (t s))⁻¹)
        (fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p)
        (fun s => -forceDerivative right δ p (t s) / 2) z' w w' s := by
    rw [metricInverse_first (hdet s hs), metricInverse_second (hdet s hs)]
    rw [energy_cometric_identity (hQP s hs) (hPs s hs) (hQs s hs)
      (coordinateCometric_deriv_transpose right δ (t s))]
    dsimp only [energyDensity, forceDerivative, Q, metricInverse]
    ring
  have hEi : (∫ s in (0 : ℝ)..L, coordinateEnergyDensity (Q (t s))
      (deriv Q (t s)) (deriv (deriv Q) (t s)) (v s, u s) (w s, z s) (w' s, z' s)) =
      ∫ s in (0 : ℝ)..L, energyDensity (fun s => (coordinateCometric right δ (t s))⁻¹)
        (fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p)
        (fun s => -forceDerivative right δ p (t s) / 2) z' w w' s := by
    apply intervalIntegral.integral_congr
    simpa only [uIcc_of_le hL.le, Set.EqOn] using hE
  have hm : L * m = p ⬝ᵥ (z L - z 0) := by
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := L)
      (by simpa only [uIcc_of_le hL.le] using hlin) intervalIntegrable_const
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hf
    rw [momentumVelocity_pairing (hdet L ⟨hL.le, le_rfl⟩),
      momentumVelocity_pairing (hdet 0 ⟨le_rfl, hL.le⟩), hwa, hwb, zero_mul, zero_add,
      zero_mul, zero_add, ← dotProduct_sub] at hf
    exact hf
  have hma : L * m ^ 2 = (p ⬝ᵥ (z L - z 0)) ^ 2 / L := by
    rw [← hm]
    field_simp [hL.ne']
  have hdet0 : (coordinateCometric right δ 0).det ≠ 0 := by
    simpa only [h0] using hdet 0 ⟨le_rfl, hL.le⟩
  change (∫ s in (0 : ℝ)..L, normalDensity (R (t s)) (Q (t s)) (deriv Q (t s))
    (deriv (deriv Q) (t s)) (v s, u s) (w s, z s) (w' s, z' s)) = _
  rw [hnorm, hEi, sub_zero, hma, h0, h1, hwa, hwb, hvL,
    metricInverse_endpoint_deriv hdet0, turning_boundary_term, turning_boundary_term]
  ring

end

open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem returning_normal_nonnegative {right : Bool} {δ C L m : ℝ} {p : TVec}
    {t v : ℝ → ℝ} (hC : 18 ≤ C)
    (hδ : SmallParameter (3 * C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q,
      sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18 * sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C ^ 2 * δ ^ 2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hL : 0 < L) (hstar : 1 / 4 < t (L / 2))
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1)
    {z z' : ℝ → TVec} {w w' : ℝ → ℝ}
    (hzc : ContinuousOn z' (Icc 0 L)) (hwc : ContinuousOn w' (Icc 0 L))
    (hz : ∀ s ∈ Icc 0 L, HasDerivAt z (z' s) s)
    (hw : ∀ s ∈ Icc 0 L, HasDerivAt w (w' s) s)
    (hwa : w 0 = 0) (hwb : w L = 0)
    (hlin : ∀ s ∈ Icc 0 L, HasDerivAt
      (fun r => metric (metricInverse right δ (t r)) (w r, z r)
        (momentumVelocity right δ p t v r)) m s) :
    0 ≤ (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v
      (fun r => (w r, z r)) (fun r => (w' r, z' r)) s) := by
  obtain ⟨hv0, _, hT, hmaps, hsym, _⟩ :=
    returning_dynamics hL hconc ht hv h0 h1 hrange henergy
  have hdet (s : ℝ) (hs : s ∈ Icc 0 L) :
      (coordinateCometric right δ (t s)).det ≠ 0 :=
    (coordinateCometric_posDef (fun q => (hbound (t s)
      ⟨(hmaps hs).1, (hmaps hs).2.trans hT.2.le⟩ q).1)).det_pos.ne'
  have hvL : v L = -v 0 := by simpa only [sub_zero] using (hsym 0 ⟨le_rfl, hL.le⟩).2
  rw [returning_normal_identity hL hdet ht hv h0 h1 hvL hzc hwc hz hw hwa hwb hlin]
  have hh := actual_returning_energy_bound hC hδ hbound hder hconc hdom hL hstar
    ht hv h0 h1 hrange henergy hzc hwc hz hw hwa hwb
  have hb := turning_boundary_reduction (mul_nonneg hδ.1.le (a_nonneg 0)) hv0.le (z 0) (z L)
  have he : e ⬝ᵥ (z L - z 0) = (z L - z 0) 0 := by
    simp [e, dotProduct, Fin.sum_univ_two]
  rw [a_zero] at hb
  rw [he] at hh
  dsimp only [aZero] at hh
  rw [a_zero]
  linarith

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck
open Set Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma contDiffAt_pairing {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : X → TMat} {u v : X → TVec} {x : X} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) (hu : ContDiffAt ℝ n u x) (hv : ContDiffAt ℝ n v x) :
    ContDiffAt ℝ n (fun s => pairing (A s) (u s) (v s)) x := by
  unfold pairing Matrix.mulVec dotProduct
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_pi.mp hu i).mul (ContDiffAt.sum fun j _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j).mul (contDiffAt_pi.mp hv j)))

lemma contDiffAt_metric {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Q : X → TMat} {V T : X → Vec} {x : X} {n : WithTop ℕ∞}
    (hQ : ContDiffAt ℝ n Q x) (hV : ContDiffAt ℝ n V x) (hT : ContDiffAt ℝ n T x) :
    ContDiffAt ℝ n (fun s => metric (Q s) (V s) (T s)) x :=
  (hV.fst.mul hT.fst).add (contDiffAt_pairing hQ hV.snd hT.snd)

lemma turningChange_smoothAt {L v₀ s : ℝ} {V T : ℝ → Vec} {Q : ℝ → TMat}
    (hQ : ContDiffAt ℝ ∞ Q s) (hV : ContDiffAt ℝ ∞ V s) (hT : ContDiffAt ℝ ∞ T s) :
    ContDiffAt ℝ ∞ (turningChange L v₀ V T Q) s :=
  ((contDiffAt_const.add ((contDiffAt_id.div_const L).mul contDiffAt_const))).sub
    (contDiffAt_metric hQ hV hT)

lemma turningField_smoothAt {L v₀ s : ℝ} {V T : ℝ → Vec} {Q : ℝ → TMat}
    (hQ : ContDiffAt ℝ ∞ Q s) (hV : ContDiffAt ℝ ∞ V s) (hT : ContDiffAt ℝ ∞ T s) :
    ContDiffAt ℝ ∞ (turningField L v₀ V T Q) s :=
  hV.add ((turningChange_smoothAt hQ hV hT).smul hT)

lemma turningField_tangential_derivative {L v₀ s : ℝ} (hL : 0 < L) (hs : s ∈ Icc 0 L)
    {V T : ℝ → Vec} {Q : ℝ → TMat}
    (hQ : ContDiffAt ℝ ∞ Q s) (hV : ContDiffAt ℝ ∞ V s) (hT : ContDiffAt ℝ ∞ T s)
    (hu : ∀ r ∈ Icc 0 L, metric (Q r) (T r) (T r) = 1) :
    HasDerivAt (fun r => metric (Q r) (turningField L v₀ V T Q r) (T r))
      (((metric (Q L) (V L) (T L) + (V L).1 / v₀) -
        (metric (Q 0) (V 0) (T 0) - (V 0).1 / v₀)) / L) s := by
  have hh := (contDiffAt_metric hQ (turningField_smoothAt (L := L) (v₀ := v₀) hQ hV hT) hT).differentiableAt (by simp)
  have he : ∀ r ∈ Icc 0 L, metric (Q r) (turningField L v₀ V T Q r) (T r) =
      turningAffine L v₀ V T Q r := fun r hr => turningField_tangential V T Q (hu r hr)
  have hw := (turningAffine_hasDerivAt L v₀ V T Q s).hasDerivWithinAt.congr he (he s hs)
  apply hh.hasDerivAt.congr_deriv
  exact ((hh.hasDerivAt.hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc hL s hs)).symm.trans
    (hw.derivWithin (uniqueDiffOn_Icc hL s hs))

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma momentumVelocity_smoothAt {right : Bool} {δ s : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (ht : ContDiffAt ℝ ∞ t s) (hv : ContDiffAt ℝ ∞ v s) :
    ContDiffAt ℝ ∞ (momentumVelocity right δ p t v) s := by
  apply hv.prodMk
  have hR := (coordinateCometric_smooth right δ).contDiffAt.comp s ht
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ ∞ (fun r => ∑ j : Fin 2, coordinateCometric right δ (t r) i j * p j) s
  exact ContDiffAt.sum (fun j _ => ((contDiffAt_pi.mp (contDiffAt_pi.mp hR i) j).mul contDiffAt_const))

theorem returning_arbitrary_field_nonnegative {right : Bool} {δ C L : ℝ} {p : TVec}
    {t v : ℝ → ℝ} (hC : 18 ≤ C)
    (hδ : SmallParameter (3 * C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q,
      sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18 * sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C ^ 2 * δ ^ 2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hL : 0 < L) (hstar : 1 / 4 < t (L / 2))
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (hta : ∀ s ∈ Icc 0 L, ContDiffAt ℝ ∞ t s)
    (hva : ∀ s ∈ Icc 0 L, ContDiffAt ℝ ∞ v s)
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1)
    {V : ℝ → Vec} (hV : ∀ s ∈ Icc 0 L, ContDiffAt ℝ ∞ V s) :
    0 ≤ (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v V (deriv V) s) := by
  obtain ⟨hv0, _, hT, hmaps, hsym, _⟩ :=
    returning_dynamics hL hconc ht hv h0 h1 hrange henergy
  have hdet (s : ℝ) (hs : s ∈ Icc 0 L) :
      (coordinateCometric right δ (t s)).det ≠ 0 :=
    (coordinateCometric_posDef (fun q => (hbound (t s)
      ⟨(hmaps hs).1, (hmaps hs).2.trans hT.2.le⟩ q).1)).det_pos.ne'
  let T := momentumVelocity right δ p t v
  let Q := fun s => metricInverse right δ (t s)
  let W := turningField L (v 0) V T Q
  have hTa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ T s :=
    momentumVelocity_smoothAt (hta s hs) (hva s hs)
  have hQa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ Q s :=
    (metricInverse_smoothAt (hdet s hs)).comp s (hta s hs)
  have hWa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ W s :=
    turningField_smoothAt (hQa s hs) (hV s hs) (hTa s hs)
  have hWd (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt W (deriv W s) s :=
    ((hWa s hs).differentiableAt (by simp)).hasDerivAt
  have hWdc : ContinuousOn (deriv W) (Icc 0 L) := fun s hs =>
    ((hWa s hs).derivWithin (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hu (s : ℝ) (hs : s ∈ Icc 0 L) : metric (Q s) (T s) (T s) = 1 :=
    momentumVelocity_unit (hdet s hs) (henergy s hs)
  have hvL : v L = -v 0 := by simpa only [sub_zero] using (hsym 0 ⟨le_rfl, hL.le⟩).2
  have hW0 : (W 0).1 = 0 := turningField_zero hv0.ne' V T Q rfl
  have hWL : (W L).1 = 0 := turningField_end hL.ne' hv0.ne' V T Q hvL
  have hb := returning_normal_nonnegative hC hδ hbound hder hconc hdom hL hstar
    ht hv h0 h1 hrange henergy hWdc.snd hWdc.fst
    (fun s hs => (hWd s hs).snd) (fun s hs => (hWd s hs).fst) hW0 hWL
    (fun s hs => turningField_tangential_derivative hL hs (hQa s hs) (hV s hs) (hTa s hs) hu)
  have he (s : ℝ) (hs : s ∈ Icc 0 L) :
      returnNormalDensity right δ p t v W (deriv W) s =
      returnNormalDensity right δ p t v V (deriv V) s := by
    apply normalDensity_deriv_gauge
      (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet s hs)))
      (metricInverse_transpose right δ (t s)) (coordinateCometric_transpose right δ (t s))
      (metricInverse_deriv_transpose right δ (t s)) (metricInverse_second_transpose right δ (t s))
      (hu s hs) (((hV s hs).differentiableAt (by simp)).hasDerivAt)
      (momentumVelocity_hasDerivAt (hdet s hs) (ht s hs) (hv s hs))
      (((turningChange_smoothAt (L := L) (v₀ := v 0) (hQa s hs) (hV s hs) (hTa s hs)).differentiableAt (by simp)).hasDerivAt)
  have hei : (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v W (deriv W) s) =
      (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v V (deriv V) s) := by
    apply intervalIntegral.integral_congr
    simpa only [uIcc_of_le hL.le, EqOn] using he
  rw [← hei]
  exact hb

end ThreeManifold.ReturningPassage

end

end OAI
