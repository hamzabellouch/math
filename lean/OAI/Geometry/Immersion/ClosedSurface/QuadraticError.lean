import OAI.Geometry.Immersion.ClosedSurface.QuadraticMean

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.WeightedEstimates

lemma contDiffOn_conjugate {n : ℕ} {U : Set Base} {Z : Base → CVec n}
    (hZ : ContDiffOn ℝ ∞ Z U) : ContDiffOn ℝ ∞ (fun p => conjugate (Z p)) U := by
  apply contDiffOn_pi.mpr
  intro i
  exact Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hZ i)

lemma weighted_conjugate {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {Z : Base → CVec n} (hs : 0 < s) (hC : 0 ≤ C)
    (hZ : ContDiffOn ℝ ∞ Z U) (hbZ : WeightedBound U s m C Z) :
    WeightedBound U s m C (fun p => conjugate (Z p)) := by
  apply WeightedBound.pi hU hs hC
  · intro i
    exact Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hZ i)
  · intro i
    have hh := (hbZ.component hU hs.le hC hZ i).linear hU hs.le
      (contDiffOn_pi.mp hZ i) Complex.conjCLE.toContinuousLinearMap
    apply hh.mono_const
    apply mul_le_of_le_one_left hC
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp



def halfReCLM : ℂ →L[ℝ] ℝ := (2 : ℝ)⁻¹ • Complex.reCLM

lemma halfReCLM_apply (z : ℂ) : halfReCLM z = z.re / 2 := by
  simp [halfReCLM, div_eq_mul_inv, mul_comm]

lemma halfReCLM_norm_le : ‖halfReCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [halfReCLM_apply]
  simp only [norm_div, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), one_mul]
  have hr := Complex.abs_re_le_norm z
  linarith [norm_nonneg z]

lemma contDiffOn_zeroPair {n : ℕ} {U : Set Base} {A B : Base → CVec n}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun p => zeroPair (A p) (B p)) U := by
  have hc := contDiffOn_conjugate hB
  have hd : ContDiffOn ℝ ∞ (fun p => A p ⬝ᵥ conjugate (B p)) U :=
    ContDiffOn.sum (fun i _ => (contDiffOn_pi.mp hA i).mul (contDiffOn_pi.mp hc i))
  simpa only [Function.comp_def, halfReCLM_apply, zeroPair] using
    halfReCLM.contDiff.comp_contDiffOn hd

lemma weighted_zeroPair {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {A B : Base → CVec n} (hs : 0 < s)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hbA : WeightedBound U s m C A) (hbB : WeightedBound U s m D B) :
    WeightedBound U s m ((n : ℝ) * (2 ^ m * C * D))
      (fun p => zeroPair (A p) (B p)) := by
  have hc := contDiffOn_conjugate hB
  have hbc := weighted_conjugate hU hs hD hB hbB
  have hd := hbA.dot hU hs.le hC hD hA hc hbc
  have hds : ContDiffOn ℝ ∞ (fun p => A p ⬝ᵥ conjugate (B p)) U :=
    ContDiffOn.sum (fun i _ => (contDiffOn_pi.mp hA i).mul (contDiffOn_pi.mp hc i))
  have hh := hd.linear hU hs.le hds halfReCLM
  simp only [Fintype.card_fin] at hh
  have hn : 0 ≤ (n : ℝ) * (2 ^ m * C * D) := by positivity
  have hh' := hh.mono_const (mul_le_of_le_one_left hn halfReCLM_norm_le)
  simpa only [Function.comp_def, halfReCLM_apply, zeroPair, Fintype.card_fin] using hh'

lemma zeroPair_sub_left {n : ℕ} (A B C : CVec n) :
    zeroPair (A - B) C = zeroPair A C - zeroPair B C := by
  simp [zeroPair, sub_dotProduct, sub_div]

lemma zeroPair_sub_right {n : ℕ} (A B C : CVec n) :
    zeroPair A (B - C) = zeroPair A B - zeroPair A C := by
  have hc : conjugate (B - C) = conjugate B - conjugate C := by ext i; simp [conjugate]
  simp [zeroPair, hc, dotProduct_sub, sub_div]

lemma zeroPair_error_identity {n : ℕ} (A B Z W : CVec n) :
    zeroPair Z W - zeroPair A B = zeroPair (Z - A) W + zeroPair A (W - B) := by
  rw [zeroPair_sub_left, zeroPair_sub_right]
  ring




theorem weighted_zeroPair_error {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C D E F : ℝ} {m : ℕ} {A B Z W : Base → CVec n} (hs : 0 < s)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U)
    (hbA : WeightedBound U s m C A) (hbW : WeightedBound U s m D W)
    (heZ : WeightedBound U s m E (fun p => Z p - A p))
    (heW : WeightedBound U s m F (fun p => W p - B p)) :
    WeightedBound U s m ((n : ℝ) * 2 ^ m * (E * D + C * F))
      (fun p => zeroPair (Z p) (W p) - zeroPair (A p) (B p)) := by
  have h1 := weighted_zeroPair hU hs hE hD (hZ.sub hA) hW heZ hbW
  have h2 := weighted_zeroPair hU hs hC hF hA (hW.sub hB) hbA heW
  have hh := h1.add hU hs.le (contDiffOn_zeroPair (hZ.sub hA) hW)
    (contDiffOn_zeroPair hA (hW.sub hB)) h2
  have he : (n : ℝ) * (2 ^ m * E * D) + (n : ℝ) * (2 ^ m * C * F) =
      (n : ℝ) * 2 ^ m * (E * D + C * F) := by ring
  rw [he] at hh
  exact hh.congr (fun p _ => zeroPair_error_identity (A p) (B p) (Z p) (W p))

end ClosedSurfaceR4.QuadraticMean

end

end OAI
