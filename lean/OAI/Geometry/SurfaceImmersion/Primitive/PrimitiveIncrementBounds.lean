import OAI.Geometry.SurfaceImmersion.Geometry.LocalIsometryBounds
import OAI.Geometry.SurfaceImmersion.Geometry.LowJetSegment

namespace OAI

/-! Preservation of the primitive iteration's derivative profiles by the
actual supported increment, including its positional two-jet. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open WeightedEstimates JetPolynomial

lemma weighted_increment_prefix {U : Set JetPolynomial.Base}
    {W : JetPolynomial.Base → JetPolynomial.Space} {τ δ S : ℝ} {m j : ℕ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (_hδ : 0 ≤ δ) (hδτ : δ ≤ τ) (hS : 0 ≤ S)
    (hb : WeightedBound U τ m (S*δ*τ) W) (hj : j ≤ m) :
    WeightedBound U 1 j (S/τ^(j-2)) W := by
  intro k hk x hx
  simp only [one_pow,one_mul]
  apply (hb.deriv_le hτ (hk.trans hj) hx).trans
  apply (div_le_div_iff₀ (pow_pos hτ k) (pow_pos hτ (j-2))).2
  calc
    (S*δ*τ)*τ^(j-2) ≤ S*(τ^2*τ^(j-2)) := by
      have hp := mul_le_mul_of_nonneg_right hδτ hτ.le
      have htp : δ*τ ≤ τ^2 := by nlinarith only [hp]
      nlinarith only [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right htp (pow_nonneg hτ.le (j-2))) hS]
    _ = S*τ^(2+(j-2)) := by rw [pow_add]
    _ ≤ S*τ^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hτ.le hτ1 (by omega : k ≤ 2+(j-2))) hS

lemma primitive_increment_prefix {U : Set JetPolynomial.Base} (hU : IsOpen U)
    {G W : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (hW : ContDiff ℝ ∞ W)
    {s τ δ P S : ℝ} {m : ℕ} (_hs : 0 < s) (hτ : 0 < τ) (hτs : τ ≤ s)
    (hs1 : s ≤ 1) (hδ : 0 ≤ δ) (hδτ : δ ≤ τ) (hP : 0 ≤ P) (hS : 0 ≤ S)
    (hGb : ∀ j ≤ m, WeightedBound U 1 j (P/s^(j-2)) G)
    (hWb : WeightedBound U τ m (S*δ*τ) W) :
    ∀ j ≤ m, WeightedBound U 1 j ((P+S)/τ^(j-2)) (G+W) := by
  intro j hj
  have hG' := (hGb j hj).mono_const (div_le_div_of_nonneg_left hP
    (pow_pos hτ _) (pow_le_pow_left₀ hτ.le hτs _))
  have hW' := weighted_increment_prefix hτ (hτs.trans hs1) hδ hδτ hS hWb hj
  have hb := hG'.add hU.uniqueDiffOn zero_le_one hG.contDiffOn hW.contDiffOn hW'
  change WeightedBound U 1 j ((P+S)/τ^(j-2)) (fun x => G x+W x)
  simpa only [add_div] using hb

lemma primitive_increment_lowJet {U : Set JetPolynomial.Base} (hU : IsOpen U)
    {G W : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (hW : ContDiff ℝ ∞ W)
    {s τ δ B S : ℝ} {m : ℕ} (hτ : 0 < τ) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hδ : 0 ≤ δ) (hδτ : δ ≤ τ) (hS : 0 ≤ S)
    (hGb : WeightedBound U s m B (lowJet G))
    (hWb : WeightedBound U τ (m+2) (S*δ*τ) W) :
    WeightedBound U τ m (B+S) (lowJet (G+W)) := by
  have hg := hGb.shrink_scale hτ.le hτs
  have hh := lowJet_segment_bound hU hG hW hτ (hτs.trans hs1)
    (mul_nonneg (mul_nonneg hS hδ) hτ.le) hg hWb (t := 1) (by constructor <;> norm_num)
  have hc : (S*δ*τ)/τ^2 ≤ S := by
    apply (div_le_iff₀ (sq_pos_of_pos hτ)).2
    nlinarith only [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hδτ hτ.le) hS]
  apply (hh.mono_const (add_le_add_right hc B)).congr
  intro x _
  change lowJet (fun p => G p+W p) x = lowJet (fun p => G p+1 • W p) x
  simp only [one_smul]

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
