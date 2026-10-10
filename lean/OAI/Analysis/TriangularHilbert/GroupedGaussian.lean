import OAI.Analysis.TriangularHilbert.WeightedCompare

namespace OAI

universe uι uν

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} {ν : Type uν} [Fintype ι] [DecidableEq ι] [DecidableEq ν]

def groupWeight (h : ℝ) (u : ι → ℝ) (loc : ι → ν) (p σ : ν → ℝ) (i : ι) : ℝ :=
  weight h (u i) (p (loc i)) (σ (loc i))

def groupFirst (h : ℝ) (u : ι → ℝ) (loc : ι → ν) (p σ : ν → ℝ) (v : ν) (i : ι) : ℝ :=
  if loc i = v then score (u i) (p v) (σ v) * weight h (u i) (p v) (σ v) else 0

def groupSecond (h : ℝ) (u : ι → ℝ) (loc : ι → ν) (p σ : ν → ℝ) (v : ν) (i : ι) : ℝ :=
  if loc i = v then (score (u i) (p v) (σ v)^2 - (σ v)⁻¹) *
    weight h (u i) (p v) (σ v) else 0

omit [Fintype ι] [DecidableEq ι] [DecidableEq ν] in
lemma groupWeight_pos {h : ℝ} (hh : 0 < h) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (i : ι) :
    0 < groupWeight h u loc p σ i := weight_pos hh (hσ (loc i)) _ _

omit [Fintype ι] [DecidableEq ι] in
lemma groupWeight_hasDerivAt_center (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) (i : ι) :
    HasDerivAt (fun q => groupWeight h u loc (Function.update p v q) σ i)
      (groupFirst h u loc p σ v i) (p v) := by
  by_cases hi : loc i = v
  · simpa [groupWeight, groupFirst, hi] using
      weight_hasDerivAt_center h (u i) (p v) (σ v) (hσ v)
  · simpa [groupWeight, groupFirst, hi] using
      hasDerivAt_const (p v) (weight h (u i) (p (loc i)) (σ (loc i)))

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_hasDerivAt_center (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) (i : ι) :
    HasDerivAt (fun q => groupFirst h u loc (Function.update p v q) σ v i)
      (groupSecond h u loc p σ v i) (p v) := by
  by_cases hi : loc i = v
  · simpa [groupFirst, groupSecond, hi] using
      weight_score_hasDerivAt_center h (u i) (p v) (σ v) (hσ v)
  · simpa [groupFirst, groupSecond, hi] using hasDerivAt_const (p v) (0 : ℝ)

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_hasDerivAt_other (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p σ : ν → ℝ) {v w : ν} (hvw : v ≠ w) (i : ι) :
    HasDerivAt (fun q => groupFirst h u loc (Function.update p w q) σ v i) 0 (p w) := by
  simpa [groupFirst, Function.update_of_ne hvw] using
    hasDerivAt_const (p w) (groupFirst h u loc p σ v i)

omit [Fintype ι] [DecidableEq ι] in
lemma groupWeight_hasDerivAt_variance (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) (i : ι) :
    HasDerivAt (fun q => groupWeight h u loc p (Function.update σ v q) i)
      ((1/2 : ℝ) * groupSecond h u loc p σ v i) (σ v) := by
  by_cases hi : loc i = v
  · simpa [groupWeight, groupSecond, hi, mul_assoc] using
      weight_hasDerivAt_variance h (u i) (p v) (σ v) (hσ v)
  · simpa [groupWeight, groupSecond, hi] using
      hasDerivAt_const (σ v) (weight h (u i) (p (loc i)) (σ (loc i)))

lemma groupEnergy_hasDerivAt_center (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) :
    HasDerivAt (fun q => energy (weightedGram B (groupWeight h u loc (Function.update p v q) σ)))
      (energyGradient (weightedGram B (groupWeight h u loc p σ))
        (weightedGram B (groupFirst h u loc p σ v))) (p v) := by
  have hd := energy_weightedGram_hasDerivAt B
    (Eventually.of_forall fun q i => groupWeight_pos hh u loc (Function.update p v q) hσ i)
    (groupWeight_hasDerivAt_center h u loc p hσ v)
  simpa only [Function.update_eq_self] using hd

lemma groupEnergyFirst_hasDerivAt_center (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) :
    HasDerivAt (fun q => energyGradient
        (weightedGram B (groupWeight h u loc (Function.update p v q) σ))
        (weightedGram B (groupFirst h u loc (Function.update p v q) σ v)))
      (hessianCost (weightedGram B (groupWeight h u loc p σ))
          (weightedGram B (groupFirst h u loc p σ v)) +
        energyGradient (weightedGram B (groupWeight h u loc p σ))
          (weightedGram B (groupSecond h u loc p σ v))) (p v) := by
  have hd := energyGradient_weightedGram_hasDerivAt B
    (Eventually.of_forall fun q i => groupWeight_pos hh u loc (Function.update p v q) hσ i)
    (groupWeight_hasDerivAt_center h u loc p hσ v)
    (groupFirst_hasDerivAt_center h u loc p hσ v)
  simp only [Function.update_eq_self] at hd
  rw [hessianPair_weightedGram_self B (groupWeight_pos hh u loc p hσ)] at hd
  exact hd

lemma groupEnergyFirst_hasDerivAt_other (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v)
    {v w : ν} (hvw : v ≠ w) :
    HasDerivAt (fun q => energyGradient
        (weightedGram B (groupWeight h u loc (Function.update p w q) σ))
        (weightedGram B (groupFirst h u loc (Function.update p w q) σ v)))
      (hessianPair (weightedGram B (groupWeight h u loc p σ))
        (weightedGram B (groupFirst h u loc p σ v))
        (weightedGram B (groupFirst h u loc p σ w))) (p w) := by
  have hd := energyGradient_weightedGram_hasDerivAt B
    (Eventually.of_forall fun q i => groupWeight_pos hh u loc (Function.update p w q) hσ i)
    (groupWeight_hasDerivAt_center h u loc p hσ w)
    (groupFirst_hasDerivAt_other h u loc p σ hvw)
  simpa only [Function.update_eq_self, weightedGram, Complex.ofReal_zero,
    Matrix.diagonal_zero, mul_zero, zero_mul, map_zero, add_zero] using hd

lemma groupEnergy_hasDerivAt_variance (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) :
    HasDerivAt (fun q => energy (weightedGram B (groupWeight h u loc p (Function.update σ v q))))
      ((1/2 : ℝ) * energyGradient (weightedGram B (groupWeight h u loc p σ))
        (weightedGram B (groupSecond h u loc p σ v))) (σ v) := by
  have hw : ∀ᶠ q in 𝓝 (σ v), ∀ i, 0 < groupWeight h u loc p (Function.update σ v q) i := by
    filter_upwards [eventually_gt_nhds (hσ v)] with q hq
    apply groupWeight_pos hh u loc p
    intro w
    by_cases hw : w = v
    · simpa [hw] using hq
    · simpa [hw] using hσ w
  have hd := energy_weightedGram_hasDerivAt B hw (groupWeight_hasDerivAt_variance h u loc p hσ v)
  simpa only [Function.update_eq_self, weightedGram_smul, map_smul, smul_eq_mul] using hd

end
end TriangularHilbert.Heat
end

end OAI
