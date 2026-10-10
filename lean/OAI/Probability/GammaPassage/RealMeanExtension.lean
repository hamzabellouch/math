import OAI.Probability.GammaPassage.RationalMean
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Linarith

namespace OAI

namespace GammaFPP
open Topology
open scoped NNReal

/-- The rational embedding uses the standard product (maximum) metric. -/
def rationalPairCast (q : ℚ × ℚ) : ℝ × ℝ := ((q.1 : ℝ), (q.2 : ℝ))

lemma rationalPairCast_uniformEmbedding : IsUniformEmbedding rationalPairCast :=
  Rat.isUniformEmbedding_coe_real.prod Rat.isUniformEmbedding_coe_real

lemma rationalPairCast_dense : DenseRange rationalPairCast :=
  Rat.isDenseEmbedding_coe_real.dense.prodMap Rat.isDenseEmbedding_coe_real.dense

@[simp] lemma rationalPairCast_add (q r : ℚ × ℚ) :
    rationalPairCast (q+r) = rationalPairCast q + rationalPairCast r := by
  ext <;> simp [rationalPairCast]

@[simp] lemma rationalPairCast_neg (q : ℚ × ℚ) :
    rationalPairCast (-q) = -rationalPairCast q := by
  ext <;> simp [rationalPairCast]

@[simp] lemma rationalPairCast_smul (a : ℚ) (q : ℚ × ℚ) :
    rationalPairCast (a • q) = (a : ℝ) • rationalPairCast q := by
  ext <;> simp [rationalPairCast, smul_eq_mul]

/-- L1 is at most twice the standard product maximum metric. -/
lemma rational_l1_lipschitz (f : ℚ × ℚ → ℝ) (C : ℝ≥0)
    (h : ∀ q r, |f q-f r| ≤ (C : ℝ) *
      (|(q.1 : ℝ)-(r.1 : ℝ)| + |(q.2 : ℝ)-(r.2 : ℝ)|)) :
    LipschitzWith (2*C) f := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [Real.dist_eq, Prod.dist_eq, Rat.dist_eq, Rat.dist_eq]
  have h₁ := le_max_left |(q.1 : ℝ)-(r.1 : ℝ)| |(q.2 : ℝ)-(r.2 : ℝ)|
  have h₂ := le_max_right |(q.1 : ℝ)-(r.1 : ℝ)| |(q.2 : ℝ)-(r.2 : ℝ)|
  have hh := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) C.coe_nonneg
  have hb := h q r
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  nlinarith

noncomputable def realMeanExtension (f : ℚ × ℚ → ℝ) : ℝ × ℝ → ℝ :=
  (rationalPairCast_uniformEmbedding.isUniformInducing.isDenseInducing
    rationalPairCast_dense).extend f

lemma realMeanExtension_uniformContinuous {f : ℚ × ℚ → ℝ}
    (hf : UniformContinuous f) : UniformContinuous (realMeanExtension f) :=
  uniformContinuous_uniformly_extend
    rationalPairCast_uniformEmbedding.isUniformInducing rationalPairCast_dense hf

lemma realMeanExtension_on_rat {f : ℚ × ℚ → ℝ}
    (hf : UniformContinuous f) (q : ℚ × ℚ) :
    realMeanExtension f (rationalPairCast q) = f q :=
  (rationalPairCast_uniformEmbedding.isUniformInducing.isDenseInducing
    rationalPairCast_dense).extend_eq hf.continuous q

lemma realMeanExtension_add_le {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (hadd : ∀ q r, f (q+r) ≤ f q + f r) (x y : ℝ × ℝ) :
    realMeanExtension f (x+y) ≤ realMeanExtension f x + realMeanExtension f y := by
  have hc := (realMeanExtension_uniformContinuous hf).continuous
  apply isClosed_property2 rationalPairCast_dense
    (p := fun x y => realMeanExtension f (x+y) ≤
      realMeanExtension f x + realMeanExtension f y) ?_ ?_ x y
  · exact isClosed_le (hc.comp (continuous_fst.add continuous_snd))
      ((hc.comp continuous_fst).add (hc.comp continuous_snd))
  · intro q r
    rw [← rationalPairCast_add, realMeanExtension_on_rat hf,
      realMeanExtension_on_rat hf, realMeanExtension_on_rat hf]
    exact hadd q r

lemma realMeanExtension_neg {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (hneg : ∀ q, f (-q) = f q) (x : ℝ × ℝ) :
    realMeanExtension f (-x) = realMeanExtension f x := by
  have hc := (realMeanExtension_uniformContinuous hf).continuous
  apply isClosed_property rationalPairCast_dense
    (p := fun x => realMeanExtension f (-x) = realMeanExtension f x) ?_ ?_ x
  · exact isClosed_eq (hc.comp continuous_neg) hc
  · intro q
    rw [← rationalPairCast_neg, realMeanExtension_on_rat hf, realMeanExtension_on_rat hf]
    exact hneg q

/-- Density in the scalar AND vector proves full real homogeneity. -/
lemma realMeanExtension_smul {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (hsmul : ∀ (a : ℚ) q, f (a • q) = |(a : ℝ)| * f q)
    (a : ℝ) (x : ℝ × ℝ) :
    realMeanExtension f (a • x) = |a| * realMeanExtension f x := by
  have hc := (realMeanExtension_uniformContinuous hf).continuous
  have hd := Rat.isDenseEmbedding_coe_real.dense.prodMap rationalPairCast_dense
  apply isClosed_property hd
    (p := fun z : ℝ × (ℝ × ℝ) => realMeanExtension f (z.1 • z.2) =
      |z.1| * realMeanExtension f z.2) ?_ ?_ (a,x)
  · exact isClosed_eq (hc.comp (continuous_fst.smul continuous_snd))
      (continuous_fst.abs.mul (hc.comp continuous_snd))
  · intro z
    change realMeanExtension f ((z.1 : ℝ) • rationalPairCast z.2) =
      |(z.1 : ℝ)| * realMeanExtension f (rationalPairCast z.2)
    rw [← rationalPairCast_smul, realMeanExtension_on_rat hf, realMeanExtension_on_rat hf]
    exact hsmul z.1 z.2

/-- Construct, rather than assume, a real seminorm from rational data. -/
noncomputable def realMeanSeminorm (f : ℚ × ℚ → ℝ) (C : ℝ≥0)
    (hlip : ∀ q r, |f q-f r| ≤ (C : ℝ) *
      (|(q.1 : ℝ)-(r.1 : ℝ)| + |(q.2 : ℝ)-(r.2 : ℝ)|))
    (hzero : f 0 = 0) (hadd : ∀ q r, f (q+r) ≤ f q + f r)
    (hneg : ∀ q, f (-q) = f q)
    (hsmul : ∀ (a : ℚ) q, f (a • q) = |(a : ℝ)| * f q) :
    Seminorm ℝ (ℝ × ℝ) where
  toFun := realMeanExtension f
  map_zero' := by
    change realMeanExtension f (0, 0) = 0
    have h := realMeanExtension_on_rat (rational_l1_lipschitz f C hlip).uniformContinuous 0
    simpa [rationalPairCast, hzero] using h
  add_le' := realMeanExtension_add_le (rational_l1_lipschitz f C hlip).uniformContinuous hadd
  neg' := realMeanExtension_neg (rational_l1_lipschitz f C hlip).uniformContinuous hneg
  smul' := by
    intro a x
    simpa only [Real.norm_eq_abs] using
      realMeanExtension_smul (rational_l1_lipschitz f C hlip).uniformContinuous hsmul a x

/-- Agreement with the original lattice mean once its rational L1 bound is supplied.
No seminorm or continuity premise on that lattice function is needed. -/
theorem realMeanExtension_integerPair (m : PlanarFPP.Vertex → ℝ)
    (hm : ∀ (k : ℕ) (x : PlanarFPP.Vertex), m (k • x) = (k : ℝ) * m x)
    (C : ℝ≥0)
    (hlip : ∀ q r, |rationalMean m q-rationalMean m r| ≤ (C : ℝ) *
      (|(q.1 : ℝ)-(r.1 : ℝ)| + |(q.2 : ℝ)-(r.2 : ℝ)|))
    (x : PlanarFPP.Vertex) :
    realMeanExtension (rationalMean m) ((x.1 : ℝ), (x.2 : ℝ)) = m x := by
  have he := realMeanExtension_on_rat
    (rational_l1_lipschitz (rationalMean m) C hlip).uniformContinuous
    ((x.1 : ℚ), (x.2 : ℚ))
  simpa only [rationalPairCast, Rat.cast_intCast, rationalMean_integerPair m hm] using he

end GammaFPP

end OAI
