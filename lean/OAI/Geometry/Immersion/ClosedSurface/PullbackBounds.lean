import OAI.Geometry.Immersion.ClosedSurface.CrossModes
import OAI.Geometry.Immersion.ClosedSurface.ComplexPullback

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (complexify)
open ClosedSurfaceR4.QuadraticMean (weighted_real_complex)

lemma weighted_base_fst {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → Base} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p).1) := by
  exact (hb.linear hU hs hf (ContinuousLinearMap.fst ℝ ℝ ℝ)).mono_const
    (mul_le_of_le_one_left hC (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ))

lemma weighted_base_snd {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → Base} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p).2) := by
  exact (hb.linear hU hs hf (ContinuousLinearMap.snd ℝ ℝ ℝ)).mono_const
    (mul_le_of_le_one_left hC (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ))

lemma weighted_complexEvaluate {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → ComplexTensor} {v w : Base → Base} {s C D B : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hA : ContDiffOn ℝ ∞ A U) (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U)
    (hbA : WeightedBound U s m C A) (hbv : WeightedBound U s m D v)
    (hbw : WeightedBound U s m B w) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * B))
      (fun p => complexEvaluate (A p) (v p) (w p)) := by
  have hvc := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.fst
  have hvd := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.snd
  have hwc := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.fst
  have hwd := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.snd
  have hvcB := weighted_real_complex hU hs hD hv.fst (weighted_base_fst hU hs hD hv hbv)
  have hvdB := weighted_real_complex hU hs hD hv.snd (weighted_base_snd hU hs hD hv hbv)
  have hwcB := weighted_real_complex hU hs hB hw.fst (weighted_base_fst hU hs hB hw hbw)
  have hwdB := weighted_real_complex hU hs hB hw.snd (weighted_base_snd hU hs hB hw hbw)
  have h0s := ((contDiffOn_pi.mp hA 0).mul hvc).mul hwc
  have h1s := (contDiffOn_pi.mp hA 1).mul ((hvc.mul hwd).add (hvd.mul hwc))
  have h2s := ((contDiffOn_pi.mp hA 2).mul hvd).mul hwd
  have h0 := ((hbA.component hU hs hC hA 0).mul hU hs hC hD
    (contDiffOn_pi.mp hA 0) hvc hvcB).mul hU hs (by positivity) hB
    ((contDiffOn_pi.mp hA 0).mul hvc) hwc hwcB
  have h2 := ((hbA.component hU hs hC hA 2).mul hU hs hC hD
    (contDiffOn_pi.mp hA 2) hvd hvdB).mul hU hs (by positivity) hB
    ((contDiffOn_pi.mp hA 2).mul hvd) hwd hwdB
  have h11 := hvcB.mul hU hs hD hB hvc hwd hwdB
  have h12 := hvdB.mul hU hs hD hB hvd hwc hwcB
  have h1 := (hbA.component hU hs hC hA 1).mul hU hs hC (by positivity)
    (contDiffOn_pi.mp hA 1) ((hvc.mul hwd).add (hvd.mul hwc))
    (h11.add hU hs (hvc.mul hwd) (hvd.mul hwc) h12)
  have hh := (h0.add hU hs h0s h1s h1).add hU hs (h0s.add h1s) h2s h2
  convert hh using 1 <;> first | rfl | ring

lemma weighted_complexPullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → ComplexTensor} {e : Base → Base} {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U)
    (hbA : WeightedBound U s m C A)
    (hbe : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m D (coordDeriv v e)) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * D))
      (fun p => complexPullbackField e p (A p)) := by
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    (contDiffOn_pi.mp (contDiffOn_complexPullbackField_apply hU hA he))
  intro i
  exact weighted_complexEvaluate hU.uniqueDiffOn hs.le hC hD hD hA
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (firstDirection i))
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (secondDirection i)) hbA
    (hbe _ (firstDirection_norm i)) (hbe _ (secondDirection_norm i))

lemma contDiffOn_complexify {n : ℕ} {U : Set Base} {A : Base → Fin n → ℝ}
    (hA : ContDiffOn ℝ ∞ A U) : ContDiffOn ℝ ∞ (fun p => complexify (A p)) U := by
  apply contDiffOn_pi.mpr
  intro i
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hA i)

lemma weighted_complexify {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → Fin n → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C)
    (hA : ContDiffOn ℝ ∞ A U) (hb : WeightedBound U s m C A) :
    WeightedBound U s m C (fun p => complexify (A p)) := by
  apply WeightedBound.pi hU hs hC (contDiffOn_pi.mp (contDiffOn_complexify hA))
  intro i
  exact weighted_real_complex hU hs.le hC (contDiffOn_pi.mp hA i)
    (hb.component hU hs.le hC hA i)

lemma realPart_complexify {n : ℕ} (A : Fin n → ℝ) :
    QuadraticMean.realPart (complexify A) = A := by ext i; rfl

lemma contDiffOn_pullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → Tensor} {e : Base → Base}
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U) :
    ContDiffOn ℝ ∞ (fun p => pullbackField e p (A p)) U := by
  have hc := (QuadraticMean.realPartCLM 3).contDiff.comp_contDiffOn
    (contDiffOn_complexPullbackField_apply hU (contDiffOn_complexify hA) he)
  simpa only [Function.comp_def, QuadraticMean.realPartCLM_apply,
    complexPullbackField, realPart_complexPullback, realPart_complexify, pullbackField] using hc

lemma weighted_pullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → Tensor} {e : Base → Base} {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U)
    (hbA : WeightedBound U s m C A)
    (hbe : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m D (coordDeriv v e)) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * D))
      (fun p => pullbackField e p (A p)) := by
  have hb := weighted_complexPullbackField_apply hU hs hC hD
    (contDiffOn_complexify hA) he (weighted_complexify hU.uniqueDiffOn hs hC hA hbA) hbe
  have hr := RealModes.weighted_realPart hU.uniqueDiffOn hs.le (by positivity)
    (contDiffOn_complexPullbackField_apply hU (contDiffOn_complexify hA) he) hb
  simpa only [complexPullbackField, realPart_complexPullback, realPart_complexify, pullbackField] using hr

end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base coordDeriv)
open ClosedSurfaceR4.WeightedEstimates



lemma weighted_coordinateTarget {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    {A : Base → ComplexTensor} {e : Base → Base} {s C J D : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e V) (heU : Set.MapsTo e V U)
    (hec : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (heb : ∀ v, ‖v‖ ≤ 1 → WeightedBound V s m D (coordDeriv v e))
    (hb : WeightedBound U s m C A) :
    WeightedBound V s m
      (4 * (2 ^ m * (2 ^ m * ((m.factorial : ℝ) * C * J ^ m) * D) * D))
      (coordinateTarget e A) := by
  exact weighted_complexPullbackField_apply hV hs (by positivity) hD
    (hA.comp he heU) he
    (hb.comp_coordinates hV.uniqueDiffOn hU.uniqueDiffOn hs hs1 hJ hC he hA heU hec) heb

end ClosedSurfaceR4.PhaseMean

end

end OAI
