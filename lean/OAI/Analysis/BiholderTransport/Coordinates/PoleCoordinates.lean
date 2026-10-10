import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.HopfGradient

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma hopfLax_lipschitz {u : M → ℝ} (hu : Continuous u) {D : ℝ≥0}
    (hD : ∀ x y : M, dist x y≤D) {t : ℝ} (ht : 0<t) :
    LipschitzWith (D/Real.toNNReal t) (hopfLax t u) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [hopfLax_eq_neg_transform hu ht,hopfLax_eq_neg_transform hu ht,
    Real.dist_eq,←sub_div,abs_div,neg_sub_neg,abs_sub_comm,abs_of_pos ht]
  have H := (cTransform_lipschitz (v := fun x => t*u x) (continuous_const.mul hu) hD).dist_le_mul x y
  rw [Real.dist_eq] at H
  calc
    _ ≤ (D:ℝ)*dist x y/t := div_le_div_of_nonneg_right H ht.le
    _ = _ := by rw [NNReal.coe_div,Real.coe_toNNReal _ ht.le]; ring

def coordinateBackward (a : M) (q : ℝ × Model n × (Model n →L[ℝ] ℝ)) : M :=
  movingNormal a (q.2.1,-q.1 • (riemannianCoordinateMetric a q.2.1).inverse q.2.2)

omit [Nonempty M] in
lemma coordinateBackward_contMDiffAt {a : M} {q : ℝ × Model n × (Model n →L[ℝ] ℝ)}
    (hq : q.2.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,ℝ × Model n × (Model n →L[ℝ] ℝ)) 𝓘(ℝ,Model n) ∞
      (coordinateBackward a) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  have hi := (riemannianCoordinateMetric_isInvertible hq).contDiffAt_map_inverse.comp q.2.1 hg
  have hz : ContDiffAt ℝ ∞ (fun q : ℝ × Model n × (Model n →L[ℝ] ℝ) => q.2.1) q :=
    contDiffAt_fst.comp q contDiffAt_snd
  have hl : ContDiffAt ℝ ∞ (fun q : ℝ × Model n × (Model n →L[ℝ] ℝ) => q.2.2) q :=
    contDiffAt_snd.comp q contDiffAt_snd
  have hv := (contDiffAt_fst.neg.smul ((hi.comp q hz).clm_apply hl))
  exact (movingNormal_contMDiffAt hq).comp q (hz.prodMk hv).contMDiffAt

omit [Nonempty M] in
lemma coordinateBackward_of_derivative {a : M} (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z.1∈(extChartAt 𝓘(ℝ,Model n) a).source) {f : M → ℝ}
    (hf : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z.1 (innerSL ℝ z.2)) (t : ℝ) :
    coordinateBackward a (t,extChartAt 𝓘(ℝ,Model n) a z.1,
      fderiv ℝ (fun w => f ((extChartAt 𝓘(ℝ,Model n) a).symm w))
        (extChartAt 𝓘(ℝ,Model n) a z.1)) = (sprayFlow (-t) z).1 := by
  have hd := coordinate_gradient_of_hasMFDerivAt z hz f 1 (by simpa using hf)
  simp only [one_smul] at hd
  rw [coordinateBackward,hd.fderiv]
  have hT := (extChartAt 𝓘(ℝ,Model n) a).map_source hz
  have hi := riemannianCoordinateMetric_isInvertible hT
  rw [hi.inverse_apply_self]
  rw [movingNormal_eq hT, (extChartAt 𝓘(ℝ,Model n) a).left_inv hz,map_smul]
  have hbase : z.1∈(chartAt (Model n) a).source := by simpa only [extChartAt_source] using hz
  have hcoord : (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) z).2 =
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ z.1 z.2 := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hbase]
    rfl
  rw [hcoord]
  change riemannianExp z.1 ((-t) •
    ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ z.1
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ z.1 z.2))) = _
  rw [Trivialization.symmL_continuousLinearMapAt _ hbase,riemannianExp_smul]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma hasMFDerivAt_riemannianGradient {f : M → ℝ} {x : M}
    (hd : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x) :
    HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x
      (innerSL ℝ (riemannianGradient (n := n) f x)) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  apply hd.hasMFDerivAt.congr_mfderiv
  exact ((InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,Model n) x)).apply_symm_apply _).symm

def hopfPole (t : ℝ) (u : M → ℝ) (z : M) : M :=
  (sprayFlow (-t) (⟨z,riemannianGradient (n := n) (hopfLax t u) z⟩ :
    TangentBundle 𝓘(ℝ,Model n) M)).1

lemma WeakMTW.coordinateBackward_eq_pole (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {a : M} {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    coordinateBackward a (t,z,
      fderiv ℝ (fun w => hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm w)) z) =
      hopfPole (n := n) t u ((extChartAt 𝓘(ℝ,Model n) a).symm z) := by
  have H := coordinateBackward_of_derivative
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,
      riemannianGradient (n := n) (hopfLax t u) ((extChartAt 𝓘(ℝ,Model n) a).symm z)⟩ :
      TangentBundle 𝓘(ℝ,Model n) M)
    ((extChartAt 𝓘(ℝ,Model n) a).map_target hz)
    (hasMFDerivAt_riemannianGradient (hmtw.mdifferentiable_hopfLax hu hv hdual ht ht1 _)) t
  simpa only [hopfPole, (extChartAt 𝓘(ℝ,Model n) a).right_inv hz] using H

end WeakMTWTransport

end

end OAI
