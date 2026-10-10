import Mathlib
import OAI.Analysis.AffineBernstein.ParametricSmoothness
import OAI.Analysis.AffineBernstein.InverseTracePullback
import OAI.Analysis.AffineBernstein.ActualTubeWeights
import OAI.Analysis.AffineBernstein.JointAngularCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section JointTubeMetrics
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] in
lemma dirDeriv_prod_left {g : S × E → ℝ} {s : S} {e : E}
    (hg : DifferentiableAt ℝ g (s,e)) (v : S) :
    dirDeriv v (fun y => g (y,e)) s = dirDeriv (v,(0:E)) g (s,e) := by
  simpa using dirDeriv_affine_pullback (0,e) (ContinuousLinearMap.inl ℝ S E)
    (by simpa using hg) v

omit [CompleteSpace E] in
lemma flatInverseTrace_prod_left {g : S × E → ℝ} {s : S} {e : E}
    (hg : ContDiffAt ℝ ∞ g (s,e)) (A : Matrix ι ι ℝ) (v : ι → S) :
    flatInverseTrace A v (fun y => g (y,e)) s =
      flatInverseTrace A (fun i => (v i,(0:E))) g (s,e) := by
  simpa using flatInverseTrace_affine_pullback (0,e) (ContinuousLinearMap.inl ℝ S E)
    (by simpa using hg) A v

omit [CompleteSpace E] in
lemma flatInversePair_prod_left {f g : S × E → ℝ} {s : S} {e : E}
    (hf : DifferentiableAt ℝ f (s,e)) (hg : DifferentiableAt ℝ g (s,e))
    (A : Matrix ι ι ℝ) (v : ι → S) :
    flatInversePair A v (fun y => f (y,e)) (fun y => g (y,e)) s =
      flatInversePair A (fun i => (v i,(0:E))) f g (s,e) := by
  simpa using flatInversePair_affine_pullback (0,e) (ContinuousLinearMap.inl ℝ S E)
    (by simpa using hf) (by simpa using hg) A v

def tubeBasePair (H : S × E → ℝ) (b : Module.Basis ι ℝ S) (f g : S × E → ℝ)
    (q : S × E) : ℝ := H q*flatInversePair (tubeBaseMatrix H q b) (fun i => (b i,(0:E))) f g q

def tubeBaseTrace (H : S × E → ℝ) (b : Module.Basis ι ℝ S) (g : S × E → ℝ)
    (q : S × E) : ℝ := H q*flatInverseTrace (tubeBaseMatrix H q b) (fun i => (b i,(0:E))) g q

def tubeAngularPair (H : S × E → ℝ) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f g : S × E → ℝ) (q : S × E) : ℝ :=
  H q/tubeAngularDensity H q b * supportNewtonTensor b (fun y => H (q.1,y)) q.2
    (tangentProjection q.2 (gradient (fun y => f (q.1,y)) q.2))
    (tangentProjection q.2 (gradient (fun y => g (q.1,y)) q.2))

def tubeAngularTrace (H : S × E → ℝ) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (g : S × E → ℝ) (q : S × E) : ℝ :=
  H q/tubeAngularDensity H q b * roundHessianContraction b
    (supportNewtonTensor b (fun y => H (q.1,y))) (fun y => g (q.1,y)) q.2

omit [CompleteSpace E] in
lemma contDiffAt_tubeBasePair {H f g : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hf : ContDiffAt ℝ ∞ f q) (hg : ContDiffAt ℝ ∞ g q)
    (b : Module.Basis ι ℝ S) (hd : (tubeBaseMatrix H q b).det ≠ 0) :
    ContDiffAt ℝ ∞ (tubeBasePair H b f g) q := by
  apply hH.mul
  unfold flatInversePair
  exact ContDiffAt.sum fun j _ => ContDiffAt.sum fun i _ =>
    ((contDiffAt_inverse_matrix_entry_param (contDiffAt_tubeBaseMatrix hH b) hd i j).mul
      (contDiffAt_dirDeriv hf _)).mul (contDiffAt_dirDeriv hg _)

omit [CompleteSpace E] in
lemma contDiffAt_tubeBaseTrace {H g : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hg : ContDiffAt ℝ ∞ g q)
    (b : Module.Basis ι ℝ S) (hd : (tubeBaseMatrix H q b).det ≠ 0) :
    ContDiffAt ℝ ∞ (tubeBaseTrace H b g) q := by
  apply hH.mul
  unfold flatInverseTrace
  exact ContDiffAt.sum fun j _ => ContDiffAt.sum fun i _ =>
    (contDiffAt_inverse_matrix_entry_param (contDiffAt_tubeBaseMatrix hH b) hd i j).mul
      (contDiffAt_dirDeriv (contDiffAt_dirDeriv hg _) _)

omit [CompleteSpace E] in
lemma continuousAt_tubeMeasureDensity {n : ℕ} {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hh : 0 < H q) : ContinuousAt (tubeMeasureDensity n H bS bE) q := by
  unfold tubeMeasureDensity tubeMeasureCoefficient
  apply (hH.continuousAt.rpow_const (Or.inl hh.ne')).mul
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp q
    (contDiffAt_tubeBaseMatrix hH bS)).continuousAt.mul
      (contDiffAt_tubeAngularDensity hH bE).continuousAt).sqrt

lemma continuousOn_tubeAngularPair {U : Set (S × E)} {H f g : S × E → ℝ}
    (hH : ∀ q ∈ U, ContDiffAt ℝ ∞ H q) (hf : ∀ q ∈ U, ContDiffAt ℝ ∞ f q)
    (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hQ : ∀ q ∈ U, tubeAngularDensity H q b ≠ 0) :
    ContinuousOn (tubeAngularPair H b f g) U := by
  have ht (g : S × E → ℝ) (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q) :
      ContinuousOn (fun q : S × E => tangentProjection q.2 (gradient (fun y => g (q.1,y)) q.2)) U := by
    have hd := continuousOn_sliceAngularGradient hg
    exact hd.sub ((((continuous_snd.continuousOn).inner hd)).smul continuous_snd.continuousOn)
  have hcH : ContinuousOn H U := fun q hq => (hH q hq).continuousAt.continuousWithinAt
  have hcQ : ContinuousOn (fun q => tubeAngularDensity H q b) U :=
    fun q hq => (contDiffAt_tubeAngularDensity (hH q hq) b).continuousAt.continuousWithinAt
  exact (hcH.div hcQ hQ).mul
    (((continuousOn_sliceNewtonTensor hH b).clm_apply (ht f hf)).clm_apply (ht g hg))

lemma continuousOn_tubeAngularTrace {U : Set (S × E)} {H g : S × E → ℝ}
    (hH : ∀ q ∈ U, ContDiffAt ℝ ∞ H q) (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q)
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) (hQ : ∀ q ∈ U, tubeAngularDensity H q b ≠ 0) :
    ContinuousOn (tubeAngularTrace H b g) U := by
  have hcH : ContinuousOn H U := fun q hq => (hH q hq).continuousAt.continuousWithinAt
  have hcQ : ContinuousOn (fun q => tubeAngularDensity H q b) U :=
    fun q hq => (contDiffAt_tubeAngularDensity (hH q hq) b).continuousAt.continuousWithinAt
  exact (hcH.div hcQ hQ).mul
    (continuousOn_sliceRoundContraction hH hg b)

end JointTubeMetrics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Cauchy--Schwarz for a positive definite inverse matrix, including zero vectors. -/

end AffineBernstein
end

end OAI
