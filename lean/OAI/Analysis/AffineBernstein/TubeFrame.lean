import Mathlib
import OAI.Analysis.AffineBernstein.TubeSecondForm

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] in
lemma support_angular_derivative {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : DifferentiableAt ℝ Y x)
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (v : S × E) (w : E) : inner ℝ w (fderiv ℝ Y x v) =
      fderiv ℝ (fderiv ℝ H) x v (0,w) := by
  have hg : (fun q => fderiv ℝ H q (0,w)) =ᶠ[𝓝 x]
      (fun q => inner ℝ (Y q) w) := hgrad.mono (fun q hq => hq w)
  have hdH := (hH.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hl := hdH.hasFDerivAt.clm_apply (hasFDerivAt_const (0,w) x)
  have hr := hY.hasFDerivAt.inner ℝ (hasFDerivAt_const w x)
  have he := congrArg (fun A : (S × E) →L[ℝ] ℝ => A v)
    ((hl.congr_of_eventuallyEq hg.symm).unique hr)
  simpa [real_inner_comm] using he.symm

def tubeBaseMatrix (H : S × E → ℝ) (x : S × E) (bS : Module.Basis ι ℝ S) :
    Matrix ι ι ℝ := Matrix.of fun i j =>
  -fderiv ℝ (fderiv ℝ H) x (bS i,0) (bS j,0)

def tubeRadiusMatrix (H : S × E → ℝ) (x : S × E) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    Matrix κ κ ℝ := Matrix.of fun i j =>
  fderiv ℝ (fderiv ℝ H) x (0,bE (Sum.inl i)) (0,bE (Sum.inl j))

def tubeTangent (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    ι ⊕ κ → S × E := Sum.elim (fun i => (bS i,0)) (fun j => (0,bE (Sum.inl j)))

def tubeFrame (Y : S × E → E) (x : S × E) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) : ι ⊕ (κ ⊕ Unit) → S × E :=
  Sum.elim (fun i => fderiv ℝ (supportParam Y) x (bS i,0))
    (Sum.elim (fun j => fderiv ℝ (supportParam Y) x (0,bE (Sum.inl j)))
      (fun _ => (0,-x.2)))

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma tubeSecondForm_blocks {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    (Matrix.of fun i j : ι ⊕ κ => supportConormal H x
      (fderiv ℝ (fderiv ℝ (supportParam Y)) x (tubeTangent bS bE i) (tubeTangent bS bE j))) =
      Matrix.fromBlocks (tubeBaseMatrix H x bS) 0 0 (tubeRadiusMatrix H x bE) := by
  ext i j
  simp only [Matrix.of_apply, supportConormal_second hH hY heul hgrad]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [tubeTangent, tubeBaseMatrix, tubeRadiusMatrix, Matrix.fromBlocks,
      show ((0,0) : S × E) = 0 from rfl]

omit [CompleteSpace E] [Fintype ι] in
lemma tubeFrame_matrix {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : bE (Sum.inr ()) = x.2) :
    (bS.prod bE.toBasis).toMatrix (tubeFrame Y x bS bE) =
      Matrix.fromBlocks 1 0
        (Matrix.of fun i j => bE.repr (fderiv ℝ Y x (bS j,0)) i)
        (Matrix.fromBlocks (tubeRadiusMatrix H x bE) 0 0 (-1 : Matrix Unit Unit ℝ)) := by
  have hy := hY.differentiableAt (by simp)
  have hs := hH.isSymmSndFDerivAt (by simp)
  have ht (j : κ) : inner ℝ x.2 (fderiv ℝ Y x (0,bE (Sum.inl j))) = 0 := by
    rw [support_tangent_identity (hH.differentiableAt (by simp)) hy heul hgrad.self_of_nhds]
    change fderiv ℝ H x 0 = 0
    exact map_zero _
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Module.Basis.toMatrix_apply, tubeFrame, supportParam_fderiv hy, Matrix.fromBlocks, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  · rcases j with j | ⟨⟩ <;>
      simp [Module.Basis.toMatrix_apply, tubeFrame, supportParam_fderiv hy, Matrix.fromBlocks]
  · simp [Module.Basis.toMatrix_apply, tubeFrame, supportParam_fderiv hy, Matrix.fromBlocks]
  · rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
    · simpa [Module.Basis.toMatrix_apply, tubeFrame, supportParam_fderiv hy,
        Matrix.fromBlocks, OrthonormalBasis.repr_apply_apply, tubeRadiusMatrix] using
          (support_angular_derivative hH hy hgrad (0,bE (Sum.inl j)) (bE (Sum.inl i))).trans
            (hs.eq (0,bE (Sum.inl j)) (0,bE (Sum.inl i)))
    · simp [Module.Basis.toMatrix_apply, tubeFrame, Matrix.fromBlocks, ← he]
    · simpa [Module.Basis.toMatrix_apply, tubeFrame, supportParam_fderiv hy,
        Matrix.fromBlocks, OrthonormalBasis.repr_apply_apply, he] using ht j
    · simp [Module.Basis.toMatrix_apply, tubeFrame, Matrix.fromBlocks, ← he]

omit [CompleteSpace E] in
lemma tubeFrame_det {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : bE (Sum.inr ()) = x.2) :
    (bS.prod bE.toBasis).det (tubeFrame Y x bS bE) = -(tubeRadiusMatrix H x bE).det := by
  rw [Module.Basis.det_apply, tubeFrame_matrix hH hY heul hgrad bS bE he,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₁₂]
  simp

end AffineBernstein
end

end OAI
