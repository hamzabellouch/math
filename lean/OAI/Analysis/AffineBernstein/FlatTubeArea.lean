import Mathlib
import OAI.Analysis.AffineBernstein.TubeDensityVariation

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

/- In a flat normal chart the final normal coordinate is one, and the
transverse column is the fixed negative final basis vector. -/
def flatTubeFrame (Y : S × E → E) (x : S × E) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) : ι ⊕ (κ ⊕ Unit) → S × E :=
  Sum.elim (fun i => fderiv ℝ (supportParam Y) x (bS i,0))
    (Sum.elim (fun j => fderiv ℝ (supportParam Y) x (0,bE (Sum.inl j)))
      (fun _ => (0,-bE (Sum.inr ()))))

omit [CompleteSpace E] [Fintype ι] in
lemma flatTubeFrame_matrix {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (hgrad : ∀ᶠ q in nhds x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    (bS.prod bE.toBasis).toMatrix (flatTubeFrame Y x bS bE) =
      Matrix.fromBlocks 1 0
        (Matrix.of fun i j => bE.repr (fderiv ℝ Y x (bS j,0)) i)
        (Matrix.fromBlocks (tubeRadiusMatrix H x bE) 0
          (Matrix.of fun (_ : Unit) j => bE.repr (fderiv ℝ Y x (0,bE (Sum.inl j))) (Sum.inr ()))
          (-1 : Matrix Unit Unit ℝ)) := by
  have hy := hY.differentiableAt (by simp)
  have hs := hH.isSymmSndFDerivAt (by simp)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Module.Basis.toMatrix_apply,flatTubeFrame,supportParam_fderiv hy,
      Matrix.fromBlocks,Matrix.one_apply,Finsupp.single_apply,eq_comm]
  · rcases j with j | ⟨⟩ <;>
      simp [Module.Basis.toMatrix_apply,flatTubeFrame,supportParam_fderiv hy,Matrix.fromBlocks]
  · simp [Module.Basis.toMatrix_apply,flatTubeFrame,supportParam_fderiv hy,Matrix.fromBlocks]
  · rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
    · simpa [Module.Basis.toMatrix_apply,flatTubeFrame,supportParam_fderiv hy,
        Matrix.fromBlocks,OrthonormalBasis.repr_apply_apply,tubeRadiusMatrix] using
        (support_angular_derivative hH hy hgrad (0,bE (Sum.inl j)) (bE (Sum.inl i))).trans
          (hs.eq (0,bE (Sum.inl j)) (0,bE (Sum.inl i)))
    · simp [Module.Basis.toMatrix_apply,flatTubeFrame,Matrix.fromBlocks]
    · simp [Module.Basis.toMatrix_apply,flatTubeFrame,supportParam_fderiv hy,Matrix.fromBlocks]
    · simp [Module.Basis.toMatrix_apply,flatTubeFrame,Matrix.fromBlocks]

omit [CompleteSpace E] in
lemma flatTubeFrame_det {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (hgrad : ∀ᶠ q in nhds x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    (bS.prod bE.toBasis).det (flatTubeFrame Y x bS bE) = -(tubeRadiusMatrix H x bE).det := by
  rw [Module.Basis.det_apply,flatTubeFrame_matrix hH hY hgrad bS bE,
    Matrix.det_fromBlocks_zero₁₂,Matrix.det_fromBlocks_zero₁₂]
  simp

omit [DecidableEq κ] in
lemma flat_supportConormal_transverse {H : S × E → ℝ} {x : S × E}
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (hx : inner ℝ x.2 (bE (Sum.inr ())) = 1) :
    supportConormal H x ((0 : S),-bE (Sum.inr ())) = 1 := by
  simp [supportConormal,hx,show ((0,0) : S × E) = 0 from rfl]

def flatTubeAffineAreaJet (H : S × E → ℝ) (Y : S × E → E) (x : S × E)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) : ℝ :=
  let n : ℝ := Fintype.card ι+Fintype.card κ
  Real.rpow (Matrix.of fun i j : ι ⊕ κ => supportConormal H x
      (fderiv ℝ (fderiv ℝ (supportParam Y)) x (tubeTangent bS bE i) (tubeTangent bS bE j))).det
        (1/(n+2)) *
    Real.rpow |(bS.prod bE.toBasis).det (flatTubeFrame Y x bS bE)| (n/(n+2))

/- Literal flat-normal-chart area density. No sphere measure change is
required to obtain the local variational equation in these coordinates. -/
lemma flatTubeAffineAreaJet_eq {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[nhds x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in nhds x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hB : 0 < (tubeBaseMatrix H x bS).det) (hR : 0 < (tubeRadiusMatrix H x bE).det) :
    flatTubeAffineAreaJet H Y x bS bE = tubeAreaDensity (tubeBaseMatrix H x bS)
      (tubeRadiusMatrix H x bE) (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) := by
  unfold flatTubeAffineAreaJet tubeAreaDensity
  dsimp only
  simp only [Real.rpow_eq_pow]
  rw [tubeSecondForm_blocks hH hY heul hgrad,Matrix.det_fromBlocks_zero₁₂,
    flatTubeFrame_det hH hY hgrad,abs_neg,abs_of_pos hR,
    Real.mul_rpow hB.le hR.le,mul_assoc,← Real.rpow_add hR]
  congr 2
  have hh : (0 : ℝ) < (Fintype.card ι : ℝ)+Fintype.card κ+2 := by positivity
  field_simp
  ring

end AffineBernstein
end

end OAI
