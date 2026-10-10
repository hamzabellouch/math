import Mathlib
import OAI.Analysis.AffineBernstein.TubeFrame

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

/- The actual second-jet affine-area density in the base and orthonormal
angular directions; the transverse column is (0,-e). -/
def tubeAffineAreaJet (H : S × E → ℝ) (Y : S × E → E) (x : S × E)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) : ℝ :=
  let n : ℝ := Fintype.card ι + Fintype.card κ
  Real.rpow (Matrix.of fun i j : ι ⊕ κ => supportConormal H x
      (fderiv ℝ (fderiv ℝ (supportParam Y)) x (tubeTangent bS bE i) (tubeTangent bS bE j))).det
        (1 / (n + 2)) *
    Real.rpow |(bS.prod bE.toBasis).det (tubeFrame Y x bS bE)| (n / (n + 2))

lemma tubeAffineAreaJet_eq {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : bE (Sum.inr ()) = x.2)
    (hB : 0 < (tubeBaseMatrix H x bS).det) (hR : 0 < (tubeRadiusMatrix H x bE).det) :
    let n : ℝ := Fintype.card ι + Fintype.card κ
    tubeAffineAreaJet H Y x bS bE =
      Real.rpow (tubeBaseMatrix H x bS).det (1 / (n + 2)) *
        Real.rpow (tubeRadiusMatrix H x bE).det (1 - 1 / (n + 2)) := by
  dsimp only
  unfold tubeAffineAreaJet
  dsimp only
  simp only [Real.rpow_eq_pow]
  rw [tubeSecondForm_blocks hH hY heul hgrad, Matrix.det_fromBlocks_zero₁₂,
    tubeFrame_det hH hY heul hgrad bS bE he, abs_neg, abs_of_pos hR,
    Real.mul_rpow hB.le hR.le, mul_assoc, ← Real.rpow_add hR]
  congr 2
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) + Fintype.card κ + 2 := by positivity
  field_simp
  ring

omit [DecidableEq κ] in
lemma supportConormal_transverse {H : S × E → ℝ} {x : S × E}
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (he : bE (Sum.inr ()) = x.2) :
    supportConormal H x (0,-x.2) = 1 := by
  change fderiv ℝ H x (0,0) - inner ℝ x.2 (-x.2) = 1
  rw [show ((0,0) : S × E) = 0 from rfl, map_zero, inner_neg_right, zero_sub, neg_neg, ← he]
  simp

lemma supportConormal_inward_velocity {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (heul : H x = inner ℝ x.2 (Y x)) :
    supportConormal H x (0,-Y x) = H x := by
  change fderiv ℝ H x (0,0) - inner ℝ x.2 (-Y x) = H x
  rw [show ((0,0) : S × E) = 0 from rfl, map_zero, inner_neg_right, zero_sub, neg_neg, heul]

end AffineBernstein
end

end OAI
