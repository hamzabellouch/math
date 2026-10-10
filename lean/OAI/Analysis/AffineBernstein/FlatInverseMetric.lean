import Mathlib
import OAI.Analysis.AffineBernstein.TubeDensityVariation
import OAI.Analysis.AffineBernstein.ParametricInverseMetric

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

lemma inverseMatrixPair_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι ι ℝ) (e : κ ≃ ι) (v w : ι → ℝ) :
    inverseMatrixPair (A.submatrix e e) (v ∘ e) (w ∘ e) = inverseMatrixPair A v w := by
  unfold inverseMatrixPair
  rw [Matrix.inv_submatrix_equiv]
  simp only [Matrix.submatrix_apply,Function.comp_apply]
  calc
    _ = ∑ j, ∑ i, A⁻¹ i (e j)*v (e j)*w i := by
      apply Finset.sum_congr rfl
      intro j _
      exact e.sum_comp (fun i => A⁻¹ i (e j)*v (e j)*w i)
    _ = _ := e.sum_comp (fun j => ∑ i, A⁻¹ i j*v j*w i)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma parametricSecondForm_flatSupport {n : ℕ} {H : S × E → ℝ} {Y : S × E → E}
    (q₀ : S × E) (J : Space n →L[ℝ] (S × E)) {x : Space n}
    (hH : ContDiffAt ℝ ∞ H (q₀+J x)) (hY : ContDiffAt ℝ ∞ Y (q₀+J x))
    (heul : H =ᶠ[nhds (q₀+J x)] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in nhds (q₀+J x), ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ ι ⊕ κ) (hJ : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i)) :
    parametricSecondForm (fun y => supportParam Y (q₀+J y))
      (supportConormal H (q₀+J x)) x =
      (Matrix.fromBlocks (tubeBaseMatrix H (q₀+J x) bS) 0 0
        (tubeRadiusMatrix H (q₀+J x) bE)).submatrix e e := by
  let ν := supportConormal H (q₀+J x)
  have hp : ContDiffAt ℝ ∞ (supportParam Y) (q₀+J x) := contDiffAt_fst.prodMk hY
  rw [← tubeSecondForm_blocks hH hY heul hgrad bS bE]
  ext i j
  change dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n j)
    (fun y => ν (supportParam Y (q₀+J y)))) x =
      ν (fderiv ℝ (fderiv ℝ (supportParam Y)) (q₀+J x)
        (tubeTangent bS bE (e i)) (tubeTangent bS bE (e j)))
  have hνp : ContDiffAt ℝ ∞ (fun q => ν (supportParam Y q)) (q₀+J x) :=
    ν.contDiff.contDiffAt.comp (q₀+J x) hp
  have hq : ContDiffAt ℝ ∞ (fun y => q₀+J y) x := contDiffAt_const.add J.contDiff.contDiffAt
  rw [dirDeriv_eq_second (f := fun y => ν (supportParam Y (q₀+J y)))
    (hνp.comp (f := fun y => q₀+J y) x hq),
    second_fderiv_affine_comp J q₀ hνp,second_fderiv_clm_comp ν hp,hJ,hJ]

/- The inverse second-form norm of a base affine coordinate in the literal
flat support chart is exactly the inverse-B contraction, not a surrogate. -/
theorem parametricInverseMetric_flat_base {n : ℕ} {H : S × E → ℝ} {Y : S × E → E}
    (q₀ : S × E) (J : Space n →L[ℝ] (S × E)) {x : Space n}
    (hH : ContDiffAt ℝ ∞ H (q₀+J x)) (hY : ContDiffAt ℝ ∞ Y (q₀+J x))
    (heul : H =ᶠ[nhds (q₀+J x)] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in nhds (q₀+J x), ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ ι ⊕ κ) (hJ : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    (hB : (tubeBaseMatrix H (q₀+J x) bS).det ≠ 0)
    (hR : (tubeRadiusMatrix H (q₀+J x) bE).det ≠ 0) (ℓ : S →L[ℝ] ℝ) :
    parametricInverseMetric (fun y => supportParam Y (q₀+J y))
      (supportConormal H (q₀+J x)) (fun y => ℓ (q₀+J y).1) x =
      inverseMatrixPair (tubeBaseMatrix H (q₀+J x) bS)
        (fun i => ℓ (bS i)) (fun i => ℓ (bS i)) := by
  have hd : (fun i => dirDeriv (coordinateVector n i) (fun y => ℓ (q₀+J y).1) x) =
      (Sum.elim (fun i => ℓ (bS i)) (fun _ : κ => (0:ℝ))) ∘ e := by
    funext i
    have hh := (ℓ.hasFDerivAt.comp x (J.hasFDerivAt.const_add q₀).fst).fderiv
    change fderiv ℝ (fun y => ℓ (q₀+J y).1) x = _ at hh
    unfold dirDeriv
    rw [hh]
    change ℓ (J (coordinateVector n i)).1 = _
    rw [hJ]
    rcases hei : e i with j | j <;> simp [tubeTangent,hei]
  unfold parametricInverseMetric
  rw [parametricSecondForm_flatSupport q₀ J hH hY heul hgrad bS bE e hJ,hd,
    inverseMatrixPair_equiv]
  exact inverseMatrixPair_block_base _ _ hB hR _ _

end AffineBernstein
end

end OAI
