import OAI.MeasureTheory.Falconer.Fourier.PublishedQuadraticStationary

namespace OAI

/-!
# Smooth dependence of the actual quadratic stationary jets

The derivatives are taken only in the tangent variable. Joint smoothness
of an amplitude therefore gives smooth dependence of every fixed quadratic
jet on its external parameters, including the evaluation direction.
-/

namespace Falconer
open InnerProductSpace
open scoped ContDiff

variable {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem partialFDeriv_contDiffAt {n : ℕ} {F : P × Space n → G} {p : P} {x : Space n}
    (hF : ContDiffAt ℝ ∞ F (p,x)) :
    ContDiffAt ℝ ∞ (fun z : P × Space n => fderiv ℝ (fun y => F (z.1,y)) z.2) (p,x) := by
  have hf : ContDiffAt ℝ ∞
      (fun z : (P × Space n) × Space n => F (z.1.1,z.2)) ((p,x),x) :=
    hF.comp ((p,x),x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact hf.fderiv contDiffAt_snd (by simp)

theorem partialLaplacian_contDiffAt {n : ℕ} {F : P × Space n → ℂ} {p : P} {x : Space n}
    (hF : ContDiffAt ℝ ∞ F (p,x)) :
    ContDiffAt ℝ ∞
      (fun z : P × Space n => Laplacian.laplacian (fun y => F (z.1,y)) z.2) (p,x) := by
  have h₂ := partialFDeriv_contDiffAt (partialFDeriv_contDiffAt hF)
  have heq : (fun z : P × Space n => Laplacian.laplacian (fun y => F (z.1,y)) z.2) =
      (fun z => ∑ i : Fin n,
        (fderiv ℝ (fun y => fderiv ℝ (fun v => F (z.1,v)) y) z.2)
          ((EuclideanSpace.basisFun (Fin n) ℝ) i)
          ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := by
    funext z
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin n) ℝ)]
    apply Finset.sum_congr rfl
    intro i _
    rw [iteratedFDeriv_two_apply]
    rfl
  rw [heq]
  exact ContDiffAt.sum (fun i _ => (h₂.clm_apply contDiffAt_const).clm_apply contDiffAt_const)

theorem partialIteratedLaplacian_contDiffAt {n : ℕ} {F : P × Space n → ℂ}
    {p : P} {x : Space n} (hF : ContDiffAt ℝ ∞ F (p,x)) (j : ℕ) :
    ContDiffAt ℝ ∞
      (fun z : P × Space n =>
        ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
          (fun y => F (z.1,y))) z.2) (p,x) := by
  induction j with
  | zero => simpa using hF
  | succ j hj =>
      simpa only [Function.iterate_succ_apply'] using partialLaplacian_contDiffAt hj

theorem quadraticJetCoefficient_contDiffAt {n : ℕ} {F : P × Space n → ℂ} {p : P}
    (hF : ContDiffAt ℝ ∞ F (p,0)) (j : ℕ) :
    ContDiffAt ℝ ∞ (fun q : P => quadraticJetCoefficient j (fun u => F (q,u))) p := by
  have h := (partialIteratedLaplacian_contDiffAt hF j).comp p
    (contDiffAt_id.prodMk contDiffAt_const)
  exact contDiffAt_const.mul h

end Falconer

end OAI
