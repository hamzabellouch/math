import OAI.Analysis.Mahler.ActualFiniteStrips
import OAI.Analysis.Mahler.PlanarRegularity
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset
open scoped Topology ContDiff
open MahlerConformal

variable {n N : ℕ}

noncomputable def rowCLM (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) :
    (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, A j i • ContinuousLinearMap.proj i

lemma rowCLM_apply (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (x : Fin n → ℝ) :
    rowCLM A j x = measurement A x j := by
  simp [rowCLM,measurement]

noncomputable def stripCoordinateCLM (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((rowCLM A j).comp (ContinuousLinearMap.fst ℝ _ _)) +
  Complex.I • Complex.ofRealCLM.comp ((rowCLM A j).comp (ContinuousLinearMap.snd ℝ _ _))

lemma stripCoordinateCLM_apply (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : stripCoordinateCLM A j z = stripCoordinate A z j := by
  simp [stripCoordinateCLM,stripCoordinate,rowCLM_apply,mul_comm]

noncomputable def planarDifferential (m : ℕ) (u : ℂ) : ℂ →L[ℝ] ℝ :=
  fderiv ℝ (fun z : ℂ => planarPrimitive m z.re z.im) u

lemma planarDifferential_I (m : ℕ) {q t : ℝ} (hu : (q : ℂ)+(t : ℂ)*I ∈ Omega) :
    planarDifferential m ((q : ℂ)+(t : ℂ)*I) I = planarDensity m ((q : ℂ)+(t : ℂ)*I) := by
  have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    simpa using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
  have hl : HasDerivAt (fun s : ℝ => (q : ℂ)+(s : ℂ)*I) I t := by
    simpa using (hid.mul_const I).const_add (q : ℂ)
  have hp := (hasFDerivAt_planarPrimitive m hu).comp_hasDerivAt t hl
  have he : HasDerivAt (planarPrimitive m q) (planarDifferential m ((q : ℂ)+(t : ℂ)*I) I) t := by
    simpa [Function.comp_def,planarDifferential] using hp
  exact he.unique (hasDerivAt_planarPrimitive_global m hu)

noncomputable def stripDerivative (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (ContinuousLinearMap.fst ℝ _ _).prod (ContinuousLinearMap.pi fun i =>
    ∑ j, A j i • (planarDifferential m (stripCoordinate A z j)).comp (stripCoordinateCLM A j))

/-- The full actual real derivative; its mixed x-derivative is retained. -/
theorem hasFDerivAt_stripMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ stripDomain A) :
    HasFDerivAt (stripMap A m) (stripDerivative A m z) z := by
  have hp : ∀ j, HasFDerivAt
      (fun w => planarPrimitive m (measurement A w.1 j) (measurement A w.2 j))
      ((planarDifferential m (stripCoordinate A z j)).comp (stripCoordinateCLM A j)) z := by
    intro j
    have hc : HasFDerivAt (fun w => stripCoordinate A w j) (stripCoordinateCLM A j) z := by
      apply (stripCoordinateCLM A j).hasFDerivAt.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun w => (stripCoordinateCLM_apply A j w).symm)
    have h := (hasFDerivAt_planarPrimitive m (hz j)).comp z hc
    simpa [Function.comp_def,stripCoordinateCLM_apply,stripCoordinate,planarDifferential] using h
  have hb : HasFDerivAt
      (fun w => push A (fun j => planarPrimitive m (measurement A w.1 j) (measurement A w.2 j)))
      (ContinuousLinearMap.pi fun i =>
        ∑ j, A j i • (planarDifferential m (stripCoordinate A z j)).comp (stripCoordinateCLM A j)) z := by
    apply hasFDerivAt_pi.mpr
    intro i
    exact HasFDerivAt.fun_sum (fun j _ => (hp j).const_mul (A j i))
  exact (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.prodMk hb

end SymmetricMahler

end OAI
