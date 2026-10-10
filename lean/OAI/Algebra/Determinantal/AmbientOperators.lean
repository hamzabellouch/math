import OAI.Algebra.Determinantal.BorderPolars

namespace OAI

namespace PermanentBorder.AmbientPolar
open MvPolynomial Matrix PolarAnalysis KernelBilinear
open scoped Classical
variable {σ κ : Type} [Fintype σ] [Fintype κ]

noncomputable def substitution (b : σ → ℂ)
    (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) : Poly σ →ₐ[ℂ] Poly (Option κ) :=
  affineSubstitution b (fun j i => L (Pi.single i 1) j)

omit [Fintype σ] in
lemma eval_substitution (b : σ → ℂ)
    (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (P : Poly σ) (z : Option κ → ℂ) :
    eval z (substitution b L P) = eval (b + L z) P := by
  classical
  change (aeval z : Poly (Option κ) →ₐ[ℂ] ℂ) (aeval _ P) = _
  rw [comp_aeval_apply]
  apply congrArg (fun g : σ → ℂ => aeval g P)
  funext j
  simp only [map_add, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self_apply]
  have hz : z = ∑ i, z i • Pi.single i 1 := by
    ext i
    simp [Pi.single_apply]
  have hL : L z j = ∑ i, L (Pi.single i 1) j * z i := by
    conv_lhs => rw [hz, map_sum]
    simp [mul_comm]
  simpa only [Pi.add_apply] using congrArg (fun v : ℂ => b j + v) hL.symm

noncomputable def directional (h : κ → σ → ℂ) (i : κ) : Poly σ →ₗ[ℂ] Poly σ :=
  ∑ j, h i j • (pderiv j).toLinearMap

noncomputable def operators (b : σ → ℂ)
    (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (h : κ → σ → ℂ) :
    Option κ → Poly σ →ₗ[ℂ] Poly (Option κ) :=
  Option.elim' (substitution b L).toLinearMap
    (fun i => (substitution b L).toLinearMap.comp (directional h i))

omit [Fintype κ] in
lemma derivative_directional (h : κ → σ → ℂ) (P : Poly σ) (y : σ → ℂ) (i : κ) :
    fderiv ℂ (fun y => eval y P) y (h i) = eval y (directional h i P) := by
  rw [(CI.hasFDerivAt_eval P y).fderiv, CI.polynomialDerivative_apply]
  simp [directional, mul_comm]

lemma polarPair_operators (b : σ → ℂ)
    (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (h : κ → σ → ℂ) (P : Poly σ) :
    polarPair (fun y => eval y P) (fun z => b + L (optionProduct.symm z)) h =
      fun z => optionProduct (polynomialSystem (operators b L h) P (optionProduct.symm z)) := by
  funext z
  apply Prod.ext
  · exact (eval_substitution b L P _).symm
  · funext i
    change fderiv ℂ (fun y => eval y P) (b + L (optionProduct.symm z)) (h i) =
      eval (optionProduct.symm z) (substitution b L (directional h i P))
    rw [eval_substitution, derivative_directional]

end PermanentBorder.AmbientPolar

end OAI
