import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOrderedDerivatives
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEnergyComponents

namespace OAI

/-! # Bounded physical ordered derivatives on the faithful Y completion

Each ordered top derivative is a bounded map into physical L², with norm at
most one. On the dense Schwartz domain it is the usual Cartesian derivative.
-/

open MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousOrderedDerivativeL2 (N : ℕ) (j : Fin N → Fin 12) :
    𝓢(E, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap.comp
    (iteratedLineDerivOpCLM ℂ 𝓢(E, ℂ)
      (fun i => (EuclideanSpace.basisFun (Fin 12) ℝ) (j i))).toLinearMap

theorem homogeneousOrderedDerivativeL2_norm_sq (N : ℕ) (j : Fin N → Fin 12)
    (f : 𝓢(E, ℂ)) :
    ‖homogeneousOrderedDerivativeL2 N j f‖ ^ 2 =
      ∫ x : E, ‖homogeneousOrderedDerivative N j f x‖ ^ 2 := by
  have h := real_inner_self_eq_norm_sq (homogeneousOrderedDerivativeL2 N j f)
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [SchwartzMap.coeFn_toLp (homogeneousOrderedDerivative N j f) 2 volume] with x hx
  change inner ℝ ((homogeneousOrderedDerivative N j f).toLp 2 volume x)
    ((homogeneousOrderedDerivative N j f).toLp 2 volume x) = _
  rw [hx, real_inner_self_eq_norm_sq]

theorem homogeneousOrderedDerivativeL2_norm_le (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (j : Fin N → Fin 12) (f : 𝓢(E, ℂ)) :
    ‖homogeneousOrderedDerivativeL2 N j f‖ ≤
      ‖homogeneousSchwartzEmbedding a N ha ha1 hk f‖ := by
  have hterm : (∫ x : E, ‖homogeneousOrderedDerivative N j f x‖ ^ 2) ≤
      ∑ l : Fin N → Fin 12, ∫ x : E, ‖homogeneousOrderedDerivative N l f x‖ ^ 2 :=
    Finset.single_le_sum (f := fun l : Fin N → Fin 12 =>
      ∫ x : E, ‖homogeneousOrderedDerivative N l f x‖ ^ 2)
      (fun l _ => integral_nonneg (fun x => sq_nonneg _)) (Finset.mem_univ j)
  rw [homogeneousOrderedDerivative_energy] at hterm
  rw [← homogeneousHighEnergy_Schwartz_norm_sq a N ha ha1 hk (radianFourierKernel f)] at hterm
  have hhigh := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (homogeneousHighEnergy_norm_le a N ha1 hk
      (homogeneousSchwartzEmbedding a N ha ha1 hk f))
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [homogeneousOrderedDerivativeL2_norm_sq]
  exact hterm.trans hhigh

noncomputable def homogeneousPhysicalDerivative (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12) :
    HomogeneousY a N →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (homogeneousOrderedDerivativeL2 N j).extendOfNorm
    (homogeneousSchwartzEmbedding a N ha ha1 hk).toLinearMap

theorem homogeneousPhysicalDerivative_Schwartz (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (j : Fin N → Fin 12) (f : 𝓢(E, ℂ)) :
    homogeneousPhysicalDerivative a N ha ha1 hk j
      (homogeneousSchwartzEmbedding a N ha ha1 hk f) = homogeneousOrderedDerivativeL2 N j f := by
  apply LinearMap.extendOfNorm_eq (homogeneousSchwartzEmbedding_dense a N ha ha1 hk)
  refine ⟨1, fun f => ?_⟩
  simpa only [one_mul] using! homogeneousOrderedDerivativeL2_norm_le a N ha ha1 hk j f

theorem homogeneousPhysicalDerivative_norm_le (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12)
    (u : HomogeneousY a N) : ‖homogeneousPhysicalDerivative a N ha ha1 hk j u‖ ≤ ‖u‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := homogeneousOrderedDerivativeL2 N j)
    (e := (homogeneousSchwartzEmbedding a N ha ha1 hk).toLinearMap)
    (homogeneousSchwartzEmbedding_dense a N ha ha1 hk) 1
    (fun f => by simpa only [one_mul] using! homogeneousOrderedDerivativeL2_norm_le a N ha ha1 hk j f) u
  simpa only [homogeneousPhysicalDerivative, one_mul] using! h

end DefocusingNLS

end OAI
