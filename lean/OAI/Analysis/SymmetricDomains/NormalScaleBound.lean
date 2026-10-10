import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Matrix

theorem independent_real_rows_complex_injective {k : ℕ}
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β) :
    Function.Injective (fun w : Fin k → ℂ => fun j => ∑ i, (β j i : ℂ)*w i) := by
  classical
  have hr : Matrix.det (Matrix.of β) ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp
      (Matrix.Nonsingular.of_linearIndependent_row hβ)
  let A : Matrix (Fin k) (Fin k) ℂ := Complex.ofRealHom.mapMatrix (Matrix.of β)
  have hc : A.det ≠ 0 := by
    dsimp [A]
    rw [←RingHom.map_det]
    simpa using hr
  have hi := Matrix.mulVec_injective_iff.mpr
    (Matrix.linearIndependent_cols_of_det_ne_zero hc)
  convert hi using 1
  rfl

theorem independent_real_rows_bound {k : ℕ}
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Fin k → ℂ,
      ‖w‖ ≤ C*‖(fun j => ∑ i, (β j i : ℂ)*w i)‖ := by
  classical
  let L : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
    Matrix.mulVecLin (Matrix.of (fun j i => (β j i : ℂ)))
  have hi : Function.Injective L := by
    convert independent_real_rows_complex_injective β hβ using 1
    rfl
  let e : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ) :=
    (LinearEquiv.ofBijective L ⟨hi,(LinearMap.injective_iff_surjective.mp hi)⟩).toContinuousLinearEquiv
  refine ⟨‖e.symm.toContinuousLinearMap‖+1,by positivity,?_⟩
  intro w
  have h := e.symm.toContinuousLinearMap.le_opNorm (e w)
  have he : e w = fun j => ∑ i, (β j i : ℂ)*w i := by
    rfl
  calc
    ‖w‖ ≤ ‖e.symm.toContinuousLinearMap‖*‖e w‖ := by simpa using h
    _ ≤ (‖e.symm.toContinuousLinearMap‖+1)*‖e w‖ := by gcongr; linarith
    _ = _ := by rw [he]

end

open Set Filter Asymptotics
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem analytic_quadratic_remainder {f : E → F} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) :
    (fun x => f x - fderiv ℂ f 0 x) =O[𝓝 0] (fun x => ‖x‖^2) := by
  obtain ⟨p,hp⟩ := hf
  have he : ∀ x, p.partialSum 2 x = fderiv ℂ f 0 x := by
    intro x
    simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,hp.coeff_zero,hf0]
    rw [hp.hasFDerivAt.fderiv,continuousMultilinearCurryFin1_apply]
    congr 1
  simpa only [zero_add,he] using hp.isBigO_sub_partialSum_pow 2

theorem normal_scale_bound {k : ℕ} (β : Fin k → Fin k → ℝ)
    (hβ : LinearIndependent ℝ β)
    (f : Fin k → E × (Fin k → ℂ) → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) (hf0 : ∀ i, f i 0 = 0)
    (hder : ∀ i x, fderiv ℂ (f i) 0 x = Complex.I*∑ j, (β i j : ℂ)*x.2 j) :
    ∃ C > 0, ∃ V ∈ 𝓝 (0 : E × (Fin k → ℂ)),
      ∀ x ∈ V, ‖x.2‖ ≤ C*(‖fun i => f i x‖+‖x‖^2) := by
  classical
  have ho : ∀ i, (fun x => f i x-fderiv ℂ (f i) 0 x) =O[𝓝 0]
      (fun x => ‖x‖^2) := fun i => analytic_quadratic_remainder (hf i) (hf0 i)
  choose C hC hbound using fun i => (ho i).exists_pos
  let M : ℝ := ∑ i, C i
  have hM (i : Fin k) : C i ≤ M := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun i _ => (hC i).le)
  have hev : ∀ᶠ x in 𝓝 (0 : E × (Fin k → ℂ)), ∀ i,
      ‖f i x-fderiv ℂ (f i) 0 x‖ ≤ M*‖x‖^2 := by
    have hh : ∀ᶠ x in 𝓝 (0 : E × (Fin k → ℂ)), ∀ i,
      ‖f i x-fderiv ℂ (f i) 0 x‖ ≤ C i*‖x‖^2 := by
      apply Filter.eventually_all.mpr
      intro i
      simpa only [norm_pow,norm_norm] using (hbound i).bound
    exact hh.mono fun x hx i => (hx i).trans (mul_le_mul_of_nonneg_right (hM i) (sq_nonneg _))
  obtain ⟨D,hD,hd⟩ := independent_real_rows_bound β hβ
  refine ⟨D*(M+1),mul_pos hD (by positivity),{x | ∀ i,
    ‖f i x-fderiv ℂ (f i) 0 x‖ ≤ M*‖x‖^2},hev,?_⟩
  intro x hx
  have hrow : ‖(fun i => ∑ j, (β i j : ℂ)*x.2 j)‖ ≤ ‖fun i => f i x‖+M*‖x‖^2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have hh := norm_le_norm_sub_add (fderiv ℂ (f i) 0 x) (f i x)
    rw [norm_sub_rev] at hh
    have hn : ‖fderiv ℂ (f i) 0 x‖ = ‖∑ j, (β i j : ℂ)*x.2 j‖ := by
      rw [hder,norm_mul,Complex.norm_I,one_mul]
    rw [hn] at hh
    have hfi := norm_le_pi_norm (fun i => f i x) i
    linarith [hx i]
  calc
    ‖x.2‖ ≤ D*‖(fun i => ∑ j, (β i j : ℂ)*x.2 j)‖ := hd x.2
    _ ≤ D*(‖fun i => f i x‖+M*‖x‖^2) := mul_le_mul_of_nonneg_left hrow hD.le
    _ ≤ D*(M+1)*(‖fun i => f i x‖+‖x‖^2) := by
      have hn := norm_nonneg (fun i => f i x)
      have hx0 := sq_nonneg ‖x‖
      nlinarith [mul_nonneg hM0 hn]

end Release061

end

end OAI
