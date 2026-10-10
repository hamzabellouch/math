import Mathlib
import OAI.MeasureTheory.Falconer.Angular.AngularBinKernel
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasure

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set Metric
open scoped ContDiff Topology

lemma coord_norm_boundND {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hr : 0 ≤ r) (hx : ∀ i, |x i| ≤ r) : ‖x‖ ≤ (d+1:ℝ)*r := by
  have hs : ‖x‖^2 ≤ (d:ℝ)*r^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin d, r^2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.norm_eq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hr).mpr (hx i)
      _ = _ := by simp
  have hd : (d:ℝ) ≤ (d+1:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) hr)).mp
  calc
    _ ≤ (d:ℝ)*r^2 := hs
    _ ≤ (d+1:ℝ)^2*r^2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
    _ = _ := by ring

noncomputable def tensorCapKernelND (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, PlanarFalconer.angularBinKernel (x i)

lemma tensorCapKernelND_contDiff (d : ℕ) : ContDiff ℝ ∞ (tensorCapKernelND d) := by
  apply contDiff_prod
  intro i _
  exact PlanarFalconer.angularBinKernel_contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

lemma tensorCapKernelND_nonneg (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ tensorCapKernelND d x :=
  Finset.prod_nonneg (fun i _ => PlanarFalconer.angularBinKernel_nonneg (x i))

lemma tensorCapKernelND_le_one (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    tensorCapKernelND d x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => PlanarFalconer.angularBinKernel_nonneg (x i))
    (fun i _ => PlanarFalconer.angularBinKernel_le_one (x i))

lemma tensorCapKernelND_support {d : ℕ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : tensorCapKernelND d x ≠ 0) : ∀ i, |x i| ≤ 1 := by
  intro i
  have hn : PlanarFalconer.angularBinKernel (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ _)
  exact abs_le.mpr (PlanarFalconer.angularBinKernel_tsupport (subset_closure hn))

lemma tensorCapKernelND_compact (d : ℕ) : HasCompactSupport (tensorCapKernelND d) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (d+1:ℝ)).of_isClosed_subset
    isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  simpa only [mem_closedBall,dist_zero_right,mul_one] using
    coord_norm_boundND (by norm_num : (0:ℝ) ≤ 1) (tensorCapKernelND_support hx)

lemma tensorCapKernelND_derivative_bound (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (tensorCapKernelND d) x‖ ≤ C := by
  have hc (k : ℕ) := ((tensorCapKernelND_compact d).iteratedFDeriv k).exists_bound_of_continuous
    ((tensorCapKernelND_contDiff d).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤)))
  choose C hC using hc
  have hC0 (k : ℕ) : 0 ≤ C k := (norm_nonneg _).trans (hC k 0)
  refine ⟨∑ k ∈ Finset.range (m+1), C k,Finset.sum_nonneg (fun k _ => hC0 k),?_⟩
  intro k hk x
  exact (hC k x).trans (Finset.single_le_sum (fun i _ => hC0 i)
    (Finset.mem_range.mpr (by omega)))

noncomputable def tensorCapND {d : ℕ} (δ : ℝ) (a : Fin d → ℤ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  tensorCapKernelND d (δ⁻¹ • x - WithLp.toLp 2 (fun i => (a i : ℝ)))

lemma tensorCapND_apply {d : ℕ} (δ : ℝ) (a : Fin d → ℤ)
    (x : EuclideanSpace ℝ (Fin d)) :
    tensorCapND δ a x = ∏ i, PlanarFalconer.angularBinKernel (δ⁻¹*x i-a i) := rfl

lemma tensorCapND_contDiff {d : ℕ} (δ : ℝ) (a : Fin d → ℤ) :
    ContDiff ℝ ∞ (tensorCapND δ a) :=
  (tensorCapKernelND_contDiff d).comp ((contDiff_id.const_smul (δ⁻¹)).sub contDiff_const)

lemma tensorCapND_derivative_bound (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (a : Fin d → ℤ), 0<δ →
      ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (tensorCapND δ a) x‖ ≤ C*δ⁻¹^k := by
  obtain ⟨C,hC,hb⟩ := tensorCapKernelND_derivative_bound d m
  refine ⟨C,hC,?_⟩
  intro δ a hδ k hk x
  let T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    δ⁻¹ • ContinuousLinearMap.id ℝ _
  let F : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun y => tensorCapKernelND d (y-WithLp.toLp 2 (fun i => (a i:ℝ)))
  have hF : ContDiff ℝ ∞ F := (tensorCapKernelND_contDiff d).comp (contDiff_id.sub contDiff_const)
  have hT : ‖T‖ ≤ δ⁻¹ := by
    dsimp [T]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hδ)]
    exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le
  change ‖iteratedFDeriv ℝ k (F ∘ T) x‖ ≤ _
  rw [T.iteratedFDeriv_comp_right hF x
    (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hT k) (by positivity) hC
  simpa only [F,iteratedFDeriv_comp_sub] using hb k hk (T x-WithLp.toLp 2 (fun i => (a i:ℝ)))

end CurrentFalconer
end
end

end OAI
