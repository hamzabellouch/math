import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import OAI.Geometry.NodalSets.SmoothLimit.UniformSummableIncrements

namespace OAI

noncomputable section

namespace Yau.Analysis

section

open Filter Set
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem finite_jet_summable_tail (f : ℕ → E → F) (g : E → F)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hg : ContDiff ℝ ∞ g)
    (Q : Set E) (hQ : Q ⊆ closure (interior Q))
    (hpoint : ∀ x ∈ interior Q, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (J : ℕ) (b : ℕ → ℝ) (hb : Summable b)
    (hstep : ∀ k, k ≤ J → ∀ n x, x ∈ Q →
      dist (iteratedFDeriv ℝ k (f n) x) (iteratedFDeriv ℝ k (f (n+1)) x) ≤ b n) :
    ∀ k, k ≤ J →
      TendstoUniformlyOn (fun n ↦ iteratedFDeriv ℝ k (f n)) (iteratedFDeriv ℝ k g) atTop Q ∧
      ∀ n x, x ∈ Q → dist (iteratedFDeriv ℝ k (f n) x) (iteratedFDeriv ℝ k g x) ≤
        ∑' j, b (n+j) := by
  classical
  have hex (k : Fin (J+1)) := uniform_limit_of_summable_increments
    (fun n ↦ iteratedFDeriv ℝ k.val (f n)) Q b hb (hstep k.val (by omega))
  choose u hu htail using hex
  have hid (k : ℕ) (hk : k ≤ J) :
      EqOn (iteratedFDeriv ℝ k g) (u ⟨k,by omega⟩) (interior Q) := by
    induction k with
    | zero =>
      intro x hx
      exact tendsto_nhds_unique
        ((continuousMultilinearCurryFin0 ℝ E F).symm.continuous.tendsto (g x) |>.comp (hpoint x hx))
        ((hu ⟨0,by omega⟩).tendsto_at (interior_subset hx))
    | succ k ih =>
      intro x hx
      let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ E) F
      have hd : HasFDerivAt (iteratedFDeriv ℝ k g) (C (u ⟨k+1,by omega⟩ x)) x := by
        apply hasFDerivAt_of_tendstoUniformlyOn isOpen_interior
          (C.isometry.uniformContinuous.comp_tendstoUniformlyOn
            ((hu ⟨k+1,by omega⟩).mono interior_subset))
          (f := fun n ↦ iteratedFDeriv ℝ k (f n))
        · intro n y hy
          exact ((hf n).differentiable_iteratedFDeriv
            (by exact_mod_cast (show (k:ℕ∞) < ⊤ from WithTop.coe_lt_top k)) y).hasFDerivAt
        · intro y hy
          rw [ih (by omega) hy]
          exact (hu ⟨k,by omega⟩).tendsto_at (interior_subset hy)
        · exact hx
      rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,hd.fderiv]
      exact C.symm_apply_apply _
  intro k hk
  have hc : ContinuousOn (u ⟨k,by omega⟩) Q := (hu ⟨k,by omega⟩).continuousOn
    (Filter.Frequently.of_forall (fun n ↦ ((hf n).continuous_iteratedFDeriv
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).continuousOn))
  have he : EqOn (iteratedFDeriv ℝ k g) (u ⟨k,by omega⟩) Q :=
    (hid k hk).of_subset_closure
      (hg.continuous_iteratedFDeriv (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).continuousOn
      hc interior_subset hQ
  refine ⟨(hu ⟨k,by omega⟩).congr_right he.symm,?_⟩
  intro n x hx
  rw [he hx]
  exact htail ⟨k,by omega⟩ n x hx

end

open Filter Set
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem smooth_limit_of_summable_jets (f : ℕ → E → F)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (S : Set E) (hS : IsOpen S)
    (b : ℕ → ℕ → ℝ) (hb : ∀ k, Summable (b k))
    (hstep : ∀ k n x, x ∈ S →
      dist (iteratedFDeriv ℝ k (f n) x) (iteratedFDeriv ℝ k (f (n+1)) x) ≤ b k n) :
    ∃ g : E → F, ContDiffOn ℝ ∞ g S ∧
      ∀ k, TendstoUniformlyOn (fun n ↦ iteratedFDeriv ℝ k (f n))
        (iteratedFDeriv ℝ k g) atTop S := by
  classical
  have hex (k : ℕ) := uniform_limit_of_summable_increments
    (fun n ↦ iteratedFDeriv ℝ k (f n)) S (b k) (hb k) (hstep k)
  choose u hu htail using hex
  let curry (k : ℕ) := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ E) F
  have hc (k : ℕ) : ContinuousOn (u k) S :=
    (hu k).continuousOn (Filter.Frequently.of_forall (fun n ↦
      ((hf n).continuous_iteratedFDeriv (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).continuousOn))
  have hd (k : ℕ) (x : E) (hx : x ∈ S) :
      HasFDerivAt (u k) (curry k (u (k+1) x)) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn hS
      ((curry k).isometry.uniformContinuous.comp_tendstoUniformlyOn (hu (k+1)))
      (f := fun n ↦ iteratedFDeriv ℝ k (f n))
    · intro n y hy
      exact ((hf n).differentiable_iteratedFDeriv (by exact_mod_cast
        (show (k:ℕ∞) < ⊤ from WithTop.coe_lt_top k)) y).hasFDerivAt
    · intro y hy
      exact (hu k).tendsto_at hy
    · exact hx
  have hsmooth (m : ℕ) : ∀ k, ContDiffOn ℝ m (u k) S := by
    induction m with
    | zero => intro k; exact contDiffOn_zero.mpr (hc k)
    | succ m ih =>
      intro k
      rw [show ((m+1:ℕ):ℕ∞ω) = (m:ℕ∞ω)+1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen hS]
      refine ⟨fun x hx ↦ (hd k x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
      apply ((curry k).contDiff.comp_contDiffOn (ih (k+1))).congr
      intro x hx
      exact (hd k x hx).fderiv
  let ev := (continuousMultilinearCurryFin0 ℝ E F)
  let g : E → F := fun x ↦ ev (u 0 x)
  have hg : ContDiffOn ℝ ∞ g S :=
    ev.contDiff.comp_contDiffOn (contDiffOn_infty.mpr (fun m ↦ hsmooth m 0))
  have hid (k : ℕ) : EqOn (iteratedFDeriv ℝ k g) (u k) S := by
    induction k with
    | zero =>
      intro x hx
      change ev.symm (ev (u 0 x)) = u 0 x
      exact ev.symm_apply_apply _
    | succ k ih =>
      intro x hx
      rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
      have he : iteratedFDeriv ℝ k g =ᶠ[𝓝 x] u k :=
        Filter.mem_of_superset (hS.mem_nhds hx) (fun y hy ↦ ih hy)
      rw [he.fderiv_eq,(hd k x hx).fderiv]
      exact (curry k).symm_apply_apply _
  refine ⟨g,hg,?_⟩
  intro k
  exact (hu k).congr_right (fun x hx ↦ (hid k hx).symm)

end Yau.Analysis

end

end OAI
