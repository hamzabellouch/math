import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology Interval ContDiff

namespace SmoothLocal.ODE

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_continuousMap_of_eval
    {a b : ℝ} {F P : ℝ → C(X, E)}
    (hP : ContinuousOn P (Ioo a b))
    (hpoint : ∀ t ∈ Ioo a b, ∀ x : X,
      HasDerivAt (fun s => F s x) (P t x) t)
    {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt F (P t) t := by
  have hmeas : StronglyMeasurableAtFilter P (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hP t ht
  have hprim : HasDerivAt (fun y => F t + ∫ s in t..y, P s) (P t) t :=
    (intervalIntegral.integral_hasDerivAt_right
      (IntervalIntegrable.refl : IntervalIntegrable P volume t t)
      hmeas (hP.continuousAt (Ioo_mem_nhds ht.1 ht.2))).const_add (F t)
  have heq : F =ᶠ[𝓝 t] (fun y => F t + ∫ s in t..y, P s) := by
    apply Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2)
    intro y hy
    have hseg : uIcc t y ⊆ Ioo a b := by
      intro s hs
      exact ⟨lt_of_lt_of_le (lt_min ht.1 hy.1) hs.1,
        lt_of_le_of_lt hs.2 (max_lt ht.2 hy.2)⟩
    have hPI : IntervalIntegrable P volume t y := (hP.mono hseg).intervalIntegrable
    apply ContinuousMap.ext
    intro x
    have hPIx : IntervalIntegrable (fun s => P s x) volume t y :=
      ((ContinuousMap.evalCLM ℝ x).continuous.comp_continuousOn
        (hP.mono hseg)).intervalIntegrable
    have hscalar : (∫ s in t..y, P s x) = F y x - F t x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hpoint s (hseg hs) x) hPIx
    change F y x = F t x + (ContinuousMap.evalCLM ℝ x) (∫ s in t..y, P s)
    rw [← (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm hPI]
    change F y x = F t x + ∫ s in t..y, P s x
    rw [hscalar]
    abel
  exact hprim.congr_of_eventuallyEq heq

theorem continuousMap_smooth_of_eval_derivative_sequence
    {a b : ℝ} (F : ℕ → ℝ → C(X, E))
    (hcont : ∀ n, ContinuousOn (F n) (Ioo a b))
    (hpoint : ∀ n t, t ∈ Ioo a b → ∀ x : X,
      HasDerivAt (fun s => F n s x) (F (n + 1) t x) t) :
    ∀ n, ContDiffOn ℝ ∞ (F n) (Ioo a b) := by
  have hd (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (F n) (F (n + 1) t) t :=
    hasDerivAt_continuousMap_of_eval (hcont (n + 1)) (hpoint n) ht
  have hnat : ∀ m : ℕ, ∀ n : ℕ, ContDiffOn ℝ m (F n) (Ioo a b) := by
    intro m
    induction m with
    | zero =>
        intro n
        simpa only [Nat.cast_zero, contDiffOn_zero] using hcont n
    | succ m hm =>
        intro n
        have hnext : ContDiffOn ℝ ((m : ℕ∞ω) + 1) (F n) (Ioo a b) := by
          rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
          refine ⟨fun t ht => (hd n t ht).differentiableAt.differentiableWithinAt,
            by simp, ?_⟩
          exact (hm (n + 1)).congr (fun t ht => (hd n t ht).deriv)
        simpa only [Nat.cast_add, Nat.cast_one] using hnext
  intro n
  exact contDiffOn_infty.mpr (fun m => hnat m n)

theorem smooth_curry_of_joint_derivative_sequence
    {a b : ℝ} (H : ℕ → ℝ → X → E)
    (hjoint : ∀ n, ContinuousOn (Function.uncurry (H n))
      ((Ioo a b) ×ˢ (Set.univ : Set X)))
    (hpoint : ∀ n t, t ∈ Ioo a b → ∀ x : X,
      HasDerivAt (fun s => H n s x) (H (n + 1) t x) t) :
    ∀ n, ContDiffOn ℝ ∞ (fun t => ContinuousMap.mkD (H n t) 0) (Ioo a b) := by
  let F : ℕ → ℝ → C(X, E) := fun n t => ContinuousMap.mkD (H n t) 0
  have hslice (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) : Continuous (H n t) :=
    (hjoint n).comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨ht, Set.mem_univ _⟩)
  have heval (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : X) : F n t x = H n t x := by
    dsimp only [F]
    rw [ContinuousMap.mkD_of_continuous (hslice n t ht)]
    rfl
  have hcont (n : ℕ) : ContinuousOn (F n) (Ioo a b) :=
    ContinuousMap.continuousOn_mkD_of_uncurry (H n) 0 (hjoint n)
  have hpointF (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : X) :
      HasDerivAt (fun s => F n s x) (F (n + 1) t x) t := by
    have hevent : (fun s => F n s x) =ᶠ[𝓝 t] (fun s => H n s x) :=
      Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2)
        (fun s hs => heval n s hs x)
    rw [heval (n + 1) t ht x]
    exact (hpoint n t ht x).congr_of_eventuallyEq hevent
  exact continuousMap_smooth_of_eval_derivative_sequence F hcont hpointF

end SmoothLocal.ODE

end

end OAI
