import OAI.Analysis.MassAction.LocalExistence
import OAI.Analysis.MassAction.ODEConcatenation

namespace OAI

universe uE

noncomputable section

open Set Filter
open scoped Topology

namespace Problem326

/-- A compatible sequence of curves on intervals with unbounded right endpoints
has a global extension. Agreement on left half-lines preserves the germ at zero. -/
theorem exists_global_of_compatible_curves
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {a : ℝ} (b : ℕ → ℝ) (hb : Monotone b)
    (hunbounded : ∀ t : ℝ, ∃ n : ℕ, t < b n)
    (x : ℕ → ℝ → E)
    (hcompat : ∀ n, EqOn (x (n + 1)) (x n) (Iic (b n)))
    (hderiv : ∀ n, ∀ t ∈ Icc a (b n), HasDerivAt (x n) (f (x n t)) t) :
    ∃ g : ℝ → E, (∀ n, EqOn g (x n) (Iic (b n))) ∧
      ∀ t, a ≤ t → HasDerivAt g (f (g t)) t := by
  classical
  have hcompat' : ∀ n m, n ≤ m → EqOn (x m) (x n) (Iic (b n)) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ m hnm ih =>
      intro t ht
      exact (hcompat m (le_trans ht (hb hnm))).trans (ih ht)
  choose index hindex using hunbounded
  let g : ℝ → E := fun t => x (index t) t
  have heq : ∀ n, EqOn g (x n) (Iic (b n)) := by
    intro n t ht
    rcases le_total n (index t) with hle | hle
    · exact hcompat' n (index t) hle ht
    · exact (hcompat' (index t) n hle (hindex t).le).symm
  refine ⟨g, heq, ?_⟩
  intro t ht
  let n := index t
  have hn : t < b n := hindex t
  have hevent : g =ᶠ[𝓝 t] x n := by
    filter_upwards [eventually_lt_nhds hn] with s hs
    exact heq n hs.le
  rw [heq n hn.le]
  exact (hderiv n t ⟨ht, hn.le⟩).congr_of_eventuallyEq hevent

/-- Compact trapping turns local existence into a global forward solution.
Only trapping of finite, closed-interval solutions is assumed. -/
theorem exists_global_solution_of_compact_trapping
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} (hf : ContDiff ℝ 1 f) {K : Set E} (hK : IsCompact K)
    (htrap : ∀ z ∈ K, ∀ S : ℝ, 0 ≤ S → ∀ x : ℝ → E,
      x 0 = z →
      (∀ t ∈ Icc (0 : ℝ) S, HasDerivAt x (f (x t)) t) →
      ∀ t ∈ Icc (0 : ℝ) S, x t ∈ K)
    {z : E} (hz : z ∈ K) :
    ∃ g : ℝ → E, g 0 = z ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt g (f (g t)) t) ∧
      ∀ t : ℝ, 0 ≤ t → g t ∈ K := by
  classical
  obtain ⟨T, hT, hlocal⟩ := exists_uniform_local_solution_on_compact hf hK 0
  have hlocal' : ∀ z ∈ K, ∃ x : ℝ → E, x 0 = z ∧
      ∀ t ∈ Icc (-T) T, HasDerivAt x (f (x t)) t := by
    simpa only [zero_sub, zero_add] using hlocal
  have hlocalForward : ∀ z ∈ K, ∃ x : ℝ → E, x 0 = z ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x (f (x t)) t := by
    intro q hq
    obtain ⟨x, hx, hd⟩ := hlocal' q hq
    exact ⟨x, hx, fun t ht => hd t ⟨by linarith [ht.1], ht.2⟩⟩
  let b : ℕ → ℝ := fun n => ((n : ℝ) + 1) * T
  have hb0 : ∀ n, 0 < b n := by
    intro n
    dsimp [b]
    positivity
  have hbsucc : ∀ n, b (n + 1) = b n + T := by
    intro n
    simp [b, Nat.cast_add, Nat.cast_one]
    ring
  let P : ℕ → (ℝ → E) → Prop := fun n x => x 0 = z ∧
    ∀ t ∈ Icc (-T) (b n), HasDerivAt x (f (x t)) t
  have hstart : ∃ x, P 0 x := by
    simpa [P, b] using hlocal' z hz
  have hstep : ∀ n x, P n x → ∃ y, P (n + 1) y ∧ EqOn y x (Iic (b n)) := by
    intro n x hx
    have hmem : x (b n) ∈ K := by
      apply htrap z hz (b n) (hb0 n).le x hx.1
      · exact fun t ht => hx.2 t ⟨by linarith [ht.1], ht.2⟩
      · exact ⟨(hb0 n).le, le_rfl⟩
    obtain ⟨y, heq, hdy⟩ := exists_extend_solution_on_Icc hlocalForward hx.2 hmem
    refine ⟨y, ⟨?_, ?_⟩, heq⟩
    · exact (heq (hb0 n).le).trans hx.1
    · simpa only [hbsucc n] using hdy
  let start : {x // P 0 x} := ⟨Classical.choose hstart, Classical.choose_spec hstart⟩
  let step : ∀ n, {x // P n x} → {x // P (n + 1) x} := fun n x =>
    ⟨Classical.choose (hstep n x.1 x.2), (Classical.choose_spec (hstep n x.1 x.2)).1⟩
  let curves : ∀ n, {x // P n x} := Nat.rec start step
  let x : ℕ → ℝ → E := fun n => (curves n).1
  have hx : ∀ n, P n (x n) := fun n => (curves n).2
  have hcompat : ∀ n, EqOn (x (n + 1)) (x n) (Iic (b n)) := by
    intro n
    exact (Classical.choose_spec (hstep n (curves n).1 (curves n).2)).2
  have hb : Monotone b := by
    intro n m hnm
    dsimp [b]
    apply mul_le_mul_of_nonneg_right _ hT.le
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hunbounded : ∀ t : ℝ, ∃ n : ℕ, t < b n := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt (t / T)
    refine ⟨n, ?_⟩
    have ht : t < (n : ℝ) * T := (div_lt_iff₀ hT).mp hn
    dsimp [b]
    nlinarith
  obtain ⟨g, heq, hd⟩ := exists_global_of_compatible_curves b hb hunbounded x hcompat
    (fun n => (hx n).2)
  refine ⟨g, (heq 0 (hb0 0).le).trans (hx 0).1, ?_, ?_⟩
  · intro t ht
    exact hd t (by linarith)
  · intro t ht
    exact htrap z hz t ht g ((heq 0 (hb0 0).le).trans (hx 0).1)
      (fun s hs => hd s (by linarith [hs.1])) t ⟨ht, le_rfl⟩

end Problem326

end

end OAI
