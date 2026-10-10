import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.QuasiValue

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology

lemma ultra_selector (u : Ultrafilter ℕ) (hu : (u : Filter ℕ)≤atTop)
    (s : ℕ → Set ℕ) (hs : ∀ n, s n ∈ u) :
    ∃ k : ℕ → ℕ, Tendsto k u atTop ∧ ∀ i, k i≠0 → ∀ j≤k i, i∈s j := by
  classical
  let P (i n : ℕ) := ∀ j≤n, i∈s j
  have he (n : ℕ) : ∀ᶠ i in (u : Filter ℕ), P i n := by
    induction n with
    | zero => simpa [P] using hs 0
    | succ n ih =>
      filter_upwards [ih,hs (n+1)] with i hi hin
      intro j hj
      rcases (Nat.le_succ_iff.mp hj) with hj | hj
      · exact hi j hj
      · simpa only [hj] using hin
  let k (i : ℕ) := Nat.findGreatest (P i) i
  refine ⟨k,?_,?_⟩
  · apply tendsto_atTop.2
    intro n
    filter_upwards [he n,hu (eventually_ge_atTop n)] with i hi hin
    exact Nat.le_findGreatest hin hi
  · intro i hi
    exact (Nat.findGreatest_eq_iff.mp (rfl : Nat.findGreatest (P i) i=k i)).2.1 hi

lemma diagonal_real_constraints {A : Type*} [NormedAddCommGroup A]
    (u : Ultrafilter ℕ) (hu : (u : Filter ℕ)≤atTop)
    (F : ℕ → ℕ → A → ℝ) (a : ℕ → ℕ → A) (C : ℝ)
    (ha : ∀ n i, ‖a n i‖≤C)
    (h : ∀ n, ∀ᶠ i in (u : Filter ℕ), ∀ j≤n, |F j i (a n i)|≤1/((n:ℝ)+1)) :
    ∃ b : ℕ → A, (∀ i, ‖b i‖≤C) ∧ ∀ j, Tendsto (fun i => F j i (b i)) u (𝓝 0) := by
  let s (n : ℕ) := {i | ∀ j≤n, |F j i (a n i)|≤1/((n:ℝ)+1)}
  obtain ⟨k,hk,hgood⟩ := ultra_selector u hu s h
  refine ⟨fun i => a (k i) i,fun i => ha _ _,?_⟩
  intro j
  have hbound : ∀ᶠ i in (u : Filter ℕ), |F j i (a (k i) i)|≤1/((k i:ℝ)+1) := by
    filter_upwards [hk (eventually_ge_atTop (max j 1))] with i hi
    have hik : max j 1≤k i := hi
    exact hgood i (by omega) (k i) le_rfl j (by omega)
  apply squeeze_zero_norm' _ ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hk)
  simpa only [Real.norm_eq_abs,Function.comp_apply] using hbound


end KaplanskyConsequences.QuasiValue

end

end OAI
