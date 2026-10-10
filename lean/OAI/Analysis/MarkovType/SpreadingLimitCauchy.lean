import Mathlib.Topology.UniformSpace.Real
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Linarith

namespace OAI

open Filter
open scoped Topology

noncomputable section

namespace MarkovSuperreflexivity

variable {E Q : Type*}

theorem cauchySeq_of_dense_lipschitz
    (v : ℕ → E → ℝ) (q : Q → E) (d : E → E → ℝ)
    (hlip : ∀ n x y, |v n x - v n y| ≤ d x y)
    (hdense : ∀ x ε, 0 < ε → ∃ a, d x (q a) < ε)
    (hcauchy : ∀ a, CauchySeq (fun n => v n (q a))) (x : E) :
    CauchySeq (fun n => v n x) := by
  apply Metric.cauchySeq_iff.2
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  obtain ⟨a, ha⟩ := hdense x (ε / 3) hthird
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hcauchy a) (ε / 3) hthird
  refine ⟨N, ?_⟩
  intro m hm n hn

  have hleft : dist (v m x) (v m (q a)) < ε / 3 := by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hlip m x (q a)) ha
  have hright : dist (v n (q a)) (v n x) < ε / 3 := by
    rw [dist_comm, Real.dist_eq]
    exact lt_of_le_of_lt (hlip n x (q a)) ha
  have hmiddle : dist (v m (q a)) (v n (q a)) < ε / 3 := hN m hm n hn
  have htriangle := dist_triangle (v m x) (v m (q a)) (v n x)
  have htriangle' := dist_triangle (v m (q a)) (v n (q a)) (v n x)
  linarith

theorem exists_tendsto_of_dense_lipschitz
    (v : ℕ → E → ℝ) (q : Q → E) (d : E → E → ℝ)
    (hlip : ∀ n x y, |v n x - v n y| ≤ d x y)
    (hdense : ∀ x ε, 0 < ε → ∃ a, d x (q a) < ε)
    (hcauchy : ∀ a, CauchySeq (fun n => v n (q a))) (x : E) :
    ∃ l : ℝ, Tendsto (fun n => v n x) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_of_dense_lipschitz v q d hlip hdense hcauchy x)

def denseLipschitzLimit
    (v : ℕ → E → ℝ) (q : Q → E) (d : E → E → ℝ)
    (hlip : ∀ n x y, |v n x - v n y| ≤ d x y)
    (hdense : ∀ x ε, 0 < ε → ∃ a, d x (q a) < ε)
    (hcauchy : ∀ a, CauchySeq (fun n => v n (q a))) (x : E) : ℝ :=
  Classical.choose (exists_tendsto_of_dense_lipschitz v q d hlip hdense hcauchy x)

theorem tendsto_denseLipschitzLimit
    (v : ℕ → E → ℝ) (q : Q → E) (d : E → E → ℝ)
    (hlip : ∀ n x y, |v n x - v n y| ≤ d x y)
    (hdense : ∀ x ε, 0 < ε → ∃ a, d x (q a) < ε)
    (hcauchy : ∀ a, CauchySeq (fun n => v n (q a))) (x : E) :
    Tendsto (fun n => v n x) atTop
      (𝓝 (denseLipschitzLimit v q d hlip hdense hcauchy x)) :=
  Classical.choose_spec (exists_tendsto_of_dense_lipschitz v q d hlip hdense hcauchy x)

theorem norm_sub_denseLipschitzLimit_lt
    (v : ℕ → E → ℝ) (q : Q → E) (d : E → E → ℝ)
    (hlip : ∀ n x y, |v n x - v n y| ≤ d x y)
    (hdense : ∀ x ε, 0 < ε → ∃ a, d x (q a) < ε)
    (hcauchy : ∀ a, CauchySeq (fun n => v n (q a))) (x : E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      ‖v n x - denseLipschitzLimit v q d hlip hdense hcauchy x‖ < ε := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (tendsto_denseLipschitzLimit v q d hlip hdense hcauchy x) ε hε
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Real.dist_eq, Real.norm_eq_abs] using hN n hn

theorem eventually_norm_sub_denseLipschitzLimit_lt
    (v : ℕ → E → ℝ) (q : Q → E) (d : E → E → ℝ)
    (hlip : ∀ n x y, |v n x - v n y| ≤ d x y)
    (hdense : ∀ x ε, 0 < ε → ∃ a, d x (q a) < ε)
    (hcauchy : ∀ a, CauchySeq (fun n => v n (q a))) (x : E)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ‖v n x - denseLipschitzLimit v q d hlip hdense hcauchy x‖ < ε := by
  obtain ⟨N, hN⟩ := norm_sub_denseLipschitzLimit_lt v q d hlip hdense hcauchy x hε
  exact Filter.eventually_atTop.2 ⟨N, hN⟩

end MarkovSuperreflexivity

end

end OAI
