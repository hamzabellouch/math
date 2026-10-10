import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

namespace OAI

open Filter Set Topology
open scoped InnerProductSpace

namespace Invariant233.HilbertEnergy

section Normed

variable {E : Type*} [SeminormedAddCommGroup E] {u : ℕ → E}

theorem monotone_norm_sq_of_energy
    (henergy : ∀ m n : ℕ, m ≤ n →
      ‖u n - u m‖ ^ 2 = ‖u n‖ ^ 2 - ‖u m‖ ^ 2) :
    Monotone (fun n => ‖u n‖ ^ 2) := by
  intro m n hmn
  have h := sq_nonneg ‖u n - u m‖
  rw [henergy m n hmn] at h
  linarith

theorem cauchySeq_of_energy
    (hbdd : BddAbove (range (fun n => ‖u n‖ ^ 2)))
    (henergy : ∀ m n : ℕ, m ≤ n →
      ‖u n - u m‖ ^ 2 = ‖u n‖ ^ 2 - ‖u m‖ ^ 2) :
    CauchySeq u := by
  have hmono := monotone_norm_sq_of_energy henergy
  have hc : CauchySeq (fun n => ‖u n‖ ^ 2) :=
    (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hd := hN m hm n hn
  rw [Real.dist_eq] at hd
  rw [dist_eq_norm]
  have hsq : ‖u m - u n‖ ^ 2 < ε ^ 2 := by
    rcases le_total m n with hmn | hnm
    · rw [norm_sub_rev, henergy m n hmn]
      have hle := hmono hmn
      rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hd
      linarith
    · rw [henergy n m hnm]
      exact lt_of_le_of_lt (le_abs_self _) hd
  nlinarith [norm_nonneg (u m - u n)]

theorem exists_limit_of_energy [CompleteSpace E]
    (hbdd : BddAbove (range (fun n => ‖u n‖ ^ 2)))
    (henergy : ∀ m n : ℕ, m ≤ n →
      ‖u n - u m‖ ^ 2 = ‖u n‖ ^ 2 - ‖u m‖ ^ 2) :
    ∃ v : E, Tendsto u atTop (𝓝 v) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_energy hbdd henergy)

theorem limit_norm_sq_eq_iSup
    (hbdd : BddAbove (range (fun n => ‖u n‖ ^ 2)))
    (henergy : ∀ m n : ℕ, m ≤ n →
      ‖u n - u m‖ ^ 2 = ‖u n‖ ^ 2 - ‖u m‖ ^ 2)
    {v : E} (hv : Tendsto u atTop (𝓝 v)) :
    ‖v‖ ^ 2 = ⨆ n, ‖u n‖ ^ 2 :=
  tendsto_nhds_unique (hv.norm.pow 2)
    (tendsto_atTop_ciSup (monotone_norm_sq_of_energy henergy) hbdd)

end Normed

section InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {u : ℕ → E}

theorem energy_of_inner
    (hinner : ∀ m n : ℕ, m ≤ n →
      RCLike.re (inner 𝕜 (u n) (u m)) = ‖u m‖ ^ 2) :
    ∀ m n : ℕ, m ≤ n → ‖u n - u m‖ ^ 2 = ‖u n‖ ^ 2 - ‖u m‖ ^ 2 := by
  intro m n hmn
  rw [@norm_sub_sq 𝕜 E _ _ _ (u n) (u m), hinner m n hmn]
  ring

theorem cauchySeq_of_inner
    (hbdd : BddAbove (range (fun n => ‖u n‖ ^ 2)))
    (hinner : ∀ m n : ℕ, m ≤ n →
      RCLike.re (inner 𝕜 (u n) (u m)) = ‖u m‖ ^ 2) :
    CauchySeq u :=
  cauchySeq_of_energy hbdd (energy_of_inner hinner)

theorem exists_limit_of_inner [CompleteSpace E]
    (hbdd : BddAbove (range (fun n => ‖u n‖ ^ 2)))
    (hinner : ∀ m n : ℕ, m ≤ n →
      RCLike.re (inner 𝕜 (u n) (u m)) = ‖u m‖ ^ 2) :
    ∃ v : E, Tendsto u atTop (𝓝 v) :=
  exists_limit_of_energy hbdd (energy_of_inner hinner)

end InnerProduct

end Invariant233.HilbertEnergy

end OAI
