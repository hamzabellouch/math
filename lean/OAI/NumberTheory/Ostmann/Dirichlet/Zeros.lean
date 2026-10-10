import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

open Set Filter
open scoped Topology

namespace Ostmann.Dirichlet

def IsNontrivialZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

noncomputable def zeroMultiplicity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  (analyticOrderAt χ.LFunction ρ).toNat

def zerosUpTo {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Set ℂ :=
  {ρ | IsNontrivialZero χ ρ ∧ |ρ.im| ≤ T}

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
include hχ

lemma analyticAt_LFunction (s : ℂ) : AnalyticAt ℂ χ.LFunction s :=
  (DirichletCharacter.differentiable_LFunction hχ).analyticAt s

lemma analyticOrderAt_LFunction_ne_top (s : ℂ) :
    analyticOrderAt χ.LFunction s ≠ ⊤ := by
  intro h
  have hz : χ.LFunction = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
      (analyticAt_LFunction χ hχ)).mp h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
    (s := 1) (by simp) (congrFun hz 1)

lemma zeroMultiplicity_pos {ρ : ℂ} (hρ : χ.LFunction ρ = 0) :
    0 < zeroMultiplicity χ ρ := by
  exact ENat.toNat_pos ((analyticAt_LFunction χ hχ ρ).analyticOrderAt_ne_zero.mpr hρ)
    (analyticOrderAt_LFunction_ne_top χ hχ ρ)

lemma zeroMultiplicity_eq_zero_iff (ρ : ℂ) :
    zeroMultiplicity χ ρ = 0 ↔ χ.LFunction ρ ≠ 0 := by
  constructor
  · intro hm hz
    have := zeroMultiplicity_pos χ hχ hz
    omega
  · intro hz
    simp only [zeroMultiplicity,
      (analyticAt_LFunction χ hχ ρ).analyticOrderAt_eq_zero.mpr hz, ENat.toNat_zero]

lemma finite_zeros_on_compact {K : Set ℂ} (hK : IsCompact K) :
    {ρ ∈ K | χ.LFunction ρ = 0}.Finite := by
  have ha : AnalyticOnNhd ℂ χ.LFunction Set.univ :=
    fun s _ => analyticAt_LFunction χ hχ s
  have hn : χ.LFunction (1 : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)
  have hd := ha.preimage_zero_mem_codiscrete hn
  have hdK : χ.LFunction ⁻¹' {0}ᶜ ∈ codiscreteWithin K :=
    (codiscreteWithin_le_codiscrete_inf_principal K).trans inf_le_left hd
  apply (hK.finite_sdiff_of_mem_codiscreteWithin hdK).subset
  intro ρ hρ
  exact ⟨hρ.1, by simpa using hρ.2⟩

lemma zerosUpTo_finite (T : ℝ) : (zerosUpTo χ T).Finite := by
  apply (finite_zeros_on_compact χ hχ (isCompact_closedBall (0 : ℂ) (1 + |T|))).subset
  intro ρ hρ
  refine ⟨?_, hρ.1.1⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    _ ≤ 1 + |T| := by
      rw [abs_of_pos hρ.1.2.1]
      have := hρ.1.2.2
      have := hρ.2.trans (le_abs_self T)
      linarith

noncomputable def zeroCount (T : ℝ) : ℕ :=
  ∑ ρ ∈ (zerosUpTo_finite χ hχ T).toFinset, zeroMultiplicity χ ρ

lemma zeroCount_mono {S T : ℝ} (hST : S ≤ T) :
    zeroCount χ hχ S ≤ zeroCount χ hχ T := by
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  simp only [Set.Finite.mem_toFinset, zerosUpTo, Set.mem_ofPred_eq] at hρ ⊢
  exact ⟨hρ.1, hρ.2.trans hST⟩

lemma zeroCount_pos_of_zero {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ zerosUpTo χ T) :
    0 < zeroCount χ hχ T := by
  apply (zeroMultiplicity_pos χ hχ hρ.1.1).trans_le
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    ((zerosUpTo_finite χ hχ T).mem_toFinset.mpr hρ)

end Ostmann.Dirichlet

end OAI
