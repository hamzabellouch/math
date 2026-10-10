import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

section
section IntroDependency0
section GrowthDependency0
namespace Ostmann.Dirichlet
open Finset MeasureTheory
open scoped Fin.NatCast

theorem sum_character_period_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ k ∈ range q, χ (k : ZMod q) = 0 := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  have heq : ∀ a : Fin q, (ZMod.finEquiv q).toEquiv a = (a : ℕ) := by
    intro a
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
      change a = ((a : ℕ) : Fin (q + 1))
      exact (Fin.cast_val_eq_self a).symm
  have hsum := Equiv.sum_comp (ZMod.finEquiv q).toEquiv (fun a => χ a)
  simpa only [heq, MulChar.sum_eq_zero_of_ne_one hχ] using hsum

end Ostmann.Dirichlet
end GrowthDependency0
end IntroDependency0
end

section
section IntroDependency0
section GrowthDependency0
namespace Ostmann.Dirichlet
open Finset MeasureTheory
open scoped Fin.NatCast

theorem norm_sum_character_range_lt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, χ (k : ZMod q)‖ < q := by
  classical
  have hperiod : Function.Periodic (fun n => ∑ k ∈ range n, χ (k : ZMod q)) q := by
    intro n
    change (∑ k ∈ range (n + q), χ (k : ZMod q)) = ∑ k ∈ range n, χ (k : ZMod q)
    rw [Nat.add_comm n q, Finset.sum_range_add, sum_character_period_eq_zero χ hχ]
    simp
  rw [← hperiod.map_mod_nat n]
  have hbound : ‖∑ k ∈ range (n % q), χ (k : ZMod q)‖ ≤ (n % q : ℕ) := by
    calc
      _ ≤ ∑ k ∈ range (n % q), ‖χ (k : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range (n % q), (1 : ℝ) := sum_le_sum fun k _ => χ.norm_le_one k
      _ = (n % q : ℕ) := by simp
  exact hbound.trans_lt (by exact_mod_cast Nat.mod_lt n (NeZero.pos q))

end Ostmann.Dirichlet
end GrowthDependency0
end IntroDependency0
end

section
section IntroDependency0
section GrowthDependency0
namespace Ostmann.Dirichlet
open Finset MeasureTheory
open scoped Fin.NatCast

theorem norm_sum_character_Icc_lt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, χ (k : ZMod q)‖ < q := by
  have hzero : χ 0 = 0 := χ.map_zero' (hχ ∘ χ.level_one')
  have hbound := norm_sum_character_range_lt χ hχ (n + 1)
  rw [sum_range_eq_add_Ico _ (Nat.succ_pos n), Nat.cast_zero, hzero, zero_add,
    Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc] at hbound
  exact hbound

end Ostmann.Dirichlet
end GrowthDependency0
end IntroDependency0
end

section
section IntroDependency0
section GrowthDependency0
namespace Ostmann.Dirichlet
open Finset MeasureTheory
open scoped Fin.NatCast

theorem isBigO_sum_character_Icc_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => ∑ k ∈ Icc 1 n, χ (k : ZMod q))
      (fun _ => (1 : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨q, Filter.Eventually.of_forall fun n => ?_⟩
  simpa using (norm_sum_character_Icc_lt χ hχ n).le

end Ostmann.Dirichlet
end GrowthDependency0
end IntroDependency0
end

section
section IntroDependency0
section GrowthDependency0
namespace Ostmann.Dirichlet
open Finset MeasureTheory
open scoped Fin.NatCast

theorem mellin_partial_sum_neg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) (-s) =
      ∫ t : ℝ in Set.Ioi 1,
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Set.Ici_subset_Ioi.mpr zero_lt_one) ?_]
  · rw [integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [smul_eq_mul, neg_add, sub_eq_add_neg]
    exact mul_comm _ _
  · intro t ht
    have ht1 : t < 1 := lt_of_not_ge ht.2
    simp [Nat.floor_eq_zero.mpr ht1]

end Ostmann.Dirichlet
end GrowthDependency0
end IntroDependency0
end

section
section IntroDependency0
section GrowthDependency0
namespace Ostmann.Dirichlet
open Finset MeasureTheory
open scoped Fin.NatCast

theorem differentiableAt_partial_sum_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => z * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(z + 1))) s := by
  have hmeas : Measurable (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) :=
    (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 1 n, χ (k : ZMod q))).comp
      Nat.measurable_floor
  have hmem : MemLp (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) ⊤ :=
    memLp_top_of_bound hmeas.aestronglyMeasurable q
      (Filter.Eventually.of_forall fun t => (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le)
  have htop : Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) (fun t => t ^ (-(0 : ℝ))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨q, Filter.Eventually.of_forall fun t => ?_⟩
    simpa using (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le
  have hbot : Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q))
      (fun t => t ^ (-(-s.re - 1))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨0, ?_⟩
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono
      nhdsWithin_le_nhds] with t ht
    simp [Nat.floor_eq_zero.mpr ht]
  have hm : DifferentiableAt ℂ
      (mellin (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q))) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      ((hmem.locallyIntegrable le_top).locallyIntegrableOn _) htop
      (by simpa using neg_neg_of_pos hs) hbot
    simp only [Complex.neg_re]
    linarith
  have hfun : (fun z : ℂ => z * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(z + 1))) =
      (fun z : ℂ => z * mellin (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) (-z)) := by
    funext z
    rw [mellin_partial_sum_neg]
  rw [hfun]
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

end Ostmann.Dirichlet
end GrowthDependency0
end IntroDependency0
end

section
section IntroDependency0
section GrowthDependency0
namespace Ostmann.Dirichlet
open Finset MeasureTheory
open scoped Fin.NatCast

theorem LFunction_eq_partial_sum_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = s * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  apply LSeries_eq_mul_integral (r := 0) _ le_rfl (zero_lt_one.trans hs)
  · exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  · simpa using isBigO_sum_character_Icc_one χ hχ

end Ostmann.Dirichlet
end GrowthDependency0
end IntroDependency0
end

section
section IntroDependency0
section GrowthDependency0
namespace Ostmann.Dirichlet
open Finset MeasureTheory
open scoped Topology

theorem LFunction_eq_partial_sum_integral_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = s * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  let U : Set ℂ := {z | 0 < z.re}
  let F := DirichletCharacter.LFunction χ
  let G : ℂ → ℂ := fun z => z * ∫ t : ℝ in Set.Ioi 1,
    (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(z + 1))
  have hUo : IsOpen U := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hUc : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hF : AnalyticOnNhd ℂ F U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUo
  have hG : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    exact (differentiableAt_partial_sum_integral χ hχ hz).differentiableWithinAt
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  have hFG : F =ᶠ[𝓝 (2 : ℂ)] G := by
    filter_upwards [hV] with z hz
    exact LFunction_eq_partial_sum_integral χ hχ hz
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hUc (by norm_num [U]) hFG hs

end Ostmann.Dirichlet
end GrowthDependency0
end IntroDependency0
end

end OAI
