import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dual.Lemmas
import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness.DualQuotientRows

noncomputable section

open Module
open UniqueGamesTheorem.Foundations.Games

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

def quotientRowEquiv (W : Submodule 𝕜 E) :
    Module.Dual 𝕜 (E ⧸ W) ≃ₗ[𝕜] W.dualAnnihilator :=
  W.dualQuotEquivDualAnnihilator

@[simp]
theorem quotientRowEquiv_val (W : Submodule 𝕜 E) (row : Module.Dual 𝕜 (E ⧸ W)) :
    (quotientRowEquiv W row : Module.Dual 𝕜 E) = row.comp W.mkQ := rfl

theorem codim_dualAnnihilator_eq [FiniteDimensional 𝕜 E] (W : Submodule 𝕜 E) :
    finrank 𝕜 (Module.Dual 𝕜 E ⧸ W.dualAnnihilator) = finrank 𝕜 W := by
  have hquotient := W.dualAnnihilator.finrank_quotient_add_finrank
  have hannihilator := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  rw [Subspace.dual_finrank_eq] at hquotient
  omega

theorem uniform_quotientRowEquiv (W : Submodule 𝕜 E)
    [Fintype (Module.Dual 𝕜 (E ⧸ W))] [Fintype W.dualAnnihilator] :
    (FiniteDistribution.uniform (Module.Dual 𝕜 (E ⧸ W))).pushforward
        (quotientRowEquiv W) = FiniteDistribution.uniform W.dualAnnihilator :=
  UniformLinearImage.uniform_pushforward_linearMap
    (quotientRowEquiv W).toLinearMap (quotientRowEquiv W).surjective

theorem uniform_pullback_rows (W : Submodule 𝕜 E)
    [Fintype (Module.Dual 𝕜 (E ⧸ W))] [Fintype W.dualAnnihilator]
    [Fintype (Module.Dual 𝕜 E)] :
    (FiniteDistribution.uniform (Module.Dual 𝕜 (E ⧸ W))).pushforward W.mkQ.dualMap =
      (FiniteDistribution.uniform W.dualAnnihilator).pushforward
        W.dualAnnihilator.subtype := by
  calc
    _ = ((FiniteDistribution.uniform (Module.Dual 𝕜 (E ⧸ W))).pushforward
        (quotientRowEquiv W)).pushforward W.dualAnnihilator.subtype := by
      rw [FiniteDistribution.pushforward_comp]
      rfl
    _ = _ := by rw [uniform_quotientRowEquiv]

theorem uniform_affine_pullback_rows (W : Submodule 𝕜 E)
    [Fintype (Module.Dual 𝕜 (E ⧸ W))] [Fintype W.dualAnnihilator]
    [Fintype (Module.Dual 𝕜 E)] (offset : Module.Dual 𝕜 E) :
    (FiniteDistribution.uniform (Module.Dual 𝕜 (E ⧸ W))).pushforward
        (fun row => offset + row.comp W.mkQ) =
      (FiniteDistribution.uniform W.dualAnnihilator).pushforward
        (fun row => offset + (row : Module.Dual 𝕜 E)) := by
  calc
    _ = ((FiniteDistribution.uniform (Module.Dual 𝕜 (E ⧸ W))).pushforward
        (quotientRowEquiv W)).pushforward
          (fun row => offset + (row : Module.Dual 𝕜 E)) := by
      rw [FiniteDistribution.pushforward_comp]
      rfl
    _ = _ := by rw [uniform_quotientRowEquiv]


variable {H : Type*} [AddCommGroup H] [Module 𝕜 H] [FiniteDimensional 𝕜 H]

def nativeRowMap (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W) →ₗ[𝕜] H :=
  (Module.evalEquiv 𝕜 H).symm.toLinearMap.comp W.mkQ.dualMap

@[simp]
theorem apply_nativeRowMap (W : Submodule 𝕜 (Module.Dual 𝕜 H))
    (row : Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W)) (q : Module.Dual 𝕜 H) :
    q (nativeRowMap W row) = row (W.mkQ q) := by
  change q ((Module.evalEquiv 𝕜 H).symm (W.mkQ.dualMap row)) = _
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

theorem nativeRowMap_injective (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    Function.Injective (nativeRowMap W) := by
  intro row₁ row₂ h
  apply (quotientRowEquiv W).injective
  apply Subtype.ext
  apply (Module.evalEquiv 𝕜 H).symm.injective
  exact h

theorem range_nativeRowMap (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    LinearMap.range (nativeRowMap W) = W.dualCoannihilator := by
  apply le_antisymm
  · rintro x ⟨row, rfl⟩
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro q hq
    rw [apply_nativeRowMap]
    have hzero : W.mkQ q = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hq
    rw [hzero, map_zero]
  · intro x hx
    let v : W.dualAnnihilator := ⟨Module.evalEquiv 𝕜 H x, hx⟩
    obtain ⟨row, hrow⟩ := (quotientRowEquiv W).surjective v
    refine ⟨row, ?_⟩
    have hvalue := congrArg (fun z : W.dualAnnihilator =>
      (z : Module.Dual 𝕜 (Module.Dual 𝕜 H))) hrow
    change W.mkQ.dualMap row = Module.evalEquiv 𝕜 H x at hvalue
    change (Module.evalEquiv 𝕜 H).symm (W.mkQ.dualMap row) = x
    rw [hvalue, LinearEquiv.symm_apply_apply]

def nativeRowLinear (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W) →ₗ[𝕜] W.dualCoannihilator :=
  (nativeRowMap W).codRestrict W.dualCoannihilator (fun row => by
    rw [← range_nativeRowMap W]
    exact LinearMap.mem_range_self (nativeRowMap W) row)

def nativeRowEquiv (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W) ≃ₗ[𝕜] W.dualCoannihilator :=
  LinearEquiv.ofBijective (nativeRowLinear W) ⟨by
    intro row₁ row₂ h
    exact nativeRowMap_injective W
      (congrArg (fun x : W.dualCoannihilator => (x : H)) h), by
    intro x
    have hx : (x : H) ∈ LinearMap.range (nativeRowMap W) := by
      rw [range_nativeRowMap]
      exact x.property
    obtain ⟨row, hrow⟩ := hx
    exact ⟨row, Subtype.ext hrow⟩⟩

@[simp]
theorem nativeRowEquiv_val (W : Submodule 𝕜 (Module.Dual 𝕜 H))
    (row : Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W)) :
    (nativeRowEquiv W row : H) = nativeRowMap W row := rfl

theorem codim_dualCoannihilator_eq (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    finrank 𝕜 (H ⧸ W.dualCoannihilator) = finrank 𝕜 W := by
  have hquotient := W.dualCoannihilator.finrank_quotient_add_finrank
  have hannihilator := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  omega

theorem uniform_nativeRowEquiv (W : Submodule 𝕜 (Module.Dual 𝕜 H))
    [Fintype (Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W))]
    [Fintype W.dualCoannihilator] :
    (FiniteDistribution.uniform (Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W))).pushforward
        (nativeRowEquiv W) = FiniteDistribution.uniform W.dualCoannihilator :=
  UniformLinearImage.uniform_pushforward_linearMap
    (nativeRowEquiv W).toLinearMap (nativeRowEquiv W).surjective

end
end PerfectCompleteness.DualQuotientRows



namespace PerfectCompleteness.LevelPairCounting

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω : Type*} [Fintype Ω] {d : Nat}

def winCount (win : Fin d → Ω → Bool) (ω : Ω) : ℝ :=
  ∑ i, if win i ω then (1 : ℝ) else 0

def pairProbability (μ : FiniteDistribution Ω) (win : Fin d → Ω → Bool)
    (i j : Fin d) : ℝ :=
  μ.probability (fun ω => win i ω && win j ω)

@[simp] theorem pairProbability_self (μ : FiniteDistribution Ω)
    (win : Fin d → Ω → Bool) (i : Fin d) :
    pairProbability μ win i i = μ.probability (win i) := by
  apply congrArg μ.probability
  funext ω
  cases win i ω <;> rfl

theorem pairProbability_comm (μ : FiniteDistribution Ω)
    (win : Fin d → Ω → Bool) (i j : Fin d) :
    pairProbability μ win i j = pairProbability μ win j i := by
  apply congrArg μ.probability
  funext ω
  cases win i ω <;> cases win j ω <;> rfl

theorem expectation_indicator (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    μ.expectation (fun ω => if event ω then (1 : ℝ) else 0) = μ.probability event := by
  simp [FiniteDistribution.expectation, FiniteDistribution.probability, mul_ite]

theorem expectation_indicator_mul (μ : FiniteDistribution Ω)
    (win : Fin d → Ω → Bool) (i j : Fin d) :
    μ.expectation (fun ω =>
      (if win i ω then (1 : ℝ) else 0) * (if win j ω then (1 : ℝ) else 0)) =
      pairProbability μ win i j := by
  unfold FiniteDistribution.expectation pairProbability FiniteDistribution.probability
  apply Finset.sum_congr rfl
  intro ω _
  cases hi : win i ω <;> cases hj : win j ω <;> simp [hi, hj]

theorem first_moment_eq_sum (μ : FiniteDistribution Ω) (win : Fin d → Ω → Bool) :
    μ.expectation (winCount win) = ∑ i, μ.probability (win i) := by
  unfold winCount
  rw [SmallBias.expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact expectation_indicator μ (win i)

theorem second_moment_eq_sum (μ : FiniteDistribution Ω) (win : Fin d → Ω → Bool) :
    μ.expectation (fun ω => winCount win ω ^ 2) = ∑ i, ∑ j, pairProbability μ win i j := by
  simp_rw [winCount, pow_two, Finset.sum_mul, Finset.mul_sum, SmallBias.expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact expectation_indicator_mul μ win i j

theorem second_moment_decomposition (μ : FiniteDistribution Ω) (win : Fin d → Ω → Bool) :
    μ.expectation (fun ω => winCount win ω ^ 2) = μ.expectation (winCount win) +
      ∑ i, ∑ j, if i = j then 0 else pairProbability μ win i j := by
  rw [second_moment_eq_sum, first_moment_eq_sum]
  calc
    _ = ∑ i, ∑ j,
        ((if i = j then μ.probability (win i) else 0) +
          (if i = j then 0 else pairProbability μ win i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem second_moment_le_mean_add (μ : FiniteDistribution Ω)
    (win : Fin d → Ω → Bool) (c : ℝ) (hc : 0 ≤ c)
    (hpair : ∀ i j, i ≠ j → pairProbability μ win i j ≤ c) :
    μ.expectation (fun ω => winCount win ω ^ 2) ≤
      μ.expectation (winCount win) + (d : ℝ) ^ 2 * c := by
  rw [second_moment_decomposition]
  apply add_le_add (le_refl _)
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, c := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · simpa only [ite_eq_left hij] using hc
      · simpa only [ite_eq_right hij] using hpair i j hij
    _ = (d : ℝ) ^ 2 * c := by
      simp [pow_two, mul_assoc]

theorem exists_level_pair (μ : FiniteDistribution Ω) (win : Fin d → Ω → Bool)
    (ε : ℝ) (hε : 0 < ε)
    (hmean : ε ≤ (𝔼 i : Fin d, μ.probability (win i)))
    (hsize : 4 ≤ (d : ℝ) * ε) :
    ∃ i j : Fin d, i < j ∧
      ε ^ 2 / 2 ≤ μ.probability (fun ω => win i ω && win j ω) := by
  have hfirst : (d : ℝ) * ε ≤ μ.expectation (winCount win) := by
    calc
      (d : ℝ) * ε ≤ (d : ℝ) * (𝔼 i : Fin d, μ.probability (win i)) :=
        mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg d)
      _ = ∑ i, μ.probability (win i) := by
        simpa only [Fintype.card_fin] using
          Fintype.card_mul_expect (fun i : Fin d => μ.probability (win i))
      _ = μ.expectation (winCount win) := (first_moment_eq_sum μ win).symm
  have hfour : 4 ≤ μ.expectation (winCount win) := hsize.trans hfirst
  have hjensen := UniqueGamesTheorem.Foundations.Information.weighted_sum_sq_le
    μ.weight (winCount win) ⟨μ.nonnegative, μ.normalized⟩
  change μ.expectation (winCount win) ^ 2 ≤
    μ.expectation (fun ω => winCount win ω ^ 2) at hjensen
  by_contra hnone
  have hsmall : ∀ i j : Fin d, i < j → pairProbability μ win i j < ε ^ 2 / 2 := by
    intro i j hij
    apply lt_of_not_ge
    intro hprob
    exact hnone ⟨i, j, hij, hprob⟩
  have hpair : ∀ i j : Fin d, i ≠ j → pairProbability μ win i j ≤ ε ^ 2 / 2 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (hsmall i j hlt).le
    · rw [pairProbability_comm μ win i j]
      exact (hsmall j i hgt).le
  have hsecond := second_moment_le_mean_add μ win (ε ^ 2 / 2)
    (div_nonneg (sq_nonneg ε) (by norm_num)) hpair
  have hscaledNonneg : 0 ≤ (d : ℝ) * ε := mul_nonneg (Nat.cast_nonneg d) hε.le
  have hsquare : ((d : ℝ) * ε) ^ 2 ≤ μ.expectation (winCount win) ^ 2 :=
    (sq_le_sq₀ hscaledNonneg (by linarith)).mpr hfirst
  have hproduct : 0 ≤ μ.expectation (winCount win) * (μ.expectation (winCount win) - 4) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

end
end PerfectCompleteness.LevelPairCounting



namespace PerfectCompleteness.LevelPairReserve

open LevelPairCounting
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

theorem exists_pair {Ω : Type*} [Fintype Ω] {d : Nat}
    (μ : FiniteDistribution Ω) (win : Fin d → Ω → Bool)
    (ε : ℝ) (hε : 0 < ε)
    (hmean : ε ≤ (𝔼 i : Fin d, μ.probability (win i)))
    (hsize : 4 ≤ (d : ℝ) * ε) :
    ∃ i j : Fin d, i < j ∧
      2 * ε ^ 2 / 3 ≤ μ.probability (fun ω => win i ω && win j ω) := by
  have hfirst : (d : ℝ) * ε ≤ μ.expectation (winCount win) := by
    calc
      (d : ℝ) * ε ≤ (d : ℝ) * (𝔼 i : Fin d, μ.probability (win i)) :=
        mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg d)
      _ = ∑ i, μ.probability (win i) := by
        simpa only [Fintype.card_fin] using
          Fintype.card_mul_expect (fun i : Fin d => μ.probability (win i))
      _ = μ.expectation (winCount win) := (first_moment_eq_sum μ win).symm
  have hfour : 4 ≤ μ.expectation (winCount win) := hsize.trans hfirst
  have hjensen := UniqueGamesTheorem.Foundations.Information.weighted_sum_sq_le
    μ.weight (winCount win) ⟨μ.nonnegative, μ.normalized⟩
  change μ.expectation (winCount win) ^ 2 ≤
    μ.expectation (fun ω => winCount win ω ^ 2) at hjensen
  by_contra hnone
  have hsmall : ∀ i j : Fin d, i < j → pairProbability μ win i j < 2 * ε ^ 2 / 3 := by
    intro i j hij
    apply lt_of_not_ge
    intro hprob
    exact hnone ⟨i, j, hij, hprob⟩
  have hpair : ∀ i j : Fin d, i ≠ j → pairProbability μ win i j ≤ 2 * ε ^ 2 / 3 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (hsmall i j hlt).le
    · rw [pairProbability_comm μ win i j]
      exact (hsmall j i hgt).le
  have hsecond := second_moment_le_mean_add μ win (2 * ε ^ 2 / 3)
    (by positivity) hpair
  have hscaledNonneg : 0 ≤ (d : ℝ) * ε := mul_nonneg (Nat.cast_nonneg d) hε.le
  have hsquare : ((d : ℝ) * ε) ^ 2 ≤ μ.expectation (winCount win) ^ 2 :=
    (sq_le_sq₀ hscaledNonneg (by linarith)).mpr hfirst
  have hproduct : 0 ≤ μ.expectation (winCount win) * (μ.expectation (winCount win) - 4) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

end
end PerfectCompleteness.LevelPairReserve



namespace PerfectCompleteness.SmallBiasSlice

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.SmallBias

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

def bitSign (b : Bool) : ℝ := if b then -1 else 1

def maskChar (s v : I → Bool) : ℝ :=
  ∏ i, if s i then bitSign (v i) else 1

omit [DecidableEq I] in
@[simp] theorem maskChar_zero (v : I → Bool) :
    maskChar (fun _ => false) v = 1 := by simp [maskChar]

omit [DecidableEq I] in
@[simp] theorem abs_maskChar (s v : I → Bool) : |maskChar s v| = 1 := by
  unfold maskChar
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  cases s i <;> cases v i <;> simp [bitSign]

omit [DecidableEq I] in
theorem maskChar_xor (s t v : I → Bool) :
    maskChar (fun i => Bool.xor (s i) (t i)) v = maskChar s v * maskChar t v := by
  unfold maskChar
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases hs : s i <;> cases ht : t i <;> cases hv : v i <;>
    simp [hs, ht, bitSign]

theorem maskChar_kernel (v t : I → Bool) :
    (∑ s : I → Bool, maskChar s v * maskChar s t) =
      if v = t then (Fintype.card (I → Bool) : ℝ) else 0 := by
  classical
  calc
    _ = ∑ s : I → Bool, ∏ i,
        ((if s i then bitSign (v i) else 1) *
         (if s i then bitSign (t i) else 1)) := by
      simp only [maskChar, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool,
        ((if b then bitSign (v i) else 1) *
         (if b then bitSign (t i) else 1)) :=
      (Fintype.prod_sum (fun (i : I) (b : Bool) =>
        (if b then bitSign (v i) else 1) * (if b then bitSign (t i) else 1))).symm
    _ = ∏ i, (if v i = t i then (2 : ℝ) else 0) := by
      apply Finset.prod_congr rfl
      intro i _
      cases v i <;> cases t i <;> norm_num [Fintype.sum_bool, bitSign]
    _ = _ := by
      rw [Fintype.prod_ite_zero]
      by_cases h : v = t
      · subst t
        simp
      · have h' : ¬ ∀ i, v i = t i := fun h' => h (funext h')
        simp [h, h']

theorem expectation_const_mul (μ : FiniteDistribution Ω) (c : ℝ) (g : Ω → ℝ) :
    μ.expectation (fun x => c * g x) = c * μ.expectation g := by
  unfold FiniteDistribution.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

def sliceNumerator (μ : FiniteDistribution Ω) (A : Ω → I → Bool)
    (t : I → Bool) (g : Ω → ℝ) : ℝ :=
  μ.expectation (fun x => if A x = t then g x else 0)

def sliceMass (μ : FiniteDistribution Ω) (A : Ω → I → Bool) (t : I → Bool) : ℝ :=
  sliceNumerator μ A t (fun _ => 1)

theorem slice_expansion (μ : FiniteDistribution Ω) (A : Ω → I → Bool)
    (t : I → Bool) (g : Ω → ℝ) :
    (Fintype.card (I → Bool) : ℝ) * sliceNumerator μ A t g =
      ∑ s : I → Bool, maskChar s t *
        μ.expectation (fun x => g x * maskChar s (A x)) := by
  classical
  have hpoint : ∀ x, (Fintype.card (I → Bool) : ℝ) *
      (if A x = t then g x else 0) =
      ∑ s : I → Bool, maskChar s t * (g x * maskChar s (A x)) := by
    intro x
    calc
      _ = g x * (if t = A x then (Fintype.card (I → Bool) : ℝ) else 0) := by
        by_cases hx : A x = t
        · simp [hx, mul_comm]
        · simp [hx, Ne.symm hx]
      _ = g x * ∑ s : I → Bool, maskChar s t * maskChar s (A x) := by
        rw [maskChar_kernel]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
  calc
    _ = μ.expectation (fun x => (Fintype.card (I → Bool) : ℝ) *
        (if A x = t then g x else 0)) :=
      (expectation_const_mul μ _ _).symm
    _ = μ.expectation (fun x => ∑ s : I → Bool,
        maskChar s t * (g x * maskChar s (A x))) := by simp only [hpoint]
    _ = _ := by
      rw [expectation_sum]
      apply Finset.sum_congr rfl
      intro s _
      exact expectation_const_mul μ _ _

theorem sliceMass_lower (μ : FiniteDistribution Ω) (A : Ω → I → Bool)
    (t : I → Bool) (biasBound : ℝ) (hb : 0 ≤ biasBound)
    (hbiased : ∀ s : I → Bool, s ≠ (fun _ => false) →
      |μ.expectation (fun x => maskChar s (A x))| ≤ biasBound) :
    1 / (Fintype.card (I → Bool) : ℝ) - biasBound ≤ sliceMass μ A t := by
  classical
  have hterm : ∀ s : I → Bool,
      (if s = (fun _ => false) then (1 : ℝ) else 0) - biasBound ≤
      maskChar s t * μ.expectation (fun x => maskChar s (A x)) := by
    intro s
    by_cases hs : s = (fun _ => false)
    · subst s
      simp only [ite_true, maskChar_zero, expectation_const, one_mul]
      linarith
    · have ha : |maskChar s t * μ.expectation (fun x => maskChar s (A x))| ≤
          biasBound := by
        rw [abs_mul, abs_maskChar, one_mul]
        exact hbiased s hs
      simpa only [ite_eq_right hs, zero_sub] using (abs_le.mp ha).1
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (I → Bool))) =>
    hterm s)
  have hexp := slice_expansion μ A t (fun _ => 1)
  simp only [one_mul] at hexp
  have hN : (0 : ℝ) < Fintype.card (I → Bool) :=
    Nat.cast_pos.mpr Fintype.card_pos
  apply le_of_mul_le_mul_left (a := (Fintype.card (I → Bool) : ℝ)) _ hN
  calc
    _ = 1 - (Fintype.card (I → Bool) : ℝ) * biasBound := by
      field_simp [hN.ne']
    _ ≤ ∑ s : I → Bool, maskChar s t *
        μ.expectation (fun x => maskChar s (A x)) := by
      simpa [Finset.sum_sub_distrib] using hsum
    _ = _ := hexp.symm

theorem slice_coefficient_witness (μ : FiniteDistribution Ω) (A : Ω → I → Bool)
    (t : I → Bool) (g : Ω → ℝ) (threshold : ℝ)
    (hlarge : threshold ≤ |sliceNumerator μ A t g|) :
    ∃ s : I → Bool,
      threshold ≤ |μ.expectation (fun x => g x * maskChar s (A x))| := by
  classical
  have hN : (0 : ℝ) ≤ Fintype.card (I → Bool) := Nat.cast_nonneg _
  have hsum : (∑ _s : I → Bool, threshold) ≤
      ∑ s : I → Bool, |μ.expectation (fun x => g x * maskChar s (A x))| := by
    calc
      _ = (Fintype.card (I → Bool) : ℝ) * threshold := by simp
      _ ≤ (Fintype.card (I → Bool) : ℝ) * |sliceNumerator μ A t g| :=
        mul_le_mul_of_nonneg_left hlarge hN
      _ = |∑ s : I → Bool, maskChar s t *
          μ.expectation (fun x => g x * maskChar s (A x))| := by
        rw [← slice_expansion, abs_mul, abs_of_nonneg hN]
      _ ≤ ∑ s : I → Bool, |maskChar s t *
          μ.expectation (fun x => g x * maskChar s (A x))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, abs_maskChar, one_mul]
  obtain ⟨s, _, hs⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨s, hs⟩


variable {F : Type*} [AddCommMonoid F]

def rowCombination (rows : I → F) (s : I → Bool) : F :=
  ∑ i, if s i then rows i else 0

omit [DecidableEq I] in
@[simp] theorem rowCombination_zero (rows : I → F) :
    rowCombination rows (fun _ => false) = 0 := by simp [rowCombination]

omit [Fintype Ω] [DecidableEq I] in
theorem character_rowCombination (χ : F → Ω → ℝ)
    (hzero : ∀ x, χ 0 x = 1)
    (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (rows : I → F) (A : Ω → I → Bool)
    (hrows : ∀ i x, χ (rows i) x = bitSign (A x i)) (s : I → Bool) (x : Ω) :
    χ (rowCombination rows s) x = maskChar s (A x) := by
  classical
  have hsum : ∀ u : Finset I,
      χ (∑ i ∈ u, if s i then rows i else 0) x =
        ∏ i ∈ u, χ (if s i then rows i else 0) x := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp [hzero]
    | @insert i u hi ih => simp [hi, hadd, ih]
  rw [rowCombination, hsum]
  unfold maskChar
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [hzero, hrows]

theorem coset_coefficient_witness (μ : FiniteDistribution Ω)
    (χ : F → Ω → ℝ) (hzero : ∀ x, χ 0 x = 1)
    (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (rows : I → F) (A : Ω → I → Bool)
    (hrows : ∀ i x, χ (rows i) x = bitSign (A x i))
    (t : I → Bool) (g : Ω → ℝ) (base : F) (threshold : ℝ)
    (hlarge : threshold ≤ |sliceNumerator μ A t (fun x => g x * χ base x)|) :
    ∃ s : I → Bool, threshold ≤
      |μ.expectation (fun x => g x * χ (base + rowCombination rows s) x)| := by
  obtain ⟨s, hs⟩ := slice_coefficient_witness μ A t (fun x => g x * χ base x)
    threshold hlarge
  refine ⟨s, ?_⟩
  simpa only [hadd, character_rowCombination χ hzero hadd rows A hrows, mul_assoc] using hs

theorem affine_coset_heavy_witness [Fintype F] (μ : FiniteDistribution Ω)
    (χ : F → Ω → ℝ) (hzero : ∀ x, χ 0 x = 1)
    (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (rows : I → F) (A : Ω → I → Bool)
    (hrows : ∀ i x, χ (rows i) x = bitSign (A x i))
    (hindependent : Function.Injective (rowCombination rows))
    (t : I → Bool) (g : Ω → ℝ) (base : F)
    (rho h0 biasBound : ℝ) (hrho : 0 < rho) (hh0 : 0 < h0)
    (hsize : h0 ≤ 1 / (Fintype.card (I → Bool) : ℝ))
    (hb : 0 ≤ biasBound) (hbsmall : biasBound ≤ h0 / 2)
    (hbias : ∀ a : F, a ≠ 0 → |μ.expectation (χ a)| ≤ biasBound)
    (hconditional : rho / 2 ≤
      |sliceNumerator μ A t (fun x => g x * χ base x) / sliceMass μ A t|) :
    ∃ s : I → Bool,
      base + rowCombination rows s ∈ heavySet μ χ g (rho * h0 / 4) := by
  classical
  have hmaskbias : ∀ s : I → Bool, s ≠ (fun _ => false) →
      |μ.expectation (fun x => maskChar s (A x))| ≤ biasBound := by
    intro s hs
    have hne : rowCombination rows s ≠ 0 := by
      intro hz
      apply hs
      apply hindependent
      simpa using hz
    have h := hbias (rowCombination rows s) hne
    change |μ.expectation (fun x => χ (rowCombination rows s) x)| ≤ biasBound at h
    simpa only [character_rowCombination χ hzero hadd rows A hrows] using h
  have hmass : h0 / 2 ≤ sliceMass μ A t := by
    have h := sliceMass_lower μ A t biasBound hb hmaskbias
    linarith
  have hmasspos : 0 < sliceMass μ A t := by linarith
  have hcond := hconditional
  rw [abs_div, abs_of_pos hmasspos] at hcond
  have hnum := (le_div_iff₀ hmasspos).1 hcond
  have hthreshold : rho * h0 / 4 ≤
      |sliceNumerator μ A t (fun x => g x * χ base x)| := by
    have hmul := mul_le_mul_of_nonneg_left hmass (show 0 ≤ rho / 2 by linarith)
    nlinarith
  obtain ⟨s, hs⟩ := coset_coefficient_witness μ χ hzero hadd rows A hrows t g base
    (rho * h0 / 4) hthreshold
  refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩


end

end PerfectCompleteness.SmallBiasSlice

end OAI
