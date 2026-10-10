import OAI.Probability.MatroidProphet.Reverse.BirthLoss
import OAI.Probability.MatroidProphet.Baseline

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def safeEndpointCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) : ℝ :=
  ∑ i ∈ range (pathHorizon h-1), if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T then 1 else 0

lemma pathHorizon_pos (h : ℕ) : 0 < pathHorizon h := by unfold pathHorizon; omega

theorem safeEndpointCount_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) :
    (((2:ℝ)^12)⁻¹) / 2 ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C)) +
        if d ∈ densityExpansion M hE κ (D h) (M.closure ∅) then 1 else 0 := by
  let H := pathHorizon h
  let f := fun i => bitsExpectation q univ (pathExitSquare M hE κ D G q d h i)
  let g : ℕ → ℝ := fun i => bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
    if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T then 1 else 0))
  have hH : 1 ≤ H := pathHorizon_pos h
  have htime : activation h = -(H:ℤ) := by have ht := activation_add_horizon h; omega
  have hvalid : ∀ i ∈ range (H-1), f i ≤ g i := by
    intro i hi
    exact safeBirth_probability M hE κ D G hG q hq0 hq1 h d hd i (by
      have hi' := mem_range.mp hi
      rw [htime]
      omega)
  have hgap : f (H-1) ≤ 0 := by
    have hb := pathExitSquare_le_birth_probability M hE κ D G hG q hq0 hq1 h d hd (H-1)
    have ht : -((H-1:ℕ):ℤ) = activation h + 1 := by omega
    have hz : bitsExpectation q univ (fun C =>
        if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -((H-1:ℕ):ℤ)
          then 1 else 0) = 0 := by
      rw [ht]
      simp only [nominalBirth_not_activation_succ, ite_false, bitsExpectation_const]
    exact hb.trans_eq hz
  have hbase : f H ≤ if d ∈ densityExpansion M hE κ (D h) (M.closure ∅) then 1 else 0 := by
    have hb := pathExitSquare_le_birth_probability M hE κ D G hG q hq0 hq1 h d hd H
    have heq : bitsExpectation q univ (fun C =>
        if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -(H:ℤ)
          then 1 else 0) = if d ∈ densityExpansion M hE κ (D h) (M.closure ∅) then 1 else 0 := by
      rw [← htime]
      simp only [nominalBirth_baseline_iff M hE κ D _ h d hd, bitsExpectation_const]
    exact hb.trans_eq heq
  have hsplit : (∑ i ∈ range (H+1), f i) = (∑ i ∈ range (H-1), f i) + f (H-1) + f H := by
    have hn : H+1 = (H-1+1)+1 := by omega
    rw [hn, sum_range_succ, sum_range_succ, Nat.sub_add_cancel hH]
  have hsum := path_squared_exit_mass M hE κ D G hG q hq0 hq1 d hd h
  change (((2:ℝ)^12)⁻¹)/2 ≤ ∑ i ∈ range (H+1), f i at hsum
  rw [hsplit] at hsum
  have hfg := sum_le_sum (fun i hi => hvalid i hi)
  have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C)) =
      ∑ i ∈ range (H-1), g i := by
    change bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      ∑ i ∈ range (H-1), if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T then 1 else 0)) = _
    simp_rw [bitsExpectation_sum]
    rfl
  rw [heq]
  linarith

noncomputable def safeCountBeforeParity (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) : ℝ :=
  ∑ d ∈ I, safeEndpointCount M hE κ D G h d C T

omit [Fintype α] [DecidableEq α] in
lemma indep_not_loop (M : Matroid α) (I : Finset α) (hI : M.Indep (I : Set α))
    {d : α} (hd : d ∈ I) : d ∉ M.closure ∅ := by
  intro he
  exact hI.notMem_closure_sdiff_of_mem hd (M.closure_subset_closure (Set.empty_subset _) he)

theorem safeCountBeforeParity_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (I : Finset α) (hI : M.Indep (I : Set α)) :
    (((2:ℝ)^12)⁻¹) / 2 * I.card - (D h).ncard / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C)) := by
  let Q := densityExpansion M hE κ (D h) (M.closure ∅)
  have hsum := sum_le_sum (fun d hd => safeEndpointCount_lower M hE κ D G hG q hq0 hq1 h d (indep_not_loop M I hI hd))
  have hpre : bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C)) =
      ∑ d ∈ I, bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C)) := by
    change bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      ∑ d ∈ I, safeEndpointCount M hE κ D G h d C T)) = _
    simp_rw [bitsExpectation_sum]
  have hcount : (∑ d ∈ I, if d ∈ Q then (1:ℝ) else 0) = ((I.filter (fun d => d ∈ Q)).card : ℝ) := by
    simp
  have hset : ((I.filter (fun d => d ∈ Q) : Finset α) : Set α) = (I : Set α) ∩ Q := by
    ext d
    simp
  have hb := baseline_independent_count M hE κ (D h) (I : Set α) hI
  change κ * ((I : Set α) ∩ Q).ncard ≤ (D h).ncard at hb
  rw [← hset, Set.ncard_coe_finset] at hb
  have hb' : (κ:ℝ) * ((I.filter (fun d => d ∈ Q)).card : ℝ) ≤ ((D h).ncard:ℝ) := by exact_mod_cast hb
  have hκ' : (0:ℝ) < κ := by exact_mod_cast hκ
  have hb'' : ((I.filter (fun d => d ∈ Q)).card : ℝ) ≤ (D h).ncard / (κ:ℝ) := (le_div_iff₀ hκ').mpr (by simpa [mul_comm] using hb')
  rw [sum_add_distrib] at hsum
  change (∑ _ ∈ I, (((2:ℝ)^12)⁻¹)/2) ≤
    (∑ d ∈ I, bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C))) +
      ∑ d ∈ I, if d ∈ Q then (1:ℝ) else 0 at hsum
  rw [hcount, ← hpre] at hsum
  simp only [sum_const, nsmul_eq_mul] at hsum
  linarith

end MatroidProphet

end OAI
