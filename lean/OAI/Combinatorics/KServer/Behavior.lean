import Mathlib
import OAI.Combinatorics.KServer.Basic

namespace OAI

noncomputable section
open scoped BigOperators
namespace KServer
universe u

section Matching
variable {k : ℕ} {X : Type u} [MetricSpace X]

def matchSum (A C : Configuration k X) (π : Equiv.Perm (Fin k)) : ℝ :=
  ∑ i, dist (A i) (C (π i))

lemma exists_minimum_matching (A C : Configuration k X) :
    ∃ π : Equiv.Perm (Fin k), ∀ τ, matchSum A C π  ≤  matchSum A C τ := by
  obtain ⟨π, _, hπ⟩ := Finset.exists_min_image Finset.univ (matchSum A C)
    Finset.univ_nonempty
  exact ⟨π, fun τ => hπ τ (Finset.mem_univ τ)⟩

def matchingPerm (A C : Configuration k X) : Equiv.Perm (Fin k) :=
  (exists_minimum_matching A C).choose

def matching (A C : Configuration k X) : ℝ := matchSum A C (matchingPerm A C)

lemma matching_le (A C : Configuration k X) (π : Equiv.Perm (Fin k)) :
    matching A C  ≤  matchSum A C π :=
  (exists_minimum_matching A C).choose_spec π

lemma matching_nonneg (A C : Configuration k X) : 0  ≤  matching A C := by
  unfold matching matchSum
  exact Finset.sum_nonneg fun _ _ => dist_nonneg

lemma matching_self (A : Configuration k X) : matching A A = 0 := by
  apply le_antisymm _ (matching_nonneg _ _)
  simpa [matchSum] using matching_le A A (Equiv.refl _)

lemma matching_triangle (A C D : Configuration k X) :
    matching A D  ≤  matching A C + matching C D := by
  let π := matchingPerm A C
  let τ := matchingPerm C D
  calc
    matching A D  ≤  matchSum A D (π.trans τ) := matching_le _ _ _
    _  ≤  ∑ i, (dist (A i) (C (π i)) + dist (C (π i)) (D (τ (π i)))) := by
      apply Finset.sum_le_sum
      intro i _
      exact dist_triangle _ _ _
    _ = matching A C + matching C D := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp π (fun i => dist (C i) (D (τ i)))]
      rfl

lemma matching_symmetric (A C : Configuration k X) : matching A C = matching C A := by
  have h (A C : Configuration k X) : matching A C  ≤  matching C A := by
    let π := matchingPerm C A
    calc
      matching A C  ≤  matchSum A C π.symm := matching_le _ _ _
      _ = matching C A := by
        unfold matchSum matching
        rw [← Equiv.sum_comp π (fun i => dist (A i) (C (π.symm i)))]
        simp only [Equiv.symm_apply_apply, dist_comm]
        rfl
  exact le_antisymm (h _ _) (h _ _)

lemma matchSum_serve (A C : Configuration k X) (π : Equiv.Perm (Fin k))
    (i : Fin k) (r : X) (hr : C (π i) = r) :
    dist (A i) r + matchSum (serve A i r) C π = matchSum A C π := by
  classical
  unfold matchSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ (fun j => dist (A j) (C (π j))) (Finset.mem_univ i)]
  have he : (∑ j ∈ Finset.univ.erase i, dist ((serve A i r) j) (C (π j))) =
      ∑ j ∈ Finset.univ.erase i, dist (A j) (C (π j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [serve, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he]
  simp [serve, hr, add_comm]

/-- A causal minimum-matching choice. Repeated actual and virtual positions are
retained: only the permutation of occurrence labels is used. -/
def lazyChoice (A C : Configuration k X) (r : X) (hc : ∃ i, C i = r) : Fin k := by
  classical
  exact if ha : ∃ i, A i = r then ha.choose else (matchingPerm A C).symm hc.choose

lemma lazyChoice_covered (A C : Configuration k X) (r : X) (hc : ∃ i, C i = r)
    (ha : ∃ i, A i = r) : A (lazyChoice A C r hc) = r := by
  simp only [lazyChoice, dite_eq_left ha]
  exact ha.choose_spec

lemma lazyChoice_cost (A C : Configuration k X) (r : X) (hc : ∃ i, C i = r) :
    dist (A (lazyChoice A C r hc)) r +
      matching (serve A (lazyChoice A C r hc) r) C  ≤  matching A C := by
  classical
  by_cases ha : ∃ i, A i = r
  · have he := lazyChoice_covered A C r hc ha
    have hserve : serve A (lazyChoice A C r hc) r = A := by
      ext j
      by_cases hj : j = lazyChoice A C r hc
      · subst j; simp [serve, he]
      · simp only [serve, Function.update_of_ne hj]
    simp [he, hserve]
  · let i := (matchingPerm A C).symm hc.choose
    have hi : C (matchingPerm A C i) = r := by
      simpa only [i, Equiv.apply_symm_apply] using hc.choose_spec
    simp only [lazyChoice, dite_eq_right ha]
    calc
      dist (A i) r + matching (serve A i r) C
           ≤  dist (A i) r + matchSum (serve A i r) C (matchingPerm A C) :=
        add_le_add_right (matching_le _ _ _) _
      _ = matching A C := matchSum_serve A C _ i r hi

end Matching


/-- Expected continuation from a specified (possibly null) history. -/
def continuationCost {k : ℕ} {X : Type u} [MetricSpace X]
    (A : Policy k X) (s : Configuration k X) (h : List (X × Fin k)) (σ : List X) : ℝ :=
  ∑ j : Fin σ.length → Fin k, pathProbability A h σ j * serviceCost s σ j

lemma continuationCost_nil {k : ℕ} {X : Type u} [MetricSpace X]
    (A : Policy k X) (s : Configuration k X) (h : List (X × Fin k)) :
    continuationCost A s h [] = 0 := by simp [continuationCost, serviceCost]

lemma continuationCost_cons {k : ℕ} {X : Type u} [MetricSpace X]
    (A : Policy k X) (s : Configuration k X) (h : List (X × Fin k))
    (r : X) (σ : List X) :
    continuationCost A s h (r :: σ) =
      ∑ i : Fin k, (A h r).val i *
        (dist (s i) r + continuationCost A (serve s i r) (h ++ [(r,i)]) σ) := by
  change (∑ j : Fin (σ.length + 1) → Fin k,
    pathProbability A h (r :: σ) j * serviceCost s (r :: σ) j) = _
  rw [sum_labelStrings]
  simp only [pathProbability, serviceCost, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  change (∑ j : Fin σ.length → Fin k, pathProbability A (h ++ [(r,i)]) σ j) *
    dist (s i) r + continuationCost A (serve s i r) (h ++ [(r,i)]) σ = _
  rw [pathProbability_sum, one_mul]

section CausalSimulation
variable {k : ℕ} {X : Type u} [MetricSpace X]
variable (start : Configuration k X) (C : List X → Configuration k X)
variable (hcover : ∀ h r, ∃ i, C (h ++ [r]) i = r)

def lazySimulation : Policy k X := fun h r =>
  pureDistribution (lazyChoice (configurationAfter start h)
    (C (h.map Prod.fst ++ [r])) r (hcover (h.map Prod.fst) r))

lemma lazySimulation_strong : StronglyLazy start (lazySimulation start C hcover) := by
  intro h r ha j hj
  have hc := lazyChoice_covered (configurationAfter start h)
    (C (h.map Prod.fst ++ [r])) r (hcover _ _) ha
  have hne : j ≠ lazyChoice (configurationAfter start h)
      (C (h.map Prod.fst ++ [r])) r (hcover _ _) := by
    intro he; exact hj (he ▸ hc)
  simp [lazySimulation, pureDistribution, hne]

/-- Simulated movement measured by occurrence matching, exactly Section02. -/
def simulatedMovement (C : List X → Configuration k X) (pre : List X) : List X → ℝ
  | [] => 0
  | r :: σ => matching (C pre) (C (pre ++ [r])) + simulatedMovement C (pre ++ [r]) σ

lemma lazySimulation_bound (h : List (X × Fin k)) (σ : List X) :
    continuationCost (lazySimulation start C hcover) (configurationAfter start h) h σ  ≤ 
      matching (configurationAfter start h) (C (h.map Prod.fst)) +
        simulatedMovement C (h.map Prod.fst) σ := by
  classical
  induction σ generalizing h with
  | nil => simpa [simulatedMovement, continuationCost_nil] using (matching_nonneg
      (configurationAfter start h) (C (h.map Prod.fst)))
  | cons r σ ih =>
    let i := lazyChoice (configurationAfter start h) (C (h.map Prod.fst ++ [r])) r
      (hcover _ _)
    rw [continuationCost_cons]
    simp only [lazySimulation, pureDistribution, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    change dist (configurationAfter start h i) r +
      continuationCost (lazySimulation start C hcover)
        (serve (configurationAfter start h) i r) (h ++ [(r,i)]) σ  ≤  _
    have hi := ih (h ++ [(r,i)])
    simp only [configurationAfter_append, List.map_append, List.map_singleton] at hi
    have hstep := lazyChoice_cost (configurationAfter start h) (C (h.map Prod.fst ++ [r]))
      r (hcover _ _)
    have htri := matching_triangle (configurationAfter start h) (C (h.map Prod.fst))
      (C (h.map Prod.fst ++ [r]))
    change dist (configurationAfter start h i) r +
      matching (serve (configurationAfter start h) i r) (C (h.map Prod.fst ++ [r]))  ≤  _ at hstep
    change _  ≤  matching (configurationAfter start h) (C (h.map Prod.fst)) +
      (matching (C (h.map Prod.fst)) (C (h.map Prod.fst ++ [r])) +
        simulatedMovement C (h.map Prod.fst ++ [r]) σ)
    linarith

/-- Actual policy exists, is strongly lazy, and obeys the matching potential bound
for every finite horizon under one common causal rule. No distributional input
or future knowledge is used. This is the deterministic/private-seed kernel of
source `lem:lazy-simulation`. -/
theorem causal_lazy_simulation :
    StronglyLazy start (lazySimulation start C hcover) ∧
      ∀ σ, expectedCost (lazySimulation start C hcover) start σ  ≤ 
        matching start (C []) + simulatedMovement C [] σ := by
  constructor
  · exact lazySimulation_strong start C hcover
  · intro σ
    simpa only [configurationAfter, List.foldl_nil, List.map_nil,
      continuationCost, expectedCost] using lazySimulation_bound start C hcover [] σ

end CausalSimulation

section OfflineComparison
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

omit [NeZero k] in
lemma optimalCost_le_service (s : Configuration k X) (σ : List X)
    (j : Fin σ.length → Fin k) : optimalCost s σ  ≤  serviceCost s σ j := by
  exact csInf_le ⟨0, by rintro _ ⟨w,rfl⟩; exact serviceCost_nonneg _ _ _⟩ ⟨j,rfl⟩

lemma optimalCost_nonneg (s : Configuration k X) (σ : List X) : 0  ≤  optimalCost s σ := by
  exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨w,rfl⟩; exact serviceCost_nonneg _ _ _)

lemma optimalCost_attained (s : Configuration k X) (σ : List X) :
    ∃ j : Fin σ.length → Fin k, serviceCost s σ j = optimalCost s σ := by
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ (serviceCost s σ)
    Finset.univ_nonempty
  refine ⟨j, le_antisymm ?_ (optimalCost_le_service s σ j)⟩
  exact le_csInf (Set.range_nonempty _) (by
    rintro _ ⟨w,rfl⟩
    exact hj w (Finset.mem_univ w))

omit [NeZero k] in
lemma matching_serve_le (C : Configuration k X) (i : Fin k) (r : X) :
    matching C (serve C i r)  ≤  dist (C i) r := by
  classical
  calc
    matching C (serve C i r)  ≤  matchSum C (serve C i r) (Equiv.refl _) := matching_le _ _ _
    _ = dist (C i) r := by
      simp [matchSum, serve, Function.update_apply, apply_ite]

omit [NeZero k] in
/-- Source lazy simulation applied purely pathwise, without a causality premise;
this is the comparison needed for repeated initial tuples. -/
theorem offline_lazy_comparison (A C : Configuration k X) (σ : List X)
    (j : Fin σ.length → Fin k) :
    ∃ w : Fin σ.length → Fin k,
      serviceCost A σ w  ≤  matching A C + serviceCost C σ j := by
  induction σ generalizing A C with
  | nil =>
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    simpa [serviceCost] using matching_nonneg A C
  | cons r σ ih =>
    let C' := serve C (j 0) r
    have hc : ∃ i, C' i = r := ⟨j 0, by simp [C',serve]⟩
    let i := lazyChoice A C' r hc
    obtain ⟨w,hw⟩ := ih (serve A i r) C' (fun t => j t.succ)
    refine ⟨Fin.cons i w, ?_⟩
    simp only [serviceCost, Fin.cons_zero, Fin.cons_succ]
    have hstep := lazyChoice_cost A C' r hc
    have htri := matching_triangle A C C'
    have hmove := matching_serve_le C (j 0) r
    change dist (A i) r + matching (serve A i r) C'  ≤  _ at hstep
    change matching C C'  ≤  _ at hmove
    change dist (A i) r + serviceCost (serve A i r) σ w  ≤ 
      matching A C + (dist (C (j 0)) r + serviceCost C' σ (fun t => j t.succ))
    linarith

/-- Exact source bound `OPT_t  ≤  OPT_s + M(s,t)`; no distinctness is used. -/
theorem optimalCost_change_start (s t : Configuration k X) (σ : List X) :
    optimalCost t σ  ≤  optimalCost s σ + matching s t := by
  obtain ⟨j,hj⟩ := optimalCost_attained s σ
  obtain ⟨w,hw⟩ := offline_lazy_comparison t s σ j
  have ho := optimalCost_le_service t σ w
  rw [hj, matching_symmetric t s] at hw
  linarith

omit [NeZero k] in
lemma optimalCost_le_expectedCost (s : Configuration k X) (A : Policy k X) (σ : List X) :
    optimalCost s σ  ≤  expectedCost A s σ := by
  calc
    optimalCost s σ = (∑ j, pathProbability A [] σ j) * optimalCost s σ := by
      rw [pathProbability_sum, one_mul]
    _ = ∑ j, pathProbability A [] σ j * optimalCost s σ := Finset.sum_mul _ _ _
    _  ≤  expectedCost A s σ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (optimalCost_le_service s σ j) (pathProbability_nonneg _ _ _ _)

end OfflineComparison
def historyProbability {k : ℕ} {X : Type u} (A : Policy k X)
    (pre : List (X × Fin k)) : List (X × Fin k) → ℝ
  | [] => 1
  | (r,i) :: h => (A pre r).val i * historyProbability A (pre ++ [(r,i)]) h

lemma historyProbability_nonneg {k : ℕ} {X : Type u} (A : Policy k X)
    (pre h : List (X × Fin k)) : 0  ≤  historyProbability A pre h := by
  induction h generalizing pre with
  | nil => simp [historyProbability]
  | cons ri h ih => exact mul_nonneg ((A pre ri.1).property.1 _) (ih _)

lemma historyProbability_append {k : ℕ} {X : Type u} (A : Policy k X)
    (pre h h' : List (X × Fin k)) :
    historyProbability A pre (h ++ h') =
      historyProbability A pre h * historyProbability A (pre ++ h) h' := by
  induction h generalizing pre with
  | nil => simp [historyProbability]
  | cons ri h ih =>
    simp only [List.cons_append, historyProbability, ih, List.append_assoc, List.nil_append, Prod.mk.eta]
    ring

lemma historyProbability_singleton {k : ℕ} {X : Type u} (A : Policy k X)
    (pre : List (X × Fin k)) (r : X) (i : Fin k) :
    historyProbability A pre [(r,i)] = (A pre r).val i := by
  simp [historyProbability]


/-! ## Explicit causal realization of finite hidden-state algorithms.
This discharges a policy-existence interface needed both by correlated rounding
and by the fictitious-prefix episode extraction. It is not a competitiveness
premise: the machine below is arbitrary and its behavioral policy is constructed. -/
namespace HiddenMachine
open Finset
variable {k : ℕ} {X : Type u} {S : Type*} [Fintype S]

structure Data (k : ℕ) (X : Type u) (S : Type*) [Fintype S] where
  initial : S → ℝ
  initial_nonneg : ∀ s, 0  ≤  initial s
  initial_sum : ∑ s, initial s = 1
  transition : List (X × Fin k) → X → S → S → ℝ
  transition_nonneg : ∀ h r s s', 0  ≤  transition h r s s'
  transition_sum : ∀ h r s, ∑ s', transition h r s s' = 1
  output : List (X × Fin k) → X → S → S → Fin k
  nullOutput : List (X × Fin k) → X → Fin k

variable (M : Data k X S)

def step (h : List (X × Fin k)) (r : X) (i : Fin k) (w : S → ℝ) : S → ℝ :=
  fun s' => ∑ s, if M.output h r s s'=i then w s*M.transition h r s s' else 0

def evolve (w : S → ℝ) (pre : List (X × Fin k)) : List (X × Fin k) → S → ℝ
  | [] => w
  | (r,i)::h => evolve (step M pre r i w) (pre++[(r,i)]) h

def weights (h : List (X × Fin k)) : S → ℝ := evolve M M.initial [] h

def mass (h : List (X × Fin k)) : ℝ := ∑ s, weights M h s

def outMass (h : List (X × Fin k)) (r : X) (i : Fin k) : ℝ :=
  ∑ s', step M h r i (weights M h) s'

lemma step_nonneg (h : List (X × Fin k)) (r : X) (i : Fin k) (w : S → ℝ)
    (hw : ∀ s, 0  ≤  w s) (s' : S) : 0  ≤  step M h r i w s' := by
  exact sum_nonneg fun s _ => by
    split_ifs
    · exact mul_nonneg (hw s) (M.transition_nonneg _ _ _ _)
    · exact le_rfl

lemma evolve_nonneg (w : S → ℝ) (hw : ∀ s, 0  ≤  w s)
    (pre h : List (X × Fin k)) (s : S) : 0  ≤  evolve M w pre h s := by
  induction h generalizing w pre with
  | nil => exact hw s
  | cons ri h ih => exact ih _ (step_nonneg M pre ri.1 ri.2 w hw) _

lemma weights_nonneg (h : List (X × Fin k)) (s : S) : 0  ≤  weights M h s :=
  evolve_nonneg M M.initial M.initial_nonneg [] h s

lemma mass_nonneg (h : List (X × Fin k)) : 0  ≤  mass M h :=
  sum_nonneg fun s _ => weights_nonneg M h s

lemma outMass_nonneg (h : List (X × Fin k)) (r : X) (i : Fin k) : 0  ≤  outMass M h r i :=
  sum_nonneg fun s _ => step_nonneg M h r i _ (weights_nonneg M h) s

lemma evolve_append (w : S → ℝ) (pre h g : List (X × Fin k)) :
    evolve M w pre (h++g) = evolve M (evolve M w pre h) (pre++h) g := by
  induction h generalizing w pre with
  | nil => simp [evolve]
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    simpa only [List.cons_append,evolve,List.append_assoc,List.singleton_append,List.nil_append] using
      ih (step M pre r i w) (pre++[(r,i)])

lemma weights_append (h : List (X × Fin k)) (r : X) (i : Fin k) :
    weights M (h++[(r,i)]) = step M h r i (weights M h) := by
  rw [weights,evolve_append]
  rfl

lemma mass_append (h : List (X × Fin k)) (r : X) (i : Fin k) :
    mass M (h++[(r,i)]) = outMass M h r i := by
  simp only [mass,weights_append,outMass]

lemma step_sum (h : List (X × Fin k)) (r : X) (w : S → ℝ) :
    (∑ i : Fin k, ∑ s', step M h r i w s') = ∑ s, w s := by
  simp only [step]
  calc
    _ = ∑ s', ∑ s, ∑ i : Fin k,
        if M.output h r s s'=i then w s*M.transition h r s s' else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro s' _
      rw [sum_comm]
    _ = ∑ s', ∑ s, w s*M.transition h r s s' := by simp
    _ = ∑ s, w s * ∑ s', M.transition h r s s' := by
      rw [sum_comm]; simp only [mul_sum]
    _ = ∑ s, w s := by simp only [M.transition_sum,mul_one]

lemma outMass_sum (h : List (X × Fin k)) (r : X) : ∑ i, outMass M h r i=mass M h :=
  step_sum M h r _

lemma outMass_le_mass (h : List (X × Fin k)) (r : X) (i : Fin k) :
    outMass M h r i  ≤  mass M h := by
  rw [←outMass_sum M h r]
  exact single_le_sum (fun j _ => outMass_nonneg M h r j) (mem_univ i)

/-- Null histories are filled by a fixed legal label, not by any future input. -/
def policy : Policy k X := fun h r =>
  if hp : 0 < mass M h then
    ⟨fun i => outMass M h r i / mass M h, by
      constructor
      · intro i; exact div_nonneg (outMass_nonneg M h r i) hp.le
      · rw [←sum_div,outMass_sum,div_self (ne_of_gt hp)]⟩
  else pureDistribution (M.nullOutput h r)

lemma mass_mul_policy (h : List (X × Fin k)) (r : X) (i : Fin k) :
    mass M h * (policy M h r).val i=outMass M h r i := by
  by_cases hp : 0 < mass M h
  · simp only [policy,hp,↓reduceDIte]
    exact mul_div_cancel₀ _ (ne_of_gt hp)
  · have hz : mass M h=0 := le_antisymm (le_of_not_gt hp) (mass_nonneg M h)
    have ho : outMass M h r i=0 := le_antisymm (by simpa [hz] using outMass_le_mass M h r i)
      (outMass_nonneg M h r i)
    simp only [hz,ho,zero_mul]

/-- Exact finite-history law of the realized behavioral policy. -/
theorem history_law (h : List (X × Fin k)) :
    historyProbability (policy M) [] h=mass M h := by
  induction h using List.reverseRecOn with
  | nil => simpa only [historyProbability,mass,weights,evolve] using M.initial_sum.symm
  | append_singleton h ri ih =>
    rw [historyProbability_append,List.nil_append,historyProbability_singleton,ih,
      mass_mul_policy,mass_append]

variable [MetricSpace X]

/-- The machine's literal finite expected movement, prior to forgetting its
private state. Physical configurations are determined by visible histories. -/
def machineCost (start : Configuration k X) (h : List (X × Fin k)) (s : S) :
    List X → ℝ
  | [] => 0
  | r::σ => ∑ s', M.transition h r s s' *
      (dist (configurationAfter start h (M.output h r s s')) r +
        machineCost start (h++[(r,M.output h r s s')]) s' σ)

lemma machineCost_nonneg (start : Configuration k X) (h : List (X × Fin k))
    (s : S) (σ : List X) : 0  ≤  machineCost M start h s σ := by
  induction σ generalizing h s with
  | nil => exact le_rfl
  | cons r σ ih =>
    exact sum_nonneg fun s' _ => mul_nonneg (M.transition_nonneg _ _ _ _)
      (add_nonneg dist_nonneg (ih _ _))

omit [MetricSpace X] in
/-- Weighted branch disintegration; a finite algebraic identity, including
zero-likelihood branches, rather than an assumed conditional kernel. -/
lemma branch_sum (h : List (X × Fin k)) (r : X) (w : S → ℝ)
    (f : Fin k → S → ℝ) :
    (∑ i : Fin k, ∑ s', step M h r i w s' * f i s') =
      ∑ s, w s * ∑ s', M.transition h r s s' * f (M.output h r s s') s' := by
  simp only [step,sum_mul,mul_sum]
  rw [sum_comm]
  conv_lhs => arg 2; ext s'; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro s' _
  simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]
  ring

/-- Forgetting a finite private state preserves *exactly* all finite expected
costs. No finite-horizon policy family is identified without constructing its
single behavioral continuation. -/
theorem realization_cost (start : Configuration k X) (h : List (X × Fin k))
    (σ : List X) :
    mass M h * continuationCost (policy M) (configurationAfter start h) h σ =
      ∑ s, weights M h s * machineCost M start h s σ := by
  induction σ generalizing h with
  | nil => simp [continuationCost_nil,machineCost]
  | cons r σ ih =>
    rw [continuationCost_cons,mul_sum]
    have hh (i : Fin k) :
        mass M h * ((policy M h r).val i *
          (dist (configurationAfter start h i) r +
            continuationCost (policy M) (serve (configurationAfter start h) i r)
              (h++[(r,i)]) σ)) =
        ∑ s', step M h r i (weights M h) s' *
          (dist (configurationAfter start h i) r +
            machineCost M start (h++[(r,i)]) s' σ) := by
      rw [←mul_assoc,mass_mul_policy,mul_add]
      have hf := ih (h++[(r,i)])
      rw [mass_append,weights_append,configurationAfter_append] at hf
      rw [hf]
      simp only [mul_add,sum_add_distrib,←sum_mul,outMass]
    simp_rw [hh]
    rw [branch_sum]
    rfl

/-- The requested externally visible policy, valid on every finite horizon. -/
theorem exists_realization (start : Configuration k X) :
    ∃ A : Policy k X, ∀ σ : List X,
      expectedCost A start σ = ∑ s, M.initial s * machineCost M start [] s σ := by
  refine ⟨policy M,?_⟩
  intro σ
  have h := realization_cost M start [] σ
  simpa only [mass,weights,evolve,M.initial_sum,one_mul,configurationAfter,
    List.foldl_nil,continuationCost,expectedCost] using h


omit [MetricSpace X] in
lemma policy_strong (start : Configuration k X)
    (hout : ∀ h r s s', (∃ i, configurationAfter start h i=r) →
      configurationAfter start h (M.output h r s s')=r)
    (hnull : ∀ h r, (∃ i, configurationAfter start h i=r) →
      configurationAfter start h (M.nullOutput h r)=r) : StronglyLazy start (policy M) := by
  intro h r hc j hj
  have hn : j ≠ M.nullOutput h r := by intro he; exact hj (he ▸ hnull h r hc)
  have ho : outMass M h r j=0 := by
    apply sum_eq_zero
    intro s' _
    apply sum_eq_zero
    intro s _
    have hne : M.output h r s s' ≠ j := by
      intro he; exact hj (he ▸ hout h r s s' hc)
    simp only [hne,ite_false]
  by_cases hp : 0 < mass M h
  · simp only [policy,hp,↓reduceDIte,ho,zero_div]
  · simp only [policy,hp,↓reduceDIte,pureDistribution,hn,ite_false]

variable [NeZero k]

/-- A null-history fallback that satisfies strong laziness at every history. -/
def lazyFallback (start : Configuration k X) (h : List (X × Fin k)) (r : X) : Fin k := by
  classical
  exact if hc : ∃ i, configurationAfter start h i=r then Classical.choose hc else 0

omit [MetricSpace X] in
lemma lazyFallback_covered (start : Configuration k X) (h : List (X × Fin k)) (r : X)
    (hc : ∃ i, configurationAfter start h i=r) :
    configurationAfter start h (lazyFallback start h r)=r := by
  simp only [lazyFallback,hc,↓reduceDIte]
  exact Classical.choose_spec hc

variable (start : Configuration k X) (V : List X → S → Configuration k X)
variable (hcover : ∀ h r s, ∃ i, V (h++[r]) s i=r)

/-- Source's matching simulation, with the entire virtual private state kept.
There is no illegal conditioning of a marginal coupling on realized ancestors. -/
def lazyMachine : Data k X S where
  initial := M.initial
  initial_nonneg := M.initial_nonneg
  initial_sum := M.initial_sum
  transition := M.transition
  transition_nonneg := M.transition_nonneg
  transition_sum := M.transition_sum
  output h r _s s' := lazyChoice (configurationAfter start h) (V (h.map Prod.fst++[r]) s') r
    (hcover (h.map Prod.fst) r s')
  nullOutput := lazyFallback start

lemma lazyMachine_strong : StronglyLazy start (policy (lazyMachine M start V hcover)) := by
  apply policy_strong
  · intro h r s s' hc
    exact lazyChoice_covered _ _ _ _ hc
  · exact lazyFallback_covered start

/-- Virtual movement under exactly the same finite hidden-state experiment. -/
def virtualCost (h : List (X × Fin k)) (s : S) : List X → ℝ
  | [] => 0
  | r::σ => ∑ s', M.transition h r s s' *
      (matching (V (h.map Prod.fst) s) (V (h.map Prod.fst++[r]) s')+
        virtualCost (h++[(r,(lazyMachine M start V hcover).output h r s s')]) s' σ)

lemma lazyMachine_bound (h : List (X × Fin k)) (s : S) (σ : List X) :
    machineCost (lazyMachine M start V hcover) start h s σ  ≤ 
      matching (configurationAfter start h) (V (h.map Prod.fst) s)+
        virtualCost M start V hcover h s σ := by
  induction σ generalizing h s with
  | nil => simpa only [machineCost,virtualCost,add_zero] using matching_nonneg _ _
  | cons r σ ih =>
    let L := lazyMachine M start V hcover
    have hh (s' : S) := ih (h++[(r,L.output h r s s')]) s'
    have hone (s' : S) :
        dist (configurationAfter start h (L.output h r s s')) r +
          machineCost L start (h++[(r,L.output h r s s')]) s' σ  ≤ 
        matching (configurationAfter start h) (V (h.map Prod.fst) s)+
          (matching (V (h.map Prod.fst) s) (V (h.map Prod.fst++[r]) s')+
            virtualCost M start V hcover (h++[(r,L.output h r s s')]) s' σ) := by
      have hi := hh s'
      simp only [configurationAfter_append,List.map_append,List.map_singleton] at hi
      have hc := lazyChoice_cost (configurationAfter start h) (V (h.map Prod.fst++[r]) s') r
        (hcover _ r s')
      have ht := matching_triangle (configurationAfter start h) (V (h.map Prod.fst) s)
        (V (h.map Prod.fst++[r]) s')
      change dist (configurationAfter start h (L.output h r s s')) r +
        matching (serve (configurationAfter start h) (L.output h r s s') r)
          (V (h.map Prod.fst++[r]) s')  ≤  _ at hc
      linarith
    calc
      _  ≤  ∑ s', M.transition h r s s' *
          (matching (configurationAfter start h) (V (h.map Prod.fst) s)+
          (matching (V (h.map Prod.fst) s) (V (h.map Prod.fst++[r]) s')+
            virtualCost M start V hcover (h++[(r,L.output h r s s')]) s' σ)) := by
        exact sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hone s')
          (M.transition_nonneg _ _ _ _)
      _ = _ := by
        simp only [virtualCost,mul_add,sum_add_distrib,←sum_mul,M.transition_sum,one_mul]
        rfl

/-- Fully constructed randomized causal strong-lazy simulation with arbitrary
finite correlated private states and an arbitrary initial virtual mismatch.
It is uniform over all fixed finite request sequences, including all horizons. -/
theorem causal_random_lazy_simulation :
    ∃ A : Policy k X, StronglyLazy start A ∧ ∀ σ : List X,
      expectedCost A start σ  ≤ 
        (∑ s, M.initial s*matching start (V [] s))+
          ∑ s, M.initial s*virtualCost M start V hcover [] s σ := by
  let L := lazyMachine M start V hcover
  refine ⟨policy L,lazyMachine_strong M start V hcover,?_⟩
  intro σ
  have he := realization_cost L start [] σ
  have hb : (∑ s, M.initial s*machineCost L start [] s σ)  ≤ 
      (∑ s, M.initial s*matching start (V [] s))+
        ∑ s, M.initial s*virtualCost M start V hcover [] s σ := by
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro s _
    have h := mul_le_mul_of_nonneg_left (lazyMachine_bound M start V hcover [] s σ)
      (M.initial_nonneg s)
    simpa only [configurationAfter,List.foldl_nil,List.map_nil,mul_add] using h
  have hinit : mass L []=1 := L.initial_sum
  rw [hinit,one_mul] at he
  exact he.trans_le hb

end HiddenMachine
end KServer

namespace KServer
namespace BoundedSimulation
noncomputable section
open Finset
universe u
variable {k : ℕ} [NeZero k] {X : Type u}

/-- Finite private memory, sufficient for a fixed local experiment. The final
policy is extended to all requests; compactness below removes this bound. -/
abbrev Memory (H k : ℕ) := Fin H → Fin k

def labelAt {H : ℕ} (s : Memory H k) (n : ℕ) : Fin k :=
  if h : n<H then s ⟨n,h⟩ else 0

def history {H : ℕ} (h : List X) (s : Memory H k) : List (X × Fin k) :=
  h.mapIdx (fun n r => (r,labelAt s n))

lemma history_append {H : ℕ} (h : List X) (r : X) (s : Memory H k) :
    history (h++[r]) s=history h s++[(r,labelAt s h.length)] := by
  exact List.mapIdx_concat

lemma history_length {H : ℕ} (h : List X) (s : Memory H k) :
    (history h s).length=h.length := List.length_mapIdx

def update {H : ℕ} (s : Memory H k) (n : ℕ) (i : Fin k) : Memory H k := by
  classical
  exact if hn : n<H then Function.update s ⟨n,hn⟩ i else s

lemma labelAt_update {H : ℕ} (s : Memory H k) (n : ℕ) (i : Fin k) (hn : n<H) :
    labelAt (update s n i) n=i := by
  classical
  simp [labelAt,update,hn]

lemma history_update {H : ℕ} (h : List X) (s : Memory H k) (i : Fin k) :
    history h (update s h.length i)=history h s := by
  classical
  apply List.ext_getElem (by simp [history])
  intro n hn hn'
  simp only [history,List.getElem_mapIdx]
  have hn0 : n<h.length := by simpa [history] using hn
  by_cases hH : h.length<H
  · have hnH := hn0.trans hH
    have hne : (⟨n,hnH⟩ : Fin H) ≠ ⟨h.length,hH⟩ := by
      intro he; have heq : n=h.length := congrArg Fin.val he; omega
    simp [labelAt,update,hH,hnH,Function.update_of_ne hne]
  · simp [update,hH]

lemma history_step {H : ℕ} (h : List X) (r : X) (s : Memory H k)
    (i : Fin k) (hh : h.length<H) :
    history (h++[r]) (update s h.length i)=history h s++[(r,i)] := by
  rw [history_append,history_update,labelAt_update s _ i hh]

variable (H : ℕ) (A : Policy k X) (pre : List (X × Fin k))

def transition (h : List (X × Fin k)) (r : X) (s s' : Memory H k) : ℝ :=
  ∑ i : Fin k, if s'=update s h.length i then (A (pre++history (h.map Prod.fst) s) r).val i else 0

lemma transition_sum (h : List (X × Fin k)) (r : X) (s : Memory H k) :
    ∑ s', transition H A pre h r s s'=1 := by
  classical
  simp only [transition]
  rw [Finset.sum_comm]
  simpa using (A (pre++history (h.map Prod.fst) s) r).property.2

lemma transition_integrate (h : List (X × Fin k)) (r : X) (s : Memory H k)
    (f : Memory H k → ℝ) :
    ∑ s', transition H A pre h r s s'*f s'=
      ∑ i : Fin k, (A (pre++history (h.map Prod.fst) s) r).val i * f (update s h.length i) := by
  classical
  simp only [transition,Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp

def machine : HiddenMachine.Data k X (Memory H k) where
  initial s := if s=(fun _=>0) then 1 else 0
  initial_nonneg _ := by split_ifs <;> norm_num
  initial_sum := by classical simp
  transition := transition H A pre
  transition_nonneg h r s s' := by
    classical
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact (A (pre++history (h.map Prod.fst) s) r).property.1 i
    · exact le_rfl
  transition_sum := transition_sum H A pre
  output _ _ _ _ := 0
  nullOutput _ _ := 0

variable (start virtualStart : Configuration k X)

def virtual (h : List X) (s : Memory H k) : Configuration k X :=
  configurationAfter virtualStart (history h s)

lemma virtual_covers (h : List X) (r : X) (s : Memory H k) :
    ∃ i, virtual H virtualStart (h++[r]) s i=r := by
  refine ⟨labelAt s h.length,?_⟩
  simp [virtual,history_append,configurationAfter_append,serve]

lemma virtual_step (h : List X) (r : X) (s : Memory H k)
    (i : Fin k) (hh : h.length<H) :
    virtual H virtualStart (h++[r]) (update s h.length i)=
      serve (virtual H virtualStart h s) i r := by
  simp only [virtual,history_step h r s i hh,configurationAfter_append]

variable [MetricSpace X]

/-- Exact virtual continuation bound, honoring the entire private label history.
In particular the virtual policy is not falsely conditioned only on the real
server positions or on the current request. -/
lemma virtual_cost_bound (h : List (X × Fin k)) (s : Memory H k) (σ : List X)
    (hb : h.length+σ.length ≤ H) :
    HiddenMachine.virtualCost (machine H A pre) start (virtual H virtualStart)
      (virtual_covers H virtualStart) h s σ  ≤ 
    continuationCost A (virtual H virtualStart (h.map Prod.fst) s)
      (pre++history (h.map Prod.fst) s) σ := by
  induction σ generalizing h s with
  | nil => simp [HiddenMachine.virtualCost,continuationCost_nil]
  | cons r σ ih =>
    have hh : h.length<H := by simpa using (show h.length< H by simp only [List.length_cons] at hb; omega)
    rw [HiddenMachine.virtualCost]
    change (∑ s', transition H A pre h r s s' * _)  ≤  _
    rw [transition_integrate,continuationCost_cons]
    apply sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ ((A (pre++history (h.map Prod.fst) s) r).property.1 i)
    let L := HiddenMachine.lazyMachine (machine H A pre) start (virtual H virtualStart)
      (virtual_covers H virtualStart)
    let s' := update s h.length i
    let j := L.output h r s s'
    have hv : virtual H virtualStart (h.map Prod.fst++[r]) s'=
        serve (virtual H virtualStart (h.map Prod.fst) s) i r := by
      simpa [s'] using virtual_step H virtualStart (h.map Prod.fst) r s i (by simpa using hh)
    have hvh : history (h.map Prod.fst++[r]) s'=history (h.map Prod.fst) s++[(r,i)] := by
      simpa [s'] using history_step (h.map Prod.fst) r s i (by simpa using hh)
    have hi := ih (h++[(r,j)]) s' (by
      simp only [List.length_append,List.length_cons,List.length_nil] at *
      omega)
    simp only [List.map_append,List.map_singleton] at hi
    rw [hv,hvh,←List.append_assoc] at hi
    have hm := matching_serve_le (virtual H virtualStart (h.map Prod.fst) s) i r
    change matching (virtual H virtualStart (h.map Prod.fst) s)
      (virtual H virtualStart (h.map Prod.fst++[r]) s') +
      HiddenMachine.virtualCost (machine H A pre) start (virtual H virtualStart)
        (virtual_covers H virtualStart) (h++[(r,j)]) s' σ  ≤  _
    rw [hv]
    exact add_le_add hm hi

/-- Realizes a supplied behavioral policy from a different actual start, up to
any prescribed finite horizon; its construction is causal on all histories.
The bound is uniform in the horizon, permitting the global compactness step. -/
theorem finite_horizon_simulation :
    ∃ B : Policy k X, StronglyLazy start B ∧ ∀ σ : List X, σ.length ≤ H →
      expectedCost B start σ  ≤  matching start virtualStart+
        continuationCost A virtualStart pre σ := by
  obtain ⟨B,hB,hcost⟩ := HiddenMachine.causal_random_lazy_simulation
    (machine H A pre) start (virtual H virtualStart) (virtual_covers H virtualStart)
  refine ⟨B,hB,?_⟩
  intro σ hσ
  have hc := hcost σ
  have hz (s : Memory H k) : virtual H virtualStart [] s=virtualStart := rfl
  have hinit (s : Memory H k) : (machine H A pre).initial s=(if s=(fun _=>0) then 1 else 0) := rfl
  simp only [hinit,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,↓reduceIte,hz] at hc
  refine hc.trans (add_le_add le_rfl ?_)
  simpa only [List.length_nil,zero_add,List.map_nil,history,List.mapIdx_nil,List.append_nil,
    virtual,configurationAfter,List.foldl_nil] using
      virtual_cost_bound H A pre start virtualStart [] (fun _=>0) σ (by simpa using hσ)

/-- One global causal simulator on an arbitrary metric. The finite-memory
constructions above incur the same initial matching, so compactness selects a
single policy valid for every finite horizon. No finiteness of X is required. -/
theorem global_simulation :
    ∃ B : Policy k X, ∀ σ : List X,
      expectedCost B start σ  ≤  matching start virtualStart+
        continuationCost A virtualStart pre σ := by
  apply compact_policy_of_finite_feasibility
  intro F
  let H := F.sup List.length
  obtain ⟨B,_,hB⟩ := finite_horizon_simulation H A pre start virtualStart
  exact ⟨B,fun σ hσ => hB σ (Finset.le_sup hσ)⟩

end
end BoundedSimulation
end KServer

namespace KServer
universe u
section Mixture
variable {k : ℕ} {X : Type u} {Ω : Type*} [Fintype Ω]
variable (w : Ω → ℝ) (hw : ∀ ω, 0  ≤  w ω) (hs : ∑ ω, w ω = 1)
variable (A : Ω → Policy k X)

def mixtureLikelihood (h : List (X × Fin k)) : ℝ :=
  ∑ ω, w ω * historyProbability (A ω) [] h

include hw in
lemma mixtureLikelihood_nonneg (h : List (X × Fin k)) :
    0  ≤  mixtureLikelihood w A h :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (historyProbability_nonneg _ _ _)

include hw in
lemma weightedLikelihood_le (h : List (X × Fin k)) (ω : Ω) :
    w ω * historyProbability (A ω) [] h  ≤  mixtureLikelihood w A h := by
  exact Finset.single_le_sum (fun i _ =>
    mul_nonneg (hw i) (historyProbability_nonneg _ _ _)) (Finset.mem_univ ω)

lemma mixtureLikelihood_append (h : List (X × Fin k)) (r : X) (i : Fin k) :
    mixtureLikelihood w A (h ++ [(r,i)]) =
      ∑ ω, w ω * historyProbability (A ω) [] h * (A ω h r).val i := by
  simp only [mixtureLikelihood, historyProbability_append, List.nil_append,
    historyProbability_singleton]
  congr 1
  funext ω
  ring

variable [NeZero k]

/-- The posterior distribution over the private mixture index is normalized
only at reached histories; all null histories receive the same fixed pure rule. -/
def mixturePolicy : Policy k X := fun h r =>
  if hpos : 0 < mixtureLikelihood w A h then
    ⟨fun i => (∑ ω, w ω * historyProbability (A ω) [] h * (A ω h r).val i) /
      mixtureLikelihood w A h, by
      constructor
      · intro i
        exact div_nonneg (Finset.sum_nonneg fun ω _ =>
          mul_nonneg (mul_nonneg (hw ω) (historyProbability_nonneg _ _ _))
            ((A ω h r).property.1 i)) hpos.le
      · rw [← Finset.sum_div, Finset.sum_comm]
        simp_rw [← Finset.mul_sum, (A _ h r).property.2, mul_one]
        exact div_self hpos.ne'⟩
  else pureDistribution 0

lemma mixturePolicy_recurrence (h : List (X × Fin k)) (r : X) (i : Fin k) :
    mixtureLikelihood w A h * (mixturePolicy w hw A h r).val i =
      mixtureLikelihood w A (h ++ [(r,i)]) := by
  rw [mixtureLikelihood_append]
  by_cases hp : 0 < mixtureLikelihood w A h
  · simp only [mixturePolicy, hp, ↓reduceDIte]
    field_simp
  · have hz : mixtureLikelihood w A h = 0 :=
      le_antisymm (le_of_not_gt hp) (mixtureLikelihood_nonneg w hw A h)
    rw [hz, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro ω _
    have hω : w ω * historyProbability (A ω) [] h = 0 :=
      le_antisymm (by simpa only [hz] using weightedLikelihood_le w hw A h ω)
        (mul_nonneg (hw ω) (historyProbability_nonneg _ _ _))
    rw [hω, zero_mul]

include hs in
lemma historyProbability_mixture (h : List (X × Fin k)) :
    historyProbability (mixturePolicy w hw A) [] h = mixtureLikelihood w A h := by
  induction h using List.reverseRecOn with
  | nil => simpa [historyProbability, mixtureLikelihood] using hs.symm
  | append_singleton h ri ih =>
    rw [historyProbability_append, List.nil_append, historyProbability_singleton, ih]
    exact mixturePolicy_recurrence w hw A h ri.1 ri.2

lemma historyProbability_ofFn {k : ℕ} {X : Type u} (A : Policy k X)
    (pre : List (X × Fin k)) (σ : List X) (j : Fin σ.length → Fin k) :
    historyProbability A pre (List.ofFn fun i => (σ.get i, j i)) =
      pathProbability A pre σ j := by
  induction σ generalizing pre with
  | nil => simp [historyProbability, pathProbability]
  | cons r rs ih =>
    rw [List.ofFn_succ]
    simp only [List.get_eq_getElem, historyProbability, pathProbability]
    exact congrArg ((A pre r).val (j 0) * ·) (ih _ _)

/- Every complete path has exactly the prescribed finite mixture law. -/
include hs in
theorem pathProbability_mixture (σ : List X) (j : Fin σ.length → Fin k) :
    pathProbability (mixturePolicy w hw A) [] σ j =
      ∑ ω, w ω * pathProbability (A ω) [] σ j := by
  rw [← historyProbability_ofFn, historyProbability_mixture w hw hs A]
  simp only [mixtureLikelihood, historyProbability_ofFn]

/- Consequently the full finite cost vector, not just a single input cost,
is the same convex combination under this one horizon-independent policy. -/
include hs in
theorem expectedCost_mixture [MetricSpace X] (s : Configuration k X) (σ : List X) :
    expectedCost (mixturePolicy w hw A) s σ = ∑ ω, w ω * expectedCost (A ω) s σ := by
  simp only [expectedCost, pathProbability_mixture w hw hs A, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Mixture

section Binary
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

/-- One private coin implements a convex combination simultaneously for all inputs. -/
lemma exists_binary_mixture (s : Configuration k X) (A B : Policy k X)
    (a b : ℝ) (ha : 0  ≤  a) (hb : 0  ≤  b) (hab : a + b = 1) :
    ∃ D : Policy k X, ∀ σ, expectedCost D s σ =
      a * expectedCost A s σ + b * expectedCost B s σ := by
  let w : Bool → ℝ := fun i => if i then a else b
  let P : Bool → Policy k X := fun i => if i then A else B
  have hw : ∀ i, 0  ≤  w i := by intro i; cases i <;> simp [w, ha, hb]
  have hs : ∑ i, w i = 1 := by simpa [w, add_comm] using hab
  refine ⟨mixturePolicy w hw P, fun σ => ?_⟩
  simpa [w, P, add_comm] using expectedCost_mixture w hw hs P s σ

end Binary

/-- The finite convex-separation implication used in source Lemma finite-set.
Its premise is an explicit distributional estimate, not an assumed online policy
existence theorem. The lemma itself is an unconditional convex-geometric fact. -/
theorem nonpositive_vector_of_distributional {ι : Type*} [Fintype ι]
    (S : Set (ι → ℝ)) (hne : S.Nonempty) (hcmp : IsCompact S) (hconv : Convex ℝ S)
    (hdist : ∀ w : ι → ℝ, (∀ i, 0  ≤  w i) → (∑ i, w i = 1) →
      ∃ v ∈ S, ∑ i, w i * v i  ≤  0) :
    ∃ v ∈ S, ∀ i, v i  ≤  0 := by
  classical
  by_contra hnot
  let N : Set (ι → ℝ) := {x | ∀ i, x i  ≤  0}
  have hnconv : Convex ℝ N := by
    intro x hx y hy a b ha hb hab i
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx i))
      (mul_nonpos_of_nonneg_of_nonpos hb (hy i))
  have hnclosed : IsClosed N := by
    have he : N = ⋂ i, {x : ι → ℝ | x i  ≤  0} := by ext; simp [N]
    rw [he]
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
  have hdisj : Disjoint N S := by
    rw [Set.disjoint_left]
    intro x hx hxs
    exact hnot ⟨x,hxs,hx⟩
  obtain ⟨f,u,v,hN,huv,hS⟩ :=
    geometric_hahn_banach_closed_compact hnconv hnclosed hconv hcmp hdisj
  have hupos : 0 < u := by simpa using hN 0 (by intro i; exact le_rfl)
  let c : ι → ℝ := fun i => f (Pi.single i 1)
  have hrepr (x : ι → ℝ) : f x = ∑ i, c i * x i := by
    have he : x = ∑ i, x i • (Pi.single i 1 : ι → ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [he]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hc : ∀ i, 0  ≤  c i := by
    intro i
    by_contra hci
    have hcneg : c i < 0 := lt_of_not_ge hci
    let t := (u + 1) / c i
    have ht : t < 0 := div_neg_of_pos_of_neg (by linarith) hcneg
    have hmem : t • (Pi.single i 1 : ι → ℝ) ∈ N := by
      intro j
      by_cases hj : j = i
      · subst j; simpa using ht.le
      · simp [hj]
    have hh := hN (t • (Pi.single i 1 : ι → ℝ)) hmem
    have hval : f (t • (Pi.single i 1 : ι → ℝ)) = u + 1 := by
      rw [map_smul]
      change t * c i = u + 1
      exact div_mul_cancel₀ _ hcneg.ne
    rw [hval] at hh
    linarith
  have htot : 0 < ∑ i, c i := by
    by_contra hpos
    have hz : ∑ i, c i = 0 := le_antisymm (le_of_not_gt hpos)
      (Finset.sum_nonneg fun i _ => hc i)
    have hc0 : ∀ i, c i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).mp hz i (Finset.mem_univ i)
    obtain ⟨x,hx⟩ := hne
    have hh := hS x hx
    rw [hrepr] at hh
    simp only [hc0, zero_mul, Finset.sum_const_zero] at hh
    linarith
  let w : ι → ℝ := fun i => c i / ∑ i, c i
  have hw : ∀ i, 0  ≤  w i := fun i => div_nonneg (hc i) htot.le
  have hws : ∑ i, w i = 1 := by
    dsimp only [w]
    rw [← Finset.sum_div, div_self htot.ne']
  obtain ⟨x,hx,hwx⟩ := hdist w hw hws
  have hfx : f x  ≤  0 := by
    rw [hrepr]
    have he : (∑ i, w i * x i) = (∑ i, c i * x i) / (∑ i, c i) := by
      simp only [w, div_mul_eq_mul_div, Finset.sum_div]
    rw [he] at hwx
    simpa only [zero_mul] using (div_le_iff₀ htot).mp hwx
  have hh := hS x hx
  linarith

section FiniteFeasibility
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

/-- Source finite-set separation, directly on the compact behavioral policy
space. Finite random-seed conversion proved above supplies its convexity. -/
theorem finite_policy_of_distributional {ι : Type*} [Fintype ι]
    (s : Configuration k X) (σ : ι → List X) (bound : ι → ℝ)
    (hdist : ∀ w : ι → ℝ, (∀ i, 0  ≤  w i) → (∑ i, w i = 1) →
      ∃ A : Policy k X, ∑ i, w i * expectedCost A s (σ i)  ≤  ∑ i, w i * bound i) :
    ∃ A : Policy k X, ∀ i, expectedCost A s (σ i)  ≤  bound i := by
  classical
  let cost : Policy k X → (ι → ℝ) := fun A i => expectedCost A s (σ i) - bound i
  have hcont : Continuous cost := continuous_pi fun i =>
    (continuous_expectedCost s (σ i)).sub continuous_const
  have hne : (Set.range cost).Nonempty := Set.range_nonempty cost
  have hconv : Convex ℝ (Set.range cost) := by
    rintro _ ⟨A,rfl⟩ _ ⟨B,rfl⟩ a b ha hb hab
    obtain ⟨D,hD⟩ := exists_binary_mixture s A B a b ha hb hab
    refine ⟨D, funext fun i => ?_⟩
    change expectedCost D s (σ i) - bound i =
      a * (expectedCost A s (σ i) - bound i) + b * (expectedCost B s (σ i) - bound i)
    rw [hD]
    linear_combination (bound i) * hab
  have hg : ∀ w : ι → ℝ, (∀ i, 0  ≤  w i) → (∑ i, w i = 1) →
      ∃ v ∈ Set.range cost, ∑ i, w i * v i  ≤  0 := by
    intro w hw hs
    obtain ⟨A,hA⟩ := hdist w hw hs
    refine ⟨cost A, ⟨A,rfl⟩, ?_⟩
    simpa only [cost, mul_sub, Finset.sum_sub_distrib, sub_nonpos] using hA
  obtain ⟨_, ⟨A,rfl⟩,hA⟩ := nonpositive_vector_of_distributional
    (Set.range cost) hne (isCompact_range hcont) hconv hg
  exact ⟨A, fun i => sub_nonpos.mp (hA i)⟩

end FiniteFeasibility

/-- Quantifier-exact combination of finite separation and product compactness.
No law-dependent or horizon-dependent policy is silently asserted: the entire
quantitative distributional premise is displayed, and remains to be obtained
from the new finite-law construction and amplification. -/
theorem global_policy_of_finite_laws {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]
    (s : Configuration k X) (bound : List X → ℝ)
    (hdist : ∀ F : Finset (List X), ∀ w : F → ℝ,
      (∀ i, 0  ≤  w i) → (∑ i, w i = 1) →
      ∃ A : Policy k X, ∑ i : F, w i * expectedCost A s i.val  ≤ 
        ∑ i : F, w i * bound i.val) :
    ∃ A : Policy k X, ∀ σ, expectedCost A s σ  ≤  bound σ := by
  apply compact_policy_of_finite_feasibility
  intro F
  obtain ⟨A,hA⟩ := finite_policy_of_distributional s (fun i : F => i.val)
    (fun i : F => bound i.val) (hdist F)
  exact ⟨A, fun σ hσ => hA ⟨σ,hσ⟩⟩

end KServer


namespace KServer
noncomputable section
open scoped BigOperators
universe u v

/-- Relabeling requests, leaving server labels unchanged. -/
def mapHistory {k : ℕ} {X : Type u} {Y : Type v} (f : X → Y)
    (h : List (X × Fin k)) : List (Y × Fin k) := h.map (fun p => (f p.1,p.2))

lemma mapHistory_comp {k : ℕ} {X : Type u} {Y : Type v} {Z : Type*}
    (f : X → Y) (g : Y → Z) (h : List (X × Fin k)) :
    mapHistory g (mapHistory f h) = mapHistory (g ∘ f) h := by
  simp [mapHistory,List.map_map,Function.comp_def]

lemma mapHistory_id {k : ℕ} {X : Type u} (h : List (X × Fin k)) :
    mapHistory id h = h := by simp [mapHistory]

lemma map_serve {k : ℕ} {X : Type u} {Y : Type v} (f : X → Y)
    (s : Configuration k X) (i : Fin k) (r : X) :
    f ∘ serve s i r = serve (f ∘ s) i (f r) := by
  classical
  funext j
  by_cases h : j=i <;> simp [serve,Function.comp_def,h]

/-- Executing an identical label string through an isometry preserves every
individual path cost, without any assumption on the ambient metric. -/
lemma serviceCost_map {k : ℕ} {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (hf : Isometry f)
    (s : Configuration k X) (σ : List X) (j : Fin σ.length → Fin k) :
    serviceCost (f ∘ s) (σ.map f) (fun i => j ⟨i.val,by simpa using i.isLt⟩) =
      serviceCost s σ j := by
  induction σ generalizing s with
  | nil => rfl
  | cons r σ ih =>
    change dist (f (s (j 0))) (f r) +
      serviceCost (serve (f ∘ s) (j 0) (f r)) (σ.map f)
        (fun i => j ⟨i.val+1,by simpa using i.isLt⟩) = _
    rw [hf.dist_eq,←map_serve]
    exact congrArg (fun z => dist (s (j 0)) r+z) (ih (serve s (j 0) r) (fun i => j i.succ))

/-- Ambient extension by a retraction. The extension is deliberately arbitrary
on requests outside the finite submetric, while agreeing exactly on all its
histories. It is one policy, not a collection indexed by horizons. -/
def retractPolicy {k : ℕ} {X : Type u} {Y : Type v}
    (f : X → Y) (A : Policy k Y) : Policy k X :=
  fun h r => A (mapHistory f h) (f r)

lemma pathProbability_retract {k : ℕ} {X : Type u} {Y : Type v}
    (f : X → Y) (g : Y → X) (hfg : Function.LeftInverse f g)
    (A : Policy k Y) (h : List (Y × Fin k)) (σ : List Y)
    (j : Fin σ.length → Fin k) :
    pathProbability (retractPolicy f A) (mapHistory g h) (σ.map g)
      (fun i => j ⟨i.val,by simpa using i.isLt⟩) = pathProbability A h σ j := by
  induction σ generalizing h with
  | nil => rfl
  | cons r σ ih =>
    have hg : mapHistory f (mapHistory g h)=h := by
      rw [mapHistory_comp]
      have : f ∘ g = id := funext hfg
      rw [this,mapHistory_id]
    change (A (mapHistory f (mapHistory g h)) (f (g r))).val (j 0) *
      pathProbability (retractPolicy f A) (mapHistory g h++[(g r,j 0)]) (σ.map g)
        (fun i => j ⟨i.val+1,by simpa using i.isLt⟩) = _
    rw [hg,hfg]
    have hh : mapHistory g h++[(g r,j 0)]=mapHistory g (h++[(r,j 0)]) := by
      simp [mapHistory]
    rw [hh]
    exact congrArg (fun z => (A h r).val (j 0)*z) (ih (h++[(r,j 0)]) (fun i => j i.succ))

lemma expectedCost_retract {k : ℕ} {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (g : Y → X)
    (hfg : Function.LeftInverse f g) (hg : Isometry g)
    (A : Policy k Y) (s : Configuration k Y) (σ : List Y) :
    expectedCost (retractPolicy f A) (g ∘ s) (σ.map g)=expectedCost A s σ := by
  classical
  unfold expectedCost
  let e : (Fin (σ.map g).length → Fin k) ≃ (Fin σ.length → Fin k) :=
    Equiv.arrowCongr (finCongr (List.length_map ..)) (Equiv.refl _)
  apply Fintype.sum_equiv e
  intro j
  have hj : j=(fun i => e j ⟨i.val,by simpa using i.isLt⟩) := by rfl
  have hc := congrArg₂ (fun a b : ℝ => a*b) (pathProbability_retract f g hfg A [] σ (e j))
      (serviceCost_map g hg s σ (e j))
  rw [←hj] at hc
  simpa only [mapHistory,List.map_nil] using hc

lemma optimalCost_map {k : ℕ} {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (g : X → Y) (hg : Isometry g)
    (s : Configuration k X) (σ : List X) :
    optimalCost (g ∘ s) (σ.map g)=optimalCost s σ := by
  unfold optimalCost
  congr 1
  ext z
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨fun i => j (Fin.cast (List.length_map ..).symm i),?_⟩
    symm
    simpa only [Fin.cast, Fin.eta] using serviceCost_map g hg s σ
      (fun i => j (Fin.cast (List.length_map ..).symm i))
  · rintro ⟨j,rfl⟩
    exact ⟨fun i => j (Fin.cast (List.length_map ..) i),serviceCost_map g hg s σ j⟩

/-- The exact conclusion needed from source §10's episode amplification, on
finite metrics only. This definition is an open obligation, not an assumption
asserted by the development, and is not the main theorem. -/
def FiniteDistinctLawBound (k : ℕ) (α : ℝ) : Prop :=
  ∀ (Y : Type u) (_ : MetricSpace Y) (_ : Fintype Y),
    ∀ s : Configuration k Y, Function.Injective s →
    ∀ (ι : Type) (_ : Fintype ι), ∀ σ : ι → List Y, ∀ w : ι → ℝ,
      (∀ i, 0  ≤  w i) → (∑ i, w i=1) →
      ∃ A : Policy k Y, (∑ i, w i*expectedCost A s (σ i))  ≤ 
        ∑ i, w i*(α*optimalCost s (σ i))

/-- Every finite family of requests lies in an actual finite submetric. Metric restriction preserves the finite laws, movement costs and offline minima needed for product compactness. -/


theorem distinct_policy_from_finite_submetrics {k : ℕ} [NeZero k]
    (α : ℝ) (hfinite : FiniteDistinctLawBound.{u} k α)
    {X : Type u} [MetricSpace X] (s : Configuration k X) (hs : Function.Injective s) :
    ∃ A : Policy k X, ∀ σ, expectedCost A s σ  ≤  α*optimalCost s σ := by
  classical
  apply global_policy_of_finite_laws s (fun σ => α*optimalCost s σ)
  intro F w hw hsum
  let points : Finset X := Finset.univ.image s ∪ F.biUnion List.toFinset
  have hstart (i : Fin k) : s i ∈ points := by
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hreq (σ : F) (x : X) (hx : x ∈ σ.val) : x ∈ points := by
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨σ.val,σ.property,by simpa using hx⟩
  let Y := {x : X // x ∈ points}
  let sy : Configuration k Y := fun i => ⟨s i,hstart i⟩
  let ret : X → Y := fun x => if hx : x ∈ points then ⟨x,hx⟩ else sy 0
  have hret : Function.LeftInverse ret (Subtype.val : Y → X) := by
    intro y
    simp only [ret,dite_eq_left y.property]
    exact Subtype.eta _ _
  have hiso : Isometry (Subtype.val : Y → X) := by exact isometry_subtype_coe
  let words : F → List Y := fun σ => σ.val.attach.map fun x => ⟨x.val,hreq σ x.val x.property⟩
  have hwords (σ : F) : (words σ).map (Subtype.val : Y → X)=σ.val := by
    simp [words,List.map_map,Function.comp_def]
  have hsy : (Subtype.val : Y → X) ∘ sy=s := rfl
  have hinj : Function.Injective sy := by
    intro i j hij
    exact hs (congrArg Subtype.val hij)
  -- `F` lives in universe u, so index the finitely many words by Fin card.
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  obtain ⟨A,hA⟩ := hfinite Y inferInstance inferInstance sy hinj _ inferInstance
    (fun i => words (e i)) (fun i => w (e i)) (fun i => hw (e i))
    (by simpa only [e.sum_comp] using hsum)
  refine ⟨retractPolicy ret A,?_⟩
  have he (i : F) : expectedCost (retractPolicy ret A) s i.val=
      expectedCost A sy (words i) := by
    rw [←hwords i,←hsy]
    exact expectedCost_retract ret Subtype.val hret hiso A sy (words i)
  have ho (i : F) : optimalCost s i.val=optimalCost sy (words i) := by
    rw [←hwords i,←hsy]
    exact optimalCost_map Subtype.val hiso sy (words i)
  simp only [he,ho]
  rw [e.sum_comp (fun i => w i*expectedCost A sy (words i)),
    e.sum_comp (fun i => w i*(α*optimalCost sy (words i)))] at hA
  exact hA

end
end KServer

namespace KServer
noncomputable section
universe u

/-- Source §10, repeated initial positions. This is a proved transformation of
policies, not a competitiveness assumption: the sole input is the virtual
policy's actual bound, and the real policy is constructed by finite filtering
and compactness above. Its additive constant is independent of every input. -/
theorem repeat_start_transfer {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]
    (s u : Configuration k X) (α : ℝ) (hα : 0 ≤ α)
    (A : Policy k X) (hA : ∀ σ, expectedCost A u σ ≤ α*optimalCost u σ) :
    ∃ B : Policy k X, ∀ σ,
      expectedCost B s σ  ≤  α*optimalCost s σ+(α+1)*matching s u := by
  obtain ⟨B,hB⟩ := BoundedSimulation.global_simulation A [] s u
  refine ⟨B,fun σ => ?_⟩
  have hb : expectedCost B s σ  ≤  matching s u+expectedCost A u σ := hB σ
  have ho := mul_le_mul_of_nonneg_left (optimalCost_change_start s u σ) hα
  have ha := hA σ
  nlinarith

lemma source_log_comparison {k : ℕ} (hk : 2 ≤ k) :
    (1+Real.log (k+1))^2 ≤ 4*(Real.log (k+1))^2 := by
  have hk3 : (3:ℝ) ≤ k+1 := by exact_mod_cast (show 3 ≤ k+1 by omega)
  have h3 : Real.exp 1< (k:ℝ)+1 := Real.exp_one_lt_three.trans_le hk3
  have hlog : 1<Real.log ((k:ℝ)+1) := (Real.lt_log_iff_exp_lt (by positivity)).mpr h3
  nlinarith [sq_nonneg (Real.log ((k:ℝ)+1)-1)]

/-- Arbitrary-metric transfer and repeated starting positions reduce the competitive estimate to a finite amplified-law bound, with constants uniform over all request horizons. -/


theorem main_reduction :
    (∃ d : ℝ, 0 ≤ d ∧ ∀ k : ℕ, 2 ≤ k →
      FiniteDistinctLawBound.{u} k (d*(1+Real.log (k+1))^2)) → ReductionStatement.{u} := by
  rintro ⟨d,hd,hfinite⟩
  refine ⟨4*d,?_⟩
  intro k hk X _ hcard s
  let : NeZero k := ⟨by omega⟩
  let α : ℝ := d*(1+Real.log (k+1))^2
  have hα : 0 ≤ α := mul_nonneg hd (sq_nonneg _)
  have halpha : α  ≤  (4*d)*(Real.log (k+1))^2 := by
    have h := mul_le_mul_of_nonneg_left (source_log_comparison hk) hd
    dsimp [α]
    nlinarith
  have hdist (u : Configuration k X) (hu : Function.Injective u) :
      ∃ A : Policy k X, ∀ σ, expectedCost A u σ ≤ α*optimalCost u σ :=
    distinct_policy_from_finite_submetrics α (hfinite k hk) u hu
  by_cases hs : Function.Injective s
  · obtain ⟨A,hA⟩ := hdist s hs
    refine ⟨A,0,le_rfl,fun _=>rfl,fun σ=> ?_⟩
    have h := mul_le_mul_of_nonneg_right halpha (optimalCost_nonneg s σ)
    simpa only [add_zero] using (hA σ).trans h
  · obtain ⟨e,he⟩ := hcard
    let u : Configuration k X := fun i=>e i.castSucc
    have hu : Function.Injective u := by
      intro i j hij
      exact Fin.castSucc_injective k (he hij)
    obtain ⟨A,hA⟩ := hdist u hu
    obtain ⟨B,hB⟩ := repeat_start_transfer s u α hα A hA
    refine ⟨B,(α+1)*matching s u,mul_nonneg (by linarith) (matching_nonneg _ _),
      fun h=>False.elim (hs h),fun σ=>?_⟩
    exact (hB σ).trans (add_le_add
      (mul_le_mul_of_nonneg_right halpha (optimalCost_nonneg s σ)) le_rfl)

end
end KServer

end

end OAI
