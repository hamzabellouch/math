import OAI.Combinatorics.ParityLifts.LeafCounts

namespace OAI

namespace ParityWL
namespace Complexity
/-- This is a full row-major adjacency matrix, not an adjacency oracle or a
colored-graph promise. Both matrices and their common order appear on the tape. -/
noncomputable def encodeGraphs {n : ℕ} (G H : SimpleGraph (Fin n)) : List Bool := by
  classical
  exact encodeNat n ++
    (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => decide (G.Adj i j)))).flatten ++
    (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => decide (H.Adj i j)))).flatten

inductive Implementation | commonColors | pureUnion
  deriving DecidableEq

noncomputable def Equivalent {n : ℕ} (G H : SimpleGraph (Fin n))
    (c : Convention) (i : Implementation) (k : ℕ) : Prop :=
  match i with
  | .commonColors => WLEquivalent G H c k
  | .pureUnion => PureWLEquivalent G H c k

/-- An actual execution bound; no computation is hidden in its interpretation. -/
def SATTimeBound (M : Machine) (B : ℕ → ℕ → ℝ) : Prop :=
  ∀ (N : ℕ) (F : Formula N), ∃ s b,
    Emits M (encodeFormula F) s b ∧ (b = true ↔ F.Satisfiable) ∧
    (s : ℝ) ≤ B N (encodeFormula F).length

/-- Positive-rate ETH: one positive forbidden rate, with arbitrary fixed
polynomial input factor. This is not the weaker uniform premise below. -/
def PositiveRateETH : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ¬ ∃ (M : Machine) (C : ℝ) (d : ℕ),
    0 < C ∧ SATTimeBound M (fun N L => C * (L + 1 : ℝ) ^ d * (2 : ℝ) ^ (δ * N))

/-- The same single machine must meet every positive exponential rate, with
one fixed polynomial input factor. Constants may depend on the chosen rate. -/
def UniformSubexponentialETH : Prop :=
  ¬ ∃ (M : Machine) (d : ℕ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    SATTimeBound M (fun N L => C * (L + 1 : ℝ) ^ d * (2 : ℝ) ^ (ε * N))

/-- Using n+1 includes the zero-order input and is exactly O(n^r) on positive
orders. The finite exceptional small orders can be absorbed in the constant. -/
noncomputable def FixedWLBound (M : Machine) (c : Convention) (i : Implementation)
    (k : ℕ) (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G H : SimpleGraph (Fin n)), ∃ s b,
    Emits M (encodeGraphs G H) s b ∧ (b = true ↔ Equivalent G H c i k) ∧
    (s : ℝ) ≤ C * (n + 1 : ℝ) ^ r

noncomputable def UniformWLBound (M : Machine) (c : Convention) (i : Implementation)
    (f g : ℕ → ℝ) : Prop :=
  (∀ k, 0 < f k) ∧ (∀ k, 0 ≤ g k) ∧
  ∀ (k : ℕ), 4 ≤ k → ∀ (n : ℕ) (G H : SimpleGraph (Fin n)), ∃ s b,
    Emits M (encodeNat k ++ encodeGraphs G H) s b ∧
    (b = true ↔ Equivalent G H c i k) ∧ (s : ℝ) ≤ f k * (n + 1 : ℝ) ^ g k

noncomputable def FixedDimensionETHStatement : Prop :=
  PositiveRateETH → ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, 4 ≤ K ∧
    ∀ k : ℕ, K ≤ k → ∀ conv : Convention, ∀ i : Implementation,
      ¬ ∃ M : Machine, FixedWLBound M conv i k (c * k)

noncomputable def UniformETHStatement : Prop :=
  UniformSubexponentialETH → ∀ c : Convention, ∀ i : Implementation,
    ¬ ∃ (M : Machine) (f g : ℕ → ℝ),
      Filter.Tendsto (fun k : ℕ => g k / k) Filter.atTop (nhds 0) ∧
      UniformWLBound M c i f g


end Complexity
namespace Complexity

def groupWidth (m t : ℕ) : ℕ := (m + t - 1) / t

lemma le_groupWidth_mul (m t : ℕ) (ht : 0 < t) : m ≤ groupWidth m t * t := by
  have hr := Nat.mod_lt (m + t - 1) ht
  have he := Nat.div_add_mod (m + t - 1) t
  dsimp [groupWidth]
  rw [Nat.mul_comm] at he
  omega

def groupAt {N t : ℕ} (F : Formula N) (ht : 0 < t) (q : Fin F.length) : Fin t :=
  ⟨q.val % t, Nat.mod_lt _ ht⟩

def groupIndices {N t : ℕ} (F : Formula N) (ht : 0 < t) (i : Fin t) :
    Finset (Fin F.length) := Finset.univ.filter (fun q => groupAt F ht q = i)

lemma group_indices_card {N t : ℕ} (F : Formula N) (ht : 0 < t) (i : Fin t) :
    (groupIndices F ht i).card ≤ groupWidth F.length t := by
  let e : (groupIndices F ht i) → Fin (groupWidth F.length t) := fun q =>
    ⟨q.1.val / t, (Nat.div_lt_iff_lt_mul ht).mpr
      (lt_of_lt_of_le q.1.isLt (le_groupWidth_mul F.length t ht))⟩
  have hinj : Function.Injective e := by
    intro q r he
    apply Subtype.ext
    apply Fin.ext
    have hq : groupAt F ht q.1 = i := (Finset.mem_filter.mp q.2).2
    have hr : groupAt F ht r.1 = i := (Finset.mem_filter.mp r.2).2
    have hm : q.1.val % t = r.1.val % t := congrArg Fin.val (hq.trans hr.symm)
    have hd : q.1.val / t = r.1.val / t := congrArg Fin.val he
    have h1 := Nat.div_add_mod q.1.val t
    have h2 := Nat.div_add_mod r.1.val t
    rw [hd, hm] at h1
    omega
  simpa using Fintype.card_le_of_injective e hinj

def clauseScope {N : ℕ} (C : Clause N) : Finset (Fin N) :=
  C.literals.toFinset.image Prod.fst

def groupScope {N t : ℕ} (F : Formula N) (ht : 0 < t) (i : Fin t) : Finset (Fin N) :=
  (groupIndices F ht i).biUnion (fun q => clauseScope (F.get q))

lemma clauseScope_card {N : ℕ} (C : Clause N) : (clauseScope C).card ≤ 3 :=
  (Finset.card_image_le.trans (List.toFinset_card_le _)).trans C.width

lemma groupScope_card {N t : ℕ} (F : Formula N) (ht : 0 < t) (i : Fin t) :
    (groupScope F ht i).card ≤ 3 * groupWidth F.length t := by
  calc
    _ ≤ ∑ q ∈ groupIndices F ht i, (clauseScope (F.get q)).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ groupIndices F ht i, 3 := Finset.sum_le_sum (fun q _ => clauseScope_card _)
    _ = 3 * (groupIndices F ht i).card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left 3 (group_indices_card F ht i)

def extendScope {N : ℕ} (s : Finset (Fin N)) (a : s → Bool) (v : Fin N) : Bool :=
  if h : v ∈ s then a ⟨v, h⟩ else false

@[simp] lemma extendScope_apply {N : ℕ} (s : Finset (Fin N)) (a : s → Bool)
    (v : Fin N) (hv : v ∈ s) : extendScope s a v = a ⟨v, hv⟩ := by
  simp [extendScope, hv]

noncomputable def groupedChoice {N t : ℕ} (F : Formula N) (ht : 0 < t) : ChoiceSystem t := by
  classical
  exact {
    Domain := fun i => {a : groupScope F ht i → Bool //
      ∀ q ∈ groupIndices F ht i, (F.get q).Satisfied (extendScope (groupScope F ht i) a)}
    domainFintype := fun _ => inferInstance
    Label := fun p => ↥(groupScope F ht p.1.1 ∩ groupScope F ht p.1.2) → Bool
    labelFintype := fun _ => inferInstance
    leftLabel := fun _ a v => a.1 ⟨v.1, (Finset.mem_inter.mp v.2).1⟩
    rightLabel := fun _ a v => a.1 ⟨v.1, (Finset.mem_inter.mp v.2).2⟩ }

lemma groupedChoice_size {N t : ℕ} (F : Formula N) (ht : 0 < t) :
    (groupedChoice F ht).SizeAtMost (2 ^ (3 * groupWidth F.length t)) := by
  classical
  constructor
  · intro i
    change Fintype.card {a : groupScope F ht i → Bool // _} ≤ _
    calc
      _ ≤ Fintype.card (groupScope F ht i → Bool) := Fintype.card_subtype_le _
      _ = 2 ^ (groupScope F ht i).card := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (groupScope_card F ht i)
  · intro p
    change Fintype.card (↥(groupScope F ht p.1.1 ∩ groupScope F ht p.1.2) → Bool) ≤ _
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    apply Nat.pow_le_pow_right (by omega)
    exact (Finset.card_le_card Finset.inter_subset_left).trans (groupScope_card F ht p.1.1)

lemma literal_mem_groupScope {N t : ℕ} (F : Formula N) (ht : 0 < t) (i : Fin t)
    (q : Fin F.length) (hq : q ∈ groupIndices F ht i) (l : Literal N)
    (hl : l ∈ (F.get q).literals) : l.1 ∈ groupScope F ht i := by
  exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_image.mpr ⟨l, by simpa using hl, rfl⟩⟩

lemma groupedChoice_successful_of_sat {N t : ℕ} (F : Formula N) (ht : 0 < t)
    (hF : F.Satisfiable) : (groupedChoice F ht).Successful := by
  classical
  rcases hF with ⟨a, ha⟩
  let d : (i : Fin t) → (groupedChoice F ht).Domain i := fun i =>
    ⟨fun v => a v.1, by
      intro q hq
      rcases ha _ (F.get_mem q) with ⟨l, hl, he⟩
      exact ⟨l, hl, by simpa [extendScope, literal_mem_groupScope F ht i q hq l hl] using he⟩⟩
  refine ⟨d, ?_⟩
  intro p
  rfl

lemma groupedChoice_agreement {N t : ℕ} (F : Formula N) (ht : 0 < t)
    (d : (i : Fin t) → (groupedChoice F ht).Domain i)
    (hd : ∀ p : MainPair t,
      (groupedChoice F ht).leftLabel p (d p.1.1) = (groupedChoice F ht).rightLabel p (d p.1.2))
    (i j : Fin t) (v : Fin N) (hi : v ∈ groupScope F ht i) (hj : v ∈ groupScope F ht j) :
    (d i).1 ⟨v, hi⟩ = (d j).1 ⟨v, hj⟩ := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact congrFun (hd ⟨(i, j), h⟩) ⟨v, Finset.mem_inter.mpr ⟨hi, hj⟩⟩
  · rfl
  · exact (congrFun (hd ⟨(j, i), h⟩) ⟨v, Finset.mem_inter.mpr ⟨hj, hi⟩⟩).symm

lemma sat_of_groupedChoice_successful {N t : ℕ} (F : Formula N) (ht : 0 < t)
    (hF : (groupedChoice F ht).Successful) : F.Satisfiable := by
  classical
  rcases hF with ⟨d, hd⟩
  let a : Fin N → Bool := fun v =>
    if h : ∃ i, v ∈ groupScope F ht i then (d h.choose).1 ⟨v, h.choose_spec⟩ else false
  have hh : ∀ i v (hv : v ∈ groupScope F ht i), a v = (d i).1 ⟨v, hv⟩ := by
    intro i v hv
    have he : ∃ j, v ∈ groupScope F ht j := ⟨i, hv⟩
    dsimp [a]
    rw [dite_eq_left he]
    exact groupedChoice_agreement F ht d hd he.choose i v he.choose_spec hv
  refine ⟨a, ?_⟩
  intro C hC
  rcases List.get_of_mem hC with ⟨q, rfl⟩
  let i := groupAt F ht q
  have hq : q ∈ groupIndices F ht i := by simp [groupIndices, i]
  rcases (d i).2 q hq with ⟨l, hl, he⟩
  refine ⟨l, hl, ?_⟩
  have hv := literal_mem_groupScope F ht i q hq l hl
  rw [hh i l.1 hv]
  simpa [extendScope, hv] using he

/-- The grouping reduction, including empty groups, empty overlaps, and empty domains. -/
theorem sat_grouping {N t : ℕ} (F : Formula N) (ht : 0 < t) :
    (groupedChoice F ht).SizeAtMost (2 ^ (3 * groupWidth F.length t)) ∧
    ((groupedChoice F ht).Successful ↔ F.Satisfiable) :=
  ⟨groupedChoice_size F ht,
    ⟨sat_of_groupedChoice_successful F ht, groupedChoice_successful_of_sat F ht⟩⟩

end Complexity

namespace Complexity

lemma bagParameter_pos (c : Convention) (k : ℕ) (hk : 4 ≤ k) : 0 < bagParameter c k := by
  cases c <;> simp only [bagParameter] <;> omega

noncomputable def satChoice (c : Convention) (k : ℕ) (hk : 4 ≤ k)
    {N : ℕ} (F : Formula N) : ChoiceSystem (bagParameter c k) :=
  groupedChoice F (bagParameter_pos c k hk)

/-- The mathematical SAT-to-uncolored-graph reduction. -/
theorem sat_parity_reduction (c : Convention) (k : ℕ) (hk : 4 ≤ k)
    {N : ℕ} (F : Formula N) :
    let C := satChoice c k hk F
    Fintype.card (LiftVertex (template (bagParameter c k)) (baseGraph C)
      (baseProjection C) (fun _ => 0)) =
      Fintype.card (LiftVertex (template (bagParameter c k)) (baseGraph C)
        (baseProjection C) (starParity (bagParameter c k))) ∧
    Fintype.card (LiftVertex (template (bagParameter c k)) (baseGraph C)
      (baseProjection C) (fun _ => 0)) ≤
      2 ^ (3 * groupWidth F.length (bagParameter c k)) * orderFactor (bagParameter c k) ∧
    (WLEquivalent (zeroLift C) (starLift C) c k ↔ ¬ F.Satisfiable) ∧
    (PureWLEquivalent (zeroLift C) (starLift C) c k ↔ ¬ F.Satisfiable) ∧
    (F.Satisfiable →
      ¬ sameHistogram (zeroLift C) (starLift C) c k (detectionRound c) ∧
      ¬ samePureHistogram (zeroLift C) (starLift C) c k (detectionRound c)) := by
  dsimp only
  have hs := sat_grouping F (bagParameter_pos c k hk)
  have hc : (satChoice c k hk F).Successful ↔ F.Satisfiable := hs.2
  obtain ⟨he, hb, hw, hp, hd⟩ := parity_reduction k hk c (satChoice c k hk F)
  exact ⟨he, hb _ (Nat.one_le_pow _ _ (by omega)) hs.1,
    hw.trans (not_congr hc), hp.trans (not_congr hc), fun h => hd (hc.mpr h)⟩

end Complexity

end ParityWL

namespace ParityWL

namespace Complexity

open Sparsification

def Formula.toCNF {N : ℕ} (F : Formula N) : CNF (Literal N) :=
  (F.map (fun C => C.literals.toFinset)).toFinset

lemma Formula.toCNF_width {N : ℕ} (F : Formula N) :
    ∀ C ∈ F.toCNF, C.card ≤ 3 := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hC)
  exact (List.toFinset_card_le _).trans D.width

lemma Formula.toCNF_holds {N : ℕ} (F : Formula N) (a : Fin N → Bool) :
    Holds F.toCNF (fun l => a l.1 = l.2) ↔ F.Satisfied a := by
  constructor
  · intro h C hC
    have hc := h C.literals.toFinset (List.mem_toFinset.mpr (List.mem_map.mpr ⟨C, hC, rfl⟩))
    simpa only [Clause.Satisfied, List.mem_toFinset] using hc
  · intro h C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hC)
    simpa only [Clause.Satisfied, List.mem_toFinset] using h D hD

noncomputable def CNF.toFormula {N : ℕ} (F : CNF (Literal N))
    (hw : ∀ C ∈ F, C.card ≤ 3) : Formula N :=
  F.attach.toList.map (fun C => ⟨C.val.toList, by simpa using hw C.val C.property⟩)

lemma CNF.toFormula_length {N : ℕ} (F : CNF (Literal N))
    (hw : ∀ C ∈ F, C.card ≤ 3) : (CNF.toFormula F hw).length = F.card := by
  simp [CNF.toFormula]

lemma CNF.toFormula_holds {N : ℕ} (F : CNF (Literal N))
    (hw : ∀ C ∈ F, C.card ≤ 3) (a : Fin N → Bool) :
    (CNF.toFormula F hw).Satisfied a ↔ Holds F (fun l => a l.1 = l.2) := by
  constructor
  · intro h C hC
    have hm : (⟨C.toList, by simpa using hw C hC⟩ : Clause N) ∈ CNF.toFormula F hw := by
      exact List.mem_map.mpr ⟨⟨C, hC⟩, by simp, rfl⟩
    simpa only [Clause.Satisfied, Finset.mem_toList] using h _ hm
  · intro h C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    simpa only [Clause.Satisfied, Finset.mem_toList] using h D.val D.property

/-- The combinatorial IPZ producer at computably chosen thresholds 12j. -/
theorem sat_sparsification {N : ℕ} (F : Formula N) (j : ℕ) (hj : 0 < j) :
    ∃ L : List (Formula N),
      (∀ H ∈ L, H.length ≤ 1 + 2 * N * (1 + (12 * j) ^ 2 + 2 * (12 * j) ^ 8)) ∧
      (∀ a : Fin N → Bool, F.Satisfied a ↔ ∃ H ∈ L, H.Satisfied a) ∧
      (L.length : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) / j) := by
  classical
  obtain ⟨L, hL, hv, hc⟩ := indexed_sparsification N (by simp [Literal, Nat.mul_comm])
    F.toCNF F.toCNF_width j hj
  let T : List (Formula N) := L.attach.map (fun H =>
    CNF.toFormula H.val (hL H.val H.property).2.1)
  refine ⟨T, ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hH
    rw [CNF.toFormula_length]
    exact (hL D.val D.property).2.2
  · intro a
    rw [← F.toCNF_holds a, hv (fun l => a l.1 = l.2)]
    constructor
    · rintro ⟨H, hH, hHa⟩
      refine ⟨CNF.toFormula H (hL H hH).2.1, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨⟨H, hH⟩, by simp, rfl⟩
      · exact (CNF.toFormula_holds _ _ a).mpr hHa
    · rintro ⟨H, hH, hHa⟩
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hH
      exact ⟨D.val, D.property, (CNF.toFormula_holds _ _ a).mp hHa⟩
  · simpa [T] using hc

lemma sat_sparsification_or {N : ℕ} (F : Formula N) (L : List (Formula N))
    (hv : ∀ a : Fin N → Bool, F.Satisfied a ↔ ∃ H ∈ L, H.Satisfied a) :
    F.Satisfiable ↔ ∃ H ∈ L, H.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨H, hH, hHa⟩ := (hv a).mp ha
    exact ⟨H, hH, a, hHa⟩
  · rintro ⟨H, hH, a, ha⟩
    exact ⟨a, (hv a).mpr ⟨H, hH, ha⟩⟩

end Complexity

end ParityWL

end OAI
