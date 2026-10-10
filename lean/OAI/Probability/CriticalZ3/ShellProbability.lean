import OAI.Probability.CriticalZ3.TrialCounts

namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem shell_blocking_lower (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (C : Box) (o : G.Node) (q : Set.Icc (0 : ℝ) 1) {p₀ : ℝ}
    (hq : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1) (L : ℕ)
    (hp : ∀ y, C.Exterior y → p (C.entryBit m y) = q) :
    (1-p₀)^L * (ProductCylinder.law p).real
      {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L} ≤
    (ProductCylinder.law p).real
      {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L ∧
        G.Blocked m C ω o} := by
  let J := G.outsideBits m C
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let P (a : J → Bool) := 0 < (G.entrants m C (ξ a) o).card ∧
    (G.entrants m C (ξ a) o).card < L
  let A (a : J → Bool) := allValue (G.entryBits m C (ξ a) o) false
  have h := select_probability_lower p J P A (fun a => measurableSet_allValue _ _) (b := (1-p₀)^L) ?_
  · have hY (ω : m.Config) : G.entrants m C ω o = G.entrants m C (ξ (J.restrict ω)) o :=
      ProductCylinder.determinedBy_eq_extend (G.entrants_determined m C o) ω
    have hK (ω : m.Config) : G.entryBits m C ω o = G.entryBits m C (ξ (J.restrict ω)) o :=
      ProductCylinder.determinedBy_eq_extend (G.entryBits_determined m C o) ω
    have heP : {ω | P (J.restrict ω)} =
        {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L} := by
      ext ω; simp only [P,Set.mem_ofPred_eq]; rw [←hY ω]
    have heA : {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} =
        {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L ∧
          G.Blocked m C ω o} := by
      ext ω
      simp only [P,A,allValue,Blocked,Set.mem_ofPred_eq]
      rw [←hY ω,←hK ω]
      exact and_assoc
    rwa [heP,heA] at h
  · intro a ha
    rw [fixed_determined_probability p J (G.entryBits m C (ξ a) o)
      (G.entryBits_disjoint_outside m C (ξ a) o).symm _ _ (allValue_determined _ _)]
    rw [allValue_probability_constant p _ q ?_ false]
    · change (1-p₀)^L ≤ (1-(q : ℝ))^(G.entryBits m C (ξ a) o).card
      have h0 : 0 ≤ 1-p₀ := by linarith
      have h1 : 1-(q : ℝ) ≤ 1 := by linarith [q.property.1]
      calc
        _ ≤ (1-(q : ℝ))^L := pow_le_pow_left₀ h0 (by linarith) L
        _ ≤ _ := pow_le_pow_of_le_one (by linarith [q.property.2]) h1
          ((G.entryBits_card m C (ξ a) o).trans (Nat.le_of_lt ha.2))
    · intro e he
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
      have hyG : y ∈ G.vertices := (Finset.mem_filter.mp hy).1
      exact hp y ((G.mem_entrants m C (ξ a) o ⟨y,hyG⟩).mp hy).1

theorem measurableSet_shell_blocked (C : Box) (o : G.Node) (L : ℕ) :
    MeasurableSet {ω | 0 < (G.entrants m C ω o).card ∧
      (G.entrants m C ω o).card < L ∧ G.Blocked m C ω o} := by
  let J := G.outsideBits m C
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let A (a : J → Bool) : Set m.Config := if 0 < (G.entrants m C (ξ a) o).card ∧
      (G.entrants m C (ξ a) o).card < L then allValue (G.entryBits m C (ξ a) o) false else ∅
  have h := measurableSet_select J A (fun a => by
    dsimp only [A]; split_ifs
    · exact measurableSet_allValue _ _
    · exact MeasurableSet.empty)
  have he : {ω | ω ∈ A (J.restrict ω)} = {ω | 0 < (G.entrants m C ω o).card ∧
      (G.entrants m C ω o).card < L ∧ G.Blocked m C ω o} := by
    ext ω
    have hY := ProductCylinder.determinedBy_eq_extend (G.entrants_determined m C o) ω
    have hK := ProductCylinder.determinedBy_eq_extend (G.entryBits_determined m C o) ω
    change G.entrants m C ω o = G.entrants m C (ξ (J.restrict ω)) o at hY
    change G.entryBits m C ω o = G.entryBits m C (ξ (J.restrict ω)) o at hK
    simp only [A,←hY,←hK,Set.mem_ofPred_eq,Blocked,allValue]
    split_ifs with hh
    · tauto
    · simp only [Set.mem_empty_iff_false]; tauto
  rwa [he] at h

/-- Deterministic shell selection for the finite graph in bond and site percolation. -/
theorem exists_shell (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (B : Box) (o : G.Node) (q : Set.Icc (0 : ℝ) 1) {p₀ : ℝ}
    (hq : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1) (L a R : ℕ) (haR : a < R)
    (ho : ¬(B.expand R).Contains o.1)
    (hp : ∀ j ∈ Finset.Ico a R, ∀ y, (B.expand j).Exterior y →
      p ((B.expand j).entryBit m y) = q) :
    ∃ j ∈ Finset.Ico a R, (ProductCylinder.law p).real
      {ω | G.Meets m ω o {x | B.Contains x} ∧ (G.entrants m (B.expand j) ω o).card < L} ≤
      1/((1-p₀)^L*(R-a : ℕ)) := by
  let I := ↥(Finset.Ico a R)
  have : Nonempty I := ⟨⟨a,Finset.mem_Ico.mpr ⟨le_rfl,haR⟩⟩⟩
  let Q (i : I) : Set m.Config :=
    {ω | G.Meets m ω o {x | B.Contains x} ∧ (G.entrants m (B.expand i.1) ω o).card < L}
  let A (i : I) : Set m.Config :=
    {ω | 0 < (G.entrants m (B.expand i.1) ω o).card ∧
      (G.entrants m (B.expand i.1) ω o).card < L ∧ G.Blocked m (B.expand i.1) ω o}
  have hoi (i : I) : ¬(B.expand i.1).Contains o.1 := fun h =>
    ho (B.expand_mono (Nat.le_of_lt (Finset.mem_Ico.mp i.2).2) h)
  have hAd : Pairwise (fun i j : I => Disjoint (A i) (A j)) := by
    intro i j hij
    have hi : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    apply Set.disjoint_left.mpr
    intro ω hωi hωj
    rcases lt_or_gt_of_ne hi with hlt | hlt
    · have he := G.blocked_earlier_entrants m hlt (hoi j) hωj.2.2
      have hpos := hωi.1
      rw [he,Finset.card_empty] at hpos
      exact Nat.not_lt_zero _ hpos
    · have he := G.blocked_earlier_entrants m hlt (hoi i) hωi.2.2
      have hpos := hωj.1
      rw [he,Finset.card_empty] at hpos
      exact Nat.not_lt_zero _ hpos
  have hblock (i : I) : (1-p₀)^L * (ProductCylinder.law p).real (Q i) ≤
      (ProductCylinder.law p).real (A i) := by
    have hsub : Q i ⊆ {ω | 0 < (G.entrants m (B.expand i.1) ω o).card ∧
        (G.entrants m (B.expand i.1) ω o).card < L} := by
      intro ω hω
      refine ⟨Finset.card_pos.mpr (G.meets_entrants_nonempty m (hoi i) ?_),hω.2⟩
      obtain ⟨z,hz,hconn⟩ := hω.1
      exact ⟨z,B.contains_expand i.1 hz,hconn⟩
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (pow_nonneg (by linarith) _)).trans
      (G.shell_blocking_lower m p (B.expand i.1) o q hq hp₀ L (hp i.1 i.2))
  obtain ⟨i,hi⟩ := ShellEstimates.exists_layer (ProductCylinder.law p) Q A
    (fun i => G.measurableSet_shell_blocked m (B.expand i.1) o L) hAd
    (pow_pos (by linarith) L) hblock
  refine ⟨i.1,i.2,?_⟩
  simpa only [I,Fintype.card_coe,Nat.card_Ico] using hi

end CriticalZ3.LatticeGraph

namespace FiniteAssociation
open Classical
variable {E : Type}

theorem indicator_monotone {P : (E → Bool) → Prop} (hP : Monotone P) :
    Monotone (fun ω => if P ω then (1 : ℝ) else 0) := by
  intro ω ω' h
  by_cases h' : P ω
  · simp [h',hP h h']
  · simp only [h',ite_false]
    split_ifs <;> norm_num

theorem prob_and_increasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    {P Q : (E → Bool) → Prop} (hP : Monotone P) (hQ : Monotone Q) :
    prob p P * prob p Q ≤ prob p (fun ω => P ω ∧ Q ω) := by
  have h := increasing p _ _ (indicator_monotone hP) (indicator_monotone hQ)
  change mean p _ * mean p _ ≤ mean p _
  convert h using 1
  congr 1
  funext ω
  by_cases h₁ : P ω <;> by_cases h₂ : Q ω <;> simp [h₁,h₂]
end FiniteAssociation

namespace ProductCylinder
open MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem probability_congr_parameters (J : Finset E)
    (p q : E → Set.Icc (0 : ℝ) 1) (hpq : ∀ e ∈ J, p e = q e)
    (A : Set (E → Bool)) (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A)) :
    (law p).real A = (law q).real A := by
  simp only [Measure.real_def,probability_determined J _ A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))]
  congr 2
  unfold finiteLaw
  congr 1
  funext e
  rw [hpq e e.2]

theorem determinedBy_mono {J K : Finset E} (hJK : J ⊆ K) {F : Type}
    {f : (E → Bool) → F} (hf : DeterminedBy J f) : DeterminedBy K f :=
  fun ω ω' h => hf ω ω' (fun e he => h e (hJK he))

theorem increasing_and (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A B : Set (E → Bool))
    (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hB : DeterminedBy (F := Prop) J (fun ω => ω ∈ B))
    (hmA : Monotone (fun ω => ω ∈ A)) (hmB : Monotone (fun ω => ω ∈ B)) :
    (law p).real A*(law p).real B ≤ (law p).real (A ∩ B) := by
  have he (C : Set (E → Bool)) (hC : DeterminedBy (F := Prop) J (fun ω => ω ∈ C)) :
      (law p).real C = FiniteAssociation.prob (fun e : J => p e) (fun ξ => extend J ξ ∈ C) := by
    rw [FiniteAssociation.prob_eq_real,Measure.real_def,Measure.real_def,
      probability_determined J p C (fun ω ω' h => eq_iff_iff.mp (hC ω ω' h))]
    rfl
  have hAB : DeterminedBy (F := Prop) J (fun ω => ω ∈ A ∩ B) := by
    intro ω ω' h
    simp only [Set.mem_inter_iff,hA ω ω' h,hB ω ω' h]
  rw [he A hA,he B hB,he (A ∩ B) hAB]
  exact FiniteAssociation.prob_and_increasing _ (hmA.comp (extend_mono J)) (hmB.comp (extend_mono J))

/-- The open-seed Harris estimate, with a separate increasing connecting event. -/
theorem seed_failure_bound (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (O A C : Set (E → Bool))
    (hO : DeterminedBy (F := Prop) J (fun ω => ω ∈ O))
    (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hmO : Monotone (fun ω => ω ∈ O)) (hmA : Monotone (fun ω => ω ∈ A))
    (hsub : O ∩ A ⊆ C) {γ : ℝ} (hprob : 1-γ ≤ (law p).real A) :
    (law p).real (O ∩ Cᶜ) ≤ (law p).real O*γ := by
  have hm := measurableSet_determined J A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))
  have ha := increasing_and J p O A hO hA hmO hmA
  have hadd := measureReal_inter_add_sdiff (μ := law p) (s := O) hm
  have hsub' : O ∩ Cᶜ ⊆ O \ A := by
    intro ω hω
    exact ⟨hω.1,fun h => hω.2 (hsub ⟨hω.1,h⟩)⟩
  have hle := measureReal_mono (μ := law p) hsub'
  have h0 : 0 ≤ (law p).real O := measureReal_nonneg
  nlinarith
end ProductCylinder

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem allValue_true_monotone (J : Finset E) : Monotone (fun ω => ω ∈ allValue J true) := by
  intro ω ω' h hh e he
  have hi := h e
  rw [hh e he] at hi
  exact le_antisymm le_top hi

theorem measurableSet_conditional_test (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) (a : ℝ) :
    MeasurableSet {ω | conditionalProbability p J C ω ≤ a} := by
  refine ProductCylinder.measurableSet_determined J _ ?_
  intro ω ω' h
  simp only [Set.mem_ofPred_eq,conditionalProbability_determined p J C ω ω' h]
end InfiniteConditioning

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem conn_mono {ω ω' : m.Config} (h : ω ≤ ω') {x y : G.Node}
    (hc : G.Conn m ω x y) : G.Conn m ω' x y := by
  have hopen {e : m.Bit} (he : ω e = true) : ω' e = true := by
    have hi := h e
    rw [he] at hi
    exact le_antisymm le_top hi
  obtain ⟨hx,hc⟩ := (G.conn_iff m ω x y).mp hc
  refine (G.conn_iff m ω' x y).mpr ⟨?_,?_⟩
  · cases m
    · trivial
    · exact hopen hx
  · apply Relation.ReflTransGen.mono (r := G.Adj m ω) (p := G.Adj m ω') ?_ x y hc
    intro a b hab
    cases m
    · obtain ⟨e,he,hi,ho⟩ := hab
      exact ⟨e,he,hi,hopen ho⟩
    · exact ⟨hab.1,hopen hab.2.1,hopen hab.2.2⟩

theorem meets_mono (o : G.Node) (T : Set Vertex) : Monotone (fun ω => G.Meets m ω o T) := by
  intro ω ω' h ⟨y,hy,hc⟩
  exact ⟨y,hy,G.conn_mono m h hc⟩

noncomputable def goodRelays (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (T : Set Vertex) (τ : ℝ) (ω : m.Config) : Set Vertex :=
  {v | ∃ a : G.Node, a.1 = v ∧ 1-τ < conditionalProbability p J {ω | G.Meets m ω a T} ω}

theorem goodRelays_determined (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (T : Set Vertex) (τ : ℝ) : ProductCylinder.DeterminedBy J (G.goodRelays m p J T τ) := by
  intro ω ω' h
  ext v
  simp only [goodRelays,Set.mem_ofPred_eq,conditionalProbability_determined p J _ ω ω' h]

theorem random_relay_failure (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (o : G.Node) (T : Set Vertex) {τ : ℝ} (hτ : 0 ≤ τ) :
    (ProductCylinder.law p).real
      {ω | G.Meets m ω o (G.goodRelays m p J T τ ω) ∧ ¬G.Meets m ω o T} ≤ τ := by
  let A (a : J → Bool) : Set m.Config :=
    {ω | G.Meets m ω o (G.goodRelays m p J T τ (ProductCylinder.extend J a)) ∧ ¬G.Meets m ω o T}
  have he : {ω | G.Meets m ω o (G.goodRelays m p J T τ ω) ∧ ¬G.Meets m ω o T} =
      {ω | ω ∈ A (J.restrict ω)} := by
    ext ω
    simp only [A,Set.mem_ofPred_eq,
      ProductCylinder.determinedBy_eq_extend (G.goodRelays_determined m p J T τ) ω]
  rw [he]
  apply select_probability_le p J A
  · intro a
    exact (G.measurableSet_meets m _ _).inter (G.measurableSet_meets m _ _).compl
  · intro a
    apply G.failure_comparison m _ o _ T hτ
    intro v ⟨u,hu,hh⟩
    have heu : u = v := Subtype.ext hu
    subst u
    exact hh.le

end CriticalZ3.LatticeGraph

end OAI
