import OAI.Probability.DirectionalWalk.BridgeWords

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def wordCylinder {d : ℕ} (a : Word d) : Set (Path d) := pathCylinder a.1 (wordPath a)

def wordEnd {d : ℕ} (a : Word d) : Site d := wordPath a a.1

def wordDepartures {d : ℕ} (a : Word d) : Set (Site d) :=
  {y | ∃ i < a.1, wordPath a i = y}

def PrefixFreeWords {d : ℕ} (A : Set (Word d)) : Prop :=
  Pairwise (fun (a b : A) => Disjoint (wordCylinder a.val) (wordCylinder b.val))

def firstHitWord {d : ℕ} (K : Set (Site d)) (a : Word d) : Prop :=
  wordEnd a ∈ K ∧ ∀ i < a.1, wordPath a i ∉ K

lemma firstHitWords_prefixFree {d : ℕ} (K : Set (Site d)) :
    PrefixFreeWords {a | firstHitWord K a} := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro X hXa hXb
  have hn : a.val.1 = b.val.1 := by
    apply le_antisymm
    · by_contra h
      have hlt : b.val.1 < a.val.1 := by omega
      apply a.property.2 _ hlt
      rw [← hXa _ hlt.le,hXb _ (le_refl _)]
      exact b.property.1
    · by_contra h
      have hlt : a.val.1 < b.val.1 := by omega
      apply b.property.2 _ hlt
      rw [← hXb _ hlt.le,hXa _ (le_refl _)]
      exact a.property.1
  apply hab
  apply Subtype.ext
  have ha := (prefixWord_eq_iff a.val.1 X a.val).mpr ⟨rfl,hXa⟩
  have hb := (prefixWord_eq_iff a.val.1 X b.val).mpr ⟨hn,hXb⟩
  exact ha.symm.trans hb

lemma PrefixFreeWords.mono {d : ℕ} {A B : Set (Word d)} (hA : PrefixFreeWords A)
    (hBA : B ⊆ A) : PrefixFreeWords B := by
  intro a b hab
  exact hA (i := ⟨a.val,hBA a.property⟩) (j := ⟨b.val,hBA b.property⟩)
    (fun he => hab (Subtype.ext (congrArg (fun u : A => u.val) he)))

lemma quenched_restart_word {d : ℕ} (ω : Environment d) (x : Site d) (a : Word d)
    {E : Set (Path d)} (hE : MeasurableSet E) :
    quenchedKernel d (ω,x) (wordCylinder a ∩ tailPath a.1 ⁻¹' E) =
      quenchedKernel d (ω,x) (wordCylinder a) * quenchedKernel d (ω,wordEnd a) E := by
  rw [wordCylinder,quenched_prefix_tail_apply ω x a.1 (wordPath a) hE,quenchedKernel_cylinder]
  rfl

lemma quenched_prefix_family {d : ℕ} (ω : Environment d) (x : Site d) (A : Set (Word d))
    (hA : PrefixFreeWords A) (E : Word d → Set (Path d)) (hE : ∀ a ∈ A, MeasurableSet (E a)) :
    quenchedKernel d (ω,x) (⋃ a : A, wordCylinder a ∩ tailPath a.val.1 ⁻¹' E a) =
      ∑' a : A, quenchedKernel d (ω,x) (wordCylinder a) *
        quenchedKernel d (ω,wordEnd a) (E a) := by
  rw [measure_iUnion (fun a b hab => (hA hab).mono Set.inter_subset_left Set.inter_subset_left)
    (fun a : A => (measurableSet_pathCylinder a.val.1 (wordPath a.val)).inter ((measurable_tailPath _) (hE a.val a.property)))]
  apply tsum_congr
  intro a
  exact quenched_restart_word ω x a (hE a a.property)

lemma quenched_prefix_family_bound {d : ℕ} (ω : Environment d) (x : Site d)
    (A : Set (Word d)) (hA : PrefixFreeWords A) (E : Word d → Set (Path d))
    (hE : ∀ a ∈ A, MeasurableSet (E a)) (B : Set (Path d)) (c : ℝ≥0∞)
    (hc : ∀ a ∈ A, c ≤ quenchedKernel d (ω,wordEnd a) (E a))
    (hsub : ∀ a ∈ A, wordCylinder a ∩ tailPath a.1 ⁻¹' E a ⊆ B) :
    c * quenchedKernel d (ω,x) (⋃ a : A, wordCylinder a) ≤ quenchedKernel d (ω,x) B := by
  rw [measure_iUnion (f := fun a : A => wordCylinder a.val) hA
    (fun _ => measurableSet_pathCylinder _ _),← ENNReal.tsum_mul_left]
  calc
    ∑' a : A, c * quenchedKernel d (ω,x) (wordCylinder a) ≤
        ∑' a : A, quenchedKernel d (ω,x) (wordCylinder a) *
          quenchedKernel d (ω,wordEnd a) (E a) := by
      apply ENNReal.tsum_le_tsum
      intro a
      rw [mul_comm c]
      exact mul_le_mul_right (hc a a.property) _
    _ = quenchedKernel d (ω,x) (⋃ a : A, wordCylinder a ∩ tailPath a.val.1 ⁻¹' E a) :=
      (quenched_prefix_family ω x A hA E hE).symm
    _ ≤ _ := measure_mono (Set.iUnion_subset (fun a => hsub a a.property))

lemma word_contact_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (a : Word d) (x : Site d) {E : Set (Path d)} (hE : MeasurableSet E) :
    (∫⁻ ω, pathWeight a.1 (wordPath a) ω *
      quenchedKernel d (ω,x) (E ∩ avoids (wordDepartures a)) ∂environmentLaw μ) =
    (∫⁻ ω, pathWeight a.1 (wordPath a) ω ∂environmentLaw μ) *
      annealed μ x (E ∩ avoids (wordDepartures a)) := by
  let r : Row d := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  rw [path_departure_transfer μ (wordDepartures a) a.1 (wordPath a)
    (fun i hi => ⟨i,hi,rfl⟩) _ (measurable_quenched_avoids_on_rows _ r _ hE),
    annealed_apply μ x (hE.inter (measurableSet_avoids _))]

lemma annealed_ae_quenched {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) {E : Set (Path d)} (hE : MeasurableSet E)
    (h : ∀ᵐ X ∂annealed μ x, X ∈ E) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ᵐ X ∂quenchedKernel d (ω,x), X ∈ E := by
  have hz : annealed μ x Eᶜ = 0 := by
    rw [ae_iff] at h
    exact h
  rw [annealed_apply μ x hE.compl] at hz
  have hm : Measurable (fun ω : Environment d => quenchedKernel d (ω,x) Eᶜ) :=
    ((quenchedKernel d).measurable_coe hE.compl).comp (measurable_id.prodMk measurable_const)
  filter_upwards [(lintegral_eq_zero_iff hm).mp hz] with ω hω
  rw [ae_iff]
  exact hω

lemma annealed_exit_band {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (x : Site d) (v : Fin d → ℝ) (hv : v ≠ 0) (a b : ℝ) :
    ∀ᵐ X ∂annealed μ x, ∃ n, height v (X n) ∉ Set.Icc a b := by
  filter_upwards [finite_supremum μ hell x v hv] with X hX
  by_contra h
  have hb : ∀ n, height v (X n) ∈ Set.Icc a b := by simpa only [not_exists,not_not] using h
  have ht := tendsto_atBot.mp (hX ⟨b,fun n => (hb n).2⟩) (a-1)
  obtain ⟨n,hn⟩ := ht.exists
  have ha := (hb n).1
  linarith

lemma measurableSet_exit_band {d : ℕ} (v : Fin d → ℝ) (a b : ℝ) :
    MeasurableSet {X : Path d | ∃ n, height v (X n) ∉ Set.Icc a b} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n =>
    (((measurable_of_countable (height v)).comp (measurable_pi_apply n)) measurableSet_Icc).compl)

lemma quenched_exit_all_integer_bands {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ (x : Site d) (a b : ℤ),
      ∀ᵐ X ∂quenchedKernel d (ω,x), ∃ n, height v (X n) ∉ Set.Icc (a : ℝ) (b : ℝ) := by
  simp only [ae_all_iff]
  intro x a b
  exact annealed_ae_quenched μ x (measurableSet_exit_band v a b)
    (annealed_exit_band μ hell x v hv a b)

def hitBefore {d : ℕ} (A B : Set (Site d)) : Set (Path d) :=
  {X | ∃ n, X n ∈ A ∧ ∀ i ≤ n, X i ∉ B}

lemma measurableSet_hitBefore {d : ℕ} (A B : Set (Site d)) : MeasurableSet (hitBefore A B) := by
  simp only [hitBefore,Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro n
  exact (((Set.to_countable A).measurableSet).preimage (measurable_pi_apply n)).inter
    (MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
      (((Set.to_countable B).measurableSet).preimage (measurable_pi_apply i)).compl)))

lemma hitBefore_disjoint {d : ℕ} (A B : Set (Site d)) : Disjoint (hitBefore A B) (hitBefore B A) := by
  apply Set.disjoint_left.mpr
  rintro X ⟨n,hn,hB⟩ ⟨m,hm,hA⟩
  rcases le_total n m with h | h
  · exact hA n h hn
  · exact hB m h hm

lemma hitBefore_union_eq_eventual {d : ℕ} (A B : Set (Site d)) (hAB : Disjoint A B) :
    hitBefore A B ∪ hitBefore B A = {X | ∃ n, X n ∈ A ∪ B} := by
  ext X
  constructor
  · rintro (⟨n,hn,_⟩ | ⟨n,hn,_⟩)
    · exact ⟨n,Or.inl hn⟩
    · exact ⟨n,Or.inr hn⟩
  · intro h
    let n := Nat.find h
    have hn := Nat.find_spec h
    have hp (i : ℕ) (hi : i < n) : X i ∉ A ∪ B := Nat.find_min h hi
    rcases hn with ha | hb
    · left
      refine ⟨n,ha,fun i hi hm => ?_⟩
      rcases lt_or_eq_of_le hi with hir | rfl
      · exact hp i hir (Or.inr hm)
      · exact Set.disjoint_left.mp hAB ha hm
    · right
      refine ⟨n,hb,fun i hi hm => ?_⟩
      rcases lt_or_eq_of_le hi with hir | rfl
      · exact hp i hir (Or.inl hm)
      · exact Set.disjoint_left.mp hAB hm hb

lemma hitBefore_tail_subset {d : ℕ} (A B : Set (Site d)) (n : ℕ) (γ : Path d)
    (hB : ∀ i < n, γ i ∉ B) :
    pathCylinder n γ ∩ tailPath n ⁻¹' hitBefore A B ⊆ hitBefore A B := by
  rintro X ⟨hX,m,hm,hbm⟩
  refine ⟨n+m,hm,fun i hi hbi => ?_⟩
  by_cases hin : i < n
  · exact hB i hin (by rwa [hX i hin.le] at hbi)
  · have hn : n ≤ i := by omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
    exact hbm j (by omega) hbi

lemma prefixWord_of_wordCylinder {d : ℕ} (a : Word d) (X : Path d)
    (hX : X ∈ wordCylinder a) (j : ℕ) (hj : j ≤ a.1) :
    prefixWord j X = prefixWord j (wordPath a) := by
  apply (prefixWord_eq_iff j X _).mpr
  refine ⟨rfl,fun i hi => ?_⟩
  rw [wordPath_prefixWord j _ hi]
  exact hX i (hi.trans hj)

def firstPrefixWord {d : ℕ} (P : Word d → Prop) (a : Word d) : Prop :=
  P a ∧ ∀ j < a.1, ¬ P (prefixWord j (wordPath a))

lemma firstPrefixWords_prefixFree {d : ℕ} (P : Word d → Prop) :
    PrefixFreeWords {a | firstPrefixWord P a} := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro X ha hb
  have hea : prefixWord a.val.1 X = a.val := (prefixWord_eq_iff _ _ _).mpr ⟨rfl,ha⟩
  have heb : prefixWord b.val.1 X = b.val := (prefixWord_eq_iff _ _ _).mpr ⟨rfl,hb⟩
  have hn : a.val.1 = b.val.1 := by
    apply le_antisymm
    · by_contra h
      have hlt : b.val.1 < a.val.1 := by omega
      apply a.property.2 _ hlt
      rw [← prefixWord_of_wordCylinder a.val X ha _ hlt.le,heb]
      exact b.property.1
    · by_contra h
      have hlt : a.val.1 < b.val.1 := by omega
      apply b.property.2 _ hlt
      rw [← prefixWord_of_wordCylinder b.val X hb _ hlt.le,hea]
      exact a.property.1
  apply hab
  apply Subtype.ext
  rw [← hea,← heb,hn]

lemma firstPrefixWords_union {d : ℕ} (P : Word d → Prop) :
    (⋃ a : {a | firstPrefixWord P a}, wordCylinder a.val) =
      {X : Path d | ∃ n, P (prefixWord n X)} := by
  ext X
  constructor
  · rintro ⟨_,⟨a,rfl⟩,ha⟩
    refine ⟨a.val.1,?_⟩
    rw [(prefixWord_eq_iff _ _ _).mpr ⟨rfl,ha⟩]
    exact a.property.1
  · intro h
    let n := Nat.find h
    have hn : P (prefixWord n X) := Nat.find_spec h
    have ha : firstPrefixWord P (prefixWord n X) := by
      refine ⟨hn,fun j hj hh => ?_⟩
      have hX : X ∈ wordCylinder (prefixWord n X) := by
        intro i hi
        exact (wordPath_prefixWord n X hi).symm
      rw [← prefixWord_of_wordCylinder _ X hX j hj.le] at hh
      exact Nat.find_min h hj hh
    apply Set.mem_iUnion.mpr
    refine ⟨⟨prefixWord n X,ha⟩,?_⟩
    intro i hi
    exact (wordPath_prefixWord n X hi).symm

def visitAfterWord {d : ℕ} (R A K : Set (Site d)) (a : Word d) : Prop :=
  wordEnd a ∈ A ∧ (∃ j ≤ a.1, wordPath a j ∈ R) ∧ ∀ j ≤ a.1, wordPath a j ∉ K

def visitAfter {d : ℕ} (R A K : Set (Site d)) : Set (Path d) :=
  {X | ∃ n, X n ∈ A ∧ (∃ j ≤ n, X j ∈ R) ∧ ∀ j ≤ n, X j ∉ K}

lemma visitAfter_eq_firstPrefix {d : ℕ} (R A K : Set (Site d)) :
    visitAfter R A K = ⋃ a : {a | firstPrefixWord (visitAfterWord R A K) a}, wordCylinder a.val := by
  rw [firstPrefixWords_union]
  ext X
  change (∃ n, X n ∈ A ∧ (∃ j ≤ n, X j ∈ R) ∧ ∀ j ≤ n, X j ∉ K) ↔
    ∃ n, wordPath (prefixWord n X) n ∈ A ∧
      (∃ j ≤ n, wordPath (prefixWord n X) j ∈ R) ∧ ∀ j ≤ n, wordPath (prefixWord n X) j ∉ K
  apply exists_congr
  intro n
  rw [wordPath_prefixWord n X le_rfl]
  constructor
  · rintro ⟨ha,⟨j,hj,hr⟩,hk⟩
    refine ⟨ha,⟨j,hj,?_⟩,fun j hj => ?_⟩
    · rwa [wordPath_prefixWord n X hj]
    · rw [wordPath_prefixWord n X hj]
      exact hk j hj
  · rintro ⟨ha,⟨j,hj,hr⟩,hk⟩
    refine ⟨ha,⟨j,hj,?_⟩,fun j hj => ?_⟩
    · rwa [wordPath_prefixWord n X hj] at hr
    · have hh := hk j hj
      rwa [wordPath_prefixWord n X hj] at hh

lemma measurableSet_visitAfter {d : ℕ} (R A K : Set (Site d)) : MeasurableSet (visitAfter R A K) := by
  rw [visitAfter_eq_firstPrefix]
  exact MeasurableSet.iUnion (fun _ => measurableSet_pathCylinder _ _)

lemma quenched_visitAfter_bound {d : ℕ} (ω : Environment d) (x : Site d)
    (R A B C : Set (Site d)) (c : ℝ≥0∞)
    (hc : ∀ y ∈ A, c ≤ quenchedKernel d (ω,y) (hitBefore B C)) :
    c * quenchedKernel d (ω,x) (visitAfter R A (B ∪ C)) ≤
      quenchedKernel d (ω,x) (hitBefore R B ∩ hitBefore B C) := by
  rw [visitAfter_eq_firstPrefix]
  apply quenched_prefix_family_bound ω x _ (firstPrefixWords_prefixFree _) (fun _ => hitBefore B C)
    (fun _ _ => measurableSet_hitBefore B C) _ c
  · intro a ha
    exact hc (wordEnd a) ha.1.1
  · intro a ha X hX
    have hp := ha.1
    constructor
    · obtain ⟨j,hj,hr⟩ := hp.2.1
      refine ⟨j,?_,fun i hi hbi => ?_⟩
      · rwa [hX.1 j hj]
      · exact hp.2.2 i (hi.trans hj) (Or.inl (by rwa [← hX.1 i (hi.trans hj)]))
    · exact hitBefore_tail_subset B C a.1 (wordPath a)
        (fun i hi hci => hp.2.2 i hi.le (Or.inr hci)) hX

end DirectionalZeroOne

end OAI
