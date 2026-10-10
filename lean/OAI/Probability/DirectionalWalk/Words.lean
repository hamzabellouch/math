import OAI.Probability.DirectionalWalk.Regeneration

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

abbrev Word (d : ℕ) := Σ n : ℕ, (Finset.Iic n → Site d)

instance (d : ℕ) : MeasurableSpace (Word d) := ⊤
instance (d : ℕ) : MeasurableSingletonClass (Word d) := ⟨fun _ => trivial⟩

def wordPath {d : ℕ} (γ : Word d) : Path d := extendPrefix γ.1 γ.2

def prefixWord {d : ℕ} (n : ℕ) (X : Path d) : Word d := ⟨n,frestrictLe n X⟩

lemma wordPath_prefixWord {d : ℕ} (n : ℕ) (X : Path d) {i : ℕ} (hi : i ≤ n) :
    wordPath (prefixWord n X) i = X i := by
  exact extendPrefix_apply n (frestrictLe n X) hi

lemma prefixWord_eq_iff {d : ℕ} (n : ℕ) (X : Path d) (γ : Word d) :
    prefixWord n X = γ ↔ n = γ.1 ∧ X ∈ pathCylinder γ.1 (wordPath γ) := by
  rcases γ with ⟨m,a⟩
  constructor
  · intro h
    have hm := congrArg Sigma.fst h
    change n = m at hm
    subst m
    have ha : frestrictLe n X = a := by simpa [prefixWord] using h
    refine ⟨rfl,fun i hi => ?_⟩
    rw [wordPath, extendPrefix_apply n a hi, ← ha]
    rfl
  · rintro ⟨rfl,h⟩
    change (⟨n, frestrictLe n X⟩ : Word d) = ⟨n,a⟩
    congr 1
    funext i
    simpa [wordPath, extendPrefix_apply n a (Finset.mem_Iic.mp i.property)] using
      h i (Finset.mem_Iic.mp i.property)

lemma measurable_prefixWord {d : ℕ} (n : ℕ) : Measurable (prefixWord (d := d) n) := by
  apply measurable_to_countable'
  intro γ
  have heq : (prefixWord n) ⁻¹' {γ} =
      {X : Path d | n = γ.1} ∩ pathCylinder γ.1 (wordPath γ) := by
    ext X; exact prefixWord_eq_iff n X γ
  rw [heq]
  exact (MeasurableSet.const _).inter (measurableSet_pathCylinder _ _)

def RegenerationWord {d : ℕ} (v : Fin d → ℝ) (γ : Word d) : Prop :=
  0 < γ.1 ∧ wordPath γ 0 = 0 ∧
  (∀ i < γ.1, ∃ e : Step d, wordPath γ (i+1) = wordPath γ i + stepVector e) ∧
  (∀ i < γ.1, 0 ≤ height v (wordPath γ i) ∧ height v (wordPath γ i) < height v (wordPath γ γ.1)) ∧
  (∀ j < γ.1, strictRecord v (wordPath γ) j →
    ∃ k, j < k ∧ k < γ.1 ∧ height v (wordPath γ k) < height v (wordPath γ j))

noncomputable def annealedWordWeight {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (γ : Word d) : ℝ≥0∞ := ∫⁻ ω, pathWeight γ.1 (wordPath γ) ω ∂environmentLaw μ

noncomputable def firstCutTime {d : ℕ} (v : Fin d → ℝ) (X : Path d) : ℕ :=
  by
    classical
    exact if h : ∃ n, trueCut v X n then Nat.find h else 0

lemma firstCutTime_spec {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (h : ∃ n, trueCut v X n) : trueCut v X (firstCutTime v X) ∧
      ∀ i < firstCutTime v X, ¬trueCut v X i := by
  classical
  simp only [firstCutTime, dite_eq_left h]
  exact ⟨Nat.find_spec h,fun i hi => Nat.find_min h hi⟩

lemma firstCutTime_eq_pos_iff {d : ℕ} (v : Fin d → ℝ) (X : Path d) {n : ℕ} (hn : 0 < n) :
    firstCutTime v X = n ↔ trueCut v X n ∧ ∀ i < n, ¬trueCut v X i := by
  classical
  constructor
  · intro h
    have hex : ∃ n, trueCut v X n := by
      by_contra hh
      simp only [firstCutTime, dite_eq_right hh] at h
      omega
    have hs := firstCutTime_spec v X hex
    simpa [h] using hs
  · rintro ⟨ht,hm⟩
    have hex : ∃ n, trueCut v X n := ⟨n,ht⟩
    simp only [firstCutTime, dite_eq_left hex]
    exact (Nat.find_eq_iff hex).mpr ⟨ht,hm⟩

lemma firstCutTime_eq_zero_iff {d : ℕ} (v : Fin d → ℝ) (X : Path d) :
    firstCutTime v X = 0 ↔ ¬∃ n, trueCut v X n := by
  constructor
  · intro hz hex
    have hs := (firstCutTime_spec v X hex).1.1.1
    omega
  · intro h; simp [firstCutTime,h]

lemma measurable_firstCutTime {d : ℕ} (v : Fin d → ℝ) : Measurable (firstCutTime v) := by
  apply measurable_to_countable'
  intro n
  by_cases hn : n = 0
  · subst n
    have heq : (firstCutTime v) ⁻¹' {0} = (⋃ n, {X : Path d | trueCut v X n})ᶜ := by
      ext X
      simp only [Set.mem_preimage, Set.mem_singleton_iff, firstCutTime_eq_zero_iff,
        Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    rw [heq]
    exact (MeasurableSet.iUnion (fun n => measurableSet_trueCut v n)).compl
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    have heq : (firstCutTime v) ⁻¹' {n} = {X : Path d | trueCut v X n} ∩
        ⋂ i, ⋂ (_ : i < n), {X : Path d | ¬trueCut v X i} := by
      ext X
      simp only [Set.mem_preimage, Set.mem_singleton_iff, firstCutTime_eq_pos_iff v X hp,
        Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact (measurableSet_trueCut v n).inter (MeasurableSet.iInter (fun i =>
      MeasurableSet.iInter (fun _ => (measurableSet_trueCut v i).compl)))

noncomputable def firstWord {d : ℕ} (v : Fin d → ℝ) (X : Path d) : Word d :=
  prefixWord (firstCutTime v X) X

noncomputable def cutSuffix {d : ℕ} (v : Fin d → ℝ) (X : Path d) : Path d :=
  shiftPath (-(X (firstCutTime v X))) (tailPath (firstCutTime v X) X)

lemma measurable_firstWord {d : ℕ} (v : Fin d → ℝ) : Measurable (firstWord v) := by
  exact (measurable_from_prod_countable_right (f := fun (p : ℕ × Path d) =>
    prefixWord p.1 p.2) (fun n => measurable_prefixWord n)).comp
    ((measurable_firstCutTime v).prodMk measurable_id)

lemma measurable_cutSuffix {d : ℕ} (v : Fin d → ℝ) : Measurable (cutSuffix v) := by
  apply Measurable.comp (measurable_from_prod_countable_right
    (f := fun (p : ℕ × Path d) => shiftPath (-(p.2 p.1)) (tailPath p.1 p.2))
    (fun n => ?_))
    ((measurable_firstCutTime v).prodMk measurable_id)
  apply Measurable.of_eval
  intro j
  change Measurable (fun X : Path d => X (n+j) + -(X n))
  exact (measurable_pi_apply (n+j)).add (measurable_pi_apply n).neg

lemma firstWord_regeneration {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (h0 : X 0 = 0) (hNN : nearestNeighbour X) (hD : X ∈ nonBacktracking v)
    (hc : ∃ n, trueCut v X n) : RegenerationWord v (firstWord v X) := by
  let m := firstCutTime v X
  change RegenerationWord v (prefixWord m X)
  have hs := firstCutTime_spec v X hc
  have hwp : ∀ i ≤ m, wordPath (firstWord v X) i = X i :=
    fun i hi => wordPath_prefixWord m X hi
  change 0 < m ∧ wordPath (firstWord v X) 0 = 0 ∧
    (∀ i < m, ∃ e : Step d, wordPath (firstWord v X) (i+1) =
      wordPath (firstWord v X) i + stepVector e) ∧
    (∀ i < m, 0 ≤ height v (wordPath (firstWord v X) i) ∧
      height v (wordPath (firstWord v X) i) < height v (wordPath (firstWord v X) m)) ∧
    (∀ j < m, strictRecord v (wordPath (firstWord v X)) j →
      ∃ k, j < k ∧ k < m ∧ height v (wordPath (firstWord v X) k) <
        height v (wordPath (firstWord v X) j))
  refine ⟨hs.1.1.1,?_,?_,?_,?_⟩
  · rw [hwp 0 (Nat.zero_le _)]; exact h0
  · intro i hi
    rw [hwp (i+1) (by omega),hwp i hi.le]
    exact hNN i
  · intro i hi
    rw [hwp i hi.le,hwp m le_rfl]
    exact ⟨hD i,hs.1.1.2 i hi⟩
  · intro j hj hrec
    have hrecX : strictRecord v X j := by
      refine ⟨hrec.1,fun i hi => ?_⟩
      have hh := hrec.2 i hi
      rw [hwp i (by omega),hwp j hj.le] at hh
      exact hh
    have hex : ∃ k, j < k ∧ k < m ∧ height v (X k) < height v (X j) := by
      by_contra h
      push Not at h
      apply hs.2 j hj
      refine ⟨hrecX,fun t => ?_⟩
      by_cases htm : j+t < m
      · by_cases ht0 : t = 0
        · simp [ht0]
        · exact h (j+t) (by omega) htm
      · have hh := hs.1.2 (j+t-m)
        rw [Nat.add_sub_of_le (by omega : m ≤ j+t)] at hh
        exact (hs.1.1.2 j hj).le.trans hh
    obtain ⟨k,hjk,hkm,hk⟩ := hex
    refine ⟨k,hjk,hkm,?_⟩
    rw [hwp k hkm.le,hwp j hj.le]
    exact hk

lemma firstWord_eq_iff {d : ℕ} (v : Fin d → ℝ) (X : Path d) (γ : Word d)
    (hγ : RegenerationWord v γ) : firstWord v X = γ ↔
      X ∈ pathCylinder γ.1 (wordPath γ) ∧
      shiftPath (-(wordPath γ γ.1)) (tailPath γ.1 X) ∈ nonBacktracking v := by
  constructor
  · intro h
    have hpre := (prefixWord_eq_iff (firstCutTime v X) X γ).mp h
    have hc := ((firstCutTime_eq_pos_iff v X hγ.1).mp hpre.1).1
    refine ⟨hpre.2,fun k => ?_⟩
    have hk := hc.2 k
    rw [hpre.2 γ.1 le_rfl] at hk
    change 0 ≤ height v (X (γ.1+k) + -(wordPath γ γ.1))
    rw [height_add, height_neg]
    linarith
  · rintro ⟨hpre,hD⟩
    have hrec : strictRecord v X γ.1 := by
      refine ⟨hγ.1,fun i hi => ?_⟩
      rw [hpre i hi.le,hpre γ.1 le_rfl]
      exact (hγ.2.2.2.1 i hi).2
    have hc : trueCut v X γ.1 := by
      refine ⟨hrec,fun k => ?_⟩
      have hk := hD k
      change 0 ≤ height v (X (γ.1+k) + -(wordPath γ γ.1)) at hk
      rw [height_add,height_neg] at hk
      rw [hpre γ.1 le_rfl]
      linarith
    have hmin : ∀ j < γ.1, ¬trueCut v X j := by
      intro j hj ht
      have hr : strictRecord v (wordPath γ) j := by
        refine ⟨ht.1.1,fun i hi => ?_⟩
        rw [← hpre i (by omega),← hpre j hj.le]
        exact ht.1.2 i hi
      obtain ⟨k,hjk,hkm,hk⟩ := hγ.2.2.2.2 j hj hr
      have hk' := ht.2 (k-j)
      rw [Nat.add_sub_of_le hjk.le,hpre k hkm.le,hpre j hj.le] at hk'
      exact (not_lt_of_ge hk') hk
    have hm := (firstCutTime_eq_pos_iff v X hγ.1).mpr ⟨hc,hmin⟩
    exact (prefixWord_eq_iff (firstCutTime v X) X γ).mpr ⟨hm,hpre⟩

lemma firstWord_event {d : ℕ} (v : Fin d → ℝ) (γ : Word d)
    (hγ : RegenerationWord v γ) (E : Set (Path d)) :
    {X | firstWord v X = γ ∧ cutSuffix v X ∈ E} =
      pathCylinder γ.1 (wordPath γ) ∩ tailPath γ.1 ⁻¹'
        (shiftPath (-(wordPath γ γ.1)) ⁻¹' (E ∩ nonBacktracking v)) := by
  ext X
  constructor
  · rintro ⟨h,hE⟩
    obtain ⟨hpre,hD⟩ := (firstWord_eq_iff v X γ hγ).mp h
    have hm : firstCutTime v X = γ.1 := congrArg Sigma.fst h
    refine ⟨hpre,?_,hD⟩
    simpa only [cutSuffix,hm,hpre γ.1 le_rfl] using hE
  · rintro ⟨hpre,hE,hD⟩
    have h := (firstWord_eq_iff v X γ hγ).mpr ⟨hpre,hD⟩
    have hm : firstCutTime v X = γ.1 := congrArg Sigma.fst h
    refine ⟨h,?_⟩
    simpa only [cutSuffix,hm,hpre γ.1 le_rfl] using hE

lemma firstWord_event_subset_nonBacktracking {d : ℕ} (v : Fin d → ℝ) (γ : Word d)
    (hγ : RegenerationWord v γ) : {X | firstWord v X = γ} ⊆ nonBacktracking v := by
  intro X hX n
  obtain ⟨hpre,hD⟩ := (firstWord_eq_iff v X γ hγ).mp hX
  by_cases hn : n < γ.1
  · rw [hpre n hn.le]; exact (hγ.2.2.2.1 n hn).1
  · have hk := hD (n-γ.1)
    change 0 ≤ height v (X (γ.1+(n-γ.1)) + -(wordPath γ γ.1)) at hk
    rw [Nat.add_sub_of_le (by omega),height_add,height_neg] at hk
    have hh := hγ.2.2.2.1 0 hγ.1
    rw [hγ.2.1,height_zero] at hh
    change 0 ≤ height v (X n)
    linarith

end DirectionalZeroOne

end OAI
