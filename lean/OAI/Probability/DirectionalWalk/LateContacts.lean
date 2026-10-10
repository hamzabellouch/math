import OAI.Probability.DirectionalWalk.LatePrefixes

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def lateContactEvent {d ι : ℕ} (e : Step d) (k r N : ℕ)
    (E : Fin ι → Set (Path d)) (z : Fin ι → Site d) : Set (Path d × Path d) :=
  {p | ∃ q, p.1 ∈ E q ∧ ∃ t τ, t ≤ τ ∧
    AxisBridgeWord e k (prefixWord t p.1) ∧
    (∀ j, t ≤ j → j ≤ τ → (k : ℤ) ≤ axisHeight e (p.1 j) ∧ axisHeight e (p.1 j) < (N : ℤ)) ∧
    (∃ j, t ≤ j ∧ j ≤ τ ∧ (r : ℤ) ≤ axisHeight e (p.1 j)) ∧
    (∃ j, p.2 j+z q = p.1 τ) ∧
    (∀ i, t ≤ i → i < τ → ∀ j, p.2 j+z q ≠ p.1 i)}

lemma lateContactEvent_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (k r N m : ℕ) (hkr : k ≤ r) (hrN : r ≤ N)
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (z : Fin ι → Site d) (hz : ∀ q, axisHeight e (z q) = (N : ℤ)-1)
    (hΔ : axisReachProb μ e (r-k)-axisReachProb μ e (N-k) ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    ((annealed μ 0).prod (conditioned μ (axisDirection (oppositeStep e))))
      (lateContactEvent e k r N E z) ≤
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  refine (measure_mono (t := latePrefixEvent e k (r-k) (N-k)
      (fun a q => prependRelative a ⁻¹' E q) (fun a q => z q-wordEnd a)) ?_).trans ?_
  · rintro ⟨X,Y⟩ ⟨q,hq,t,τ,htτ,ha,hband,hr,hh,hbefore⟩
    exact latePrefixEvent_of_contact e k r N hkr (hkr.trans hrN) E z X Y q hq t τ htτ ha hband hr hh hbefore
  · apply latePrefixEvent_bound μ hell e k (r-k) (N-k) m (Nat.sub_le_sub_right hrN k)
      _ (fun a q => measurable_prependRelative a (hE q))
      (fun a i j hij => (hdis hij).preimage _) _ _ hΔ
    intro a ha q
    rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,hz q,ha.1,Nat.cast_sub (hkr.trans hrN)]
    omega

lemma conditioned_bridge_late_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (k r N m : ℕ) (hkr : k ≤ r) (hrN : r ≤ N)
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (z : Fin ι → Site d) (hz : ∀ q, axisHeight e (z q) = (N : ℤ)-1)
    (hΔ : axisReachProb μ e (r-k)-axisReachProb μ e (N-k) ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    ((ProbabilityTheory.cond (annealed μ 0) (reachRecord (axisDirection e) N)).prod
      (conditioned μ (axisDirection (oppositeStep e)))) (lateContactEvent e k r N E z) ≤
      (axisReachProb μ e N)⁻¹ *
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  have : IsFiniteMeasure (conditioned μ (axisDirection (oppositeStep e))) := by
    unfold conditioned
    infer_instance
  rw [ProbabilityTheory.cond,Measure.prod_smul_left,Measure.smul_apply,← axisReachProb_eq_record]
  change (axisReachProb μ e N)⁻¹ * _ ≤ _
  rw [mul_assoc]
  apply mul_le_mul_right
  refine (Measure.prod_mono Measure.restrict_le_self le_rfl _).trans ?_
  exact lateContactEvent_bound μ hell e k r N m hkr hrN E hE hdis z hz hΔ

lemma iid_tape_strongLaw {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → ℝ)
    (hf : Measurable f) (hi : Integrable f ν) :
    ∀ᵐ Z ∂Measure.infinitePi (fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f (Z i))/n) atTop (𝓝 (∫ a, f a ∂ν)) := by
  let P := Measure.infinitePi (fun _ : ℕ => ν)
  have hid (k : ℕ) : IdentDistrib (fun Z : ℕ → α => f (Z k)) f P ν := by
    refine ⟨(hf.comp (measurable_pi_apply k)).aemeasurable,hf.aemeasurable,?_⟩
    rw [show P.map (fun Z => f (Z k)) = (P.map (fun Z => Z k)).map f from
      (Measure.map_map hf (measurable_pi_apply k)).symm,Measure.infinitePi_map_eval]
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => f) (fun _ => hf)
  have hx := strong_law_ae_real (fun k (Z : ℕ → α) => f (Z k))
    ((hid 0).integrable_iff.mpr hi) (fun i j hij => hind.indepFun hij)
    (fun k => (hid k).trans (hid 0).symm)
  rwa [(hid 0).integral_eq] at hx

lemma tapeHeight_strongLaw {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hi : Integrable (fun a => (L a : ℝ)) ν) :
    ∀ᵐ Z ∂Measure.infinitePi (fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => (tapeHeight L Z n : ℝ)/n) atTop (𝓝 (∫ a, (L a : ℝ) ∂ν)) := by
  simpa only [tapeHeight,Nat.cast_sum] using iid_tape_strongLaw ν _ (measurable_of_countable _) hi

lemma firstCommonBlock_height {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    chunkHeight L (firstCommonBlock L Z) = firstCommonWidth L Z := by
  exact ((commonCutList_atom_iff L _ Z hZ (firstCommonBlock L Z)).mp
    ⟨(firstCommonWidth_spec L Z he).2.1,rfl⟩).1 false

lemma commonDepth_strongLaw {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν)) :
    ∀ᵐ Z ∂twoTapeLaw ν,
      Tendsto (fun n : ℕ => (commonDepth L Z n : ℝ)/n) atTop
        (𝓝 (∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)) := by
  have ha : (fun Z => (chunkHeight L (firstCommonBlock L Z) : ℝ)) =ᵐ[twoTapeLaw ν]
      fun Z => (firstCommonWidth L Z : ℝ) := by
    filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
      (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,he] with Z hZ he
    exact_mod_cast firstCommonBlock_height L Z hZ he
  have hii : Integrable (fun a => (chunkHeight L a : ℝ)) (commonBlockLaw ν L) := by
    rw [commonBlockLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_firstCommonBlock L).aemeasurable]
    exact hi.congr ha.symm
  have hei : (∫ a, (chunkHeight L a : ℝ) ∂commonBlockLaw ν L) =
      ∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν := by
    rw [commonBlockLaw,integral_map (measurable_firstCommonBlock L).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    exact integral_congr_ae ha
  let : IsProbabilityMeasure (commonBlockLaw ν L) :=
    probabilityMeasure_map (measurable_firstCommonBlock L).aemeasurable
  have hh := iid_tape_strongLaw (commonBlockLaw ν L) (fun a => (chunkHeight L a : ℝ))
    (measurable_of_countable _) hii
  rw [← commonBlocks_map ν L hL he] at hh
  have hm : Measurable (commonBlocks L) := by
    apply Measurable.of_eval
    intro k
    exact (measurable_firstCommonBlock L).comp ((measurable_commonRestart L).iterate k)
  have ht := ae_of_ae_map hm.aemeasurable hh
  rw [hei] at ht
  filter_upwards [ht,ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,
    ae_common_iterates ν L hL he] with Z hZ hpos hiter
  have hsum (n : ℕ) : (∑ i ∈ Finset.range n, (chunkHeight L (commonBlocks L Z i) : ℝ)) =
      (commonDepth L Z n : ℝ) := by
    simp only [commonDepth,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hposi : ∀ b j, 0 < L b (((commonRestart L)^[i] Z) (b,j)) := by
      rw [← (commonDepth_spec L Z hpos hiter i).2.1]
      exact fun b j => hpos b _
    exact_mod_cast firstCommonBlock_height L _ hposi (hiter i)
  simpa only [hsum] using hZ

lemma placed_slab_positive {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) (b : Bool) :
    ∀ᵐ a ∂slabLaw μ (axisDirection (placedAxis e b)), 0 < placedWidth e b a := by
  filter_upwards [ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero _) (hp b)] with a ha
  exact slabRecords_pos _ _ ha

lemma placed_common_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) (H : ℕ) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    annealed μ 0 (nonBacktracking (axisDirection e)) *
      annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))) ≤
      twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))) (commonCut (placedWidth e) H) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  rw [commonCut_mass,show Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection (placedAxis e false)))
      (renewalCut (placedWidth e false) H) = axisReachProb μ e H from axis_tapeCut_mass μ hell _ (hp false) H,
    show Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection (placedAxis e true)))
      (renewalCut (placedWidth e true) H) = axisReachProb μ (oppositeStep e) H from axis_tapeCut_mass μ hell _ (hp true) H]
  exact mul_le_mul' (axisReachProb_lower μ hell e H) (axisReachProb_lower μ hell (oppositeStep e) H)

lemma placed_common_data {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    (∀ᵐ Z ∂twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))),
      ∃ H, 0 < H ∧ Z ∈ commonCut (placedWidth e) H) ∧
    Integrable (fun Z => (firstCommonWidth (placedWidth e) Z : ℝ))
      (twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b)))) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  have hc := mul_ne_zero (ne_of_gt (hp false)) (ne_of_gt (hp true))
  exact ⟨ae_exists_commonCut _ _ (placed_slab_positive μ hell e hp) _ hc (placed_common_lower μ hell e hp),
    integrable_firstCommonWidth _ _ (placed_slab_positive μ hell e hp) _ hc (placed_common_lower μ hell e hp)⟩

lemma placed_slabRadius_integrable {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) (b : Bool) :
    Integrable slabRadius (slabLaw μ (axisDirection (placedAxis e b))) := by
  have hn : annealed μ 0 (nonBacktracking (-axisDirection e)) > 0 := by
    rw [← axisDirection_opposite]
    exact hp true
  have hh := integrable_slabRadius_normalized μ hell _ (axisDirection_ne_zero e)
    (axisDirection_normalized e).1 (axisDirection_normalized e).2 (hp false) hn
  cases b
  · exact hh.1
  · simpa only [placedAxis,↓reduceIte,axisDirection_opposite] using hh.2

lemma placed_wordEnd_integrable {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) (b : Bool) (i : Fin d) :
    Integrable (fun a => (wordEnd a i : ℝ)) (slabLaw μ (axisDirection (placedAxis e b))) := by
  have hh := integrable_slabProjection μ hell _ (axisDirection_ne_zero _) (hp b)
    (placed_slabRadius_integrable μ hell e hp b) (Pi.single i 1)
  change Integrable (fun a => height (Pi.single i 1) (wordEnd a)) _ at hh
  simpa [height,Pi.single_apply] using hh

lemma concatenateWords_end {d : ℕ} (n : ℕ) (a : Fin n → Word d) :
    wordEnd (concatenateWords n a) = ∑ i, wordEnd (a i) := by
  induction n with
  | zero => simp [concatenateWords,wordEnd,prefixWord,wordPath,extendPrefix]
  | succ n ih =>
    change wordPath (appendWord (concatenateWords n (fun i => a i.castSucc)) (a (Fin.last n)))
      ((concatenateWords n (fun i => a i.castSucc)).1+(a (Fin.last n)).1) = _
    rw [appendWord_after _ _ le_rfl]
    change wordEnd (concatenateWords n _) + wordEnd (a (Fin.last n)) = _
    rw [ih,Fin.sum_univ_castSucc]

lemma concatenateList_end {d : ℕ} (a : TapeList (Word d)) :
    wordEnd (concatenateList a) = listTotal wordEnd a := concatenateWords_end a.1 a.2

lemma fin_prefix_sum_castSucc {G : Type*} [AddCommMonoid G] {n : ℕ}
    (f : Fin (n+1) → G) (i : Fin n) :
    (∑ j : Fin (n+1) with j < i.castSucc, f j) = ∑ j : Fin n with j < i, f j.castSucc := by
  classical
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp [show ¬Fin.last n < i.castSucc by simp only [Fin.lt_def,Fin.val_last,Fin.val_castSucc];omega]

lemma fin_prefix_sum_last {G : Type*} [AddCommMonoid G] {n : ℕ}
    (f : Fin (n+1) → G) :
    (∑ j : Fin (n+1) with j < Fin.last n, f j) = ∑ j : Fin n, f j.castSucc := by
  classical
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp

lemma concatenateWords_site {d n : ℕ} (a : Fin n → Word d)
    (h0 : ∀ i, wordPath (a i) 0 = 0) (i : Fin n) (t : ℕ) (ht : t ≤ (a i).1) :
    wordPath (concatenateWords n a) ((∑ j : Fin n with j < i, (a j).1)+t) =
      (∑ j : Fin n with j < i, wordEnd (a j)) + wordPath (a i) t := by
  classical
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert ht
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro ht
      rw [fin_prefix_sum_last,fin_prefix_sum_last]
      change wordPath (appendWord (concatenateWords n (fun j => a j.castSucc)) (a (Fin.last n)))
        ((∑ j : Fin n, (a j.castSucc).1)+t) = _
      rw [← concatenateWords_length,appendWord_after _ _ ht,← concatenateWords_end]
      rfl
    · intro ht
      rw [fin_prefix_sum_castSucc,fin_prefix_sum_castSucc]
      change wordPath (appendWord (concatenateWords n (fun j => a j.castSucc)) (a (Fin.last n))) _ = _
      rw [appendWord_before _ _ (h0 _) ?_]
      · exact ih (fun j => a j.castSucc) (fun j => h0 _) i ht
      · rw [concatenateWords_length]
        have hs : (∑ j : Fin n with j < i, (a j.castSucc).1)+(a i.castSucc).1 ≤
            ∑ j : Fin n, (a j.castSucc).1 := by
          rw [add_comm,← Finset.sum_insert (f := fun j : Fin n => (a j.castSucc).1) (a := i) (s := Finset.univ.filter (fun j : Fin n => j < i))
            (by simp)]
          exact Finset.sum_le_sum_of_subset (by intro j hj;simp)
        omega

lemma fin_reverse_prefix_sum {G : Type*} [AddCommMonoid G] {n : ℕ}
    (f : Fin n → G) (i : Fin n) :
    (∑ j : Fin n with j < i.rev, f j.rev) + (∑ j : Fin n with j ≤ i, f j) = ∑ j, f j := by
  classical
  have he : (∑ j : Fin n with j < i.rev, f j.rev) = ∑ j : Fin n with ¬j ≤ i, f j := by
    simp only [Finset.sum_filter]
    have hh := Equiv.sum_comp Fin.revPerm (fun j : Fin n => if ¬j ≤ i then f j else 0)
    simpa only [Fin.revPerm_apply,not_le,Fin.lt_rev_iff] using hh
  rw [he,add_comm]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

lemma fin_prefix_sum_range {G : Type*} [AddCommMonoid G] {n : ℕ}
    (f : ℕ → G) (k : ℕ) (hk : k ≤ n) :
    (∑ j : Fin n with j.val < k, f j) = ∑ j ∈ Finset.range k, f j := by
  classical
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then f j else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

lemma reversePrefix_site {d n : ℕ} (Z : ℕ → Word d)
    (h0 : ∀ j < n, wordPath (Z j) 0 = 0) (i : Fin n) (t : ℕ) (ht : t ≤ (Z i).1) :
    wordPath (concatenateList (reverseTapeList (tapePrefix n Z)))
      ((∑ j : Fin n with j < i.rev, (Z j.rev).1)+t) =
      (∑ j ∈ Finset.range n, wordEnd (Z j)) - (∑ j ∈ Finset.range (i.val+1), wordEnd (Z j)) +
        wordPath (Z i) t := by
  have hs := concatenateWords_site (fun j : Fin n => Z j.rev)
    (fun j => h0 _ j.rev.isLt) i.rev t (by simpa using ht)
  simp only [Fin.rev_rev] at hs
  change wordPath (concatenateList (reverseTapeList (tapePrefix n Z))) _ = _ at hs
  rw [hs]
  congr 1
  have hh := fin_reverse_prefix_sum (fun j : Fin n => wordEnd (Z j)) i
  have he : (∑ j : Fin n with j ≤ i, wordEnd (Z j)) = ∑ j ∈ Finset.range (i.val+1), wordEnd (Z j) := by
    have heq : Finset.univ.filter (fun j : Fin n => j ≤ i) =
        Finset.univ.filter (fun j : Fin n => j.val < i.val+1) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.le_def]
      omega
    rw [heq]
    exact fin_prefix_sum_range (fun j => wordEnd (Z j)) (i.val+1) (by omega)
  rw [he,Fin.sum_univ_eq_sum_range (fun j => wordEnd (Z j))] at hh
  exact eq_sub_of_add_eq hh

end DirectionalZeroOne

end OAI
