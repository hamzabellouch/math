import OAI.Probability.DirectionalWalk.AxisCubes

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma nthCommon_shift_prefix {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r s : ℕ) (b : Bool) :
    nthCommonList L s ((commonRestart L)^[r] Z) b =
      tapePrefix (nthCommonList L s ((commonRestart L)^[r] Z) b).1
        (fun j => Z (b,(nthCommonList L r Z b).1+j)) := by
  symm
  apply (tapePrefix_eq_iff _ _ _).mpr
  refine ⟨rfl,?_⟩
  have hh := (nthCommonList_data L _ (common_iterate_positive L Z hZ he r)
    (common_iterate_exists L Z he r) s).2 b
  have hz := common_iterates_shift L Z hZ he r
  intro i
  exact (congr_fun hz (b,i)).symm.trans (hh i)

lemma consecutiveThree_joins {d : ℕ} (L : Bool → Word d → ℕ) (Z : TwoTape (Word d))
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r s t : ℕ) :
    positiveJoin (splitThree (consecutiveThree L r s t Z)).1 =
      concatenateList (reverseTapeList (nthCommonList L (s+t) ((commonRestart L)^[r] Z) false)) ∧
    negativeJoin (splitThree (consecutiveThree L r s t Z)).2 =
      concatenateList (nthCommonList L (r+s) Z true) := by
  have hs := nthCommonList_append L ((commonRestart L)^[r] Z)
    (common_iterate_positive L Z hZ he r) (common_iterate_exists L Z he r) s t false
  have hit : (commonRestart L)^[s] ((commonRestart L)^[r] Z) = (commonRestart L)^[r+s] Z := by
    rw [Nat.add_comm r s,Function.iterate_add_apply]
  rw [hit] at hs
  constructor
  · dsimp only [positiveJoin,splitThree,consecutiveThree]
    rw [← reverseTapeList_append,← hs]
  · dsimp only [negativeJoin,splitThree,consecutiveThree]
    rw [← nthCommonList_append L Z hZ he r s true]

lemma signedTotal_consecutiveThree {α G : Type*} [AddCommGroup G]
    (L : Bool → α → ℕ) (D : α → G) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r s t : ℕ) :
    signedTotal D (splitThree (consecutiveThree L r s t Z)).1 =
      listTotal D (nthCommonList L (r+s+t) Z false) := by
  rw [nthCommonList_append L Z hZ he (r+s) t false,listTotal_append,
    nthCommonList_append L Z hZ he r s false,listTotal_append]
  simp only [signedTotal,splitThree,consecutiveThree]
  abel

lemma consecutiveFour_total {α G : Type*} [AddCommGroup G]
    (L : Bool → α → ℕ) (D : Bool → α → G) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (u r s t : ℕ) :
    pairTotal D (consecutiveFour L u r s t Z).1 +
      signedTotal (D false) (splitThree (consecutiveFour L u r s t Z).2).1 =
      listTotal (D false) (nthCommonList L (u+(r+s+t)) Z false) +
      listTotal (D true) (nthCommonList L u Z true) := by
  dsimp only [consecutiveFour]
  rw [signedTotal_consecutiveThree L (D false) _ (common_iterate_positive L Z hZ he u)
    (common_iterate_exists L Z he u),nthCommonList_append L Z hZ he u (r+s+t) false,
    listTotal_append,pairTotal]
  ac_rfl

lemma nthCommon_index_height {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) (b : Bool) :
    tapeHeight (L b) (fun j => Z (b,j)) (nthCommonList L r Z b).1 = commonDepth L Z r :=
  cutListIndex_spec (L b) (commonDepth L Z r) _ (hZ b) ((commonDepth_spec L Z hZ he r).1 b)

lemma listTotal_nthCommon {α G : Type*} [AddCommGroup G]
    (L : Bool → α → ℕ) (D : α → G) (Z : TwoTape α) (r : ℕ) (b : Bool) :
    listTotal D (nthCommonList L r Z b) =
      ∑ j ∈ Finset.range (nthCommonList L r Z b).1, D (Z (b,j)) := by
  exact listTotal_prefix D _ _

lemma departure_between_common {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart (placedWidth e))^[r] Z) ∈ commonCut (placedWidth e) H)
    (a c h : ℕ) (ha : commonDepth (placedWidth e) Z a < h)
    (hc : h ≤ commonDepth (placedWidth e) Z c)
    (b : Bool) (i t : ℕ) (ht : t < (Z (b,i)).1)
    (hd : -axisHeight e (opposedSite e Z b i t) = (h : ℤ)) :
    (nthCommonList (placedWidth e) a Z b).1 ≤ i ∧
      i < (nthCommonList (placedWidth e) c Z b).1 := by
  have hpos : ∀ b i, 0 < placedWidth e b (Z (b,i)) := fun b i => slabRecords_pos _ _ (hZ b i)
  have hs := opposed_departure_band e Z hZ b i t ht
  dsimp only at hs
  rw [hd] at hs
  have hm := (tapeHeight_strictMono (placedWidth e b) (fun j => Z (b,j)) (hpos b)).monotone
  have hea := nthCommon_index_height (placedWidth e) Z hpos he a b
  have hec := nthCommon_index_height (placedWidth e) Z hpos he c b
  have hi : tapeHeight (placedWidth e b) (fun j => Z (b,j)) (i+1) =
      tapeHeight (placedWidth e b) (fun j => Z (b,j)) i + placedWidth e b (Z (b,i)) := by
    exact Finset.sum_range_succ _ _
  constructor
  · by_contra hn
    have hh := hm (show i+1 ≤ (nthCommonList (placedWidth e) a Z b).1 by omega)
    rw [hea,hi] at hh
    omega
  · by_contra hn
    have hh := hm (show (nthCommonList (placedWidth e) c Z b).1 ≤ i by omega)
    rw [hec] at hh
    omega

lemma commonBand_experiment_contact {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart (placedWidth e))^[r] Z) ∈ commonCut (placedWidth e) H)
    (u r s t h : ℕ) (ha : commonDepth (placedWidth e) Z (u+r) < h)
    (hc : h ≤ commonDepth (placedWidth e) Z (u+r+s)) (hcon : contactDepth e Z h) :
    let p := consecutiveFour (placedWidth e) u r s t Z
    ((threeHeight (placedWidth e) p.2,pairTotal (fun _ => wordEnd) p.1+
      signedTotal wordEnd (splitThree p.2).1),splitThree p.2) ∈ experimentContact e := by
  let L := placedWidth e
  have hpos : ∀ b i, 0 < L b (Z (b,i)) := fun b i => slabRecords_pos _ _ (hZ b i)
  have hmono := (commonDepth_strictMono L Z he).monotone
  obtain ⟨y,⟨⟨i,ti,hti,hyi⟩,⟨j,tj,htj,hyj⟩⟩,hy⟩ := hcon
  have hi := departure_between_common e Z hZ he (u+r) (u+r+(s+t)) h ha
    (hc.trans (hmono (by omega))) false i ti hti (by rwa [hyi])
  have hj := departure_between_common e Z hZ he u (u+(r+s)) h
    ((hmono (by omega : u ≤ u+r)).trans_lt ha) (by simpa [Nat.add_assoc] using hc)
    true j tj htj (by rwa [hyj])
  let Y := (commonRestart L)^[u] Z
  have hYY : (commonRestart L)^[r] Y = (commonRestart L)^[u+r] Z := by
    dsimp [Y]
    rw [Nat.add_comm u r,Function.iterate_add_apply]
  have hjoin := consecutiveThree_joins L Y (common_iterate_positive L Z hpos he u)
    (common_iterate_exists L Z he u) r s t
  rw [hYY] at hjoin
  have hip := reverseSlice_departure (fun j => Z (false,j))
    (nthCommonList L (u+r) Z false).1
    (nthCommonList L (s+t) ((commonRestart L)^[u+r] Z) false).1 i ti
    (fun j => (hZ false j).2.1) hi.1
    (by rw [← nthCommon_length_add L Z hpos he (u+r) (s+t) false];exact hi.2) hti
  have hjp := forwardSlice_departure (fun j => Z (true,j))
    (nthCommonList L u Z true).1 (nthCommonList L (r+s) Y true).1 j tj
    (fun j => (hZ true j).2.1) hj.1
    (by rw [← nthCommon_length_add L Z hpos he u (r+s) true];exact hj.2) htj
  rw [← nthCommon_shift_prefix L Z hpos he (u+r) (s+t) false,
    ← nthCommon_length_add L Z hpos he (u+r) (s+t) false] at hip
  rw [← nthCommon_shift_prefix L Z hpos he u (r+s) true] at hjp
  obtain ⟨v,hv,hev⟩ := hip
  obtain ⟨w,hw,hew⟩ := hjp
  dsimp only
  change ∃ v < (positiveJoin (splitThree (consecutiveThree L r s t Y)).1).1,
    ∃ w < (negativeJoin (splitThree (consecutiveThree L r s t Y)).2).1,
      wordPath (positiveJoin (splitThree (consecutiveThree L r s t Y)).1) v =
      wordPath (negativeJoin (splitThree (consecutiveThree L r s t Y)).2) w +
        (pairTotal (fun _ => wordEnd) (nthCommonList L u Z) +
          signedTotal wordEnd (splitThree (consecutiveThree L r s t Y)).1-stepVector e)
  rw [hjoin.1,hjoin.2]
  refine ⟨v,hv,w,hw,?_⟩
  have htot := consecutiveFour_total L (fun _ => wordEnd) Z hpos he u r s t
  change pairTotal (fun _ => wordEnd) (nthCommonList L u Z) +
      signedTotal wordEnd (splitThree (consecutiveThree L r s t Y)).1 = _ at htot
  rw [htot,listTotal_nthCommon,listTotal_nthCommon,hev,hew]
  have hadd : u+r+(s+t) = u+(r+s+t) := by omega
  rw [hadd]
  simp only [opposedSite,opposedAnchor,Bool.false_eq_true,↓reduceIte] at hyi hyj
  have heq := hyi.trans hyj.symm
  abel_nf at heq ⊢
  simpa only [add_assoc] using congrArg (fun x => x + ∑ j ∈ Finset.range (nthCommonList L (u+(r+s+t)) Z false).1, wordEnd (Z (false,j))) heq

lemma averageProd_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (n : ℕ) (M : Fin n → Measure α) (P : Measure β) [SFinite P] :
    (((n : ℝ≥0∞)⁻¹ • ∑ i, M i).prod P) =
      (n : ℝ≥0∞)⁻¹ • ∑ i, (M i).prod P := by
  rw [Measure.prod_smul_left]
  congr 1
  rw [← Measure.sum_fintype,Measure.prod_sum_left,Measure.sum_fintype]

lemma averageProd_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (n : ℕ) (P : Measure α) (M : Fin n → Measure β) [∀ i, SFinite (M i)] :
    P.prod ((n : ℝ≥0∞)⁻¹ • ∑ i, M i) =
      (n : ℝ≥0∞)⁻¹ • ∑ i, P.prod (M i) := by
  have : SFinite (∑ i, M i) := by
    rw [← Measure.sum_fintype]
    infer_instance
  rw [Measure.prod_smul_right]
  congr 1
  rw [← Measure.sum_fintype,Measure.prod_sum_right,Measure.sum_fintype]

lemma average_ge (n : ℕ) (hn : 0 < n) (c : ℝ≥0∞) (f : Fin n → ℝ≥0∞)
    (h : ∀ i, c ≤ f i) : c ≤ (n : ℝ≥0∞)⁻¹ * ∑ i, f i := by
  have hne : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  calc
    c = (n : ℝ≥0∞)⁻¹ * ∑ _i : Fin n, c := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← mul_assoc,ENNReal.inv_mul_cancel hne (by finiteness),one_mul]
    _ ≤ _ := by
      gcongr
      exact h _

lemma fourWindow_average {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (n : ℕ) [NeZero n] (E : Set (TwoTapeList α × ThreeChunk α)) :
    ((windowCommonLaw ν L n n).prod (threeChunkLaw ν L n)) E =
      (n : ℝ≥0∞)⁻¹ * ∑ u : Fin n, (n : ℝ≥0∞)⁻¹ * ∑ r : Fin n,
        (n : ℝ≥0∞)⁻¹ * ∑ s : Fin n, (n : ℝ≥0∞)⁻¹ * ∑ t : Fin n,
          ((nthCommonLaw ν L (n+u)).prod ((nthCommonLaw ν L (n+r)).prod
            ((nthCommonLaw ν L (7*n+s)).prod (nthCommonLaw ν L (n+t))))) E := by
  simp only [windowCommonLaw,threeChunkLaw]
  simp_rw [averageProd_left,averageProd_right]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply]

lemma fourWindow_ge {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (n : ℕ) [NeZero n] (E : Set (TwoTapeList α × ThreeChunk α))
    (c : ℝ≥0∞) (h : ∀ u r s t : Fin n,
      c ≤ ((nthCommonLaw ν L (n+u)).prod ((nthCommonLaw ν L (n+r)).prod
        ((nthCommonLaw ν L (7*n+s)).prod (nthCommonLaw ν L (n+t))))) E) :
    c ≤ ((windowCommonLaw ν L n n).prod (threeChunkLaw ν L n)) E := by
  rw [fourWindow_average]
  exact average_ge n (Nat.pos_of_ne_zero (NeZero.ne n)) c _ (fun u =>
    average_ge n (Nat.pos_of_ne_zero (NeZero.ne n)) c _ (fun r =>
      average_ge n (Nat.pos_of_ne_zero (NeZero.ne n)) c _ (fun s =>
        average_ge n (Nat.pos_of_ne_zero (NeZero.ne n)) c _ (fun t => h u r s t))))

end DirectionalZeroOne

end OAI
