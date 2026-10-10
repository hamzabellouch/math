import OAI.Probability.DirectionalWalk.MixedTapes

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def coveredDepthBand {d : ℕ} (e : Step d) (low high : ℕ) : Set (TwoTape (Word d)) :=
  {Z | ∃ h, low ≤ h ∧ h < high ∧ contactDepth e Z h}

lemma measurableSet_coveredDepthBand {d : ℕ} (e : Step d) (low high : ℕ) :
    MeasurableSet (coveredDepthBand e low high) := by
  simp only [coveredDepthBand,Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun h => (MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter (measurableSet_contactDepth e h)))

lemma two_cuts_uncovered_mixed {d : ℕ} (e : Step d) (p : (ℕ → Word d) × Path d)
    (hpos : ∀ i, RegenerationWord (axisDirection e) (p.1 i))
    (hneg : GoodSlabPath (axisDirection (oppositeStep e)) p.2)
    (s N low high : ℕ) (hs : 0 < s) (hsN : s ≤ N) (hls : low ≤ s) (hsh : s < high)
    (hcs : p.1 ∈ tapeCut (axisDirection e) s) (hcN : p.1 ∈ tapeCut (axisDirection e) N)
    (hno : mixedTapes e p ∉ coveredDepthBand e low high) :
    finiteLateContact e (N-s) (N-low) N
      (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N p.1))) p.2 := by
  obtain ⟨m,hm⟩ := hcs
  obtain ⟨n,hn⟩ := hcN
  change tapeHeight (slabRecords (axisDirection e)) p.1 m = s at hm
  change tapeHeight (slabRecords (axisDirection e)) p.1 n = N at hn
  have hL : ∀ i, 0 < slabRecords (axisDirection e) (p.1 i) := fun i => slabRecords_pos _ _ (hpos i)
  have hm0 : 0 < m := by
    by_contra hh
    have hmz : m = 0 := by omega
    rw [hmz] at hm
    change 0 = s at hm
    omega
  have hmn : m ≤ n := (tapeHeight_strictMono _ _ hL).le_iff_le.mp (by rw [hm,hn];exact hsN)
  have hgood : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (mixedTapes e p (b,i)) := by
    intro b i
    cases b
    · exact hpos i
    · exact hneg.2 i
  have hh := uncovered_bridge_late e (mixedTapes e p) hgood p.2 hneg (fun _ => rfl)
    m n low high hm0 hmn (by change low ≤ tapeHeight (slabRecords (axisDirection e)) p.1 m;rw [hm];exact hls)
    (by change tapeHeight (slabRecords (axisDirection e)) p.1 m < high;rw [hm];exact hsh)
    (fun h hl hh hc => hno ⟨h,hl,hh,hc⟩)
  change finiteLateContact e (tapeHeight (slabRecords (axisDirection e)) p.1 n-tapeHeight (slabRecords (axisDirection e)) p.1 m)
    (tapeHeight (slabRecords (axisDirection e)) p.1 n-low) (tapeHeight (slabRecords (axisDirection e)) p.1 n)
      (concatenateList (reverseTapeList (tapePrefix n p.1))) p.2 at hh
  rw [hm,hn] at hh
  rw [cutList,cutListIndex_eq _ N p.1 hL hn]
  exact hh

lemma nthCommon_suffix_map {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (r : ℕ) (f : TwoTape α → β) (hf : Measurable f) :
    (twoTapeLaw ν).map (fun Z => (nthCommonList L r Z,f ((commonRestart L)^[r] Z))) =
      (nthCommonLaw ν L r).prod ((twoTapeLaw ν).map f) := by
  apply Measure.ext_of_singleton
  intro a
  have hpair : Measurable (fun Z => (nthCommonList L r Z,f ((commonRestart L)^[r] Z))) :=
    (measurable_nthCommonList L r).prodMk (hf.comp ((measurable_commonRestart L).iterate r))
  have hprod : ((nthCommonLaw ν L r).prod ((twoTapeLaw ν).map f)) {a} =
      nthCommonLaw ν L r {a.1} * ((twoTapeLaw ν).map f) {a.2} := by
    rw [show {a} = {a.1} ×ˢ {a.2} from (Set.singleton_prod_singleton).symm,Measure.prod_prod]
  rw [Measure.map_apply hpair (measurableSet_singleton a),hprod,
    Measure.map_apply hf (measurableSet_singleton _)]
  have heq : (fun Z => (nthCommonList L r Z,f ((commonRestart L)^[r] Z))) ⁻¹' {a} =
      {Z | nthCommonList L r Z = a.1 ∧ (commonRestart L)^[r] Z ∈ f ⁻¹' {a.2}} := by
    rcases a with ⟨a,b⟩
    ext Z;simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.mk.injEq,Set.mem_ofPred_eq]
  rw [heq]
  exact nthCommon_suffix_factorization ν L hL he r a.1 _ (hf (measurableSet_singleton _))

noncomputable def consecutiveThree {α : Type*} (L : Bool → α → ℕ)
    (r s t : ℕ) (Z : TwoTape α) : ThreeChunk α :=
  (nthCommonList L r Z,nthCommonList L s ((commonRestart L)^[r] Z),
    nthCommonList L t ((commonRestart L)^[r+s] Z))

lemma measurable_consecutiveThree {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (r s t : ℕ) :
    Measurable (consecutiveThree L r s t) :=
  (measurable_nthCommonList L r).prodMk
    (((measurable_nthCommonList L s).comp ((measurable_commonRestart L).iterate r)).prodMk
      ((measurable_nthCommonList L t).comp ((measurable_commonRestart L).iterate (r+s))))

lemma consecutiveThree_law {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (r s t : ℕ) :
    (twoTapeLaw ν).map (consecutiveThree L r s t) =
      (nthCommonLaw ν L r).prod ((nthCommonLaw ν L s).prod (nthCommonLaw ν L t)) := by
  have hm := nthCommon_suffix_map ν L hL he s (nthCommonList L t) (measurable_nthCommonList L t)
  have hr := nthCommon_suffix_map ν L hL he r
    (fun Z => (nthCommonList L s Z,nthCommonList L t ((commonRestart L)^[s] Z)))
    ((measurable_nthCommonList L s).prodMk
      ((measurable_nthCommonList L t).comp ((measurable_commonRestart L).iterate s)))
  rw [hm] at hr
  have heq : consecutiveThree L r s t = (fun Z =>
      (nthCommonList L r Z,nthCommonList L s ((commonRestart L)^[r] Z),
        nthCommonList L t ((commonRestart L)^[s] ((commonRestart L)^[r] Z)))) := by
    funext Z
    simp only [consecutiveThree]
    rw [Nat.add_comm r s,Function.iterate_add_apply]
  rw [heq]
  exact hr

noncomputable def consecutiveFour {α : Type*} (L : Bool → α → ℕ)
    (u r s t : ℕ) (Z : TwoTape α) : TwoTapeList α × ThreeChunk α :=
  (nthCommonList L u Z,consecutiveThree L r s t ((commonRestart L)^[u] Z))

lemma measurable_consecutiveFour {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (u r s t : ℕ) :
    Measurable (consecutiveFour L u r s t) :=
  (measurable_nthCommonList L u).prodMk
    ((measurable_consecutiveThree L r s t).comp ((measurable_commonRestart L).iterate u))

lemma consecutiveFour_law {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (u r s t : ℕ) :
    (twoTapeLaw ν).map (consecutiveFour L u r s t) =
      (nthCommonLaw ν L u).prod ((nthCommonLaw ν L r).prod
        ((nthCommonLaw ν L s).prod (nthCommonLaw ν L t))) := by
  change (twoTapeLaw ν).map (fun Z => (nthCommonList L u Z,
    consecutiveThree L r s t ((commonRestart L)^[u] Z))) = _
  rw [nthCommon_suffix_map ν L hL he u _ (measurable_consecutiveThree L r s t),
    consecutiveThree_law ν L hL he]

end DirectionalZeroOne

end OAI
