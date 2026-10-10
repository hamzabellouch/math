import OAI.Probability.DirectionalWalk.ReversedContacts

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def finiteLateContact {d : ℕ} (e : Step d) (k r N : ℕ) (a : Word d) (Y : Path d) : Prop :=
  ∃ t τ, t ≤ τ ∧ τ < a.1 ∧ AxisBridgeWord e k (prefixWord t (wordPath a)) ∧
    (∀ j, t ≤ j → j ≤ τ → (k : ℤ) ≤ axisHeight e (wordPath a j) ∧ axisHeight e (wordPath a j) < (N : ℤ)) ∧
    (r : ℤ) ≤ axisHeight e (wordPath a τ) ∧
    (∃ j, Y j+(wordEnd a-stepVector e) = wordPath a τ) ∧
    (∀ i, t ≤ i → i < τ → ∀ j, Y j+(wordEnd a-stepVector e) ≠ wordPath a i)

lemma uncovered_bridge_late {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (Y : Path d) (hY : GoodSlabPath (axisDirection (oppositeStep e)) Y)
    (hZY : ∀ i, Z (true,i) = slabs (axisDirection (oppositeStep e)) Y i)
    (m n low high : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hslo : low ≤ tapeHeight (placedWidth e false) (fun j => Z (false,j)) m)
    (hshi : tapeHeight (placedWidth e false) (fun j => Z (false,j)) m < high)
    (hno : ∀ h, low ≤ h → h < high → ¬contactDepth e Z h) :
    let H := tapeHeight (placedWidth e false) (fun j => Z (false,j)) n
    let s := tapeHeight (placedWidth e false) (fun j => Z (false,j)) m
    finiteLateContact e (H-s) (H-low) H
      (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))) Y := by
  classical
  let H := tapeHeight (placedWidth e false) (fun j => Z (false,j)) n
  let s := tapeHeight (placedWidth e false) (fun j => Z (false,j)) m
  let a := concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))
  let D := ∑ j ∈ Finset.range n, wordEnd (Z (false,j))
  have hl : ∀ j, 0 < placedWidth e false (Z (false,j)) := fun j => slabRecords_pos _ _ (hZ false j)
  have hsH : s ≤ H := (tapeHeight_strictMono _ _ hl).monotone hmn
  have hsp : 0 < s := hm.trans_le (le_tapeHeight _ _ hl m)
  have hH : 1 ≤ H := (Nat.succ_le_of_lt hsp).trans hsH
  have hD : wordEnd a = D := by
    rw [concatenateList_end]
    change (∑ j : Fin n, wordEnd (Z (false,j.rev))) = _
    have hh := Equiv.sum_comp Fin.revPerm (fun j : Fin n => wordEnd (Z (false,j)))
    apply (show (∑ j : Fin n, wordEnd (Z (false,j.rev))) = ∑ j : Fin n, wordEnd (Z (false,j)) by
      simpa only [Fin.revPerm_apply] using hh).trans
    rw [Fin.sum_univ_eq_sum_range (fun j => wordEnd (Z (false,j)))]
  have hDh : axisHeight e D = (H : ℤ) := axisHeight_tapeTotal e (fun j => Z (false,j)) (hZ false) n
  have ha : AxisBridgeWord e H a := by
    have hh := concatenateWords_axis_bridge e (fun j : Fin n => Z (false,j.rev)) (fun j => hZ false j.rev)
    have he : (∑ j : Fin n, slabRecords (axisDirection e) (Z (false,j.rev))) = H := by
      have hh := Equiv.sum_comp Fin.revPerm (fun j : Fin n => slabRecords (axisDirection e) (Z (false,j)))
      apply (show (∑ j : Fin n, slabRecords (axisDirection e) (Z (false,j.rev))) =
          ∑ j : Fin n, slabRecords (axisDirection e) (Z (false,j)) by
        simpa only [Fin.revPerm_apply] using hh).trans
      rw [Fin.sum_univ_eq_sum_range (fun j => slabRecords (axisDirection e) (Z (false,j)))]
      rfl
    exact he ▸ hh
  obtain ⟨t,ht,htbridge,htband⟩ := reversePrefix_cut_geometry e Z hZ m n hm hmn
  change t < a.1 at ht
  have hforce := (opposed_forced_contact e Z hZ).1.1
  obtain ⟨v,hv,hvsite⟩ := opposed_positive_in_finite_bridge e Z hZ n 1 hH (-stepVector e) hforce
    (by rw [axisHeight_neg,axisHeight_step_self];norm_num)
  change v < a.1 at hv
  change wordPath a v-D = -stepVector e at hvsite
  have hvheight : axisHeight e (wordPath a v) = (H : ℤ)-1 := by
    have hh := congrArg (axisHeight e) hvsite
    rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,hDh,axisHeight_neg,axisHeight_step_self] at hh
    omega
  have htv : t ≤ v := by
    by_contra h
    have hvt : v < t := Nat.lt_of_not_ge h
    have hh := (htbridge.2 v hvt).2
    rw [wordPath_prefixWord t _ hvt.le,hvheight,Nat.cast_sub hsH] at hh
    omega
  have hex : ∃ τ, t ≤ τ ∧ τ < a.1 ∧ ∃ j, Y j+(wordEnd a-stepVector e) = wordPath a τ := by
    refine ⟨v,htv,hv,0,?_⟩
    rw [hY.1,zero_add,hD]
    calc
      D-stepVector e = -stepVector e+D := by abel
      _ = wordPath a v := (sub_eq_iff_eq_add.mp hvsite).symm
  let τ := Nat.find hex
  have hτ := Nat.find_spec hex
  have hcontact : contactAt e Z (wordPath a τ-D) := by
    constructor
    · exact reversePrefix_departure_in_opposed e Z (fun i => (hZ false i).2.1) τ hτ.2.1
    · rw [opposed_negative_slabs e Z Y hY hZY]
      obtain ⟨j,hj⟩ := hτ.2.2
      refine ⟨j,?_⟩
      change Y j+(wordEnd a-stepVector e) = wordPath a τ at hj
      rw [hD] at hj
      rw [← hj]
      abel
  have hτband : ((H-s : ℕ) : ℤ) ≤ axisHeight e (wordPath a τ) ∧ axisHeight e (wordPath a τ) < (H : ℤ) :=
    ⟨htband τ hτ.1 hτ.2.1,(ha.2 τ hτ.2.1).2⟩
  let δ : ℤ := (H : ℤ)-axisHeight e (wordPath a τ)
  have hδ0 : 0 < δ := sub_pos.mpr hτband.2
  have hδs : δ ≤ (s : ℤ) := by dsimp [δ];rw [Nat.cast_sub hsH] at hτband;omega
  have hδ : (Int.toNat δ : ℤ) = δ := Int.toNat_of_nonneg hδ0.le
  have hdep : contactDepth e Z (Int.toNat δ) := by
    refine ⟨wordPath a τ-D,hcontact,?_⟩
    rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,hDh,hδ]
    dsimp [δ]
    omega
  have hsmall : Int.toNat δ < low := by
    by_contra h
    apply hno _ (Nat.le_of_not_gt h) ?_ hdep
    have hh : Int.toNat δ ≤ s := by
      rw [← hδ] at hδs
      exact_mod_cast hδs
    exact hh.trans_lt hshi
  have hr : ((H-low : ℕ) : ℤ) ≤ axisHeight e (wordPath a τ) := by
    rw [Nat.cast_sub (hslo.trans hsH)]
    have hh : δ < (low : ℤ) := by
      rw [← hδ]
      exact_mod_cast hsmall
    dsimp [δ] at hh
    omega
  refine ⟨t,τ,hτ.1,hτ.2.1,htbridge,?_,hr,hτ.2.2,?_⟩
  · intro j htj hjτ
    exact ⟨htband j htj (hjτ.trans_lt hτ.2.1),(ha.2 j (hjτ.trans_lt hτ.2.1)).2⟩
  · intro i hti hiτ j hj
    exact Nat.find_min hex hiτ ⟨hti,hiτ.trans hτ.2.1,j,hj⟩

lemma measurableSet_finiteLateContact {d : ℕ} (e : Step d) (k r N : ℕ) :
    MeasurableSet {p : Word d × Path d | finiteLateContact e k r N p.1 p.2} := by
  classical
  have hword (P : Word d → Prop) : MeasurableSet {p : Word d × Path d | P p.1} :=
    measurable_fst (Set.to_countable _).measurableSet
  have heq (i j : ℕ) : MeasurableSet {p : Word d × Path d |
      p.2 j + (wordEnd p.1-stepVector e) = wordPath p.1 i} := by
    apply measurableSet_eq_fun
    · exact ((measurable_pi_apply j).comp measurable_snd).add
        ((measurable_of_countable (fun a : Word d => wordEnd a-stepVector e)).comp measurable_fst)
    · exact (measurable_of_countable (fun a : Word d => wordPath a i)).comp measurable_fst
  simp only [finiteLateContact,Set.ofPred_exists]
  apply MeasurableSet.iUnion;intro t
  apply MeasurableSet.iUnion;intro τ
  refine (hword (fun _ => t ≤ τ)).inter ((hword (fun a => τ < a.1)).inter
    ((hword (fun a => AxisBridgeWord e k (prefixWord t (wordPath a)))).inter
    ((hword (fun a => ∀ j, t ≤ j → j ≤ τ → (k : ℤ) ≤ axisHeight e (wordPath a j) ∧
      axisHeight e (wordPath a j) < (N : ℤ))).inter
    ((hword (fun a => (r : ℤ) ≤ axisHeight e (wordPath a τ))).inter ?_))))
  apply MeasurableSet.inter
  · change MeasurableSet {p : Word d × Path d | ∃ j, p.2 j+(wordEnd p.1-stepVector e) = wordPath p.1 τ}
    simpa only [Set.ofPred_exists] using MeasurableSet.iUnion (fun j => heq τ j)
  · change MeasurableSet {p : Word d × Path d | ∀ i, t ≤ i → i < τ → ∀ j,
      p.2 j+(wordEnd p.1-stepVector e) ≠ wordPath p.1 i}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
      MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun j => (heq i j).compl))))

end DirectionalZeroOne

end OAI
