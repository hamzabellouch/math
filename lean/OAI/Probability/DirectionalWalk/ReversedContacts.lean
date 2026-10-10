import OAI.Probability.DirectionalWalk.LateContacts

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma reversePrefix_opposedSite {d n : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (h0 : ∀ j < n, wordPath (Z (false,j)) 0 = 0) (i : Fin n) (t : ℕ) (ht : t ≤ (Z (false,i)).1) :
    wordPath (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j)))))
      ((∑ j : Fin n with j < i.rev, (Z (false,j.rev)).1)+t) -
      (∑ j ∈ Finset.range n, wordEnd (Z (false,j))) = opposedSite e Z false i t := by
  rw [reversePrefix_site _ h0 i t ht]
  simp only [opposedSite,opposedAnchor,Bool.false_eq_true,↓reduceIte]
  abel

lemma concatenateWords_departure {d n : ℕ} (a : Fin n → Word d)
    (i : Fin n) (t : ℕ) (ht : t < (a i).1) :
    (∑ j : Fin n with j < i, (a j).1)+t < (concatenateWords n a).1 := by
  classical
  rw [concatenateWords_length]
  have hs : (∑ j : Fin n with j < i, (a j).1)+(a i).1 ≤ ∑ j : Fin n, (a j).1 := by
    rw [add_comm,← Finset.sum_insert (f := fun j : Fin n => (a j).1) (a := i)
      (s := Finset.univ.filter (fun j : Fin n => j < i)) (by simp)]
    exact Finset.sum_le_sum_of_subset (by intro j hj;simp)
  omega

lemma opposed_positive_in_finite_bridge {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (n h : ℕ) (hn : h ≤ tapeHeight (placedWidth e false) (fun j => Z (false,j)) n)
    (y : Site d) (hy : opposedDeparture e Z false y) (hh : -axisHeight e y = (h : ℤ)) :
    ∃ t < (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))).1,
      wordPath (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))) t -
        (∑ j ∈ Finset.range n, wordEnd (Z (false,j))) = y := by
  obtain ⟨i,t,ht,hy⟩ := hy
  have hb := (opposed_departure_band e Z hZ false i t ht).1
  rw [hy,hh] at hb
  have hin : i < n := by
    by_contra hi
    have hm := (tapeHeight_strictMono (placedWidth e false) (fun j => Z (false,j))
      (fun j => slabRecords_pos _ _ (hZ false j))).monotone (Nat.le_of_not_gt hi)
    have hh' : tapeHeight (placedWidth e false) (fun j => Z (false,j)) i < h := by exact_mod_cast hb
    omega
  refine ⟨(∑ j : Fin n with j < (⟨i,hin⟩ : Fin n).rev, (Z (false,j.rev)).1)+t,?_,?_⟩
  · exact concatenateWords_departure (fun j : Fin n => Z (false,j.rev))
      (⟨i,hin⟩ : Fin n).rev t (by simpa using ht)
  · exact (reversePrefix_opposedSite e Z (fun j _ => (hZ false j).2.1) ⟨i,hin⟩ t ht.le).trans hy

lemma concatenateWords_departure_exists {d n : ℕ} (a : Fin n → Word d)
    (t : ℕ) (ht : t < (concatenateWords n a).1) :
    ∃ i : Fin n, ∃ u < (a i).1, t = (∑ j : Fin n with j < i, (a j).1)+u := by
  classical
  induction n with
  | zero => simp [concatenateWords,prefixWord] at ht
  | succ n ih =>
    let b := concatenateWords n (fun j => a j.castSucc)
    change t < b.1+(a (Fin.last n)).1 at ht
    by_cases htb : t < b.1
    · obtain ⟨i,u,hu,he⟩ := ih (fun j => a j.castSucc) htb
      refine ⟨i.castSucc,u,hu,?_⟩
      rw [fin_prefix_sum_castSucc]
      exact he
    · refine ⟨Fin.last n,t-b.1,by omega,?_⟩
      rw [fin_prefix_sum_last,← concatenateWords_length]
      exact (Nat.add_sub_of_le (Nat.le_of_not_gt htb)).symm

lemma concatenateWords_axis_bridge {d n : ℕ} (e : Step d) (a : Fin n → Word d)
    (ha : ∀ i, RegenerationWord (axisDirection e) (a i)) :
    AxisBridgeWord e (∑ i, slabRecords (axisDirection e) (a i)) (concatenateWords n a) := by
  classical
  constructor
  · rw [concatenateWords_end,axisHeight_sum]
    simp only [axisHeight_wordEnd e _ (ha _),Nat.cast_sum]
  · intro t ht
    obtain ⟨i,u,hu,rfl⟩ := concatenateWords_departure_exists a t ht
    rw [concatenateWords_site a (fun i => (ha i).2.1) i u hu.le,axisHeight_add,axisHeight_sum]
    have hw := axisHeight_word_interior e (a i) (ha i) u hu
    have hh : (∑ j : Fin n with j < i, axisHeight e (wordEnd (a j))) =
        ((∑ j : Fin n with j < i, slabRecords (axisDirection e) (a j)) : ℕ) := by
      simp only [axisHeight_wordEnd e _ (ha _),Nat.cast_sum]
    rw [hh]
    constructor
    · exact add_nonneg (Nat.cast_nonneg _) hw.1
    · have hs : (∑ j : Fin n with j < i, slabRecords (axisDirection e) (a j))+
          slabRecords (axisDirection e) (a i) ≤ ∑ j, slabRecords (axisDirection e) (a j) := by
        rw [add_comm,← Finset.sum_insert (f := fun j : Fin n => slabRecords (axisDirection e) (a j))
          (a := i) (s := Finset.univ.filter (fun j : Fin n => j < i)) (by simp)]
        exact Finset.sum_le_sum_of_subset (by intro j hj;simp)
      have hs' : ((∑ j : Fin n with j < i, slabRecords (axisDirection e) (a j)) : ℕ) +
          (slabRecords (axisDirection e) (a i) : ℤ) ≤ ((∑ j, slabRecords (axisDirection e) (a j)) : ℕ) := by exact_mod_cast hs
      omega

lemma wordEnd_slabs_sum {d : ℕ} (v : Fin d → ℝ) (Y : Path d) (h0 : Y 0 = 0) (n : ℕ) :
    (∑ i ∈ Finset.range n, wordEnd (slabs v Y i)) = Y (slabTime v Y n) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => wordEnd (slabs v Y i)),← concatenateWords_end]
  change wordEnd (concatenateList (tapePrefix n (slabs v Y))) = _
  rw [concatenateList_prefix_slabs v Y h0]
  exact wordPath_prefixWord _ _ le_rfl

lemma opposed_negative_slabs {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (Y : Path d) (hY : GoodSlabPath (axisDirection (oppositeStep e)) Y)
    (hZ : ∀ i, Z (true,i) = slabs (axisDirection (oppositeStep e)) Y i)
    (y : Site d) : opposedDeparture e Z true y ↔ ∃ t, Y t-stepVector e = y := by
  constructor
  · rintro ⟨i,j,hj,hij⟩
    refine ⟨slabTime (axisDirection (oppositeStep e)) Y i+j,?_⟩
    simp only [opposedSite,opposedAnchor,↓reduceIte,hZ,wordEnd_slabs_sum _ _ hY.1] at hij
    have hp := slab_word_path (axisDirection (oppositeStep e)) Y i (show j ≤ (slabs (axisDirection (oppositeStep e)) Y i).1 by simpa only [hZ] using hj.le)
    rw [iterated_cutSuffix _ Y hY.1] at hp
    rw [hp] at hij
    convert hij using 1; abel
  · rintro ⟨t,ht⟩
    obtain ⟨i,hi,hi'⟩ := slab_location _ Y hY t
    refine ⟨i,t-slabTime (axisDirection (oppositeStep e)) Y i,?_,?_⟩
    · rw [slabTime_succ] at hi'
      rw [hZ]
      omega
    · simp only [opposedSite,opposedAnchor,↓reduceIte,hZ,wordEnd_slabs_sum _ _ hY.1]
      have hj : t-slabTime (axisDirection (oppositeStep e)) Y i ≤
          (slabs (axisDirection (oppositeStep e)) Y i).1 := by rw [slabTime_succ] at hi';omega
      rw [slab_word_path _ _ _ hj,iterated_cutSuffix _ Y hY.1,Nat.add_sub_of_le hi]
      convert ht using 1; abel

lemma fin_prefix_length_mono {α : Type*} {n : ℕ} (L : α → ℕ) (a : Fin n → α)
    {i j : Fin n} (hij : i ≤ j) :
    (∑ k : Fin n with k < i, L (a k)) ≤ ∑ k : Fin n with k < j, L (a k) := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hk ⊢
  exact hk.trans_le hij

lemma fin_prefix_length_separated {α : Type*} {n : ℕ} (L : α → ℕ) (a : Fin n → α)
    {i j : Fin n} (hij : i < j) :
    (∑ k : Fin n with k < i, L (a k))+L (a i) ≤ ∑ k : Fin n with k < j, L (a k) := by
  classical
  rw [add_comm,← Finset.sum_insert (f := fun k : Fin n => L (a k)) (a := i)
    (s := Finset.univ.filter (fun k : Fin n => k < i)) (by simp)]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and] at hk ⊢
  rcases hk with rfl | hk
  · exact hij
  · exact hk.trans hij

lemma axisHeight_tapeTotal {d : ℕ} (e : Step d) (Z : ℕ → Word d)
    (hZ : ∀ i, RegenerationWord (axisDirection e) (Z i)) (n : ℕ) :
    axisHeight e (∑ j ∈ Finset.range n, wordEnd (Z j)) =
      (tapeHeight (slabRecords (axisDirection e)) Z n : ℤ) := by
  rw [axisHeight_sum]
  simp only [axisHeight_wordEnd e _ (hZ _),tapeHeight,Nat.cast_sum]

lemma reversePrefix_departure_in_opposed {d n : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ i, wordPath (Z (false,i)) 0 = 0) (t : ℕ)
    (ht : t < (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))).1) :
    opposedDeparture e Z false
      (wordPath (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))) t -
        (∑ j ∈ Finset.range n, wordEnd (Z (false,j)))) := by
  obtain ⟨i,u,hu,rfl⟩ := concatenateWords_departure_exists (fun i : Fin n => Z (false,i.rev)) t ht
  refine ⟨i.rev,u,hu,?_⟩
  simpa only [Fin.rev_rev] using (reversePrefix_opposedSite e Z (fun j _ => hZ j) i.rev u hu.le).symm

lemma reversePrefix_cut_geometry {d : ℕ} (e : Step d) (Z : TwoTape (Word d))
    (hZ : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) (Z (b,i)))
    (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    let L := placedWidth e false
    let H := tapeHeight L (fun j => Z (false,j)) n
    let s := tapeHeight L (fun j => Z (false,j)) m
    let a := concatenateList (reverseTapeList (tapePrefix n (fun j => Z (false,j))))
    ∃ t < a.1, AxisBridgeWord e (H-s) (prefixWord t (wordPath a)) ∧
      ∀ u, t ≤ u → u < a.1 → (H-s : ℕ) ≤ axisHeight e (wordPath a u) := by
  classical
  dsimp only
  let i : Fin n := ⟨m-1,by omega⟩
  let a : Fin n → Word d := fun j => Z (false,j.rev)
  let t := ∑ j : Fin n with j < i.rev, (a j).1
  let H := tapeHeight (placedWidth e false) (fun j => Z (false,j)) n
  let s := tapeHeight (placedWidth e false) (fun j => Z (false,j)) m
  have hl : ∀ j, 0 < placedWidth e false (Z (false,j)) := fun j => slabRecords_pos _ _ (hZ false j)
  have hsH : s ≤ H := (tapeHeight_strictMono _ _ hl).monotone hmn
  have htotal := axisHeight_tapeTotal e (fun j => Z (false,j)) (hZ false) n
  have htlen : t < (concatenateWords n a).1 := by
    have hh := concatenateWords_departure a i.rev 0 (by simpa only [a,Fin.rev_rev] using (hZ false i).1)
    simpa only [Nat.add_zero] using hh
  have hend : axisHeight e (wordPath (concatenateWords n a) t) = ((H-s : ℕ) : ℤ) := by
    have hh := reversePrefix_opposedSite e Z (fun j _ => (hZ false j).2.1) i 0 (Nat.zero_le _)
    simp only [Nat.add_zero] at hh
    have he := congrArg (axisHeight e) hh
    rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,htotal] at he
    have hi : i.val+1 = m := by dsimp [i];omega
    have ho := opposedAnchor_height e Z hZ false i
    simp only [Bool.false_eq_true,↓reduceIte,hi] at ho
    simp only [opposedSite,(hZ false i).2.1,add_zero] at he
    change axisHeight e (wordPath (concatenateWords n a) t)-(H : ℤ) = _ at he
    rw [Nat.cast_sub hsH]
    change -axisHeight e (opposedAnchor e Z false i) = (s : ℤ) at ho
    omega
  have hheight (j : Fin n) (u : ℕ) (hu : u < (a j).1) :
      let y := wordPath (concatenateWords n a) ((∑ q : Fin n with q < j, (a q).1)+u)
      (tapeHeight (placedWidth e false) (fun q => Z (false,q)) j.rev.val : ℤ) < (H : ℤ)-axisHeight e y ∧
      (H : ℤ)-axisHeight e y ≤ (tapeHeight (placedWidth e false) (fun q => Z (false,q)) (j.rev.val+1) : ℤ) := by
    have hh := reversePrefix_opposedSite e Z (fun q _ => (hZ false q).2.1) j.rev u hu.le
    simp only [Fin.rev_rev] at hh
    have he := congrArg (axisHeight e) hh
    rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,htotal] at he
    have hb := opposed_departure_band e Z hZ false j.rev u hu
    have hsucc : tapeHeight (placedWidth e false) (fun q => Z (false,q)) (j.rev.val+1) =
        tapeHeight (placedWidth e false) (fun q => Z (false,q)) j.rev.val + placedWidth e false (Z (false,j.rev)) := by
      simp only [tapeHeight,Finset.sum_range_succ]
    dsimp only at hb
    rw [← hsucc] at hb
    dsimp only
    change axisHeight e (wordPath (concatenateWords n a) ((∑ q : Fin n with q < j, (a q).1)+u)) - (H : ℤ) = _ at he
    omega
  refine ⟨t,htlen,⟨?_,?_⟩,?_⟩
  · change axisHeight e (wordPath (prefixWord t (wordPath (concatenateWords n a))) t) = _
    rw [wordPath_prefixWord t _ le_rfl]
    exact hend
  · intro u hu
    change u < t at hu
    rw [wordPath_prefixWord t _ hu.le]
    obtain ⟨j,v,hv,rfl⟩ := concatenateWords_departure_exists a u (hu.trans htlen)
    have hji : j < i.rev := by
      by_contra h
      have hh := fin_prefix_length_mono (fun w : Word d => w.1) a (le_of_not_gt h)
      dsimp [t] at hu
      omega
    have hij : m ≤ j.rev.val := by
      have hh := Fin.lt_rev_iff.mp hji
      change m-1 < j.rev.val at hh
      omega
    have hmj := (tapeHeight_strictMono _ _ hl).monotone hij
    have hh := hheight j v hv
    dsimp only at hh
    have hab := concatenateWords_axis_bridge e a (fun q => hZ false q.rev)
    have hnon := (hab.2 _ (by have := concatenateWords_departure a j v hv;exact this)).1
    change 0 ≤ axisHeight e (wordPath (concatenateWords n a) _) ∧
      axisHeight e (wordPath (concatenateWords n a) _) < _
    constructor
    · exact hnon
    · rw [Nat.cast_sub hsH]
      have hmj' : (s : ℤ) ≤ (tapeHeight (placedWidth e false) (fun q => Z (false,q)) j.rev.val : ℤ) := by exact_mod_cast hmj
      omega
  · intro u htu hu
    obtain ⟨j,v,hv,rfl⟩ := concatenateWords_departure_exists a u hu
    have hij : i.rev ≤ j := by
      by_contra h
      have hh := fin_prefix_length_separated (fun w : Word d => w.1) a (lt_of_not_ge h)
      dsimp [t] at htu
      omega
    have hjm : j.rev.val+1 ≤ m := by
      have hh := Fin.rev_le_rev.mpr hij
      simp only [Fin.rev_rev,Fin.le_def] at hh
      change j.rev.val ≤ m-1 at hh
      omega
    have hjs := (tapeHeight_strictMono _ _ hl).monotone hjm
    have hh := hheight j v hv
    dsimp only at hh
    change ((H-s : ℕ) : ℤ) ≤ axisHeight e (wordPath (concatenateWords n a) _)
    rw [Nat.cast_sub hsH]
    have hjs' : (tapeHeight (placedWidth e false) (fun q => Z (false,q)) (j.rev.val+1) : ℤ) ≤ (s : ℤ) := by exact_mod_cast hjs
    omega

end DirectionalZeroOne

end OAI
