import OAI.Probability.DirectionalWalk.CommonBands

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

abbrev CubeSite (d R : ℕ) := Fin d → Set.Icc (-(R : ℤ)) (R : ℤ)

abbrev AxisCubeSite {d : ℕ} (e : Step d) (N R : ℕ) :=
  {z : CubeSite d R // axisHeight e (fun i => z i) = (N : ℤ)-1}

lemma card_cubeSite (d R : ℕ) : Fintype.card (CubeSite d R) = (2*R+1)^d := by
  simp only [CubeSite,Fintype.card_fun,Fintype.card_fin]
  congr 1
  rw [Fintype.card_ofFinset (Finset.Icc (-(R : ℤ)) R) (by simp),Int.card_Icc]
  omega

lemma card_axisCubeSite_le {d : ℕ} (e : Step d) (N R : ℕ) :
    Fintype.card (AxisCubeSite e N R) ≤ (2*R+1)^d := by
  rw [← card_cubeSite d R]
  exact Fintype.card_subtype_le _

lemma axisCubeSite_nonempty {d : ℕ} (e : Step d) (N R : ℕ) (hN : 0 < N) (hR : N ≤ R) :
    Nonempty (AxisCubeSite e N R) := by
  let z : Site d := (N-1 : ℕ) • stepVector e
  have hbd (i : Fin d) : z i ∈ Set.Icc (-(R : ℤ)) (R : ℤ) := by
    dsimp [z,stepVector]
    simp only [Int.natCast_sub hN]
    split_ifs <;> constructor <;> omega
  exact ⟨⟨(fun i => ⟨z i,hbd i⟩),by
    change axisHeight e z = _
    dsimp [z,axisHeight,stepVector]
    cases e.2 <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
      omega⟩⟩

noncomputable def axisCubeEnumeration {d : ℕ} (e : Step d) (N R : ℕ) :
    Fin (Fintype.card (AxisCubeSite e N R)) → Site d :=
  fun q i => ((Fintype.equivFin (AxisCubeSite e N R)).symm q).val i

lemma axisCubeEnumeration_injective {d : ℕ} (e : Step d) (N R : ℕ) :
    Function.Injective (axisCubeEnumeration e N R) := by
  intro q r h
  apply (Fintype.equivFin (AxisCubeSite e N R)).symm.injective
  apply Subtype.ext
  funext i
  exact Subtype.ext (congr_fun h i)

lemma axisCubeEnumeration_height {d : ℕ} (e : Step d) (N R : ℕ)
    (q : Fin (Fintype.card (AxisCubeSite e N R))) :
    axisHeight e (axisCubeEnumeration e N R q) = (N : ℤ)-1 :=
  ((Fintype.equivFin (AxisCubeSite e N R)).symm q).property

lemma axisCubeEnumeration_surjective {d : ℕ} (e : Step d) (N R : ℕ) (z : Site d)
    (hz : axisHeight e z = (N : ℤ)-1) (hbd : ∀ i, |z i| ≤ (R : ℤ)) :
    ∃ q, axisCubeEnumeration e N R q = z := by
  let a : AxisCubeSite e N R := ⟨fun i => ⟨z i,abs_le.mp (hbd i)⟩,hz⟩
  refine ⟨Fintype.equivFin _ a,?_⟩
  change (fun i => (((Fintype.equivFin (AxisCubeSite e N R)).symm
    ((Fintype.equivFin (AxisCubeSite e N R)) a)).val i : ℤ)) = z
  rw [Equiv.symm_apply_apply]

lemma abs_wordEnd_coord_le_radius {d : ℕ} (a : Word d) (h0 : wordPath a 0 = 0) (i : Fin d) :
    |(wordEnd a i : ℝ)| ≤ slabRadius a := by
  have hh := norm_wordPath_le_radius a (j := a.1) le_rfl
  rw [h0,sub_zero] at hh
  have hc : |(wordEnd a i : ℝ)| ≤ ‖euclideanSite (wordPath a a.1)‖ := by
    simpa [euclideanSite,wordEnd] using PiLp.norm_apply_le (euclideanSite (wordPath a a.1)) i
  exact hc.trans hh

lemma reversePrefix_endpoint_coord {d n : ℕ} (Z : ℕ → Word d)
    (h0 : ∀ j < n, wordPath (Z j) 0 = 0) (i : Fin d) :
    |(wordEnd (concatenateList (reverseTapeList (tapePrefix n Z))) i : ℝ)| ≤
      ∑ j ∈ Finset.range n, slabRadius (Z j) := by
  have he : wordEnd (concatenateList (reverseTapeList (tapePrefix n Z))) =
      ∑ j ∈ Finset.range n, wordEnd (Z j) := by
    change wordEnd (concatenateWords n (fun j : Fin n => Z j.rev)) = _
    rw [concatenateWords_end]
    exact (Equiv.sum_comp Fin.revPerm (fun j : Fin n => wordEnd (Z j))).trans
      (Fin.sum_univ_eq_sum_range (fun j => wordEnd (Z j)) n)
  rw [he]
  simp only [Finset.sum_apply,Int.cast_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
    (fun j hj => abs_wordEnd_coord_le_radius _ (h0 j (Finset.mem_range.mp hj)) i))

lemma cutIndex_le_height {α : Type*} (L : α → ℕ) (Z : ℕ → α)
    (hL : ∀ i, 0 < L (Z i)) (N : ℕ) (hC : Z ∈ renewalCut L N) :
    cutListIndex L N Z ≤ N := by
  have he := cutListIndex_spec L N Z hL hC
  have hh := (tapeHeight_strictMono L Z hL).id_le (cutListIndex L N Z)
  rwa [he] at hh

lemma reversed_cut_endpoint_radius {d : ℕ} (e : Step d) (Z : ℕ → Word d)
    (hZ : ∀ i, RegenerationWord (axisDirection e) (Z i)) (N : ℕ)
    (hC : Z ∈ tapeCut (axisDirection e) N) (i : Fin d) :
    |((wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) i : ℤ) : ℝ)| ≤
      ∑ j ∈ Finset.range N, slabRadius (Z j) := by
  have hh := reversePrefix_endpoint_coord Z (n := cutListIndex (slabRecords (axisDirection e)) N Z)
    (fun j _ => (hZ j).2.1) i
  refine hh.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (cutIndex_le_height _ Z (fun j => slabRecords_pos _ _ (hZ j)) N hC)
  · intro j _ _
    exact slabRadius_nonneg _

lemma commonDepth_add {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) (r s : ℕ) :
    commonDepth L Z (r+s) = commonDepth L Z r +
      commonDepth L ((commonRestart L)^[r] Z) s := by
  rw [commonDepth,Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm r i,Function.iterate_add_apply]

lemma commonDepth_strictMono {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) :
    StrictMono (commonDepth L Z) := by
  apply strictMono_nat_of_lt_succ
  intro r
  rw [commonDepth_succ]
  have hh := (firstCommonWidth_spec L _ (he r)).1
  omega

lemma common_iterates_shift {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    (commonRestart L)^[r] Z = twoShift (fun b => (nthCommonList L r Z b).1) Z := by
  rw [← (commonDepth_spec L Z hZ he r).2.1]
  rfl

lemma nthCommonList_data {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    (∀ b, listHeight (L b) (nthCommonList L r Z b) = commonDepth L Z r) ∧
      Z ∈ twoCylinder (nthCommonList L r Z) := by
  exact (commonCutList_atom_iff L _ Z hZ _).mp ⟨(commonDepth_spec L Z hZ he r).1,rfl⟩

lemma nthCommonList_append {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r s : ℕ) (b : Bool) :
    nthCommonList L (r+s) Z b = appendTapeList (nthCommonList L r Z b)
      (nthCommonList L s ((commonRestart L)^[r] Z) b) := by
  have hr := nthCommonList_data L Z hZ he r
  let Y := (commonRestart L)^[r] Z
  have hYZ : ∀ b i, 0 < L b (Y (b,i)) := by
    dsimp only [Y]
    rw [common_iterates_shift L Z hZ he r]
    exact fun b i => hZ b _
  have hYe : ∀ s, ∃ H, 0 < H ∧ ((commonRestart L)^[s] Y) ∈ commonCut L H := by
    intro s
    dsimp only [Y]
    rw [← Function.iterate_add_apply]
    exact he (s+r)
  have hs := nthCommonList_data L Y hYZ hYe s
  have hshift : Y = twoShift (fun b => (nthCommonList L r Z b).1) Z := common_iterates_shift L Z hZ he r
  have hl : listHeight (L b) (appendTapeList (nthCommonList L r Z b) (nthCommonList L s Y b)) =
      commonDepth L Z (r+s) := by
    rw [listHeight_append,hr.1 b,hs.1 b,commonDepth_add]
  have hc : (fun i => Z (b,i)) ∈ tapeCylinder
      (appendTapeList (nthCommonList L r Z b) (nthCommonList L s Y b)) := by
    rw [tapeCylinder_append]
    refine ⟨hr.2 b,?_⟩
    intro i
    exact (congr_fun hshift (b,i)).symm.trans (hs.2 b i)
  exact ((cutList_atom_iff (L b) _ _ (hZ b) _).mpr ⟨hl,hc⟩).2

lemma appendTapeList_prefix {α : Type*} (Z : ℕ → α) (m n : ℕ) :
    appendTapeList (tapePrefix m Z) (tapePrefix n (fun i => Z (m+i))) = tapePrefix (m+n) Z := by
  change (⟨m+n,Fin.append (fun i : Fin m => Z i) (fun i : Fin n => Z (m+i))⟩ : TapeList α) =
    ⟨m+n,fun i => Z i⟩
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

lemma listTotal_append {α G : Type*} [AddCommMonoid G] (D : α → G) (a b : TapeList α) :
    listTotal D (appendTapeList a b) = listTotal D a + listTotal D b := by
  change (∑ i : Fin (a.1+b.1), D (Fin.append a.2 b.2 i)) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  rfl

lemma listTotal_reverse {α G : Type*} [AddCommMonoid G] (D : α → G) (a : TapeList α) :
    listTotal D (reverseTapeList a) = listTotal D a := by
  exact Equiv.sum_comp Fin.revPerm (fun i => D (a.2 i))

lemma iid_lintegral_sum {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (f : α → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    (∫⁻ Z, ∑ j ∈ Finset.range n, f (Z j) ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      (n : ℝ≥0∞) * ∫⁻ a, f a ∂ν := by
  rw [lintegral_finsetSum (Finset.range n) (f := fun (j : ℕ) (Z : ℕ → α) => f (Z j)) (fun j _ => hf.comp (measurable_pi_apply j))]
  have he (j : ℕ) : (∫⁻ Z, f (Z j) ∂Measure.infinitePi (fun _ : ℕ => ν)) = ∫⁻ a, f a ∂ν := by
    rw [← lintegral_map' hf.aemeasurable (measurable_pi_apply j).aemeasurable,Measure.infinitePi_map_eval]
  simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

lemma iid_radius_large {d : ℕ} (ν : Measure (Word d)) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) :
    Measure.infinitePi (fun _ : ℕ => ν)
      {Z | (n : ℝ)^2 ≤ ∑ j ∈ Finset.range n, slabRadius (Z j)} ≤
      (∫⁻ a, ENNReal.ofReal (slabRadius a) ∂ν) / (n : ℝ≥0∞) := by
  let f : (ℕ → Word d) → ℝ≥0∞ := fun Z => ∑ j ∈ Finset.range n, ENNReal.ofReal (slabRadius (Z j))
  have hf : Measurable f := Finset.measurable_sum _ (fun j _ =>
    (measurable_of_countable (fun a : Word d => ENNReal.ofReal (slabRadius a))).comp (measurable_pi_apply j))
  have hne : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  have htop : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  have hset : {Z | (n : ℝ)^2 ≤ ∑ j ∈ Finset.range n, slabRadius (Z j)} =
      {Z | (n : ℝ≥0∞)^2 ≤ f Z} := by
    ext Z
    dsimp only [Set.mem_ofPred_eq,f]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => slabRadius_nonneg (Z j))]
    have he : ENNReal.ofReal ((n : ℝ)^2) = (n : ℝ≥0∞)^2 := by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg n),ENNReal.ofReal_natCast]
    rw [← he,ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun j _ => slabRadius_nonneg (Z j)))]
  rw [hset]
  have hh := meas_ge_le_lintegral_div (μ := Measure.infinitePi (fun _ : ℕ => ν)) hf.aemeasurable (pow_ne_zero _ hne) (by finiteness : (n : ℝ≥0∞)^2 ≠ ∞)
  refine hh.trans_eq ?_
  change ((∫⁻ Z, ∑ j ∈ Finset.range n, ENNReal.ofReal (slabRadius (Z j)) ∂Measure.infinitePi (fun _ : ℕ => ν)) / (n : ℝ≥0∞)^2) = _
  rw [iid_lintegral_sum ν (fun a => ENNReal.ofReal (slabRadius a)) (measurable_of_countable _) n,pow_two,ENNReal.mul_div_mul_left _ _ hne htop]

lemma tapeList_ext {α : Type*} {a b : TapeList α} (hl : a.1 = b.1)
    (h : ∀ i hi hj, a.2 ⟨i,hi⟩ = b.2 ⟨i,hj⟩) : a = b := by
  rcases a with ⟨m,a⟩
  rcases b with ⟨n,b⟩
  dsimp only at hl
  subst n
  exact congrArg (Sigma.mk m) (funext (fun i => h i i.isLt i.isLt))

lemma reverseTapeList_append {α : Type*} (a b : TapeList α) :
    reverseTapeList (appendTapeList a b) = appendTapeList (reverseTapeList b) (reverseTapeList a) := by
  apply tapeList_ext (Nat.add_comm a.1 b.1)
  intro i hi hj
  exact Fin.append_rev a.2 b.2 ⟨i,hi⟩

lemma slice_sum {G : Type*} [AddCommGroup G] (f : ℕ → G) (a n : ℕ) :
    (∑ j ∈ Finset.range n, f (a+j)) =
      (∑ j ∈ Finset.range (a+n), f j) - (∑ j ∈ Finset.range a, f j) := by
  rw [Finset.sum_range_add]
  abel

lemma reverseSlice_departure {d : ℕ} (Z : ℕ → Word d) (a n i t : ℕ)
    (h0 : ∀ j, wordPath (Z j) 0 = 0) (hai : a ≤ i) (hin : i < a+n) (ht : t < (Z i).1) :
    ∃ u < (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (a+j))))).1,
      wordPath (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (a+j))))) u =
        (∑ j ∈ Finset.range (a+n), wordEnd (Z j)) -
        (∑ j ∈ Finset.range (i+1), wordEnd (Z j)) + wordPath (Z i) t := by
  let q : Fin n := ⟨i-a,by omega⟩
  have hq : a+q.val = i := by dsimp [q];omega
  let u := (∑ j : Fin n with j < q.rev, (Z (a+j.rev)).1)+t
  have hu := concatenateWords_departure (fun j : Fin n => Z (a+j.rev)) q.rev t
    (by simpa only [Fin.rev_rev,hq] using ht)
  refine ⟨u,hu,?_⟩
  have he := reversePrefix_site (fun j => Z (a+j)) (fun j _ => h0 _) q t
    (by simpa only [hq] using ht.le)
  change wordPath (concatenateList (reverseTapeList (tapePrefix n (fun j => Z (a+j))))) u = _ at he
  rw [he,slice_sum (fun j => wordEnd (Z j)) a n,slice_sum (fun j => wordEnd (Z j)) a (q.val+1),hq]
  have hh : a+(q.val+1) = i+1 := by omega
  rw [hh]
  abel

lemma forwardSlice_departure {d : ℕ} (Z : ℕ → Word d) (a n i t : ℕ)
    (h0 : ∀ j, wordPath (Z j) 0 = 0) (hai : a ≤ i) (hin : i < a+n) (ht : t < (Z i).1) :
    ∃ u < (concatenateList (tapePrefix n (fun j => Z (a+j)))).1,
      wordPath (concatenateList (tapePrefix n (fun j => Z (a+j)))) u =
        (∑ j ∈ Finset.range i, wordEnd (Z j)) -
        (∑ j ∈ Finset.range a, wordEnd (Z j)) + wordPath (Z i) t := by
  let q : Fin n := ⟨i-a,by omega⟩
  have hq : a+q.val = i := by dsimp [q];omega
  let u := (∑ j : Fin n with j < q, (Z (a+j)).1)+t
  have hu := concatenateWords_departure (fun j : Fin n => Z (a+j)) q t (by simpa only [hq] using ht)
  refine ⟨u,hu,?_⟩
  have he := concatenateWords_site (fun j : Fin n => Z (a+j)) (fun j => h0 _) q t
    (by simpa only [hq] using ht.le)
  change wordPath (concatenateList (tapePrefix n (fun j => Z (a+j)))) u = _ at he
  rw [he,hq]
  have hsum : (∑ j : Fin n with j < q, wordEnd (Z (a+j))) =
      ∑ j ∈ Finset.range q.val, wordEnd (Z (a+j)) :=
    fin_prefix_sum_range (fun j => wordEnd (Z (a+j))) q.val (by omega)
  rw [hsum,slice_sum (fun j => wordEnd (Z j)) a q.val,hq]

lemma common_iterate_positive {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    ∀ b i, 0 < L b (((commonRestart L)^[r] Z) (b,i)) := by
  rw [common_iterates_shift L Z hZ he r]
  exact fun b i => hZ b _

lemma common_iterate_exists {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    ∀ s, ∃ H, 0 < H ∧ ((commonRestart L)^[s] ((commonRestart L)^[r] Z)) ∈ commonCut L H := by
  intro s
  rw [← Function.iterate_add_apply]
  exact he (s+r)

lemma nthCommon_length_add {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r s : ℕ) (b : Bool) :
    (nthCommonList L (r+s) Z b).1 = (nthCommonList L r Z b).1 +
      (nthCommonList L s ((commonRestart L)^[r] Z) b).1 := by
  rw [nthCommonList_append L Z hZ he r s b]
  rfl

end DirectionalZeroOne

end OAI
