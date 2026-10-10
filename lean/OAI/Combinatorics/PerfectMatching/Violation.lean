import OAI.Combinatorics.PerfectMatching.FeasibilityRepair

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy
variable {n : ℕ}

def Affine.evalReal (r : Affine n) (x : Pair n → ℝ) : ℝ :=
  (∑ e,(r.coeff e:ℝ)*x e)+r.constant

def allRows (n : ℕ) : List (Affine n) :=
  zeroRow :: ((List.finRange n).flatMap (fun v => [degreeRow v true,degreeRow v false])) ++
    (univ.toList.filter (fun S : Finset (Fin n) => decide (Odd S.card))).map cutRow

def maxRow (x : Pair n → ℝ) : Affine n := by
  classical
  exact ((allRows n).argmax (fun r => r.evalReal x)).getD zeroRow

def violation (x : Pair n → ℝ) : ℝ := (maxRow x).evalReal x

lemma maxRow_mem_argmax (x : Pair n → ℝ) :
    maxRow x ∈ (allRows n).argmax (fun r => r.evalReal x) := by
  classical
  unfold maxRow
  cases he : (allRows n).argmax (fun r => r.evalReal x) with
  | none => have hh := List.argmax_eq_none.mp he; simp [allRows] at hh
  | some r => simp

lemma row_le_violation (x : Pair n → ℝ) (r : Affine n) (hr : r∈allRows n) :
    r.evalReal x≤violation x := List.le_of_mem_argmax hr (maxRow_mem_argmax x)

lemma violation_le (x : Pair n → ℝ) (b : ℝ) (h : ∀ r∈allRows n,r.evalReal x≤b) :
    violation x≤b := h _ (List.argmax_mem (maxRow_mem_argmax x))

lemma mem_allRows (r : Affine n) : r∈allRows n ↔
    r=zeroRow ∨ (∃ v,r=degreeRow v true ∨ r=degreeRow v false) ∨
      ∃ S : Finset (Fin n),Odd S.card ∧ r=cutRow S := by
  simp only [allRows,List.mem_append,List.mem_cons,List.mem_flatMap,List.mem_finRange,
    true_and,List.mem_map,List.mem_filter,mem_toList,mem_univ]
  aesop

lemma zero_row_eval (x : Pair n → ℝ) : (zeroRow : Affine n).evalReal x=0 := by
  simp [Affine.evalReal,zeroRow]

lemma degree_row_eval_pos (x : Pair n → ℝ) (v : Fin n) :
    (degreeRow v true).evalReal x=(completeGraph n).degree x v-1 := by
  simp [Affine.evalReal,degreeRow,LooplessGraph.degree,LooplessGraph.Incident,completeGraph,
    ite_mul,sub_eq_add_neg]
  apply sum_congr rfl; intro e _; rfl

lemma degree_row_eval_neg (x : Pair n → ℝ) (v : Fin n) :
    (degreeRow v false).evalReal x=1-(completeGraph n).degree x v := by
  simp only [Affine.evalReal,degreeRow,Bool.false_eq_true,↓reduceIte,Int.cast_one,
    Int.cast_ite,Int.cast_neg,Int.cast_zero,ite_mul,neg_one_mul,zero_mul]
  have he : (∑ e : Pair n,if e.val.1=v ∨ e.val.2=v then -x e else 0)=
      -(completeGraph n).degree x v := by
    simp only [LooplessGraph.degree,LooplessGraph.Incident,completeGraph,←sum_neg_distrib]
    apply sum_congr rfl; intro e _; split_ifs <;> simp_all
  rw [he]; ring

lemma cut_row_eval (x : Pair n → ℝ) (S : Finset (Fin n)) :
    (cutRow S).evalReal x=1-(completeGraph n).cutMass x S := by
  have he (e : Pair n) : ((e.val.1∈S ∧ e.val.2∉S) ∨ (e.val.2∈S ∧ e.val.1∉S)) ↔
      (completeGraph n).Crosses S e := by
    simp only [LooplessGraph.Crosses,completeGraph]; tauto
  simp only [Affine.evalReal,cutRow,he,Int.cast_ite,Int.cast_neg,Int.cast_one,
    Int.cast_zero,ite_mul,neg_one_mul,zero_mul]
  have hsum : (∑ e : Pair n,if (completeGraph n).Crosses S e then -x e else 0)=
      -(completeGraph n).cutMass x S := by
    simp only [LooplessGraph.cutMass,LooplessGraph.cut,sum_filter,←sum_neg_distrib]
    apply sum_congr rfl; intro e _; split_ifs <;> simp_all
  rw [hsum]; ring

lemma violation_nonneg (x : Pair n → ℝ) : 0≤violation x := by
  simpa only [zero_row_eval] using row_le_violation x zeroRow ((mem_allRows _).2 (Or.inl rfl))

lemma degree_violation (x : Pair n → ℝ) (v : Fin n) :
    |(completeGraph n).degree x v-1|≤violation x := by
  have hp := row_le_violation x (degreeRow v true)
    ((mem_allRows _).2 (Or.inr (Or.inl ⟨v,Or.inl rfl⟩)))
  have hm := row_le_violation x (degreeRow v false)
    ((mem_allRows _).2 (Or.inr (Or.inl ⟨v,Or.inr rfl⟩)))
  rw [degree_row_eval_pos] at hp; rw [degree_row_eval_neg] at hm
  exact abs_le.mpr ⟨by linarith,hp⟩

lemma cut_violation (x : Pair n → ℝ) (S : Finset (Fin n)) (hS : Odd S.card) :
    1-violation x≤(completeGraph n).cutMass x S := by
  have hh := row_le_violation x (cutRow S)
    ((mem_allRows _).2 (Or.inr (Or.inr ⟨S,hS,rfl⟩)))
  rw [cut_row_eval] at hh; linarith

lemma violation_feasible (heven : Even n) {x : Pair n → ℝ}
    (hx : x∈(completeGraph n).polytope) : violation x=0 := by
  rw [(completeGraph n).polytope_eq_constraints (by simpa using heven)] at hx
  apply le_antisymm _ (violation_nonneg x)
  apply violation_le
  intro r hr
  rcases (mem_allRows r).1 hr with rfl|⟨v,rfl|rfl⟩|⟨S,hS,rfl⟩
  · rw [zero_row_eval]
  · rw [degree_row_eval_pos,hx.2.1]; norm_num
  · rw [degree_row_eval_neg,hx.2.1]; norm_num
  · rw [cut_row_eval]; linarith [hx.2.2 S hS]

lemma violation_repair (hn : 4≤n) (heven : Even n) (x : Pair n → ℝ)
    (hx : ∀ e,x e∈Set.Icc (0:ℝ) 1) : ∃ y∈(completeGraph n).polytope,
      ∀ e,|y e-x e|≤(2+10*(n:ℝ)^2)*violation x :=
  feasibility_repair hn heven hx (violation_nonneg x) (degree_violation x) (cut_violation x)

lemma row_difference (r : Affine n) (x z : Pair n → ℝ) :
    r.evalReal z=r.evalReal x+∑ e,(r.coeff e:ℝ)*(z e-x e) := by
  simp only [Affine.evalReal,mul_sub,sum_sub_distrib]; ring

lemma row_coeff_bound (r : Affine n) (hr : r∈allRows n) (e : Pair n) : |(r.coeff e:ℝ)|≤1 := by
  rcases (mem_allRows r).1 hr with rfl|⟨v,rfl|rfl⟩|⟨S,_,rfl⟩
  · simp [zeroRow]
  · simp only [degreeRow,↓reduceIte]; split_ifs <;> norm_num
  · simp only [degreeRow,Bool.false_eq_true,↓reduceIte]; split_ifs <;> norm_num
  · simp only [cutRow]; split_ifs <;> norm_num

lemma active_row_subgradient (x : Pair n → ℝ) (r : Affine n)
    (hr : r∈allRows n) (ha : r.evalReal x=violation x) (z : Pair n → ℝ) :
    violation x+∑ e,(r.coeff e:ℝ)*(z e-x e)≤violation z := by
  rw [←ha,←row_difference]
  exact row_le_violation z r hr

lemma eval_cast (a : Affine n) (x : Pair n → ℚ) :
    a.evalReal (fun e => (x e:ℝ))=(a.eval x:ℝ) := by
  simp [Affine.eval,Affine.evalReal]

lemma capacities_symm (a : Table n ℤ) (i j : Fin n) : capacities a i j=capacities a j i := by
  unfold capacities
  rcases lt_trichotomy i j with h|h|h
  · simp [h,not_lt_of_ge h.le]
  · subst j; rfl
  · simp [h,not_lt_of_ge h.le]

lemma capacities_pair (a : Table n ℤ) (e : Pair n) :
    capacities a e.val.1 e.val.2=(entry a e).toNat := by
  simp [capacities,e.property,entry]

lemma cut_coordinates (D : ℕ) (a : Table n ℤ) (ha : ∀ e,0≤entry a e)
    (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun e => (coordinates D a e:ℝ)) S=
      (UnitFlow.cutCapacity (capacities a) S:ℝ)/(D:ℝ) := by
  have hx : (fun e => (coordinates D a e:ℝ))=
      (fun e : Pair n => (capacities a e.val.1 e.val.2:ℝ)/(D:ℝ)) := by
    funext e
    simp only [coordinates,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,capacities_pair]
    have he : ((entry a e).toNat:ℝ)=((entry a e:ℤ):ℝ) := by exact_mod_cast Int.toNat_of_nonneg (ha e)
    rw [he]
  rw [hx,cut_from_symm (fun i j => (capacities a i j:ℝ)/(D:ℝ)) (fun i j => by rw [capacities_symm a i j])]
  simp only [UnitFlow.cutCapacity,Nat.cast_sum,sum_div]

lemma activeRows_nonempty (a : Table n ℤ) : activeRows a≠[] := by simp [activeRows]

lemma activeRow_mem_argmax (D : ℕ) (a : Table n ℤ) :
    activeRow D a∈(activeRows a).argmax (fun r => r.eval (coordinates D a)) := by
  unfold activeRow
  cases he : (activeRows a).argmax (fun r => r.eval (coordinates D a)) with
  | none => exact (activeRows_nonempty a (List.argmax_eq_none.mp he)).elim
  | some r => simp

lemma mem_activeRows (a : Table n ℤ) (r : Affine n) : r∈activeRows a ↔
    r=zeroRow ∨ (∃ v,r=degreeRow v true ∨ r=degreeRow v false) ∨
      r=cutRow (OddMincut.oddCut (capacities a) univ) := by
  simp only [activeRows,List.mem_append,List.mem_cons,List.mem_flatMap,List.mem_finRange,
    true_and]
  aesop

lemma activeRow_correct (hn : 2≤n) (heven : Even n) {D : ℕ} (hD : 0<D)
    (a : Table n ℤ) (ha : ∀ e,0≤entry a e) :
    activeRow D a∈allRows n ∧
      (activeRow D a).evalReal (fun e => (coordinates D a e:ℝ))=
        violation (fun e => (coordinates D a e:ℝ)) := by
  let S₀ := OddMincut.oddCut (capacities a) univ
  have hh := OddMincut.oddCut_correct (capacities a) (capacities_symm a) univ
    (by simpa using heven) (by simpa using hn)
  have hodd : Odd S₀.card := by simpa [OddCutParity.OddSide] using hh.1
  have hmin (S : Finset (Fin n)) (hS : Odd S.card) :
      UnitFlow.cutCapacity (capacities a) S₀≤UnitFlow.cutCapacity (capacities a) S :=
    hh.2 S (by simpa [OddCutParity.OddSide] using hS)
  have hsub : ∀ r∈activeRows a,r∈allRows n := by
    intro r hr
    rcases (mem_activeRows a r).1 hr with h|h|h
    · exact (mem_allRows r).2 (Or.inl h)
    · exact (mem_allRows r).2 (Or.inr (Or.inl h))
    · exact (mem_allRows r).2 (Or.inr (Or.inr ⟨S₀,hodd,h⟩))
  have ham := List.argmax_mem (activeRow_mem_argmax D a)
  refine ⟨hsub _ ham,le_antisymm (row_le_violation _ _ (hsub _ ham)) ?_⟩
  apply violation_le
  intro r hr
  have hdom (r' : Affine n) (hr' : r'∈activeRows a) :
      r'.evalReal (fun e => (coordinates D a e:ℝ))≤
        (activeRow D a).evalReal (fun e => (coordinates D a e:ℝ)) := by
    simp only [eval_cast]
    exact_mod_cast List.le_of_mem_argmax hr' (activeRow_mem_argmax D a)
  rcases (mem_allRows r).1 hr with h|h|⟨S,hS,rfl⟩
  · exact hdom r ((mem_activeRows a r).2 (Or.inl h))
  · exact hdom r ((mem_activeRows a r).2 (Or.inr (Or.inl h)))
  · apply le_trans _ (hdom (cutRow S₀) ((mem_activeRows a _).2 (Or.inr (Or.inr rfl))))
    rw [cut_row_eval,cut_row_eval,cut_coordinates D a ha,cut_coordinates D a ha]
    have hd : (0:ℝ)≤D := (Nat.cast_pos.mpr hD).le
    have hle : (UnitFlow.cutCapacity (capacities a) S₀:ℝ)≤
        UnitFlow.cutCapacity (capacities a) S := by exact_mod_cast hmin S hS
    linarith [div_le_div_of_nonneg_right hle hd]

end
end BinaryMatching.Algorithm
end

end OAI
