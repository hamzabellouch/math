import OAI.Combinatorics.ContingencyTables.Rooted.ForestPenaltyApplication

namespace OAI

/-!
# Literal doubled-coordinate profiles for companion completion counts

Small views are retained separately. Every large pair is balanced, with
its physical tree or free-cell value represented in the prescribed finite
interval. These identities connect the concrete laminar factor family to
the actual graph completion sum.
-/

namespace ContingencyTables.ForestLiteralCount

open scoped BigOperators Classical
open SimpleGraph
open GraphIntegralCompletion GraphCompletionCounts ForestCapacity

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def width (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ) (i : I) (j : J) : ℕ :=
  if T.Adj (.inl i) (.inr j) then 20*d*b i j else b i j

noncomputable def lower (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ) (i : I) (j : J) : ℤ :=
  if T.Adj (.inl i) (.inr j) then -((10*d*b i j:ℕ):ℤ) else 0

noncomputable def cellCount (T : SimpleGraph (I⊕J)) (d : ℕ) (b free : I → J → ℕ)
    (a : TreeIndex T d b) (i : I) (j : J) : ℕ :=
  if h : T.Adj (.inl i) (.inr j) then (a ⟨(i,j),h⟩).val else free i j

noncomputable def profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (d : ℕ) (b x y free : I → J → ℕ) (a : TreeIndex T d b) (u : (I×J)×Bool) : ℕ :=
  if small u.1.1 u.1.2 then (if u.2 then y u.1.1 u.1.2 else x u.1.1 u.1.2)
  else if u.2 then width T d b u.1.1 u.1.2-cellCount T d b free a u.1.1 u.1.2
    else cellCount T d b free a u.1.1 u.1.2

noncomputable def largeValue (T : SimpleGraph (I⊕J)) (tree : I → J → ℤ)
    (free : I → J → ℕ) (i : I) (j : J) : ℤ :=
  if T.Adj (.inl i) (.inr j) then tree i j else free i j

omit [Fintype I] [Fintype J] in
lemma cellCount_le (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (d : ℕ) (b free : I → J → ℕ) (a : TreeIndex T d b)
    (hf : ∀ i j, small i j=false → ¬T.Adj (.inl i) (.inr j) → free i j≤b i j)
    (i : I) (j : J) (hs : small i j=false) : cellCount T d b free a i j≤width T d b i j := by
  by_cases ht : T.Adj (.inl i) (.inr j)
  · simp only [cellCount,ht,dite_eq_left,width,ite_true]
    have h := (a ⟨(i,j),ht⟩).isLt
    change (a ⟨(i,j),ht⟩).val <20*d*b i j+1 at h
    omega
  · simp only [cellCount,ht,not_false_eq_true,dite_eq_right,width,ite_false]
    exact hf i j hs ht

omit [Fintype I] [Fintype J] in
lemma row_profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (d : ℕ) (b x y free : I → J → ℕ) (a : TreeIndex T d b)
    (i : I) (j : J) :
    ForestPenaltyApplication.physicalRow (lower T d b) (profile small T d b x y free a) i j=
      (if small i j then (x i j:ℤ) else largeValue T (physical T d b a) free i j : ℤ) := by
  by_cases ht : T.Adj (.inl i) (.inr j)
  · have hs : small i j=false := hTG ht
    simp only [ForestPenaltyApplication.physicalRow,lower,profile,hs,Bool.false_eq_true,
      ite_false,ht,ite_true,cellCount,dite_eq_left,largeValue,physical]
    push_cast
    ring
  · simp only [ForestPenaltyApplication.physicalRow,lower,ht,ite_false,profile,
      Bool.false_eq_true,cellCount,not_false_eq_true,dite_eq_right,largeValue]
    split_ifs <;> norm_num

omit [Fintype I] [Fintype J] in
lemma column_profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (d : ℕ) (b x y free : I → J → ℕ) (a : TreeIndex T d b)
    (hy : ∀ i j, small i j=true → y i j≤b i j)
    (hf : ∀ i j, small i j=false → ¬T.Adj (.inl i) (.inr j) → free i j≤b i j)
    (i : I) (j : J) :
    ForestPenaltyApplication.physicalColumn (lower T d b) (width T d b)
      (profile small T d b x y free a) i j=
      (if small i j then ((b i j-y i j:ℕ):ℤ)
        else largeValue T (physical T d b a) free i j : ℤ) := by
  by_cases hs : small i j=true
  · have ht : ¬T.Adj (.inl i) (.inr j) := by
      intro h
      have hh : small i j=false := hTG h
      exact Bool.false_ne_true (hh.symm.trans hs)
    simp only [ForestPenaltyApplication.physicalColumn,lower,width,ht,ite_false,profile,
      hs,ite_true,Int.cast_zero,zero_add]
    push_cast
    rw [Nat.cast_sub (hy i j hs)]
  · have hs' : small i j=false := Bool.eq_false_iff.mpr hs
    have hbound := cellCount_le small T d b free a hf i j hs'
    have hcol : ForestPenaltyApplication.physicalColumn (lower T d b) (width T d b)
        (profile small T d b x y free a) i j=
        ForestPenaltyApplication.physicalRow (lower T d b) (profile small T d b x y free a) i j := by
      simp only [ForestPenaltyApplication.physicalColumn,ForestPenaltyApplication.physicalRow,
        profile,hs',Bool.false_eq_true,ite_false,ite_true,Nat.cast_sub hbound]
      ring
    rw [hcol,row_profile small T hTG d b x y free a i j]
    simp only [hs',Bool.false_eq_true,ite_false]

noncomputable def actualDeviation (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b x y free : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (tree : I → J → ℤ) : I⊕J → ℝ :=
  Sum.elim
    (fun i => ((∑ j, if small i j then (x i j:ℤ) else largeValue T tree free i j):ℤ)-r i)
    (fun j => ((∑ i, if small i j then ((b i j-y i j:ℕ):ℤ)
      else largeValue T tree free i j):ℤ)-c j)

noncomputable def actualPenalty (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b x y free : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (tree : I → J → ℤ) : ℝ :=
  (∑ v, if ForestPenaltyApplication.rootFlag T v then
    |actualDeviation small T b x y free r c tree v| else 0)+
  ∑ i, ∑ j, if T.Adj (.inl i) (.inr j) then
    max 0 (max (-(tree i j:ℝ)) ((tree i j:ℝ)-b i j))/(b i j:ℝ) else 0

lemma deviation_profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (d : ℕ) (b x y free : I → J → ℕ) (a : TreeIndex T d b)
    (r : I → ℤ) (c : J → ℤ)
    (hy : ∀ i j, small i j=true → y i j≤b i j)
    (hf : ∀ i j, small i j=false → ¬T.Adj (.inl i) (.inr j) → free i j≤b i j) :
    ForestPenaltyApplication.deviation (lower T d b) (width T d b) r c
      (profile small T d b x y free a)=actualDeviation small T b x y free r c (physical T d b a) := by
  funext g
  cases g with
  | inl i =>
    simp only [ForestPenaltyApplication.deviation,actualDeviation,Sum.elim_inl]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Int.cast_ite,Int.cast_natCast] using row_profile small T hTG d b x y free a i j
  | inr j =>
    simp only [ForestPenaltyApplication.deviation,actualDeviation,Sum.elim_inr]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Int.cast_ite,Int.cast_natCast] using column_profile small T hTG d b x y free a hy hf i j

lemma penalty_profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (d : ℕ) (b x y free : I → J → ℕ) (a : TreeIndex T d b)
    (r : I → ℤ) (c : J → ℤ)
    (hy : ∀ i j, small i j=true → y i j≤b i j)
    (hf : ∀ i j, small i j=false → ¬T.Adj (.inl i) (.inr j) → free i j≤b i j) :
    ForestPenaltyApplication.penalty T b (lower T d b) (width T d b) r c
      (profile small T d b x y free a)=actualPenalty small T b x y free r c (physical T d b a) := by
  unfold ForestPenaltyApplication.penalty ForestPenaltyApplication.rootPenalty actualPenalty
  rw [deviation_profile small T hTG d b x y free a r c hy hf]
  congr 1
  unfold ForestPenaltyApplication.treePenalty
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases ht : T.Adj (.inl i) (.inr j)
  · have hs : small i j=false := hTG ht
    have hrow := row_profile small T hTG d b x y free a i j
    simp only [hs,Bool.false_eq_true,ite_false,largeValue,ht,ite_true] at hrow
    simp only [ht,ite_true,EqualitySoftening.affineDistance,mul_one]
    rw [show (lower T d b i j:ℝ)+(profile small T d b x y free a ((i,j),false):ℝ)=
      (physical T d b a i j:ℝ) from hrow]
  · simp only [ht,ite_false]

omit [Fintype I] [Fintype J] in
lemma row_pointwise (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (x free : I → J → ℕ) (tree : I → J → ℤ)
    (hsupport : ∀ i j, ¬T.Adj (.inl i) (.inr j) → tree i j=0) (i : I) (j : J) :
    (if small i j then (x i j:ℤ) else largeValue T tree free i j)=tree i j+
      ForestPhysicalCompletion.fixedRow small T (fun i j => (x i j:ℤ))
        (fun i j => (free i j:ℤ)) i j := by
  by_cases ht : T.Adj (.inl i) (.inr j)
  · have hs : small i j=false := hTG ht
    simp only [hs,Bool.false_eq_true,ite_false,largeValue,ht,ite_true,
      ForestPhysicalCompletion.fixedRow,add_zero]
  · simp only [largeValue,ht,ite_false,hsupport i j ht,zero_add,
      ForestPhysicalCompletion.fixedRow]

omit [Fintype I] [Fintype J] in
lemma column_pointwise (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (b y free : I → J → ℕ) (tree : I → J → ℤ)
    (hsupport : ∀ i j, ¬T.Adj (.inl i) (.inr j) → tree i j=0) (i : I) (j : J) :
    (if small i j then ((b i j-y i j:ℕ):ℤ) else largeValue T tree free i j)=tree i j+
      ForestPhysicalCompletion.fixedColumn small T (fun i j => ((b i j-y i j:ℕ):ℤ))
        (fun i j => (free i j:ℤ)) i j := by
  by_cases ht : T.Adj (.inl i) (.inr j)
  · have hs : small i j=false := hTG ht
    simp only [hs,Bool.false_eq_true,ite_false,largeValue,ht,ite_true,
      ForestPhysicalCompletion.fixedColumn,add_zero]
  · simp only [largeValue,ht,ite_false,hsupport i j ht,zero_add,
      ForestPhysicalCompletion.fixedColumn]

lemma nonroot_iff (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (b x y free : I → J → ℕ) (r : I → ℤ) (c : J → ℤ)
    (tree : I → J → ℤ) (hsupport : ∀ i j, ¬T.Adj (.inl i) (.inr j) → tree i j=0) :
    (∀ g, ForestPenaltyApplication.rootFlag T g=false →
      actualDeviation small T b x y free r c tree g=0) ↔
    NonrootMargins T
      (ForestPhysicalCompletion.rowResidual small T r (fun i j => (x i j:ℤ))
        (fun i j => (free i j:ℤ)))
      (ForestPhysicalCompletion.columnResidual small T c (fun i j => ((b i j-y i j:ℕ):ℤ))
        (fun i j => (free i j:ℤ))) tree := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hflag : ForestPenaltyApplication.rootFlag T (.inl i)=false := by
        simpa only [ForestPenaltyApplication.rootFlag,decide_eq_false_iff_not] using hi
      have hraw := h (.inl i) hflag
      simp only [actualDeviation,Sum.elim_inl] at hraw
      have hsum : (∑ j, if small i j then (x i j:ℤ) else largeValue T tree free i j)=r i := by
        exact_mod_cast sub_eq_zero.mp hraw
      simp_rw [row_pointwise small T hTG x free tree hsupport] at hsum
      rw [Finset.sum_add_distrib] at hsum
      unfold ForestPhysicalCompletion.rowResidual
      omega
    · intro j hj
      have hflag : ForestPenaltyApplication.rootFlag T (.inr j)=false := by
        simpa only [ForestPenaltyApplication.rootFlag,decide_eq_false_iff_not] using hj
      have hraw := h (.inr j) hflag
      simp only [actualDeviation,Sum.elim_inr] at hraw
      have hsum : (∑ i, if small i j then ((b i j-y i j:ℕ):ℤ)
          else largeValue T tree free i j)=c j := by exact_mod_cast sub_eq_zero.mp hraw
      simp_rw [column_pointwise small T hTG b y free tree hsupport] at hsum
      rw [Finset.sum_add_distrib] at hsum
      unfold ForestPhysicalCompletion.columnResidual
      omega
  · intro h g hg
    cases g with
    | inl i =>
      have hi : Sum.inl i≠componentRoot T (.inl i) := by
        simpa only [ForestPenaltyApplication.rootFlag,decide_eq_false_iff_not] using hg
      have hsum : (∑ j, if small i j then (x i j:ℤ) else largeValue T tree free i j)=r i := by
        simp_rw [row_pointwise small T hTG x free tree hsupport]
        rw [Finset.sum_add_distrib,h.1 i hi]
        exact sub_add_cancel _ _
      simp only [actualDeviation,Sum.elim_inl]
      have hreal : (((∑ j, if small i j then (x i j:ℤ)
        else largeValue T tree free i j):ℤ):ℝ)=(r i:ℝ) := by exact_mod_cast hsum
      rw [hreal,sub_self]
    | inr j =>
      have hj : Sum.inr j≠componentRoot T (.inr j) := by
        simpa only [ForestPenaltyApplication.rootFlag,decide_eq_false_iff_not] using hg
      have hsum : (∑ i, if small i j then ((b i j-y i j:ℕ):ℤ)
          else largeValue T tree free i j)=c j := by
        simp_rw [column_pointwise small T hTG b y free tree hsupport]
        rw [Finset.sum_add_distrib,h.2 j hj]
        exact sub_add_cancel _ _
      simp only [actualDeviation,Sum.elim_inr]
      have hreal : (((∑ i, if small i j then ((b i j-y i j:ℕ):ℤ)
        else largeValue T tree free i j):ℤ):ℝ)=(c j:ℝ) := by exact_mod_cast hsum
      rw [hreal,sub_self]

/-- For each actual small profile and free assignment, the concrete
laminar factor sum retains exactly the source's root/tree penalty at
the unique integral completion, with its tree values in the prescribed
completion intervals. -/
theorem literal_tree_sum (small : I → J → Bool) (b : I → J → ℕ)
    (T : SimpleGraph (I⊕J)) (hTG : T≤cellGraph small) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph (I⊕J), F≤cellGraph small → F.IsAcyclic →
      MaximumForest.weight F (capacity b)≤MaximumForest.weight T (capacity b))
    (r : I → ℤ) (c : J → ℤ) (x y free : I → J → ℕ) (X : I → J → ℤ)
    (d W : ℕ) (alpha : ℝ) (hd : 1≤d) (hcard : Fintype.card I*Fintype.card J≤d)
    (hlarge : ∀ i j, small i j=false → W≤b i j ∧ 1≤b i j)
    (hsmall : ∀ i j, small i j=true → b i j<W ∧ x i j≤b i j ∧ y i j≤b i j)
    (hf : ∀ i j, small i j=false → ¬T.Adj (.inl i) (.inr j) → free i j≤b i j)
    (hX : ∀ i j, 0≤X i j ∧ X i j≤b i j)
    (hXr : ∀ i, (∑ j, X i j)=r i) (hXc : ∀ j, (∑ i, X i j)=c j) :
    (∑ a : TreeIndex T d b, ForestPenaltyApplication.physicalWeight T b
      (lower T d b) (width T d b) r c alpha (profile small T d b x y free a))=
      (2:ℝ)^(-alpha*actualPenalty small T b x y free r c
        (ForestPhysicalCompletion.solved small T r c (fun i j => (x i j:ℤ))
          (fun i j => ((b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ)))) := by
  have hy : ∀ i j, small i j=true → y i j≤b i j := fun i j hs => (hsmall i j hs).2.2
  have hsum := ForestPhysicalCompletion.tree_indicator_sum small b T hTG hT hmax r c
    (fun i j => (x i j:ℤ)) (fun i j => ((b i j-y i j:ℕ):ℤ))
    (fun i j => (free i j:ℤ)) X d W hd hcard hlarge
    (by
      intro i j hs
      refine ⟨(hsmall i j hs).1,⟨Nat.cast_nonneg _,?_⟩,⟨Nat.cast_nonneg _,?_⟩⟩
      · exact_mod_cast (hsmall i j hs).2.1
      · exact_mod_cast Nat.sub_le (b i j) (y i j))
    (by
      intro i j hs ht
      exact ⟨Nat.cast_nonneg _,by exact_mod_cast hf i j hs ht⟩)
    hX hXr hXc (fun tree => (2:ℝ)^(-alpha*actualPenalty small T b x y free r c tree))
  calc
    _=(∑ a : TreeIndex T d b,
      if NonrootMargins T
        (ForestPhysicalCompletion.rowResidual small T r (fun i j => (x i j:ℤ))
          (fun i j => (free i j:ℤ)))
        (ForestPhysicalCompletion.columnResidual small T c (fun i j => ((b i j-y i j:ℕ):ℤ))
          (fun i j => (free i j:ℤ))) (physical T d b a)
      then (2:ℝ)^(-alpha*actualPenalty small T b x y free r c (physical T d b a)) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [ForestPenaltyApplication.exact_eq,deviation_profile small T hTG d b x y free a r c hy hf,
          penalty_profile small T hTG d b x y free a r c hy hf]
        simp only [nonroot_iff small T hTG b x y free r c (physical T d b a) (physical_supported T d b a)]
    _=_ := hsum

end ContingencyTables.ForestLiteralCount

end OAI
