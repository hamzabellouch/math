import Mathlib
import OAI.Probability.Contingency.Completions

namespace OAI

/-! Concrete Kernel. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators

namespace Contingency.PaddedGraph
variable {m n : ℕ}

abbrev SmallSlot (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :=
  {w : Cell m n // IsSmall U r c w}
abbrev LargeSlot (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :=
  {w : Cell m n // IsLarge U r c w}
abbrev SmallCoord (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :=
  SmallSlot U r c × Bool

noncomputable def largeIndex (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :=
  Fintype.equivFin (LargeSlot U r c)

 

noncomputable def wholeCoordinates (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Coordinate m n ≃ (SmallCoord U r c ⊕ (Fin (Fintype.card (LargeSlot U r c)) × Bool)) where
  toFun w := if h : IsSmall U r c w.2 then .inl (⟨w.2,h⟩,w.1)
    else .inr (largeIndex U r c ⟨w.2,Classical.not_not.mp h⟩,w.1)
  invFun w := match w with
    | .inl (s,b) => (b,s.val)
    | .inr (s,b) => (b,((largeIndex U r c).symm s).val)
  left_inv w := by
    rcases w with ⟨b,w⟩
    by_cases hw : IsSmall U r c w
    · simp only [dite_eq_left hw]
    · simp only [dite_eq_right hw,Equiv.symm_apply_apply]
  right_inv w := by
    rcases w with ⟨s,b⟩ | ⟨s,b⟩
    · dsimp; rw [dite_eq_left s.property]
    · dsimp
      rw [dite_eq_right (show ¬IsSmall U r c ((largeIndex U r c).symm s).val from
        fun h => h ((largeIndex U r c).symm s).property)]
      simp

@[simp] theorem wholeCoordinates_small (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s : SmallSlot U r c) (b : Bool) :
    wholeCoordinates U r c (b,s.val) = Sum.inl (s,b) := by
  simp only [wholeCoordinates,Equiv.coe_fn_mk,dite_eq_left s.property]

@[simp] theorem wholeCoordinates_large (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s : LargeSlot U r c) (b : Bool) :
    wholeCoordinates U r c (b,s.val) = Sum.inr (largeIndex U r c s,b) := by
  simp only [wholeCoordinates,Equiv.coe_fn_mk,dite_eq_right (show ¬IsSmall U r c s.val from
    fun h => h s.property)]

 theorem capacity_box (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    (fun w : Coordinate m n => capacity U C r c w.2) ∘ (wholeCoordinates U r c).symm =
      balanceBox (fun _ : SmallCoord U r c => (U:ℤ)) (fun _ => C) := by
  funext w
  rcases w with ⟨s,b⟩ | ⟨s,b⟩
  · simp [wholeCoordinates,capacity,balanceBox,(show ¬IsLarge U r c s.val from s.property)]
  · simp [wholeCoordinates,capacity,balanceBox,((largeIndex U r c).symm s).property]

 theorem capacity_total (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    (∑ w, capacity U C r c w) =
      (Fintype.card (SmallSlot U r c):ℤ)*U+(Fintype.card (LargeSlot U r c):ℤ)*C := by
  have h := Fintype.sum_subtype_add_sum_subtype (IsLarge U r c) (capacity U C r c)
  have hl (w : LargeSlot U r c) : capacity U C r c w.val = (C:ℤ) := by
    simp [capacity,w.property]
  have hs (w : SmallSlot U r c) : capacity U C r c w.val = (U:ℤ) := by
    simp [capacity,(show ¬IsLarge U r c w.val from w.property)]
  change (∑ w : LargeSlot U r c, capacity U C r c w.val) +
    (∑ w : SmallSlot U r c, capacity U C r c w.val) = _ at h
  simp only [hl,hs,Finset.sum_const,Finset.card_univ, nsmul_eq_mul] at h
  linarith

noncomputable def smallKernel (η : ℝ) (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : SmallCoord U r c → ℤ) : ℝ :=
  balancedSlots (fun q => softWeight η (fun i => r i) (paddedRow U L r c)
    (fun j => c j) (paddedCol U L r c) (capacity U C r c) (smallSet U r c)
    (q ∘ wholeCoordinates U r c)) (fun _ => C) p

 

theorem smallKernel_signature (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (U L C : ℕ) (hC : 2 ≤ C) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    PositiveSlice (smallKernel η U L C r c) (fun _ => (U:ℤ))
      ((Fintype.card (SmallSlot U r c):ℤ)*U) ∧
    HasSignature (smallKernel η U L C r c) (fun _ => (U:ℤ))
      ((Fintype.card (SmallSlot U r c):ℤ)*U) := by
  have hp := (softWeight_positive η hη (fun i => r i) (paddedRow U L r c)
    (fun j => c j) (paddedCol U L r c) (capacity U C r c) (smallSet U r c)).reindex
      (wholeCoordinates U r c)
  have hs := (softWeight_signature η hη hη1 (fun i => r i) (paddedRow U L r c)
    (fun j => c j) (paddedCol U L r c) (capacity U C r c) (smallSet U r c)).reindex
      (wholeCoordinates U r c)
  rw [capacity_box] at hp hs
  have h := balancedSlots_closure _ _ _ (fun _ => C) (fun _ => hC) _ hp hs
  rw [capacity_total] at h
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fin,add_sub_cancel_right] at h
  exact h

noncomputable def stateCoordinates (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (w : SmallCoord U r c) : ℤ :=
  if w.2 then X.x w.1.val else (U:ℤ)-X.q w.1.val

noncomputable def coordinatesState (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : SmallCoord U r c → ℤ) : State m n where
  x w := if h : IsSmall U r c w then p (⟨w,h⟩,true) else 0
  q w := if h : IsSmall U r c w then (U:ℤ)-p (⟨w,h⟩,false) else 0

@[simp] theorem coordinatesState_x (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : SmallCoord U r c → ℤ) (w : SmallSlot U r c) :
    (coordinatesState U r c p).x w.val = p (w,true) := by simp [coordinatesState,w.property]
@[simp] theorem coordinatesState_q (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : SmallCoord U r c → ℤ) (w : SmallSlot U r c) :
    (coordinatesState U r c p).q w.val = (U:ℤ)-p (w,false) := by simp [coordinatesState,w.property]

@[simp] theorem stateCoordinates_coordinatesState (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : SmallCoord U r c → ℤ) :
    stateCoordinates U r c (coordinatesState U r c p) = p := by
  funext ⟨w,b⟩
  cases b <;> simp [stateCoordinates]

def largeChoicesEquiv (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    LargeChoices U C r c ≃ (LargeSlot U r c → Fin (C+1)) where
  toFun A w := ⟨(A.val w.val).toNat,by have h := A.property w.val; omega⟩
  invFun a := ⟨(fun w => if h : IsLarge U r c w then (a ⟨w,h⟩:ℕ) else 0),by
    intro w
    dsimp
    by_cases hw : IsLarge U r c w
    · rw [dite_eq_left hw]
      have h := (a ⟨w,hw⟩).isLt
      exact ⟨by omega,by omega,fun hh => (hh hw).elim⟩
    · rw [dite_eq_right hw]
      exact ⟨by omega,by omega,fun _ => rfl⟩⟩
  left_inv A := by
    apply Subtype.ext
    funext w
    dsimp
    by_cases hw : IsLarge U r c w
    · rw [ite_eq_left hw,Int.toNat_of_nonneg (A.property w).1]
    · rw [ite_eq_right hw,(A.property w).2.2 hw]
  right_inv a := by
    funext w
    apply Fin.ext
    simp only [dite_eq_left w.property,Int.toNat_natCast]

noncomputable def largeProfileEquiv (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    LargeChoices U C r c ≃ (Fin (Fintype.card (LargeSlot U r c)) → Fin (C+1)) :=
  (largeChoicesEquiv U C r c).trans ((largeIndex U r c).arrowCongr (Equiv.refl _))

 theorem balanced_fullCoordinates (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (hX : ∀ w, IsLarge U r c w → X.x w=0 ∧ X.q w=0)
    (A : LargeChoices U C r c) :
    (Sum.elim (stateCoordinates U r c X) (balanceProfile (fun _ => C) (largeProfileEquiv U C r c A))) ∘
      wholeCoordinates U r c = fullCoordinates U C r c X A.val := by
  funext ⟨b,w⟩
  by_cases hw : IsSmall U r c w
  · have hA := (A.property w).2.2 hw
    have he := wholeCoordinates_small U r c ⟨w,hw⟩ b
    simp only [Function.comp_apply,he,Sum.elim_inl,stateCoordinates]
    cases b <;> simp [fullCoordinates,capacity,(show ¬IsLarge U r c w from hw),hA]
  · have hl := Classical.not_not.mp hw
    have hx := hX w hl
    have he := wholeCoordinates_large U r c ⟨w,hl⟩ b
    simp only [Function.comp_apply,he,Sum.elim_inr,balanceProfile]
    have ha : (largeProfileEquiv U C r c A (largeIndex U r c ⟨w,hl⟩):ℕ) = (A.val w).toNat := by
      simp [largeProfileEquiv,largeChoicesEquiv]
      rfl
    rw [ha,Int.toNat_of_nonneg (A.property w).1]
    cases b <;> simp [fullCoordinates,capacity,hl,hx]

 
theorem smallKernel_zero_count (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i) = ∑ j, c j) (X : State m n) (hf : Feasible U r c X)
    (hC : ∀ i, paddedRow U L r c i ≤ C) :
    smallKernel 0 U L C r c (stateCoordinates U r c X) =
      (Nat.card (Completion U L r c X):ℝ) := by
  unfold smallKernel balancedSlots
  rw [← Equiv.sum_comp (largeProfileEquiv U C r c)]
  simp_rw [balanced_fullCoordinates U C r c X hf.2.1]
  exact sum_choice_softWeight U L C r c hrc X hf hC

 theorem full_zero_feasible (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (hX : ∀ w, IsLarge U r c w → X.x w=0 ∧ X.q w=0)
    (A : LargeChoices U C r c)
    (hb : InBox (fun w => capacity U C r c w.2) (fullCoordinates U C r c X A.val))
    (hp : softPenalty (fun i => r i) (paddedRow U L r c)
      (fun j => c j) (paddedCol U L r c) (capacity U C r c) (smallSet U r c)
      (fullCoordinates U C r c X A.val)=0) : Feasible U r c X := by
  rw [softPenalty_zero_iff] at hp
  have hsx (w : Cell m n) :
      (if w ∈ smallSet U r c then fullCoordinates U C r c X A.val (true,w) else 0) = X.x w := by
    by_cases hw : IsSmall U r c w
    · simp [smallSet,hw,fullCoordinates,(A.property w).2.2 hw]
    · simp [smallSet,hw,(hX w (Classical.not_not.mp hw)).1]
  have hsq (w : Cell m n) :
      (if w ∈ smallSet U r c then capacity U C r c w -
        fullCoordinates U C r c X A.val (false,w) else 0) = X.q w := by
    rw [fullCoordinates_q]
    by_cases hw : IsSmall U r c w
    · simp [smallSet,hw,(A.property w).2.2 hw]
    · simp [smallSet,hw,(hX w (Classical.not_not.mp hw)).2]
  refine ⟨?_,hX,?_,?_⟩
  · intro w
    by_cases hw : IsLarge U r c w
    · rw [(hX w hw).1,(hX w hw).2]; exact ⟨by omega,by omega,by omega,by omega⟩
    · have hx := hb (true,w)
      have hq := hb (false,w)
      simp only [fullCoordinates,capacity,ite_eq_right hw,(A.property w).2.2 hw,
        Bool.false_eq_true,ite_false,ite_true,add_zero] at hx hq
      omega
  · intro i
    have hi := hp.2.2.1 i
    simp only [hsx] at hi
    refine ⟨hi,?_⟩
    intro hno
    have ha (j : Fin n) : A.val (i,j)=0 := (A.property (i,j)).2.2 (hno j)
    have he := hp.1 i
    simp only [fullCoordinates_x,ha,add_zero] at he
    simpa [rowSum,paddedRow,rowPadding,hno] using he
  · intro j
    have hj := hp.2.2.2 j
    simp only [hsq] at hj
    refine ⟨hj,?_⟩
    intro hno
    have ha (i : Fin m) : A.val (i,j)=0 := (A.property (i,j)).2.2 (hno i)
    have he := hp.2.1 j
    simp only [fullCoordinates_q,ha,add_zero] at he
    simpa [colSum,paddedCol,colPadding,hno] using he

 theorem coordinatesState_supported (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : SmallCoord U r c → ℤ) :
    ∀ w, IsLarge U r c w → (coordinatesState U r c p).x w=0 ∧
      (coordinatesState U r c p).q w=0 := by
  intro w hw
  have hs : ¬IsSmall U r c w := fun h => h hw
  simp [coordinatesState,hs]

 theorem smallKernel_zero_infeasible (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : SmallCoord U r c → ℤ) (hf : ¬Feasible U r c (coordinatesState U r c p)) :
    smallKernel 0 U L C r c p = 0 := by
  let X := coordinatesState U r c p
  have hX := coordinatesState_supported U r c p
  have he : p = stateCoordinates U r c X := (stateCoordinates_coordinatesState U r c p).symm
  rw [he]
  unfold smallKernel balancedSlots
  rw [← Equiv.sum_comp (largeProfileEquiv U C r c)]
  simp_rw [balanced_fullCoordinates U C r c X hX]
  apply Finset.sum_eq_zero
  intro A hA
  rw [softWeight_zero,ite_eq_right]
  rintro ⟨hb,ht,hp⟩
  exact hf (full_zero_feasible U L C r c X hX A hb hp)

 theorem smallKernel_continuous (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : SmallCoord U r c → ℤ) : Continuous (fun η : ℝ => smallKernel η U L C r c p) := by
  unfold smallKernel balancedSlots
  apply continuous_finsetSum
  intro a _
  exact softWeight_continuous _ _ _ _ _ _ _

 theorem smallKernel_nonneg (η : ℝ) (hη : 0 ≤ η) (U L C : ℕ)
    (r : Fin m → ℕ) (c : Fin n → ℕ) (p : SmallCoord U r c → ℤ) :
    0 ≤ smallKernel η U L C r c p := by
  unfold smallKernel balancedSlots
  apply Finset.sum_nonneg
  intro a _
  unfold softWeight
  dsimp only
  split_ifs
  · exact pow_nonneg hη _
  · rfl

end Contingency.PaddedGraph

 

 

open scoped BigOperators

namespace Contingency
section Nonnegative
variable {α : Type*} [Fintype α]

theorem weight_zero_of_total_zero (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hz : totalWeight w = 0) : ∀ x, w x=0 := by
  have h := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hw x).mp hz
  exact fun x => h x (Finset.mem_univ x)

theorem mass_mul_mean (w H : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    totalWeight w*weightedMean w H = ∑ x, w x*H x := by
  by_cases hz : totalWeight w = 0
  · have h := weight_zero_of_total_zero w hw hz
    simp [hz,h]
  · unfold weightedMean
    exact mul_div_cancel₀ _ hz

theorem centered_sum_nonneg (w H : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x*(H x-weightedMean w H))=0 := by
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  change (∑ x, w x*H x)-totalWeight w*weightedMean w H = 0
  rw [mass_mul_mean w H hw,sub_self]

theorem variance_translate_nonneg (w H : α → ℝ) (hw : ∀ x, 0 ≤ w x) (a : ℝ) :
    (∑ x, w x*(H x-a)^2) =
      weightedVariance w H + totalWeight w*(weightedMean w H-a)^2 := by
  have h (x : α) : w x*(H x-a)^2 =
      w x*(H x-weightedMean w H)^2 +
      2*(weightedMean w H-a)*(w x*(H x-weightedMean w H)) +
      w x*(weightedMean w H-a)^2 := by ring
  simp only [h,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  rw [centered_sum_nonneg w H hw]
  simp [weightedVariance,totalWeight]

theorem variance_le_deviation (w H : α → ℝ) (hw : ∀ x, 0 ≤ w x) (a : ℝ) :
    weightedVariance w H ≤ ∑ x, w x*(H x-a)^2 := by
  rw [variance_translate_nonneg w H hw a]
  have hZ : 0 ≤ totalWeight w := Finset.sum_nonneg fun x _ => hw x
  exact le_add_of_nonneg_right (mul_nonneg hZ (sq_nonneg _))

end Nonnegative

section Decomposition
variable {α β : Type*} [Fintype α] [Fintype β]

 

theorem variance_decompose (w H : α × β → ℝ) (hw : ∀ x, 0 ≤ w x) :
    weightedVariance w H =
      (∑ a, weightedVariance (fun b => w (a,b)) (fun b => H (a,b))) +
      weightedVariance (fun a => totalWeight (fun b => w (a,b)))
        (fun a => weightedMean (fun b => w (a,b)) (fun b => H (a,b))) := by
  have hmean : weightedMean w H =
      weightedMean (fun a => totalWeight (fun b => w (a,b)))
        (fun a => weightedMean (fun b => w (a,b)) (fun b => H (a,b))) := by
    unfold weightedMean
    congr 1
    · simp_rw [show ∀ a, totalWeight (fun b => w (a,b)) *
          ((∑ b, w (a,b)*H (a,b))/totalWeight (fun b => w (a,b))) =
          ∑ b, w (a,b)*H (a,b) from fun a => mass_mul_mean _ _ (fun b => hw (a,b))]
      exact Fintype.sum_prod_type _
    · simp [totalWeight,Fintype.sum_prod_type]
  unfold weightedVariance
  rw [Fintype.sum_prod_type]
  simp_rw [variance_translate_nonneg _ _ (fun b => hw (_,b)) (weightedMean w H)]
  rw [Finset.sum_add_distrib]
  rw [hmean]
  rfl

end Decomposition

 

def Profiles (C : ℕ) : ℕ → Type
  | 0 => PUnit
  | n+1 => Fin (C+1) × Profiles C n

instance profilesFintype (C : ℕ) : (n : ℕ) → Fintype (Profiles C n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => letI := profilesFintype C n
           inferInstanceAs (Fintype (Fin (C+1) × Profiles C n))

 

def ExposureEnergies (C : ℕ) : ℕ → Type
  | 0 => PUnit
  | n+1 => ℝ × (Fin (C+1) → ExposureEnergies C n)

noncomputable def exposureEnergy (C : ℕ) : (n : ℕ) → ExposureEnergies C n → ℝ
  | 0, _ => 0
  | n+1, E => E.1 + ∑ j, exposureEnergy C n (E.2 j)

 

def ChildVarianceBounds (C : ℕ) (A : ℝ) : (n : ℕ) →
    (Profiles C n → ℝ) → (Profiles C n → ℝ) → ExposureEnergies C n → Prop
  | 0, _, _, _ => True
  | n+1, w, H, E =>
      weightedVariance (fun j => totalWeight (fun b => w (j,b)))
        (fun j => weightedMean (fun b => w (j,b)) (fun b => H (j,b))) ≤ A*E.1 ∧
      ∀ j, ChildVarianceBounds C A n (fun b => w (j,b)) (fun b => H (j,b)) (E.2 j)

 

theorem exposure_variance_bound (C : ℕ) (A : ℝ) (n : ℕ)
    (w H : Profiles C n → ℝ) (hw : ∀ x, 0 ≤ w x) (E : ExposureEnergies C n)
    (h : ChildVarianceBounds C A n w H E) :
    weightedVariance w H ≤ A*exposureEnergy C n E := by
  induction n with
  | zero =>
    simp only [exposureEnergy,mul_zero]
    let : Unique (Profiles C 0) := inferInstanceAs (Unique PUnit)
    by_cases hz : w (default : Profiles C 0)=0
    · simp [weightedVariance,hz]
    · simp [weightedVariance,weightedMean,totalWeight,
        mul_div_cancel_left₀ _ hz]
  | succ n ih =>
    have hd := variance_decompose (α:=Fin (C+1)) (β:=Profiles C n) w H hw
    change weightedVariance w H = _ at hd
    rw [hd]
    change _ ≤ A*(E.1 + ∑ j, exposureEnergy C n (E.2 j))
    have hb : (∑ j, weightedVariance (fun b => w (j,b)) (fun b => H (j,b))) ≤
        ∑ j, A*exposureEnergy C n (E.2 j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ih _ _ (fun b => hw (j,b)) (E.2 j) (h.2 j)
    rw [← Finset.mul_sum] at hb
    dsimp only [ChildVarianceBounds] at h
    nlinarith [h.1]

 

noncomputable def exposureLevel (C : ℕ) : (n : ℕ) → ExposureEnergies C n → ℕ → ℝ
  | 0, _, _ => 0
  | _+1, E, 0 => E.1
  | n+1, E, k+1 => ∑ j, exposureLevel C n (E.2 j) k

theorem exposureEnergy_levels (C n : ℕ) (E : ExposureEnergies C n) :
    exposureEnergy C n E = ∑ k ∈ Finset.range n, exposureLevel C n E k := by
  induction n with
  | zero => simp [exposureEnergy]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [exposureEnergy,exposureLevel]
    simp_rw [ih]
    rw [Finset.sum_comm]
    ring

theorem exposure_variance_level_bound (C : ℕ) (A : ℝ) (hA : 0 ≤ A) (n : ℕ)
    (w H : Profiles C n → ℝ) (hw : ∀ x, 0 ≤ w x) (E : ExposureEnergies C n)
    (h : ChildVarianceBounds C A n w H E) (G : ℝ)
    (hlevel : ∀ k < n, exposureLevel C n E k ≤ G) :
    weightedVariance w H ≤ (n:ℝ)*A*G := by
  have he : exposureEnergy C n E ≤ (n:ℝ)*G := by
    rw [exposureEnergy_levels]
    calc
      _ ≤ ∑ k ∈ Finset.range n, G := Finset.sum_le_sum fun k hk => hlevel k (Finset.mem_range.mp hk)
      _ = _ := by simp
  calc
    _ ≤ A*exposureEnergy C n E := exposure_variance_bound C A n w H hw E h
    _ ≤ A*((n:ℝ)*G) := mul_le_mul_of_nonneg_left he hA
    _ = _ := by ring

end Contingency

 

 

open scoped BigOperators

namespace Contingency

noncomputable def nodeMass (C n : ℕ) (f : (PairCoords Bool n → ℤ) → ℝ) (j : ℕ) : ℝ :=
  allBalance C n f (childProfile C j)

noncomputable def nodeMean (C n : ℕ) (f H : (PairCoords Bool n → ℤ) → ℝ) (j : ℕ) : ℝ :=
  nodeMass C n (fun x => f x*H x) j / nodeMass C n f j

def adjacentDisplay (C j : ℕ) : Bool → ℤ := fun b => if b then (j:ℤ)+1 else (C:ℤ)-j

@[simp] theorem adjacent_minus (C j : ℕ) :
    removeOne (adjacentDisplay C j) true = childProfile C j := by
  funext b; cases b <;> simp [removeOne,adjacentDisplay,childProfile]

@[simp] theorem adjacent_plus (C j : ℕ) :
    removeOne (adjacentDisplay C j) false = childProfile C (j+1:ℕ) := by
  funext b; cases b <;> simp [removeOne,adjacentDisplay,childProfile]
  ring

theorem nodeMass_min (C : ℕ) (hC : 2 ≤ C) (n : ℕ)
    (f : ℝ → (PairCoords Bool n → ℤ) → ℝ)
    (hc : ∀ x, Continuous (fun η => f η x))
    (hf : ∀ η, 0 < η → η < 1 → PositiveSlice (f η) (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C))
    (hs : ∀ η, 0 < η → η < 1 → HasSignature (f η) (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C))
    (a b j : ℕ) (haj : a ≤ j) (hjb : j ≤ b) (hb : b ≤ C) :
    min (nodeMass C n (f 0) a) (nodeMass C n (f 0) b) ≤ nodeMass C n (f 0) j := by
  have hcl (η : ℝ) (hη : 0 < η) (hη' : η < 1) :=
    allBalance_closure C hC n (f η) (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C)
      (by simpa only [pairBox_const] using hf η hη hη')
      (by simpa only [pairBox_const] using hs η hη hη')
  have ht : ((n+1:ℕ):ℤ)*C-(n:ℤ)*C = C := by push_cast; ring
  simp only [ht] at hcl
  exact zero_child_min C (fun η => allBalance C n (f η))
    (allBalance_continuous C n f hc) (fun η hη hη' => (hcl η hη hη').1)
    (fun η hη hη' => (hcl η hη hη').2) a b j (by positivity)
    (by exact_mod_cast haj) (by exact_mod_cast hjb) (by exact_mod_cast hb)

 

theorem node_adjacent_bound (C : ℕ) (hC : 2 ≤ C) (n : ℕ)
    (f : ℝ → (PairCoords Bool n → ℤ) → ℝ)
    (hc : ∀ x, Continuous (fun η => f η x))
    (hf : ∀ η, 0 < η → η < 1 → PositiveSlice (f η) (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C))
    (hs : ∀ η, 0 < η → η < 1 → HasSignature (f η) (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C))
    (hz : ∀ x, 0 ≤ f 0 x) (H : (PairCoords Bool n → ℤ) → ℝ)
    (d : ℝ) (hd : 0 ≤ d) (j : ℕ) (hj : j < C)
    (ha : auxiliaryMass n C (f 0) (adjacentDisplay C j) ≤
      d*max (nodeMass C n (f 0) j) (nodeMass C n (f 0) (j+1))) :
    min (nodeMass C n (f 0) j) (nodeMass C n (f 0) (j+1)) *
      (nodeMean C n (f 0) H j-nodeMean C n (f 0) H (j+1))^2 ≤
    (2+2*d*((C:ℝ)+1)^2) * ∑ e ∈ smallUnitEdges C n, edgeEnergy (f 0) H e := by
  have hzm (i : ℕ) : 0 ≤ nodeMass C n (f 0) i := allBalance_nonneg C n (f 0) hz _
  have hE : 0 ≤ ∑ e ∈ smallUnitEdges C n, edgeEnergy (f 0) H e :=
    Finset.sum_nonneg fun e _ => edgeEnergy_nonneg (f 0) H hz e
  have hA : 0 ≤ 2+2*d*((C:ℝ)+1)^2 := by positivity
  by_cases hm : nodeMass C n (f 0) j = 0
  · rw [hm,min_eq_left (hzm (j+1)),zero_mul]
    exact mul_nonneg hA hE
  by_cases hp : nodeMass C n (f 0) (j+1) = 0
  · rw [hp,min_eq_right (hzm j),zero_mul]
    exact mul_nonneg hA hE
  have hm' : 0 < nodeMass C n (f 0) j := lt_of_le_of_ne (hzm j) (Ne.symm hm)
  have hp' : 0 < nodeMass C n (f 0) (j+1) := lt_of_le_of_ne (hzm (j+1)) (Ne.symm hp)
  have hb : InBox (fun _ => (C:ℤ)) (adjacentDisplay C j) := by
    intro b; cases b <;> dsimp [adjacentDisplay] <;> omega
  have ht : adjacentDisplay C j true+adjacentDisplay C j false = (C:ℤ)+1 := by
    simp [adjacentDisplay]; ring
  have hv := zero_root_transport C hC n f hc hf hs H (adjacentDisplay C j) hb ht
    (by simpa only [minusMass,adjacent_minus,nodeMass] using hm')
    (by simpa only [plusMass,adjacent_plus,nodeMass] using hp')
  simp only [minusMass,plusMass,adjacent_minus,adjacent_plus] at hv
  exact transport_repair_arithmetic _ _ _ _ _ d C hm' hp' hE hd ha hv

 

theorem node_variance_bound (C : ℕ) (z H : ℕ → ℝ) (A E : ℝ)
    (hz : ∀ j ≤ C, 0 ≤ z j) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hmin : ∀ a b j, a ≤ j → j ≤ b → b ≤ C → min (z a) (z b) ≤ z j)
    (hadj : ∀ j < C, min (z j) (z (j+1))*(H j-H (j+1))^2 ≤ A*E) :
    weightedVariance (fun j : Fin (C+1) => z j) (fun j => H j) ≤
      ((C:ℝ)+1)^4*A*E := by
  let w : Fin (C+1) → ℝ := fun j => z j
  have hw : ∀ j, 0 ≤ w j := fun j => hz j (by omega)
  have hZ : 0 ≤ totalWeight w := Finset.sum_nonneg fun j _ => hw j
  by_cases hZ0 : totalWeight w = 0
  · have hh := weight_zero_of_total_zero w hw hZ0
    have he : weightedVariance w (fun j => H j)=0 := by
      unfold weightedVariance; simp only [hh,zero_mul,Finset.sum_const_zero]
    change weightedVariance w _ ≤ _
    rw [he]; positivity
  have hZ' : 0 < totalWeight w := lt_of_le_of_ne hZ (Ne.symm hZ0)
  have hzZ (j : ℕ) (hj : j ≤ C) : z j ≤ totalWeight w := by
    exact Finset.single_le_sum (fun i _ => hw i) (Finset.mem_univ (⟨j,by omega⟩ : Fin (C+1)))
  have hp (a b : Fin (C+1)) :
      w a*w b/totalWeight w*(H a-H b)^2 ≤ (C:ℝ)^2*A*E := by
    rcases le_total a.val b.val with hab | hba
    · exact child_pair_bound C z H (totalWeight w) A E hZ' hz hzZ hA hE hmin hadj a b hab (by omega)
    · have hh := child_pair_bound C z H (totalWeight w) A E hZ' hz hzZ hA hE hmin hadj b a hba (by omega)
      have he : w a*w b/totalWeight w*(H a-H b)^2 =
          z b*z a/totalWeight w*(H b-H a)^2 := by dsimp [w]; ring
      rw [he]; exact hh
  have hv := variance_le_card_sq w (fun j => H j) hZ' ((C:ℝ)^2*A*E) (by positivity) hp
  have hf : ((C:ℝ)+1)^2*(C:ℝ)^2 ≤ ((C:ℝ)+1)^4 := by
    have hh : (C:ℝ)^2 ≤ ((C:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) C]
    calc
      _ ≤ ((C:ℝ)+1)^2*((C:ℝ)+1)^2 := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ (Fintype.card (Fin (C+1)):ℝ)^2*((C:ℝ)^2*A*E) := hv
    _ = (((C:ℝ)+1)^2*(C:ℝ)^2)*(A*E) := by simp; ring
    _ ≤ ((C:ℝ)+1)^4*(A*E) := mul_le_mul_of_nonneg_right hf (mul_nonneg hA hE)
    _ = _ := by ring

end Contingency

end

end OAI
