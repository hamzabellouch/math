import Mathlib
import OAI.Probability.Contingency.ConcreteKernel

namespace OAI

/-! Concrete Contexts. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ}

def smallRank (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (s : SmallSlot U r c) : Fin (m*n) :=
  finProdFinEquiv s.val

theorem smallRank_injective (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Function.Injective (smallRank U r c) := by
  intro s t h
  exact Subtype.ext (finProdFinEquiv.injective h)

 

noncomputable def smallIndex (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Fin (Fintype.card (SmallSlot U r c)) ≃ SmallSlot U r c := by
  letI := LinearOrder.lift' (smallRank U r c) (smallRank_injective U r c)
  exact (monoEquivOfFin (SmallSlot U r c) rfl).toEquiv

theorem smallRank_lt_iff (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : SmallSlot U r c) : smallRank U r c s < smallRank U r c t ↔ Before s.val t.val := by
  change s.val.2.val+n*s.val.1.val < t.val.2.val+n*t.val.1.val ↔ _
  have hs := s.val.2.isLt
  have ht := t.val.2.isLt
  unfold Before
  constructor
  · intro hh
    by_cases hi : s.val.1 < t.val.1
    · exact Or.inl hi
    · have hti : t.val.1 ≤ s.val.1 := le_of_not_gt hi
      have he : s.val.1=t.val.1 := by
        apply Fin.ext
        by_contra hn
        have hlt : t.val.1.val+1 ≤ s.val.1.val := by omega
        have hm := Nat.mul_le_mul_left n hlt
        simp only [Nat.mul_add,Nat.mul_one] at hm
        omega
      exact Or.inr ⟨he,by rw [he] at hh; omega⟩
  · rintro (hi | ⟨hi,hj⟩)
    · have hm := Nat.mul_le_mul_left n (show s.val.1.val+1 ≤ t.val.1.val by omega)
      simp only [Nat.mul_add,Nat.mul_one] at hm
      omega
    · rw [hi]; omega

theorem smallIndex_lt (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Fin (Fintype.card (SmallSlot U r c))) :
    Before (smallIndex U r c s).val (smallIndex U r c t).val ↔ s < t := by
  let := LinearOrder.lift' (smallRank U r c) (smallRank_injective U r c)
  rw [← smallRank_lt_iff]
  exact @OrderIso.lt_iff_lt _ _ _
    (LinearOrder.lift' (smallRank U r c) (smallRank_injective U r c)).toPreorder
    (monoEquivOfFin (SmallSlot U r c) rfl) s t

 

noncomputable def contextCoordinates (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) :
    SmallCoord U r c ≃ ((Fin k × Bool) ⊕ PairCoords Bool a) :=
  (((smallIndex U r c).symm.trans (finCongr h)).trans finSumFinEquiv.symm |>.prodCongr (Equiv.refl Bool)).trans
    ((Equiv.sumProdDistrib (Fin k) (Fin (a+1)) Bool).trans
      (Equiv.sumCongr (Equiv.refl _) (smallCoords a).symm))

noncomputable def contextKernel (η : ℝ) (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1))
    (σ : Fin k → Fin (U+1)) (p : PairCoords Bool a → ℤ) : ℝ :=
  smallKernel η U L C r c ((Sum.elim (balanceProfile (fun _ => U) σ) p) ∘
    contextCoordinates U r c k a h)

theorem balanceProfile_box (U k : ℕ) (σ : Fin k → Fin (U+1)) :
    InBox (fun _ => (U:ℤ)) (balanceProfile (fun _ => U) σ) := by
  intro ⟨s,b⟩
  have hs := (σ s).isLt
  cases b <;> dsimp [balanceProfile] <;> omega

theorem balanceProfile_total (U k : ℕ) (σ : Fin k → Fin (U+1)) :
    (∑ w, balanceProfile (fun _ => U) σ w) = (k:ℤ)*U := by
  rw [Fintype.sum_prod_type]
  simp [balanceProfile]

 

theorem contextKernel_signature (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (U L C : ℕ) (hC : 2 ≤ C) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1)) :
    PositiveSlice (contextKernel η U L C r c k a h σ) (fun _ => (U:ℤ)) (((a+1:ℕ):ℤ)*U) ∧
    HasSignature (contextKernel η U L C r c k a h σ) (fun _ => (U:ℤ)) (((a+1:ℕ):ℤ)*U) := by
  obtain ⟨hp,hs⟩ := smallKernel_signature η hη hη1 U L C hC r c
  have hp' := hp.reindex (contextCoordinates U r c k a h)
  have hs' := hs.reindex (contextCoordinates U r c k a h)
  have hbox : (fun _ : SmallCoord U r c => (U:ℤ)) ∘ (contextCoordinates U r c k a h).symm =
      Sum.elim (fun _ : Fin k × Bool => (U:ℤ)) (fun _ : PairCoords Bool a => (U:ℤ)) := by
    funext w; cases w <;> rfl
  rw [hbox] at hp' hs'
  have hp'' := hp'.fixedContext _ (balanceProfile_box U k σ)
  have hs'' := hs'.fixedContext _ (balanceProfile_box U k σ)
  rw [balanceProfile_total,h] at hp'' hs''
  have he : ((k+(a+1):ℕ):ℤ)*U-(k:ℤ)*U = ((a+1:ℕ):ℤ)*U := by push_cast; ring
  rw [he] at hp'' hs''
  exact ⟨hp'',hs''⟩

theorem contextKernel_continuous (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1))
    (σ : Fin k → Fin (U+1)) (p : PairCoords Bool a → ℤ) :
    Continuous (fun η => contextKernel η U L C r c k a h σ p) :=
  smallKernel_continuous U L C r c _

theorem contextKernel_nonneg (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1))
    (σ : Fin k → Fin (U+1)) (p : PairCoords Bool a → ℤ) :
    0 ≤ contextKernel 0 U L C r c k a h σ p :=
  smallKernel_nonneg 0 (by norm_num) U L C r c _

theorem context_child_no_holes (U L C : ℕ) (hU : 2 ≤ U) (hC : 2 ≤ C)
    (r : Fin m → ℕ) (c : Fin n → ℕ) (k a : ℕ)
    (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (u v j : ℕ) (huj : u ≤ j) (hjv : j ≤ v) (hv : v ≤ U) :
    min (nodeMass U a (contextKernel 0 U L C r c k a h σ) u)
      (nodeMass U a (contextKernel 0 U L C r c k a h σ) v) ≤
      nodeMass U a (contextKernel 0 U L C r c k a h σ) j :=
  nodeMass_min U hU a _ (contextKernel_continuous U L C r c k a h σ)
    (fun η hη hη' => (contextKernel_signature η hη hη' U L C hC r c k a h σ).1)
    (fun η hη hη' => (contextKernel_signature η hη hη' U L C hC r c k a h σ).2)
    u v j huj hjv hv

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency
universe u

noncomputable def branchEquiv (C : ℕ) : (n : ℕ) → Branches C n ≃ (Fin n → Fin (C+1))
  | 0 => { toFun := fun _ i => Fin.elim0 i
           invFun := fun _ => PUnit.unit
           left_inv := fun x => by cases x; rfl
           right_inv := fun x => by funext i; exact Fin.elim0 i }
  | n+1 => ((Equiv.refl (Fin (C+1))).prodCongr (branchEquiv C n)).trans
      (piHeadEquiv (fun _ : Fin (n+1) => Fin (C+1))).symm

theorem branchEquiv_value (C n : ℕ) (a : Branches C n) (s : Fin n) :
    branchEquiv C n a s = branchValue C n a s := by
  induction n with
  | zero => exact Fin.elim0 s
  | succ n ih =>
    refine Fin.cases ?_ (fun t => ?_) s
    · rfl
    · exact ih a.2 t

theorem allBalance_sum_leaf {ι : Type u} (C n : ℕ)
    (f : (PairCoords ι n → ℤ) → ℝ) (p : ι → ℤ) :
    allBalance C n f p = ∑ a : Branches C n, f (leafDisplay C n p a) := by
  induction n generalizing ι with
  | zero => simp [allBalance,leafDisplay]
  | succ n ih =>
    change (∑ j ∈ Finset.range (C+1), allBalance C n f (pairAssembly p (j:ℤ) ((C:ℤ)-j))) = _
    rw [← Fin.sum_univ_eq_sum_range]
    simp_rw [ih]
    change _ = ∑ a : Fin (C+1) × Branches C n, f (leafDisplay C (n+1) p a)
    rw [Fintype.sum_prod_type]
    rfl

noncomputable def mixedDisplay {ι : Type u} (n : ℕ) (D : Fin n → ℕ)
    (p : ι → ℤ) (a : ∀ s, Fin (D s+1)) : PairCoords ι n → ℤ :=
  Sum.elim p (balanceProfile D a) ∘ pairCoordsEquiv ι n

@[simp] theorem mixedDisplay_base {ι : Type u} (n : ℕ) (D : Fin n → ℕ)
    (p : ι → ℤ) (a : ∀ s, Fin (D s+1)) (i : ι) :
    mixedDisplay n D p a ((pairCoordsEquiv ι n).symm (.inl i)) = p i := by
  simp [mixedDisplay]

@[simp] theorem mixedDisplay_slot {ι : Type u} (n : ℕ) (D : Fin n → ℕ)
    (p : ι → ℤ) (a : ∀ s, Fin (D s+1)) (s : Fin n) (b : Bool) :
    mixedDisplay n D p a ((pairCoordsEquiv ι n).symm (.inr (s,b))) =
      if b then ((a s:ℕ):ℤ) else (D s:ℤ)-(a s:ℕ) := by
  simp [mixedDisplay,balanceProfile]

theorem leafDisplay_mixed {ι : Type u} (C n : ℕ) (p : ι → ℤ) (a : Branches C n) :
    leafDisplay C n p a = mixedDisplay n (fun _ => C) p (branchEquiv C n a) := by
  funext i
  obtain ⟨q,rfl⟩ := (pairCoordsEquiv ι n).symm.surjective i
  rcases q with i | ⟨s,b⟩
  · rw [leafDisplay_base,mixedDisplay_base]
  · rw [leafDisplay_slot,mixedDisplay_slot,branchEquiv_value]

theorem mixedDisplay_injective {ι : Type u} (n : ℕ) (D : Fin n → ℕ) (p : ι → ℤ) :
    Function.Injective (mixedDisplay n D p) := by
  intro a b hab
  funext s
  have hh := congrFun hab ((pairCoordsEquiv ι n).symm (.inr (s,true)))
  simp only [mixedDisplay_slot,ite_true] at hh
  apply Fin.ext
  exact_mod_cast hh

theorem leafDisplay_injective {ι : Type u} (C n : ℕ) (p : ι → ℤ) :
    Function.Injective (leafDisplay C n p) := by
  intro a b hab
  simp only [leafDisplay_mixed] at hab
  exact (branchEquiv C n).injective (mixedDisplay_injective n _ p hab)

noncomputable def mixedBalance {ι : Type u} (n : ℕ) (D : Fin n → ℕ)
    (f : (PairCoords ι n → ℤ) → ℝ) (p : ι → ℤ) : ℝ :=
  ∑ a : ∀ s, Fin (D s+1), f (mixedDisplay n D p a)

theorem allBalance_mixed {ι : Type u} (C n : ℕ)
    (f : (PairCoords ι n → ℤ) → ℝ) (p : ι → ℤ) :
    allBalance C n f p = mixedBalance n (fun _ => C) f p := by
  rw [allBalance_sum_leaf]
  simp only [leafDisplay_mixed,mixedBalance]
  exact Equiv.sum_comp (branchEquiv C n) (fun a => f (mixedDisplay n (fun _ => C) p a))

 

theorem mixedDisplay_succ {ι : Type u} (n : ℕ) (D : Fin (n+1) → ℕ)
    (p : ι → ℤ) (a : ∀ s, Fin (D s+1)) :
    mixedDisplay (n+1) D p a = mixedDisplay n (fun s => D s.succ)
      (pairAssembly p (a 0:ℕ) ((D 0:ℤ)-(a 0:ℕ))) (fun s => a s.succ) := by
  funext i
  obtain ⟨q,rfl⟩ := (pairCoordsEquiv (ι ⊕ Bool) n).symm.surjective i
  rcases q with (i | b) | ⟨s,b⟩ <;>
    simp only [mixedDisplay, Function.comp_apply, pairCoordsEquiv, Equiv.trans_apply,
      Equiv.apply_symm_apply, joinPairHead, Equiv.coe_fn_mk, balanceProfile, pairAssembly,
      Sum.elim_inl, Sum.elim_inr]

theorem mixedBalance_succ {ι : Type u} (n : ℕ) (D : Fin (n+1) → ℕ)
    (f : (PairCoords ι (n+1) → ℤ) → ℝ) (p : ι → ℤ) :
    mixedBalance (n+1) D f p = ∑ j : Fin (D 0+1),
      mixedBalance n (fun s => D s.succ) f (pairAssembly p (j:ℕ) ((D 0:ℤ)-(j:ℕ))) := by
  unfold mixedBalance
  rw [← Equiv.sum_comp (piHeadEquiv (fun s => Fin (D s+1))).symm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro a ha
  congr 1
  rw [mixedDisplay_succ]
  rfl

noncomputable def surplusCaps (C n : ℕ) (t : Fin n) (s : Fin n) : ℕ :=
  if s=t then C+1 else C

 

theorem allSurplus_sum_types {ι : Type u} (C n : ℕ)
    (f : (PairCoords ι n → ℤ) → ℝ) (p : ι → ℤ) :
    allSurplus C n f p = ∑ t : Fin n, mixedBalance n (surplusCaps C n t) f p := by
  induction n generalizing ι with
  | zero => simp [allSurplus]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    change balancedMarginal (allBalance C n f) (C+1) p +
      balancedMarginal (allSurplus C n f) C p = _
    congr 1
    · rw [mixedBalance_succ]
      simp only [surplusCaps,ite_eq_left,Fin.succ_ne_zero,ite_false]
      unfold balancedMarginal
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl; intro j hj
      exact allBalance_mixed C n f _
    · have hs (t : Fin n) : mixedBalance (n+1) (surplusCaps C (n+1) t.succ) f p =
          ∑ j : Fin (C+1), mixedBalance n (surplusCaps C n t) f
            (pairAssembly p (j:ℕ) ((C:ℤ)-(j:ℕ))) := by
        have he : surplusCaps C (n+1) t.succ = Fin.cases C (surplusCaps C n t) := by
          funext s
          refine Fin.cases ?_ (fun v => ?_) s
          · simp [surplusCaps,Ne.symm (Fin.succ_ne_zero t)]
          · simp [surplusCaps]
        rw [he,mixedBalance_succ]
        rfl
      simp_rw [hs]
      rw [Finset.sum_comm]
      unfold balancedMarginal
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl; intro j hj
      exact ih f _

end Contingency

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ}

noncomputable def splitSlots (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) :
    SmallSlot U r c ≃ (Fin k ⊕ Fin (a+1)) :=
  ((smallIndex U r c).symm.trans (finCongr h)).trans finSumFinEquiv.symm

noncomputable def prefixSlot (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (s : Fin k) :=
  (splitSlots U r c k a h).symm (.inl s)

noncomputable def suffixSlot (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (s : Fin (a+1)) :=
  (splitSlots U r c k a h).symm (.inr s)

@[simp] theorem contextCoordinates_prefix (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (s : Fin k) (b : Bool) :
    contextCoordinates U r c k a h (prefixSlot U r c k a h s,b) = .inl (s,b) := by
  change ((Equiv.sumCongr (Equiv.refl _) (smallCoords a).symm)
    ((Equiv.sumProdDistrib (Fin k) (Fin (a+1)) Bool)
      (splitSlots U r c k a h ((splitSlots U r c k a h).symm (.inl s)),b))) = _
  rw [Equiv.apply_symm_apply]; rfl

@[simp] theorem contextCoordinates_suffix (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (s : Fin (a+1)) (b : Bool) :
    contextCoordinates U r c k a h (suffixSlot U r c k a h s,b) =
      .inr ((smallCoords a).symm (s,b)) := by
  change ((Equiv.sumCongr (Equiv.refl _) (smallCoords a).symm)
    ((Equiv.sumProdDistrib (Fin k) (Fin (a+1)) Bool)
      (splitSlots U r c k a h ((splitSlots U r c k a h).symm (.inr s)),b))) = _
  rw [Equiv.apply_symm_apply]; rfl

theorem prefix_before_suffix (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (s : Fin k) (t : Fin (a+1)) :
    Before (prefixSlot U r c k a h s).val (suffixSlot U r c k a h t).val := by
  apply (smallIndex_lt U r c _ _).2
  change ((finCongr h).symm (finSumFinEquiv (.inl s))) <
    ((finCongr h).symm (finSumFinEquiv (.inr t)))
  change s.val < k+t.val
  omega

theorem suffix_before (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (s t : Fin (a+1)) (hst : s<t) :
    Before (suffixSlot U r c k a h s).val (suffixSlot U r c k a h t).val := by
  apply (smallIndex_lt U r c _ _).2
  change k+s.val < k+t.val
  exact Nat.add_lt_add_left hst k

theorem slot_cases (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (w : SmallSlot U r c) :
    (∃ s, w=prefixSlot U r c k a h s) ∨ (∃ s, w=suffixSlot U r c k a h s) := by
  obtain ⟨v,rfl⟩ := (splitSlots U r c k a h).symm.surjective w
  cases v with
  | inl s => exact Or.inl ⟨s,rfl⟩
  | inr s => exact Or.inr ⟨s,rfl⟩

noncomputable def contextState (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) : State m n :=
  coordinatesState U r c (Sum.elim (balanceProfile (fun _ => U) σ) p ∘ contextCoordinates U r c k a h)

@[simp] theorem contextState_prefix (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) (s : Fin k) :
    (contextState U r c k a h σ p).x (prefixSlot U r c k a h s).val = (σ s:ℕ) ∧
    (contextState U r c k a h σ p).q (prefixSlot U r c k a h s).val = (σ s:ℕ) := by
  simp [contextState,balanceProfile]

@[simp] theorem contextState_suffix (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) (s : Fin (a+1)) :
    (contextState U r c k a h σ p).x (suffixSlot U r c k a h s).val = p ((smallCoords a).symm (s,true)) ∧
    (contextState U r c k a h σ p).q (suffixSlot U r c k a h s).val = U-p ((smallCoords a).symm (s,false)) := by
  simp [contextState]

theorem contextState_supported (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) (w : Cell m n) (hw : IsLarge U r c w) :
    (contextState U r c k a h σ p).x w=0 ∧ (contextState U r c k a h σ p).q w=0 :=
  coordinatesState_supported U r c _ w hw

theorem contextState_injective (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1)) :
    Function.Injective (contextState U r c k a h σ) := by
  intro p q hpq
  have he := congrArg (stateCoordinates U r c) hpq
  dsimp [contextState] at he
  simp only [stateCoordinates_coordinatesState] at he
  funext i
  have hh := congrFun he ((contextCoordinates U r c k a h).symm (.inr i))
  simpa using hh

theorem contextKernel_weight (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (k a : ℕ) (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))
    (p : PairCoords Bool a → ℤ) :
    contextKernel 0 U L C r c k a h σ p = (weight U L r c (contextState U r c k a h σ p):ℝ) := by
  classical
  let X := contextState U r c k a h σ p
  by_cases hx : Feasible U r c X
  · rw [weight,ite_eq_left hx]
    have he := smallKernel_zero_count U L C r c hrc X hx hC
    simpa only [X,contextState,stateCoordinates_coordinatesState,contextKernel] using he
  · rw [weight,ite_eq_right hx,Nat.cast_zero]
    exact smallKernel_zero_infeasible U L C r c _ hx

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ}

@[ext] theorem State.ext {X Y : State m n} (hx : X.x=Y.x) (hq : X.q=Y.q) : X=Y := by
  cases X; cases Y; simp_all

variable (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (k a : ℕ)
    (h : Fintype.card (SmallSlot U r c)=k+(a+1)) (σ : Fin k → Fin (U+1))

@[simp] theorem suffixSlot_val_inj (s t : Fin (a+1)) :
    (suffixSlot U r c k a h s).val=(suffixSlot U r c k a h t).val ↔ s=t := by
  constructor
  · intro he
    have he' := Subtype.ext he
    exact Sum.inr.inj ((splitSlots U r c k a h).symm.injective he')
  · rintro rfl; rfl

@[simp] theorem prefix_suffix_ne (s : Fin k) (t : Fin (a+1)) :
    (prefixSlot U r c k a h s).val ≠ (suffixSlot U r c k a h t).val := by
  intro he
  have he' := Subtype.ext he
  have hh := (splitSlots U r c k a h).symm.injective he'
  cases hh

@[simp] theorem mixedDisplay_current (D : Fin a → ℕ) (p : Bool → ℤ)
    (α : ∀ s, Fin (D s+1)) (b : Bool) :
    mixedDisplay a D p α ((smallCoords a).symm (0,b)) = p b := by
  exact mixedDisplay_base a D p α b

@[simp] theorem mixedDisplay_ordinary (D : Fin a → ℕ) (p : Bool → ℤ)
    (α : ∀ s, Fin (D s+1)) (s : Fin a) (b : Bool) :
    mixedDisplay a D p α ((smallCoords a).symm (s.succ,b)) =
      if b then ((α s:ℕ):ℤ) else (D s:ℤ)-(α s:ℕ) := by
  exact mixedDisplay_slot a D p α s b

 

def defectProfile (j : ℕ) : Bool → ℤ := fun b => if b then (j:ℤ) else (U:ℤ)-j-1

@[simp] theorem adjacent_removePair (j : ℕ) :
    removePair (adjacentDisplay U j) true false = defectProfile U j := by
  funext b; cases b <;> simp [removePair,adjacentDisplay,defectProfile]

noncomputable def defectState (j : ℕ) (t : Fin a) (α : ∀ v, Fin (surplusCaps U a t v+1)) : State m n :=
  contextState U r c k a h σ (mixedDisplay a (surplusCaps U a t) (defectProfile U j) α)

@[simp] theorem defectState_current (j : ℕ) (t : Fin a) (α : ∀ v, Fin (surplusCaps U a t v+1)) :
    (defectState U r c k a h σ j t α).x (suffixSlot U r c k a h 0).val = j ∧
    (defectState U r c k a h σ j t α).q (suffixSlot U r c k a h 0).val = (j:ℤ)+1 := by
  have hh := contextState_suffix U r c k a h σ (mixedDisplay a (surplusCaps U a t) (defectProfile U j) α) 0
  refine ⟨hh.1.trans ?_,hh.2.trans ?_⟩
  · simp only [mixedDisplay_current,defectProfile,ite_true]
  · simp only [mixedDisplay_current,defectProfile,Bool.false_eq_true,ite_false]
    ring

@[simp] theorem defectState_ordinary (j : ℕ) (t v : Fin a) (α : ∀ v, Fin (surplusCaps U a t v+1)) :
    (defectState U r c k a h σ j t α).x (suffixSlot U r c k a h v.succ).val = (α v:ℕ) ∧
    (defectState U r c k a h σ j t α).q (suffixSlot U r c k a h v.succ).val =
      (α v:ℕ)-(if v=t then (1:ℤ) else 0) := by
  have hh := contextState_suffix U r c k a h σ (mixedDisplay a (surplusCaps U a t) (defectProfile U j) α) v.succ
  simp only [mixedDisplay_ordinary,Bool.false_eq_true,ite_true,ite_false] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  unfold surplusCaps
  split_ifs <;> push_cast <;> ring

theorem defectState_defect (j : ℕ) (t : Fin a) (α : ∀ v, Fin (surplusCaps U a t v+1)) :
    DefectAt U r c (suffixSlot U r c k a h 0).val (suffixSlot U r c k a h t.succ).val
      (defectState U r c k a h σ j t α) := by
  refine ⟨(suffixSlot U r c k a h 0).property,(suffixSlot U r c k a h t.succ).property,?_,?_⟩
  · rw [ne_eq,suffixSlot_val_inj]
    exact Ne.symm (Fin.succ_ne_zero t)
  · funext w
    by_cases hw : IsSmall U r c w
    · rcases slot_cases U r c k a h ⟨w,hw⟩ with ⟨v,hv⟩ | ⟨v,hv⟩
      · have he : w=(prefixSlot U r c k a h v).val := congrArg Subtype.val hv
        subst w
        have hp := contextState_prefix U r c k a h σ
          (mixedDisplay a (surplusCaps U a t) (defectProfile U j) α) v
        dsimp [defectState] at *
        rw [hp.1,hp.2]
        simp [unit]
      · have he : w=(suffixSlot U r c k a h v).val := congrArg Subtype.val hv
        subst w
        refine Fin.cases ?_ (fun v => ?_) v
        · rw [(defectState_current U r c k a h σ j t α).1,
            (defectState_current U r c k a h σ j t α).2]
          simp [unit,Ne.symm (Fin.succ_ne_zero t)]
        · rw [(defectState_ordinary U r c k a h σ j t v α).1,
            (defectState_ordinary U r c k a h σ j t v α).2]
          simp [unit]
    · have hl : IsLarge U r c w := Classical.not_not.mp hw
      have hh := contextState_supported U r c k a h σ
        (mixedDisplay a (surplusCaps U a t) (defectProfile U j) α) w hl
      have hs : w ≠ (suffixSlot U r c k a h 0).val := by
        rintro rfl; exact (suffixSlot U r c k a h 0).property hl
      have ht : w ≠ (suffixSlot U r c k a h t.succ).val := by
        rintro rfl; exact (suffixSlot U r c k a h t.succ).property hl
      change _ = _-unit _ _+unit _ _
      simp only [defectState] at *
      rw [hh.1,hh.2]; simp [unit,hs,ht]

noncomputable def stateSuffix (X : State m n) (hf : Feasible U r c X) : Fin a → Fin (U+1) :=
  fun v => ⟨(X.x (suffixSlot U r c k a h v.succ).val).toNat,by
    have hh := hf.1 (suffixSlot U r c k a h v.succ).val; omega⟩

 

theorem contextState_reconstruct (X : State m n) (hf : Feasible U r c X)
    (htr : Transversal X) (hp : ∀ v, X.x (prefixSlot U r c k a h v).val=(σ v:ℕ))
    (j : ℕ) (hj : X.x (suffixSlot U r c k a h 0).val=(j:ℤ)) :
    contextState U r c k a h σ (mixedDisplay a (fun _ => U) (childProfile U j)
      (stateSuffix U r c k a h X hf)) = X := by
  apply State.ext
  · funext w
    by_cases hw : IsSmall U r c w
    · rcases slot_cases U r c k a h ⟨w,hw⟩ with ⟨v,hv⟩ | ⟨v,hv⟩
      · have he : w=(prefixSlot U r c k a h v).val := congrArg Subtype.val hv
        subst w
        rw [(contextState_prefix U r c k a h σ _ v).1,hp]
      · have he : w=(suffixSlot U r c k a h v).val := congrArg Subtype.val hv
        subst w
        rw [(contextState_suffix U r c k a h σ _ v).1]
        refine Fin.cases ?_ (fun t => ?_) v
        · simpa [childProfile] using hj.symm
        · simp only [mixedDisplay_ordinary,ite_true,stateSuffix]
          exact Int.toNat_of_nonneg (hf.1 _).1
    · exact (contextState_supported U r c k a h σ _ w (Classical.not_not.mp hw)).1.trans
        ((hf.2.1 w (Classical.not_not.mp hw)).1.symm)
  · funext w
    by_cases hw : IsSmall U r c w
    · rcases slot_cases U r c k a h ⟨w,hw⟩ with ⟨v,hv⟩ | ⟨v,hv⟩
      · have he : w=(prefixSlot U r c k a h v).val := congrArg Subtype.val hv
        subst w
        rw [(contextState_prefix U r c k a h σ _ v).2,htr,hp]
      · have he : w=(suffixSlot U r c k a h v).val := congrArg Subtype.val hv
        subst w
        rw [(contextState_suffix U r c k a h σ _ v).2,htr]
        refine Fin.cases ?_ (fun t => ?_) v
        · simp [childProfile,hj]
        · simp only [mixedDisplay_ordinary,Bool.false_eq_true,ite_false,stateSuffix]
          rw [Int.toNat_of_nonneg (hf.1 _).1]; ring
    · exact (contextState_supported U r c k a h σ _ w (Classical.not_not.mp hw)).2.trans
        ((hf.2.1 w (Classical.not_not.mp hw)).2.symm)

end Contingency.PaddedGraph

end

end OAI
