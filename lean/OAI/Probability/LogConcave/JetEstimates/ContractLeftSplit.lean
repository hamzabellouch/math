import Mathlib
import OAI.Probability.LogConcave.JetEstimates.WireStep
import OAI.Probability.LogConcave.JetEstimates.ProperSplit
import OAI.Probability.LogConcave.JetEstimates.Reindex

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

universe u
variable {Ai Ao Bi Bo : Type u} [Fintype Ai] [Fintype Ao] [Fintype Bi] [Fintype Bo] {d : ℕ}

def contractLeftSplit : ((Ai ⊕ Ao) ⊕ Unit) ≃ (Ai ⊕ Unit) ⊕ Ao where
  toFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  invFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  left_inv s := by rcases s with (s|s)|s <;> rfl
  right_inv s := by rcases s with (s|s)|s <;> rfl

def contractRightSplit : ((Bi ⊕ Bo) ⊕ Unit) ≃ Bi ⊕ (Unit ⊕ Bo) where
  toFun := Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)) (Sum.inr ∘ Sum.inl)
  invFun := Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr))
  left_inv s := by rcases s with (s|s)|s <;> rfl
  right_inv s := by rcases s with s|(s|s) <;> rfl

def appendCoordinate (I : Type u) : (I → Fin d) × Fin d ≃ (I ⊕ Unit → Fin d) :=
  ((Equiv.refl _).prodCongr (Equiv.funUnique Unit (Fin d)).symm).trans
    (Equiv.sumArrowEquivProdArrow I Unit (Fin d)).symm

def prependCoordinate (O : Type u) : Fin d × (O → Fin d) ≃ (Unit ⊕ O → Fin d) :=
  (((Equiv.funUnique Unit (Fin d)).symm).prodCongr (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow Unit O (Fin d)).symm

lemma allSplit_contract_oriented [Nonempty Ao] [Nonempty Bi]
    {A : ((Ai ⊕ Ao) ⊕ Unit → Fin d) → ℝ}
    {B : ((Bi ⊕ Bo) ⊕ Unit → Fin d) → ℝ} {M N : ℝ}
    (hA : AllSplitBound A M) (hB : AllSplitBound B N) :
    Bound (fun (o : (Ao → Fin d) × (Bo → Fin d)) (i : (Ai → Fin d) × (Bi → Fin d)) =>
      ∑z : Fin d,A (Sum.elim (Sum.elim i.1 o.1) (fun _ => z))*
        B (Sum.elim (Sum.elim i.2 o.2) (fun _ => z))) ((M*N)^2) := by
  have ha := (hA (Ai ⊕ Unit) Ao contractLeftSplit).reindex
    (Equiv.refl (Ao → Fin d)) (appendCoordinate Ai)
  have hb := (hB Bi (Unit ⊕ Bo) contractRightSplit).reindex
    (prependCoordinate Bo) (Equiv.refl (Bi → Fin d))
  have hab := ha.contract hb (sq_nonneg M)
  convert hab using 1
  · funext o i
    apply Finset.sum_congr rfl
    intro z hz
    congr 1
    · congr 1
      funext s
      rcases s with (s|s)|s <;> rfl
    · congr 1
      funext s
      rcases s with (s|s)|s <;> rfl
  · ring

lemma allSplit_contract_reverse [Nonempty Ai] [Nonempty Bo]
    {A : ((Ai ⊕ Ao) ⊕ Unit → Fin d) → ℝ}
    {B : ((Bi ⊕ Bo) ⊕ Unit → Fin d) → ℝ} {M N : ℝ}
    (hA : AllSplitBound A M) (hB : AllSplitBound B N) :
    Bound (fun (o : (Ao → Fin d) × (Bo → Fin d)) (i : (Ai → Fin d) × (Bi → Fin d)) =>
      ∑z : Fin d,A (Sum.elim (Sum.elim i.1 o.1) (fun _ => z))*
        B (Sum.elim (Sum.elim i.2 o.2) (fun _ => z))) ((M*N)^2) := by
  have h := (allSplit_contract_oriented hB hA).reindex
    (Equiv.prodComm (Ao → Fin d) (Bo → Fin d))
    (Equiv.prodComm (Ai → Fin d) (Bi → Fin d))
  simpa only [Equiv.prodComm_apply,Prod.swap_prod_mk,Prod.fst_swap,Prod.snd_swap,mul_comm] using h

lemma allSplit_contract_either
    {A : ((Ai ⊕ Ao) ⊕ Unit → Fin d) → ℝ}
    {B : ((Bi ⊕ Bo) ⊕ Unit → Fin d) → ℝ} {M N : ℝ}
    (hA : AllSplitBound A M) (hB : AllSplitBound B N)
    (ho : (Nonempty Ao ∧ Nonempty Bi) ∨ (Nonempty Ai ∧ Nonempty Bo)) :
    Bound (fun (o : (Ao → Fin d) × (Bo → Fin d)) (i : (Ai → Fin d) × (Bi → Fin d)) =>
      ∑z : Fin d,A (Sum.elim (Sum.elim i.1 o.1) (fun _ => z))*
        B (Sum.elim (Sum.elim i.2 o.2) (fun _ => z))) ((M*N)^2) := by
  rcases ho with ⟨_,_⟩|⟨_,_⟩
  · exact allSplit_contract_oriented hA hB
  · exact allSplit_contract_reverse hA hB

def singleContract {S T : Type u}
    (A : (S ⊕ Unit → Fin d) → ℝ) (B : (T ⊕ Unit → Fin d) → ℝ) :
    (S ⊕ T → Fin d) → ℝ := fun c =>
  ∑z : Fin d,A (Sum.elim (fun s => c (Sum.inl s)) (fun _ => z))*
    B (Sum.elim (fun t => c (Sum.inr t)) (fun _ => z))

section partition
variable {S T : Type u} [Fintype S] [Fintype T]
local instance leftInDec (p : S ⊕ T → Bool) : DecidableEq {s : S // p (Sum.inl s)=true} := Classical.decEq _
local instance leftOutDec (p : S ⊕ T → Bool) : DecidableEq {s : S // ¬p (Sum.inl s)=true} := Classical.decEq _
local instance rightInDec (p : S ⊕ T → Bool) : DecidableEq {t : T // p (Sum.inr t)=true} := Classical.decEq _
local instance rightOutDec (p : S ⊕ T → Bool) : DecidableEq {t : T // ¬p (Sum.inr t)=true} := Classical.decEq _

def partEquiv (p : S → Bool) : S ≃ {s // p s=true} ⊕ {s // ¬p s=true} :=
  (Equiv.sumCompl (fun s => p s=true)).symm

def outputCoords (p : ProperSplit (S ⊕ T)) :
    (OutSlots p → Fin d) ≃
      ({s : S // ¬p.val (Sum.inl s)=true} → Fin d) ×
      ({t : T // ¬p.val (Sum.inr t)=true} → Fin d) :=
  (Equiv.arrowCongr Equiv.subtypeSum (Equiv.refl (Fin d))).trans
    (Equiv.sumArrowEquivProdArrow _ _ (Fin d))

def inputCoords (p : ProperSplit (S ⊕ T)) :
    (InSlots p → Fin d) ≃
      ({s : S // p.val (Sum.inl s)=true} → Fin d) ×
      ({t : T // p.val (Sum.inr t)=true} → Fin d) :=
  (Equiv.arrowCongr Equiv.subtypeSum (Equiv.refl (Fin d))).trans
    (Equiv.sumArrowEquivProdArrow _ _ (Fin d))

omit [Fintype S] [Fintype T] in
lemma splitOrientation [Nonempty S] [Nonempty T] (p : ProperSplit (S ⊕ T)) :
    (Nonempty {s : S // ¬p.val (Sum.inl s)=true} ∧
      Nonempty {t : T // p.val (Sum.inr t)=true}) ∨
    (Nonempty {s : S // p.val (Sum.inl s)=true} ∧
      Nonempty {t : T // ¬p.val (Sum.inr t)=true}) := by
  by_cases hs : Nonempty {s : S // ¬p.val (Sum.inl s)=true}
  · by_cases ht : Nonempty {t : T // p.val (Sum.inr t)=true}
    · exact Or.inl ⟨hs,ht⟩
    · right
      constructor
      · obtain ⟨s,h⟩ := p.property.1
        cases s with
        | inl s => exact ⟨s,h⟩
        | inr t => exact (ht ⟨t,h⟩).elim
      · obtain ⟨t⟩ := ‹Nonempty T›
        exact ⟨t,fun h => ht ⟨t,h⟩⟩
  · right
    constructor
    · obtain ⟨s⟩ := ‹Nonempty S›
      exact ⟨s,by by_contra h; exact hs ⟨s,h⟩⟩
    · obtain ⟨s,h⟩ := p.property.2
      cases s with
      | inl s => exact (hs ⟨s,by simp [h]⟩).elim
      | inr t => exact ⟨t,by simp [h]⟩

omit [Fintype S] [Fintype T] in
lemma part_colors_left (p : ProperSplit (S ⊕ T))
    (o : OutSlots p → Fin d) (i : InSlots p → Fin d) (s : S) :
    Sum.elim (inputCoords p i).1 (outputCoords p o).1
        (partEquiv (fun s : S => p.val (Sum.inl s)) s) =
      Sum.elim i o (splitEquiv p (Sum.inl s)) := by
  change Sum.elim (fun x : {s : S // p.val (Sum.inl s)=true} => i ⟨Sum.inl x.val,x.property⟩)
      (fun x : {s : S // ¬p.val (Sum.inl s)=true} => o ⟨Sum.inl x.val,x.property⟩)
      (if h : p.val (Sum.inl s)=true then Sum.inl ⟨s,h⟩ else Sum.inr ⟨s,h⟩) =
    Sum.elim i o (if h : p.val (Sum.inl s)=true
      then Sum.inl ⟨Sum.inl s,h⟩ else Sum.inr ⟨Sum.inl s,h⟩)
  split <;> rfl

omit [Fintype S] [Fintype T] in
lemma part_colors_right (p : ProperSplit (S ⊕ T))
    (o : OutSlots p → Fin d) (i : InSlots p → Fin d) (t : T) :
    Sum.elim (inputCoords p i).2 (outputCoords p o).2
        (partEquiv (fun t : T => p.val (Sum.inr t)) t) =
      Sum.elim i o (splitEquiv p (Sum.inr t)) := by
  change Sum.elim (fun x : {t : T // p.val (Sum.inr t)=true} => i ⟨Sum.inr x.val,x.property⟩)
      (fun x : {t : T // ¬p.val (Sum.inr t)=true} => o ⟨Sum.inr x.val,x.property⟩)
      (if h : p.val (Sum.inr t)=true then Sum.inl ⟨t,h⟩ else Sum.inr ⟨t,h⟩) =
    Sum.elim i o (if h : p.val (Sum.inr t)=true
      then Sum.inl ⟨Sum.inr t,h⟩ else Sum.inr ⟨Sum.inr t,h⟩)
  split <;> rfl

lemma singleContract_split_bound [Nonempty S] [Nonempty T]
    {A : (S ⊕ Unit → Fin d) → ℝ} {B : (T ⊕ Unit → Fin d) → ℝ}
    {M N : ℝ} (hA : AllSplitBound A M) (hB : AllSplitBound B N)
    (p : ProperSplit (S ⊕ T)) :
    Bound (splitMatrix (singleContract A B) p) ((M*N)^2) := by
  let eS := partEquiv (fun s : S => p.val (Sum.inl s))
  let eT := partEquiv (fun t : T => p.val (Sum.inr t))
  have ha := hA.reindex (eS.sumCongr (Equiv.refl Unit))
  have hb := hB.reindex (eT.sumCongr (Equiv.refl Unit))
  have h : Bound (fun (o : ({s : S // ¬p.val (Sum.inl s)=true} → Fin d) ×
            ({t : T // ¬p.val (Sum.inr t)=true} → Fin d))
        (i : ({s : S // p.val (Sum.inl s)=true} → Fin d) ×
            ({t : T // p.val (Sum.inr t)=true} → Fin d)) =>
      ∑z : Fin d,A ((Sum.elim (Sum.elim i.1 o.1) (fun _ => z)) ∘ eS.sumCongr (Equiv.refl Unit))*
        B ((Sum.elim (Sum.elim i.2 o.2) (fun _ => z)) ∘ eT.sumCongr (Equiv.refl Unit)))
        ((M*N)^2) := by
    exact allSplit_contract_either
      (Ai:={s : S // p.val (Sum.inl s)=true})
      (Ao:={s : S // ¬p.val (Sum.inl s)=true})
      (Bi:={t : T // p.val (Sum.inr t)=true})
      (Bo:={t : T // ¬p.val (Sum.inr t)=true})
      (A:=fun f => A (f ∘ eS.sumCongr (Equiv.refl Unit)))
      (B:=fun f => B (f ∘ eT.sumCongr (Equiv.refl Unit))) ha hb (splitOrientation p)
  have hh := h.reindex (outputCoords p) (inputCoords p)
  suffices he : splitMatrix (singleContract A B) p =
      (fun o i => ∑z : Fin d,
        A ((Sum.elim (Sum.elim (inputCoords p i).1 (outputCoords p o).1) (fun _ => z)) ∘
          eS.sumCongr (Equiv.refl Unit))*
        B ((Sum.elim (Sum.elim (inputCoords p i).2 (outputCoords p o).2) (fun _ => z)) ∘
          eT.sumCongr (Equiv.refl Unit))) by
    rw [he]
    exact hh
  ext o i
  unfold splitMatrix singleContract
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  · congr 1
    funext s
    rcases s with s|s
    · exact (part_colors_left p o i s).symm
    · rfl
  · congr 1
    funext t
    rcases t with t|t
    · exact (part_colors_right p o i t).symm
    · rfl

end partition

end LogConcaveSampling.TensorEnergy

namespace LogConcaveSampling.TensorEnergy
open scoped Classical

universe u

lemma allSplitBound_of_proper {S : Type u} [Fintype S] {d : ℕ}
    {T : (S → Fin d) → ℝ} {M : ℝ}
    (h : ∀p : ProperSplit S,Bound (splitMatrix T p) (M^2)) : AllSplitBound T M := by
  intro I O _ _ _ _ _ _ e
  have h' := (h (properOfEquiv e)).reindex
    (Equiv.arrowCongr (rightOfEquiv e) (Equiv.refl (Fin d)))
    (Equiv.arrowCongr (leftOfEquiv e) (Equiv.refl (Fin d)))
  convert h' using 1
  ext o i
  unfold splitMatrix
  congr 1
  funext s
  rw [splitEquiv_ofEquiv]
  cases e s <;> simp

lemma AllSplitBound.singleContract {S T : Type u} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] {d : ℕ}
    {A : (S ⊕ Unit → Fin d) → ℝ} {B : (T ⊕ Unit → Fin d) → ℝ}
    {M N : ℝ} (hA : AllSplitBound A M) (hB : AllSplitBound B N) :
    AllSplitBound (singleContract A B) (M*N) :=
  allSplitBound_of_proper (singleContract_split_bound hA hB)

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators Matrix.Norms.L2Operator

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

lemma AllSplitBound.mono {T : (S → Fin d) → ℝ} {M N : ℝ}
    (h : AllSplitBound T M) (hM : 0≤M) (hMN : M≤N) : AllSplitBound T N := by
  intro I O _ _ _ _ _ _ e
  exact (h I O e).mono (pow_le_pow_left₀ hM hMN 2)

lemma AllSplitBound.const_mul {T : (S → Fin d) → ℝ} {M : ℝ}
    (h : AllSplitBound T M) (c : ℝ) : AllSplitBound (fun a => c*T a) (c*M) := by
  intro I O _ _ _ _ _ _ e
  convert (h I O e).smul c using 1
  ring

lemma Bound.finite_sum_norm {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]
    {A : J → Matrix O I ℝ} {M : J → ℝ}
    (hM : ∀j,0≤M j) (h : ∀j,Bound (A j) ((M j)^2)) :
    Bound (fun o i => ∑j,A j o i) ((∑j,M j)^2) := by
  have he : (fun o i => ∑j,A j o i)=∑j,A j := by
    ext o i
    exact (Matrix.sum_apply o i Finset.univ A).symm
  rw [he]
  apply (bound_iff_norm_le (Finset.sum_nonneg (fun j _ => hM j))).mpr
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => (h j).norm_le (hM j)))

lemma AllSplitBound.finite_sum {J : Type*} [Fintype J]
    {T : J → (S → Fin d) → ℝ} {M : J → ℝ}
    (hM : ∀j,0≤M j) (h : ∀j,AllSplitBound (T j) (M j)) :
    AllSplitBound (fun a => ∑j,T j a) (∑j,M j) := by
  intro I O _ _ _ _ _ _ e
  exact Bound.finite_sum_norm hM (fun j => h j I O e)

lemma nonempty_properSplit (hS : 2≤Fintype.card S) : Nonempty (ProperSplit S) := by
  let : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨s,t,hst⟩ := exists_pair_ne S
  exact ⟨⟨fun x => decide (x=s),⟨s,by simp⟩,⟨t,by simp [Ne.symm hst]⟩⟩⟩

lemma AllSplitBound.entry_le {T : (S → Fin d) → ℝ} {M : ℝ}
    (h : AllSplitBound T M) (hM : 0≤M) (hS : 2≤Fintype.card S) (c : S → Fin d) :
    |T c|≤M := by
  obtain ⟨p⟩ := nonempty_properSplit hS
  have hh := (h _ _ (splitEquiv p)).entry_sq
    (fun o => c ((splitEquiv p).symm (Sum.inr o)))
    (fun i => c ((splitEquiv p).symm (Sum.inl i)))
  have he : (fun s => Sum.elim (fun i => c ((splitEquiv p).symm (Sum.inl i)))
      (fun o => c ((splitEquiv p).symm (Sum.inr o))) (splitEquiv p s))=c := by
    funext s
    have hs := (splitEquiv p).symm_apply_apply s
    cases hsp : splitEquiv p s <;> simp only [Sum.elim_inl,Sum.elim_inr] <;>
      simp only [hsp] at hs <;> rw [hs]
  rw [he] at hh
  exact (sq_le_sq₀ (abs_nonneg _) hM).mp (by simpa only [sq_abs] using hh)

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
