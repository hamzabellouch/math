import OAI.Analysis.FourierLLogL.Compress.Variational
/-! # Indexed blocks of letters -/

open Function Filter Set
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real

abbrev Letters (n : ℕ) (α : Type) := Fin n → α
abbrev WordSample (n : ℕ) (α G : Type) := Sample (Fin n) α G

variable {ι τ κ n m k : ℕ} {α Ω G : Type}

def offset (j l : ℕ) (h : j+l ≤ n) (i : Fin l) : Fin n := ⟨j+i, by have := i.isLt; omega⟩

def readBlock (X : Ω → Letters n α) (j l : ℕ) (h : j+l ≤ n) :=
  keep X (offset j l h)
def prefixB (X : Ω → Letters n α) (l : ℕ) (h : l ≤ n) := readBlock X 0 l (by omega)
def readLetter (X : Ω → Letters n α) (j : ℕ) (h : j<n) := fun x => X x ⟨j,h⟩

lemma offset_injective (j l : ℕ) (h : j+l ≤ n) : Injective (offset j l h) := by
  intro a b hab
  have H := congrArg Fin.val hab
  simp only [offset,Nat.add_left_cancel_iff] at H
  exact Fin.ext H

lemma prefix_partition (X : Ω → Letters n α) (l k : ℕ) (h : l+k ≤ n) (x y : Ω) :
    prefixB X (l+k) h x = prefixB X (l+k) h y ↔
      prefixB X l (by omega) x = prefixB X l (by omega) y ∧ readBlock X l k h x = readBlock X l k h y := by
  simp only [funext_iff]
  constructor
  · intro H; constructor
    · intro i
      exact H (i.castAdd k)
    · intro ⟨i,hi⟩
      have h1 := H (⟨l+i,by omega⟩:Fin (l+k))
      simpa only [prefixB,readBlock,keep,offset,zero_add] using h1
  · rintro ⟨H,G⟩ ⟨i,hi⟩
    by_cases hp : i < l
    · exact H ⟨i,hp⟩
    · have h1 := G (⟨i-l,by omega⟩:Fin k)
      simpa only [prefixB,readBlock,keep,offset,zero_add, Nat.add_sub_of_le (le_of_not_gt hp)]
        using h1

lemma prefix_last_partition (X : Ω → Letters n α) (l : ℕ) (h : l<n) (x y : Ω) :
    prefixB X (l+1) h x = prefixB X (l+1) h y ↔
      readLetter X l h x = readLetter X l h y ∧
      prefixB X l (by omega) x = prefixB X l (by omega) y := by
  rw [prefix_partition X l 1 h]
  have HH : readBlock X l 1 h x = readBlock X l 1 h y ↔ readLetter X l h x = readLetter X l h y :=
    ⟨fun e => congrFun e (0:Fin 1),fun e => by funext i; rw [Subsingleton.elim i 0]; exact e⟩
  rw [HH,and_comm]

lemma prefix_zero (X : Ω → Letters n α) : prefixB X 0 (by omega) = fun _ => Fin.elim0 :=
  funext fun _ => Subsingleton.elim _ _

lemma prefix_all (X : Ω → Letters n α) : prefixB X n le_rfl = X := by
  funext a ⟨i,hi⟩
  simp only [prefixB,readBlock,keep,offset,zero_add]

lemma block_cut (X : Ω → Letters n α) (j m l : ℕ) (h : j+m ≤ n) (hl : l ≤ m) :
    readBlock X j l (by omega) = prefixB (readBlock X j m h) l hl := by
  funext a ⟨i,hi⟩; simp only [prefixB,readBlock,keep,offset,zero_add]

lemma block_in_prefix (X : Ω → Letters n α) (j k l : ℕ) (hk : j+k ≤ l) (hl : l ≤ n) :
    readBlock X j k (hk.trans hl) = readBlock (prefixB X l hl) j k hk := by
  funext a ⟨i,hi⟩; simp only [prefixB,readBlock,keep,offset,zero_add]


def splitIx {n : ℕ} (l m : ℕ) (h : l+m=n) : (Fin m ⊕ Fin l) ≃ Fin n :=
  ((Equiv.sumComm _ _).trans finSumFinEquiv).trans (finCongr h)

lemma splitIx_left (l m : ℕ) (h : l+m=n) (i : Fin m) :
    splitIx l m h (.inl i) = offset l m h.le i := by
  apply Fin.ext
  simp only [splitIx,Equiv.trans_apply,finCongr_apply_coe]
  rfl

lemma splitIx_right (l m : ℕ) (h : l+m=n) (i : Fin l) :
    splitIx l m h (.inr i) = offset 0 l (by omega : 0+l≤n) i := by
  apply Fin.ext
  simp only [splitIx,Equiv.trans_apply,finCongr_apply_coe,offset,zero_add]
  rfl


section reindex
variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

omit [Fintype I] [Fintype J] [DecidableEq J] [DecidableEq I] in
lemma lift_perm (g : J → I) (hg : Injective g) (e : Equiv.Perm J) :
    ∃ f : Equiv.Perm I, (∀ i, f (g i) = g (e i)) ∧ ∀ x, x ∉ range g → f x = x := by
  classical
  let T := (Equiv.sumCongr (Equiv.ofInjective g hg) (Equiv.refl {x : I // x ∉ range g}))
    |>.trans (Equiv.sumCompl (fun x => x ∈ range g))
  let E := Equiv.sumCongr e (Equiv.refl {x : I // x ∉ range g})
  have H (x) : ((T.symm.trans E).trans T) (T x) = T (E x) := by simp
  refine ⟨(T.symm.trans E).trans T,fun i => H (.inl i),fun x hx => ?_⟩
  exact H (.inr ⟨x,hx⟩)

variable [Fintype α] [Fintype G]

def subSample (g : J → I) (p : Sample I α G) : Sample J α G :=
  ((fun j => p.1 (g j)), p.2)

lemma exch_subSample {P : Law (Sample I α G)} (hx : exch P)
    (g : J → I) (hg : Injective g) : exch (P.send (subSample g)) := by
  intro e
  obtain ⟨f,hf,hf'⟩ := lift_perm g hg e
  rw [send_send]
  have HH := congrArg (fun R : Law (Sample I α G) => R.send (subSample g)) (hx f)
  rw [send_send] at HH
  simpa [subSample,appPerm,hf] using HH

lemma exch_subSample_cond {P : Law (Sample I α G)} (hx : exch P)
    (g : J → I) (hg : Injective g) (u : K → I) (hu : ∀ i, u i ∉ range g)
    (w : K → α) :
    let W := keep (fun p : Sample I α G => p.1) u
    exch ((P.after W w).send (subSample g)) := by
  intro W e
  obtain ⟨f,hf,hf'⟩ := lift_perm g hg e
  have HH := congrArg (fun R : Law (Sample I α G) => R.send fun x => (subSample g x,W x)) (hx f)
  rw [send_send] at HH
  have h1 (x : Sample I α G) : subSample g (appPerm f x) = appPerm e (subSample g x) := by
    simp only [appPerm,subSample,hf]
  have h2 (x : Sample I α G) : W (appPerm f x) = W x := by
    funext i
    simp only [W,keep,appPerm,hf' _ (hu i)]
  simp_rw [h1,h2] at HH
  rw [send_send]
  exact after_send_eq_of_send_pair_eq (X:=fun x => appPerm e (subSample g x)) (W:=W)
    (Y:=subSample g) (V:=W) HH w

end reindex

section billsplit
variable [Fintype α] [Fintype Ω] [Fintype G] [AddCommGroup G]
lemma prefix_bill (tag : α → G) (c : G → ℝ) (q : Law α)
    (P : Law Ω) (X : Ω → Letters n α) (U : Ω → G) (h : covered P X q)
    (j m : ℕ) (hh : j+m ≤ n) :
    let W := prefixB X j (by omega)
    (P.send W).Ex (fun w => bill tag c q (P.after W w) (readBlock X j m hh) U) ≤
      bill tag c q P X U := by
  intro W
  let l := n-j
  have he : j+l=n := by dsimp [l]; omega
  have hhh := bill_split tag c q P X U h (splitIx j l he)
  let V := readBlock X j l he.le
  have H1 :
      (P.send W).Ex (fun w => bill tag c q (P.after W w) V U) ≤ bill tag c q P X U := by
    simpa only [W,V,prefixB,readBlock,splitIx_left,splitIx_right] using hhh
  apply le_trans ?_ H1
  refine Ex_mono_mem _ (fun w hw => ?_)
  have hB : readBlock X j m hh = prefixB V m (by omega) := block_cut X j l m he.le (by omega)
  rw [hB]
  exact bill_subfamily tag c q _ V U
    (covered_subfamily (covered_after h _ _ hw) _) _ (offset_injective 0 m _)
end billsplit

end FourierLLogL.Compress

end OAI
