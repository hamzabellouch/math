import OAI.Analysis.MarkovType.OrderedNorm
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

def SupportedBelow (x : C00) (B : ℕ) : Prop := ∀ i, B ≤ i → x i = 0

theorem ofArray_restrict (x : C00) (B : ℕ) (h : SupportedBelow x B) :
    ofArray (fun i : Fin B => x i.val) = x := by
  classical
  ext i
  by_cases hi : i < B
  · exact ofArray_apply _ ⟨i, hi⟩
  · rw [h i (Nat.le_of_not_gt hi)]
    simp only [ofArray, place, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j _
    apply Finsupp.single_eq_of_ne
    omega

theorem mapDomain_ofArray {B : ℕ} (f : ℕ → ℕ) (a : Fin B → ℝ) :
    Finsupp.mapDomain f (ofArray a) = place (fun i => f i.val) a := by
  classical
  simp only [ofArray, place, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]

def skipAfter (i j : ℕ) : ℕ := if j ≤ i then j else j + 1

theorem skipAfter_monotone (i : ℕ) : Monotone (skipAfter i) := by
  intro a b hab
  unfold skipAfter
  split_ifs <;> omega

theorem factor_mergeIndex (f : ℕ → ℕ) (i : ℕ) (hi : f i = f (i + 1)) :
    f = (f ∘ skipAfter i) ∘ mergeIndex i := by
  funext j
  simp only [Function.comp_apply, mergeIndex, skipAfter]
  by_cases hji : j ≤ i
  · simp [hji]
  · rw [ite_eq_right hji]
    by_cases hnext : j = i + 1
    · subst j
      simpa using hi.symm
    · have hskip : ¬j - 1 ≤ i := by omega
      rw [ite_eq_right hskip]
      congr 1
      omega

theorem mergeAt_supportedBelow {x : C00} {B i : ℕ}
    (hx : SupportedBelow x (B + 1)) (hi : i < B) :
    SupportedBelow (mergeAt i x) B := by
  classical
  intro j hj
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  have himage := Finsupp.mapDomain_support hmem
  obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp himage
  have hkB : k < B + 1 := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hk) (hx k (Nat.le_of_not_gt h))
  unfold mergeIndex at hkj
  split_ifs at hkj <;> omega

end C00

namespace OrderedNorm

theorem mapDomain_le_of_supportedBelow (N : OrderedNorm) :
    ∀ (B : ℕ) (x : C00), C00.SupportedBelow x B →
      ∀ (f : ℕ → ℕ), Monotone f → N (Finsupp.mapDomain f x) ≤ N x := by
  classical
  intro B
  induction B with
  | zero =>
      intro x hx f hf
      have hx0 : x = 0 := by
        ext i
        exact hx i (Nat.zero_le i)
      simp [hx0]
  | succ B ih =>
      intro x hx f hf
      by_cases hs : StrictMono (fun i : Fin (B + 1) => f i.val)
      · have hrepr := C00.ofArray_restrict x (B + 1) hx
        calc
          N (Finsupp.mapDomain f x) =
              N (Finsupp.mapDomain f
                (C00.ofArray (fun i : Fin (B + 1) => x i.val))) :=
                  congrArg (fun y => N (Finsupp.mapDomain f y)) hrepr.symm
          _ =
              N (C00.place (fun i : Fin (B + 1) => f i.val) (fun i => x i.val)) := by
                rw [C00.mapDomain_ofArray]
          _ = N (C00.ofArray (fun i : Fin (B + 1) => x i.val)) := N.spreading _ hs _
          _ = N x := congrArg N hrepr
          _ ≤ N x := le_rfl
      · have hbad : ∃ i : Fin B, ¬f i.val < f (i.val + 1) := by
          by_contra h
          push Not at h
          apply hs
          exact Fin.strictMono_iff_lt_succ.mpr h
        obtain ⟨i, hi⟩ := hbad
        have heq : f i.val = f (i.val + 1) :=
          le_antisymm (hf (Nat.le_succ _)) (Nat.le_of_not_gt hi)
        have hfactor : Finsupp.mapDomain f x =
            Finsupp.mapDomain (f ∘ C00.skipAfter i.val) (C00.mergeAt i.val x) := by
          calc
            Finsupp.mapDomain f x =
                Finsupp.mapDomain ((f ∘ C00.skipAfter i.val) ∘ C00.mergeIndex i.val) x :=
                  congrArg (fun g => Finsupp.mapDomain g x)
                    (C00.factor_mergeIndex f i.val heq)
            _ = Finsupp.mapDomain (f ∘ C00.skipAfter i.val)
                (C00.mergeAt i.val x) := Finsupp.mapDomain_comp
        rw [hfactor]
        exact (ih _ (C00.mergeAt_supportedBelow hx i.isLt) _
          (hf.comp (C00.skipAfter_monotone i.val))).trans (N.merge_le i.val x)

theorem mapDomain_le (N : OrderedNorm) (f : ℕ → ℕ) (hf : Monotone f) (x : C00) :
    N (Finsupp.mapDomain f x) ≤ N x := by
  classical
  obtain ⟨B, hB⟩ := Finset.exists_nat_subset_range x.support
  apply N.mapDomain_le_of_supportedBelow B x _ f hf
  intro i hi
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  have := Finset.mem_range.mp (hB hmem)
  omega

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
