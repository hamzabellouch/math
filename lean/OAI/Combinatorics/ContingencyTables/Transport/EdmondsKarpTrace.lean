import OAI.Combinatorics.ContingencyTables.Transport.EdmondsKarpAugmentation
import Mathlib.Order.Fin.Basic

namespace OAI

/-! # Repeated critical arcs strictly increase their distance label -/
namespace ContingencyTables.EdmondsKarpTrace
open PublishedEdmondsKarp EdmondsKarpDistance EdmondsKarpAugmentation
open scoped Classical
noncomputable section
variable {n K : ℕ}

lemma descent_between (a : Fin (K+1)→ℤ) (i j : Fin (K+1)) (hij : i ≤ j)
    (h : a j < a i) :
    ∃ k : Fin K,i ≤ k.castSucc ∧ k.succ ≤ j ∧ a k.succ < a k.castSucc := by
  by_contra hn
  have hstep (k : Fin K) (hik : i ≤ k.castSucc) (hkj : k.succ ≤ j) :
      a k.castSucc ≤ a k.succ :=
    le_of_not_gt (fun hlt => hn ⟨k,hik,hkj,hlt⟩)
  have hm : ∀ u : Fin (K+1),i ≤ u → u ≤ j → a i ≤ a u := by
    intro u
    refine Fin.induction ?_ (fun k ih => ?_) u
    · intro hi _
      change i.val ≤ 0 at hi
      have he : i=0 := by
        apply Fin.ext
        simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero hi
      subst i
      exact le_rfl
    · intro hi hj'
      by_cases hik : i ≤ k.castSucc
      · exact (ih hik ((Fin.castSucc_le_succ k).trans hj')).trans (hstep k hik hj')
      · have he : i=k.succ := Fin.ext (by
          change i.val ≤ k.val+1 at hi
          change ¬i.val ≤ k.val at hik
          change i.val=k.val+1
          omega)
        rw [he]
  exact (not_le_of_gt h) (hm j hij le_rfl)

lemma labels_monotone {c : Capacity n} {s t : Fin n} {F : Fin (K+1)→Flow n}
    (h : ∀ i : Fin K,ShortestAugmentation c s t (F i.castSucc) (F i.succ)) (v : Fin n) :
    Monotone (fun i => label c (F i) s v) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  exact EdmondsKarpAugmentation.labels_monotone (h i) v

/-- Once (u,v) is saturated, using it again requires a reverse
augmentation and hence at least two more source-distance layers at u. -/
theorem repeated_critical {c : Capacity n} {s t : Fin n} {F : Fin (K+1)→Flow n}
    (h : ∀ i : Fin K,ShortestAugmentation c s t (F i.castSucc) (F i.succ))
    (i j : Fin K) (hij : i < j) (u v : Fin n)
    (hsat : F i.succ u v=(c u v:ℤ))
    (hlevel : label c (F i.castSucc) s v=label c (F i.castSucc) s u+1)
    (hres : F j.castSucc u v < (c u v:ℤ)) :
    label c (F i.castSucc) s u+2 ≤ label c (F j.castSucc) s u := by
  have hisj : i.succ ≤ j.castSucc := by
    change i.val+1 ≤ j.val
    exact hij
  obtain ⟨k,hik,hkj,hdec⟩ := descent_between (fun q => F q u v) i.succ j.castSucc hisj
    (by rw [hsat]; exact hres)
  have hreverse := decrease_labels (h k) u v hdec
  have hfirst := labels_monotone h v ((Fin.castSucc_le_succ i).trans hik)
  have hlast := labels_monotone h u ((Fin.castSucc_le_succ k).trans hkj)
  dsimp only at hfirst hlast
  omega

end
end ContingencyTables.EdmondsKarpTrace

end OAI
