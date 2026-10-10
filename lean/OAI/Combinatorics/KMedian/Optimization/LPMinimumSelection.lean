import Mathlib
import OAI.Combinatorics.KMedian.Optimization.ComputedNearest
import OAI.Combinatorics.KMedian.Optimization.LPListFacts

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

def minimum (xs : Row) : ℚ := xs.foldl min (xs.head?.getD 0)

theorem minimum_eq_finset (xs : Row) (U : Finset ℚ) (hU : U.Nonempty)
    (hm : ∀ q, q∈xs ↔ q∈U) : minimum xs=U.min' hU := by
  have hne : xs≠[] := by
    intro he
    obtain ⟨q,hq⟩ := hU
    have hx := (hm q).mpr hq
    rw [he] at hx
    cases hx
  have hd : xs.head?.getD 0∈xs := by
    cases xs with
    | nil => contradiction
    | cons a xs => exact List.mem_cons_self
  apply @foldl_max_eq ℚᵒᵈ _ xs _ _
  · exact min'_le U _ ((hm _).mp hd)
  · exact (hm _).mpr (min'_mem U hU)
  · intro q hq
    exact min'_le U q ((hm q).mp hq)

 theorem firstNearest_value {n : ℕ} (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty) :
    d (Preparation.firstNearest U d hU)=(U.image d).min' (hU.image _) := by
  unfold Preparation.firstNearest
  exact (mem_filter.mp (min'_mem (U.filter (fun i => d i=(U.image d).min' (hU.image _))) _)).2

 theorem firstNearest_le {n : ℕ} (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty)
    (j : Fin n) (hj : j∈U) (hd : d j=d (Preparation.firstNearest U d hU)) :
    Preparation.firstNearest U d hU ≤ j := by
  unfold Preparation.firstNearest
  apply min'_le
  exact mem_filter.mpr ⟨hj,hd.trans (firstNearest_value U d hU)⟩

variable {α : Type}
def selectMinimum (d : α → ℚ) (as : List α) (a0 : α) : α :=
  (as.filter (fun a => decide (d a=minimum (as.map d)))).head?.getD a0

 theorem selectMinimum_ofFn {n : ℕ} [NeZero n] (f : Fin n → α) (d : α → ℚ) (a0 : α) :
    selectMinimum d (List.ofFn f) a0=
      f (Preparation.firstNearest univ (fun i => d (f i)) univ_nonempty) := by
  let a := Preparation.firstNearest univ (fun i => d (f i)) univ_nonempty
  have hval : minimum ((List.ofFn f).map d)=d (f a) := by
    apply Eq.trans _ (firstNearest_value univ (fun i => d (f i)) univ_nonempty).symm
    apply minimum_eq_finset
    intro q
    simp only [List.mem_map,List.mem_ofFn,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨x,⟨i,rfl⟩,h⟩
      exact ⟨i,h⟩
    · rintro ⟨i,h⟩
      exact ⟨f i,⟨i,rfl⟩,h⟩
  have hfind : (List.ofFn f).find? (fun x => decide (d x=minimum ((List.ofFn f).map d)))=some (f a) := by
    apply List.find?_ofFn_eq_some.mpr
    refine ⟨by rw [hval]; simp, a,rfl,?_⟩
    intro j hj hp
    have he : d (f j)=d (f a) := by simpa only [decide_eq_true_eq,hval] using hp
    have hh := firstNearest_le univ (fun i => d (f i)) univ_nonempty j (mem_univ j) he
    exact (not_le_of_gt hj) hh
  unfold selectMinimum
  rw [List.head?_filter,hfind]
  rfl

namespace Program
open Binary Binary.PolyProgram
noncomputable def minFold : PolyProgram (encodePair er Ratio.encode) Ratio.encode (fun x : Row × ℚ => x.1.foldl min x.2) :=
  (listChoose ((exchange Ratio.encode Ratio.encode).comp ratLT) 0).congr _ (fun x => by
    congr 1
    funext a b
    by_cases h : b<a
    · simp [h,min_eq_right h.le]
    · simp [h,min_eq_left (le_of_not_gt h)])
noncomputable def minimumProgram : PolyProgram er Ratio.encode minimum :=
  (((identity er).fanout (listHead Ratio.encode 0)).comp minFold).congr _ (fun _ => rfl)
end Program
end MetricKMedian.LPBinary
end

end OAI
