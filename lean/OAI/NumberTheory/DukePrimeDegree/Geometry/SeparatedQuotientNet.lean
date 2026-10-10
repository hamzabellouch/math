import OAI.NumberTheory.DukePrimeDegree.Geometry.QuantitativeDistanceNet
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Pairwise.Basic

namespace OAI

/-! # Separated quotient-distance nets

Thinning the existing quantitative net retains its cardinality bound and
adds separation. This is the local packing input for controlling how
many covering labels can meet one small image cell.
-/

noncomputable section
open Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_separated_quotient_subnet {n N : ℕ} (z : Fin N → X n)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ S : Finset (Fin N),
      (S : Set (Fin N)).Pairwise (fun i j => r < quotientLogDistance (z i) (z j)) ∧
      ∀ i, ∃ j ∈ S, quotientLogDistance (z i) (z j) ≤ r := by
  classical
  let F : Finset (Finset (Fin N)) := Finset.univ.filter
    (fun S => (S : Set (Fin N)).Pairwise (fun i j => r < quotientLogDistance (z i) (z j)))
  have hF : F.Nonempty := ⟨∅,by simp [F]⟩
  obtain ⟨S,hS,hmax⟩ := F.exists_max_image Finset.card hF
  have hsep : (S : Set (Fin N)).Pairwise (fun i j => r < quotientLogDistance (z i) (z j)) :=
    (Finset.mem_filter.mp hS).2
  refine ⟨S,hsep,?_⟩
  intro i
  by_contra hn
  have hfar (j : Fin N) (hj : j ∈ S) : r < quotientLogDistance (z i) (z j) := by
    exact lt_of_not_ge (fun h => hn ⟨j,hj,h⟩)
  have hi : i ∉ S := by
    intro hi
    have hh := hfar i hi
    rw [quotientLogDistance_self] at hh
    linarith
  have hnew : ((insert i S : Finset (Fin N)) : Set (Fin N)).Pairwise
      (fun a b => r < quotientLogDistance (z a) (z b)) := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hai | has
    · subst a
      rcases Finset.mem_insert.mp hb with hbi | hbs
      · subst b
        exact (hab rfl).elim
      · exact hfar b hbs
    · rcases Finset.mem_insert.mp hb with hbi | hbs
      · subst b
        rw [quotientLogDistance_symm]
        exact hfar a has
      · exact hsep has hbs hab
  have hmem : insert i S ∈ F := by simp only [F,Finset.mem_filter,Finset.mem_univ,true_and]; exact hnew
  have hc := hmax (insert i S) hmem
  rw [Finset.card_insert_of_notMem hi] at hc
  omega

theorem exists_separated_quantitative_distance_net {n : ℕ} (hn : 0 < n)
    (R r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ (N : ℕ) (z : Fin N → X n),
      (N:ℝ) ≤ quotientNetBound n R (r/2) ∧
      (∀ i j, i ≠ j → r/2 < quotientLogDistance (z i) (z j)) ∧
      ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R →
        ∃ i, quotientLogDistance (z i) x < r := by
  classical
  obtain ⟨M,w,hM,hcover⟩ := exists_quantitative_distance_net hn R (r/2)
    (by positivity) (by linarith)
  obtain ⟨S,hsep,hnet⟩ := exists_separated_quotient_subnet w (show 0 ≤ r/2 by positivity)
  let e : Fin S.card ≃ S := S.equivFin.symm
  let z : Fin S.card → X n := fun i => w (e i).val
  refine ⟨S.card,z,?_,?_,?_⟩
  · have hcN : S.card ≤ M := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    have hc : (S.card:ℝ) ≤ M := by exact_mod_cast hcN
    exact hc.trans hM
  · intro i j hij
    apply hsep (e i).prop (e j).prop
    intro he
    exact hij (e.injective (Subtype.ext he))
  · intro x hx
    obtain ⟨i,hi⟩ := hcover x hx
    obtain ⟨j,hj,hd⟩ := hnet i
    refine ⟨e.symm ⟨j,hj⟩,?_⟩
    have htri := quotientLogDistance_triangle (w j) (w i) x
    rw [quotientLogDistance_symm (w j) (w i)] at htri
    change quotientLogDistance (w (e (e.symm ⟨j,hj⟩)).val) x < r
    simp only [Equiv.apply_symm_apply]
    linarith

end DukePrimeDegree

end

end OAI
