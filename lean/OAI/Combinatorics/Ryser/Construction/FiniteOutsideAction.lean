import OAI.Combinatorics.Ryser.Construction.LabelAction
import OAI.Combinatorics.Ryser.Construction.FiniteSelectionCounting
import OAI.Combinatorics.Ryser.Geometry.AffineJoins

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]
variable [instFintypeF : Fintype F] [instFintypeG : Fintype G]

def offPencilGroups (data : ConfigurationData k F G) (p : Point F)
    (ell : AffineLine F) : Finset G := by
  classical
  exact Finset.univ.filter (fun i => ∃ w ∈ data.retained,
    Incidence (data.base i w) ell ∧
      joinDirection p (data.base i w) ∈ data.altered i)

@[simp] theorem mem_offPencilGroups (data : ConfigurationData k F G)
    (p : Point F) (ell : AffineLine F) (i : G) :
    i ∈ offPencilGroups data p ell ↔ ∃ w ∈ data.retained,
      Incidence (data.base i w) ell ∧
        joinDirection p (data.base i w) ∈ data.altered i := let _ := instFieldk; let _ := instDecidableEqk; let _ := instDecidableEqG; let _ := instFintypeF; by
  classical
  simp only [offPencilGroups, Finset.mem_filter, Finset.mem_univ, true_and]

def OffPencilThin (data : ConfigurationData k F G) (p : Point F) : Prop :=
  ∀ ell : AffineLine F, ¬ Incidence p ell →
    (offPencilGroups data p ell).card ≤ 5

theorem joinDirection_mem_altered_of_incident_line
    (data : ConfigurationData k F G) (i : G) (p : Point F) (w : Point k)
    (ell : AffineLine F) (hne : p ≠ data.base i w)
    (hp : Incidence p ell) (hw : Incidence (data.base i w) ell)
    (hd : ell.1 ∈ data.altered i) :
    joinDirection p (data.base i w) ∈ data.altered i := let _ := instFieldk; let _ := instDecidableEqk; let _ := instDecidableEqG; let _ := instFintypeF; let _ := instFintypeG; by
  have hdir := congrArg Prod.fst (eq_joinLine_of_incidence hne hp hw)
  change ell.1 = joinDirection p (data.base i w) at hdir
  rw [← hdir]
  exact hd

theorem ordinaryVertex_notMem_exceptionalEdge_of_altered_join
    (data : ConfigurationData k F G) (p : Point F) (i : G) (w : Point k)
    (hne : p ≠ data.base i w)
    (hjoin : joinDirection p (data.base i w) ∈ data.altered i)
    (ell : AffineLine F) (hp : Incidence p ell) :
    ordinaryVertex data ell ∉ exceptionalEdge data i w := let _ := instFintypeG; by
  intro hhit
  obtain ⟨hunaltered, hw⟩ :=
    (ordinaryVertex_mem_exceptionalEdge_iff data i w ell).mp hhit
  have hdir := congrArg Prod.fst (eq_joinLine_of_incidence hne hp hw)
  change ell.1 = joinDirection p (data.base i w) at hdir
  apply hunaltered
  rw [hdir]
  exact hjoin

open scoped Classical

theorem selectedPositions_hit_card_le_five
    (data : ConfigurationData k F G) (p : Point F)
    (I : Finset G) (lines : G → AffineLine F) (S : G → Finset (Point k))
    (hbase : ∀ i, Function.Injective (data.base i))
    (hretained : ∀ i ∈ I, S i ⊆ data.retained)
    (houtside : ∀ i ∈ I, ∀ w ∈ S i, p ≠ data.base i w)
    (hthrough : ∀ i ∈ I, Incidence p (lines i))
    (haltered : ∀ i ∈ I, (lines i).1 ∈ data.altered i)
    (honlines : ∀ i ∈ I, ∀ w ∈ S i, Incidence (data.base i w) (lines i))
    (hsize : ∀ i, (S i).card ≤ 5) (hthin : OffPencilThin data p)
    (v : Vertex (k := k) data.altered) :
    ((selectedPositions I S).filter
      (fun x : G × Point k => v ∈ exceptionalEdge data x.1 x.2)).card ≤ 5 := by
  classical
  cases v with
  | inl ell =>
      change ((selectedPositions I S).filter
        (fun x : G × Point k => ordinaryVertex data ell ∈ exceptionalEdge data x.1 x.2)).card ≤ 5
      let E := (selectedPositions I S).filter
        (fun x : G × Point k => ordinaryVertex data ell ∈ exceptionalEdge data x.1 x.2)
      change E.card ≤ 5
      by_cases hp : Incidence p ell
      · have hempty : E = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨hxS, hxhit⟩ := Finset.mem_filter.mp hx
          obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hxS
          have hjoin := joinDirection_mem_altered_of_incident_line data x.1 p x.2
            (lines x.1) (houtside x.1 hi x.2 hw) (hthrough x.1 hi)
            (honlines x.1 hi x.2 hw) (haltered x.1 hi)
          exact ordinaryVertex_notMem_exceptionalEdge_of_altered_join data p x.1 x.2
            (houtside x.1 hi x.2 hw) hjoin ell hp hxhit
        simp only [hempty, Finset.card_empty, Nat.zero_le]
      · have hone : ∀ (i : G) (w z : Point k),
            (i, w) ∈ E → (i, z) ∈ E → w = z := by
          intro i w z hw hz
          obtain ⟨hwS, hwhit⟩ := Finset.mem_filter.mp hw
          obtain ⟨hzS, hzhit⟩ := Finset.mem_filter.mp hz
          obtain ⟨hi, hwsel⟩ := mem_selectedPositions.mp hwS
          have hzsel := (mem_selectedPositions.mp hzS).2
          have hne : ell ≠ lines i := by
            intro heq
            apply hp
            rw [heq]
            exact hthrough i hi
          apply hbase i
          exact eq_of_common_incidence_of_ne_lines hne
            ((ordinaryVertex_mem_exceptionalEdge_iff data i w ell).mp hwhit).2
            (honlines i hi w hwsel)
            ((ordinaryVertex_mem_exceptionalEdge_iff data i z ell).mp hzhit).2
            (honlines i hi z hzsel)
        have hgroups : E.image Prod.fst ⊆ offPencilGroups data p ell := by
          intro i hi
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨hxS, hxhit⟩ := Finset.mem_filter.mp hx
          obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hxS
          apply (mem_offPencilGroups data p ell x.1).mpr
          refine ⟨x.2, hretained x.1 hi hw,
            ((ordinaryVertex_mem_exceptionalEdge_iff data x.1 x.2 ell).mp hxhit).2, ?_⟩
          exact joinDirection_mem_altered_of_incident_line data x.1 p x.2
            (lines x.1) (houtside x.1 hi x.2 hw) (hthrough x.1 hi)
            (honlines x.1 hi x.2 hw) (haltered x.1 hi)
        calc
          E.card = (E.image Prod.fst).card :=
            card_eq_card_image_fst_of_one_per_group E hone
          _ ≤ (offPencilGroups data p ell).card := Finset.card_le_card hgroups
          _ ≤ 5 := hthin ell hp
  | inr label =>
      rcases label with ⟨i, d, c⟩
      change ((selectedPositions I S).filter
        (fun x : G × Point k => specialVertex data i d c ∈ exceptionalEdge data x.1 x.2)).card ≤ 5
      apply card_le_five_of_subset_selectedPositions_one_group I S _ i
      · exact Finset.filter_subset _ _
      · intro x hx
        by_contra hxi
        exact specialVertex_notMem_exceptionalEdge_of_ne data i x.1 (Ne.symm hxi)
          x.2 d c (Finset.mem_filter.mp hx).2
      · exact hsize i

end RyserCoveringCounterexample.Construction

end

end OAI
