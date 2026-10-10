import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.DistanceLayers
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorFrames
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorPaths
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.FourCycles
import OAI.Combinatorics.Ramsey.CycleClique.FrameProperties
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.InducedGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

structure ThreeHyp {V : Type*} [Fintype V] (G : SimpleGraph V) (a : ℕ) : Prop where
  order : Fintype.card V = 3*a+1
  alpha : G.indepNum ≤ a
  a_max : a ≤ 3
  cycle : ¬ SimpleGraph.cycleGraph 4 ⊑ G
  clique : G.cliqueNum ≤ 3
  expansion : ∀ I, G.IsIndepSet I → I.Nonempty → 3*I.ncard+1 ≤ (closedNeighborhood G I).ncard

namespace ThreeHyp
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {a : ℕ} (H : ThreeHyp G a)
include H

theorem separated (T : Frame G 3) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (T.U i) (T.U j) ∧ ∀ u ∈ T.U i, ∀ v ∈ T.U j, ¬ G.Adj u v := by
  rw [T.U_ball,T.U_ball]
  apply outside_balls_separated (T.memQ i) (T.memQ j) (fun he => hij (T.q.injective he))
  intro d hd hd'
  apply outsidePath_clique_forbidden T.clique (by omega) (by rw [T.cardQ]) H.cycle
  · rw [T.cardQ]
    omega
  · omega

theorem U_nonempty (T : Frame G 3) (i : Fin 3) : (T.U i).Nonempty := by
  have hd := T.U_degree H.expansion i
  exact (Set.ncard_pos).mp (by omega)

theorem alpha_sum (T : Frame G 3) : ∑ i, independence G (T.U i) ≤ a := by
  classical
  have hh := sum_independence_layers G T.U (fun _ _ hij => (H.separated T hij).1)
    Finset.univ (fun _ _ _ _ hij => (H.separated T hij).2)
  have hb := independence_mono (G:=G) (Set.subset_univ (⋃ i ∈ Finset.univ,T.U i))
  rw [independence_univ] at hb
  exact hh.trans (hb.trans H.alpha)

theorem a_eq (T : Frame G 3) : a=3 := by
  have hs := H.alpha_sum T
  rw [Fin.sum_univ_three] at hs
  have h0 := independence_pos (G:=G) (H.U_nonempty T 0)
  have h1 := independence_pos (G:=G) (H.U_nonempty T 1)
  have h2 := independence_pos (G:=G) (H.U_nonempty T 2)
  have := H.a_max
  omega

theorem U_clique (T : Frame G 3) (i : Fin 3) : G.IsClique (T.U i) := by
  have hs := H.alpha_sum T
  rw [Fin.sum_univ_three] at hs
  have h0 := independence_pos (G:=G) (H.U_nonempty T 0)
  have h1 := independence_pos (G:=G) (H.U_nonempty T 1)
  have h2 := independence_pos (G:=G) (H.U_nonempty T 2)
  have := H.a_max
  apply clique_of_independence_le_one
  fin_cases i <;> dsimp at * <;> omega

theorem U_card (T : Frame G 3) (i : Fin 3) : 1 ≤ (T.U i).ncard ∧ (T.U i).ncard ≤ 2 := by
  have hmin := (Set.ncard_pos).mpr (H.U_nonempty T i)
  have hmax := T.clique_U_bound H.clique i (H.U_clique T i)
  omega

 
def W (T : Frame G 3) : Set V := T.Qᶜ \ ⋃ i,T.U i

omit H in
theorem W_outside (_H : ThreeHyp G a) (T : Frame G 3) : W T ⊆ T.Qᶜ := Set.sdiff_subset

omit H in
theorem W_not_U (_H : ThreeHyp G a) (T : Frame G 3) {w : V}
    (hw : w ∈ W T) (i : Fin 3) : w ∉ T.U i :=
  fun hh => hw.2 (Set.mem_iUnion.mpr ⟨i,hh⟩)

theorem W_nonadj_Q (T : Frame G 3) {w : V} (hw : w ∈ W T) (i : Fin 3) : ¬ G.Adj w (T.q i) :=
  fun hh => H.W_not_U T hw i ⟨hh.symm,hw.1⟩

theorem W_card (T : Frame G 3) :
    (W T).ncard + ((T.U 0).ncard + (T.U 1).ncard + (T.U 2).ncard) = 7 := by
  classical
  have hd : Pairwise (fun i j => Disjoint (T.U i) (T.U j)) :=
    fun _ _ hij => (H.separated T hij).1
  have hsum := ncard_union_layers T.U hd Finset.univ
  simp only [Finset.mem_univ,Set.iUnion_true] at hsum
  rw [Fin.sum_univ_three] at hsum
  have hsub : (⋃ i,T.U i) ⊆ T.Qᶜ := by
    intro u hu
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
    exact hi.2
  have he := Set.ncard_sdiff_add_ncard_of_subset hsub
  have hq := Set.ncard_add_ncard_compl T.Q
  rw [T.cardQ,Nat.card_eq_fintype_card,H.order,H.a_eq T] at hq
  change (W T).ncard+(⋃ i,T.U i).ncard = _ at he
  omega

theorem W_nonempty (T : Frame G 3) : (W T).Nonempty := by
  have hw := H.W_card T
  have h0 := H.U_card T 0
  have h1 := H.U_card T 1
  have h2 := H.U_card T 2
  exact (Set.ncard_pos).mp (by omega)

 
theorem W_at_most_one (T : Frame G 3) {w u v : V} (hw : w ∈ W T) {i : Fin 3}
    (hu : u ∈ T.U i) (hv : v ∈ T.U i) (hwu : G.Adj w u) (hwv : G.Adj w v) : u=v := by
  by_contra huv
  have hnw := T.neQ hw.1
  have hnu := T.neQ hu.2
  have hnv := T.neQ hv.2
  apply H.cycle
  apply cycle_of_list [w,u,T.q i,v] (by simp)
  · simp [hwu.ne,hwv.ne,hnw,hnu,Ne.symm (hnv i),huv]
  · simpa using And.intro hwu (And.intro hu.1.symm hv.1)
  · simpa using hwv.symm

 
theorem indep_four_bound {w u v z : V}
    (hwu : w ≠ u) (hwv : w ≠ v) (hwz : w ≠ z)
    (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    (nwu : ¬ G.Adj w u) (nwv : ¬ G.Adj w v) (nwz : ¬ G.Adj w z)
    (nuv : ¬ G.Adj u v) (nuz : ¬ G.Adj u z) (nvz : ¬ G.Adj v z) : False := by
  have hI : G.IsIndepSet {w,u,v,z} := by
    intro x hx y hy hxy hadj
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact hxy rfl | exact nwu hadj | exact nwu hadj.symm |
        exact nwv hadj | exact nwv hadj.symm | exact nwz hadj | exact nwz hadj.symm |
        exact nuv hadj | exact nuv hadj.symm | exact nuz hadj | exact nuz hadj.symm |
        exact nvz hadj | exact nvz hadj.symm
  have hc : ({w,u,v,z} : Set V).ncard=4 := by
    simp [Set.ncard_insert_of_notMem,hwu,hwv,hwz,huv,huz,hvz]
  have hb := (indep_ncard_le hI).trans H.alpha
  have := H.a_max
  omega

 
theorem W_no_two_misses (T : Frame G 3) {w u v : V} (hw : w ∈ W T)
    {i j : Fin 3} (hij : i ≠ j) (hu : u ∈ T.U i) (hv : v ∈ T.U j)
    (hwu : ¬ G.Adj w u) (hwv : ¬ G.Adj w v) : False := by
  obtain ⟨l,hli,hlj⟩ : ∃ l : Fin 3, l ≠ i ∧ l ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  have hdis := (H.separated T hij).1
  have hnu := T.neQ hu.2
  have hnv := T.neQ hv.2
  apply H.indep_four_bound (w:=w) (u:=u) (v:=v) (z:=T.q l) (fun he => H.W_not_U T hw i (he ▸ hu))
    (fun he => H.W_not_U T hw j (he ▸ hv)) (T.neQ hw.1 l)
    (fun he => Set.disjoint_left.mp hdis hu (he ▸ hv)) (hnu l) (hnv l)
    hwu hwv (H.W_nonadj_Q T hw l) ((H.separated T hij).2 u hu v hv)
  · intro hh
    exact Set.disjoint_left.mp (H.separated T hli).1 ⟨hh.symm,hu.2⟩ hu
  · intro hh
    exact Set.disjoint_left.mp (H.separated T hlj).1 ⟨hh.symm,hv.2⟩ hv

 
theorem W_two_complete (T : Frame G 3) {w : V} (hw : w ∈ W T) :
    ∃ h : Fin 3, ∀ i, i ≠ h → ∀ u ∈ T.U i, G.Adj w u := by
  classical
  by_cases hbad : ∃ i : Fin 3, ¬ ∀ u ∈ T.U i, G.Adj w u
  · obtain ⟨h,hh⟩ := hbad
    push Not at hh
    obtain ⟨v,hv,hwv⟩ := hh
    refine ⟨h,?_⟩
    intro i hih u hu
    by_contra hwu
    exact H.W_no_two_misses T hw hih hu hv hwu hwv
  · push Not at hbad
    exact ⟨0,fun i _ => hbad i⟩

theorem W_complete_singleton (T : Frame G 3) {w : V} (hw : w ∈ W T) (i : Fin 3)
    (hi : ∀ u ∈ T.U i, G.Adj w u) : (T.U i).ncard=1 := by
  obtain ⟨u,hu⟩ := H.U_nonempty T i
  have he : T.U i={u} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨hu,?_⟩
    intro v hv
    exact H.W_at_most_one T hw hv hu (hi v hv) (hi u hu)
  simp [he]

theorem W_at_least_three (T : Frame G 3) : 3 ≤ (W T).ncard := by
  obtain ⟨w,hw⟩ := H.W_nonempty T
  obtain ⟨h,hh⟩ := H.W_two_complete T hw
  have hs := H.W_card T
  have hmax := (H.U_card T h).2
  have hc : ∀ i, i ≠ h → (T.U i).ncard=1 := by
    intro i hi
    exact H.W_complete_singleton T hw i (hh i hi)
  fin_cases h
  · have h1 := hc 1 (by decide)
    have h2 := hc 2 (by decide)
    dsimp at *
    omega
  · have h0 := hc 0 (by decide)
    have h2 := hc 2 (by decide)
    dsimp at *
    omega
  · have h0 := hc 0 (by decide)
    have h1 := hc 1 (by decide)
    dsimp at *
    omega

 
theorem no_two_common {x y u v : V} (hxy : x ≠ y) (huv : u ≠ v)
    (hxu : G.Adj x u) (hxv : G.Adj x v) (hyu : G.Adj y u) (hyv : G.Adj y v) : False := by
  apply H.cycle
  apply cycle_of_list [x,u,y,v] (by simp)
  · simp [hxu.ne,hxv.ne,hyu.ne.symm,hyv.ne,hxy,huv]
  · simpa using And.intro hxu (And.intro hyu.symm hyv)
  · simpa using hxv.symm

 

theorem contradiction (T : Frame G 3) : False := by
  classical
  let f : W T → Fin 3 := fun w => (H.W_two_complete T w.property).choose
  have hf : ∀ w : W T, ∀ i, i ≠ f w → ∀ u ∈ T.U i, G.Adj w.val u :=
    fun w => (H.W_two_complete T w.property).choose_spec
  have hinj : Function.Injective f := by
    intro w w' he
    apply Subtype.ext
    by_contra hww
    obtain ⟨i,j,hij,hi,hj⟩ : ∃ i j : Fin 3, i ≠ j ∧ i ≠ f w ∧ j ≠ f w := by
      generalize f w = l
      fin_cases l <;> decide
    obtain ⟨u,hu⟩ := H.U_nonempty T i
    obtain ⟨v,hv⟩ := H.U_nonempty T j
    have huv : u ≠ v := fun he => Set.disjoint_left.mp (H.separated T hij).1 hu (he ▸ hv)
    exact H.no_two_common hww huv (hf w i hi u hu) (hf w j hj v hv)
      (hf w' i (he ▸ hi) u hu) (hf w' j (he ▸ hj) v hv)
  have hcW : Fintype.card (W T)=(W T).ncard := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hupper : (W T).ncard ≤ 3 := by
    have hh := Fintype.card_le_of_injective f hinj
    simpa only [hcW,Fintype.card_fin] using hh
  have hlower := H.W_at_least_three T
  have hvar : ∀ i : Fin 3, ∃ w : W T, f w ≠ i := by
    intro i
    by_contra hh
    push Not at hh
    have hsub : Subsingleton (W T) := ⟨fun w w' => hinj ((hh w).trans (hh w').symm)⟩
    have hhcard := Fintype.card_le_one_iff_subsingleton.mpr hsub
    rw [hcW] at hhcard
    omega
  have hone : ∀ i, (T.U i).ncard=1 := by
    intro i
    obtain ⟨w,hw⟩ := hvar i
    exact H.W_complete_singleton T w.property i (hf w i hw.symm)
  have h0 := hone 0
  have h1 := hone 1
  have h2 := hone 2
  have hc := H.W_card T
  omega

end ThreeHyp

end CycleClique

end OAI
