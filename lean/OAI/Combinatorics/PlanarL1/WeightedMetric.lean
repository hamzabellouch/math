import OAI.Combinatorics.PlanarL1.Statement

namespace OAI

section

namespace PlanarL1.WeightedGraph
open SimpleGraph
variable {V : Type} {G : SimpleGraph V} {ℓ : V → V → ℝ}

lemma length_nonneg (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) {u v : V} (p : G.Walk u v) :
    0 ≤ walkLength ℓ p := by
  induction p with
  | nil => rfl
  | cons h p ih => exact add_nonneg (hℓ _ _ h) ih

lemma length_pos (hℓ : ∀ u v, G.Adj u v → 0 < ℓ u v) {u v : V} (p : G.Walk u v)
    (hne : u ≠ v) : 0 < walkLength ℓ p := by
  cases p with
  | nil => exact False.elim (hne rfl)
  | cons h p => exact add_pos_of_pos_of_nonneg (hℓ _ _ h) (length_nonneg (fun i j h => (hℓ i j h).le) p)

lemma length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkLength ℓ (p.append q) = walkLength ℓ p+walkLength ℓ q := by
  induction p with
  | nil => simp [walkLength]
  | cons h p ih => simp [walkLength,ih,add_assoc]

lemma length_darts {u v : V} (p : G.Walk u v) :
    walkLength ℓ p = (p.darts.map (fun d => ℓ d.fst d.snd)).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [walkLength,Walk.darts_cons,ih]

lemma length_reverse (hs : ∀ u v, ℓ u v = ℓ v u) {u v : V} (p : G.Walk u v) :
    walkLength ℓ p.reverse = walkLength ℓ p := by
  rw [length_darts,length_darts,Walk.darts_reverse,List.map_reverse,List.sum_reverse,List.map_map]
  congr 1
  apply List.map_congr_left
  intro d _
  exact hs _ _

lemma length_bypass_le [DecidableEq V] (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v)
    {u v : V} (p : G.Walk u v) : walkLength ℓ p.bypass ≤ walkLength ℓ p := by
  rw [length_darts,length_darts]
  apply (p.darts_bypass_sublist_darts.map _).sum_le_sum
  intro a ha
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp ha
  exact hℓ _ _ d.adj

lemma distance_nonneg (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) (u v : V) :
    0 ≤ graphDistance G ℓ u v := by
  apply Real.sInf_nonneg
  rintro _ ⟨p,rfl⟩
  exact length_nonneg hℓ p

lemma distance_le_length (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v)
    {u v : V} (p : G.Walk u v) : graphDistance G ℓ u v ≤ walkLength ℓ p := by
  apply csInf_le
  · exact ⟨0,by rintro _ ⟨q,rfl⟩; exact length_nonneg hℓ q⟩
  · exact ⟨p,rfl⟩

lemma distance_self (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) (u : V) :
    graphDistance G ℓ u u = 0 := by
  apply le_antisymm _ (distance_nonneg hℓ u u)
  exact distance_le_length hℓ Walk.nil

lemma distance_attained [Finite V] (hG : G.Connected)
    (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath ∧ graphDistance G ℓ u v = walkLength ℓ p := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let q := (hG u v).some.toPath
  obtain ⟨p,_,hp⟩ := Finset.exists_min_image (Finset.univ : Finset (G.Path u v))
    (fun p => walkLength ℓ p.val) ⟨q,Finset.mem_univ q⟩
  refine ⟨p.val,p.property,le_antisymm (distance_le_length hℓ p.val) ?_⟩
  unfold graphDistance
  apply le_csInf (show (Set.range (fun r : G.Walk u v => walkLength ℓ r)).Nonempty from ⟨walkLength ℓ p.val,⟨p.val,rfl⟩⟩)
  rintro _ ⟨r,rfl⟩
  exact (hp r.toPath (Finset.mem_univ _)).trans (length_bypass_le hℓ r)

lemma distance_symm [Finite V] (hG : G.Connected) (hs : ∀ u v, ℓ u v = ℓ v u)
    (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) (u v : V) :
    graphDistance G ℓ u v = graphDistance G ℓ v u := by
  suffices h : ∀ a b, graphDistance G ℓ a b ≤ graphDistance G ℓ b a from
    le_antisymm (h u v) (h v u)
  intro a b
  obtain ⟨p,_,hp⟩ := distance_attained hG hℓ b a
  rw [hp]
  exact (distance_le_length hℓ p.reverse).trans_eq (length_reverse hs p)

lemma distance_triangle [Finite V] (hG : G.Connected)
    (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) (u v w : V) :
    graphDistance G ℓ u w ≤ graphDistance G ℓ u v+graphDistance G ℓ v w := by
  obtain ⟨p,_,hp⟩ := distance_attained hG hℓ u v
  obtain ⟨q,_,hq⟩ := distance_attained hG hℓ v w
  rw [hp,hq,← length_append]
  exact distance_le_length hℓ (p.append q)

lemma distance_pos [Finite V] (hG : G.Connected)
    (hℓ : ∀ u v, G.Adj u v → 0 < ℓ u v) {u v : V} (hne : u ≠ v) :
    0 < graphDistance G ℓ u v := by
  obtain ⟨p,_,hp⟩ := distance_attained hG (fun i j h => (hℓ i j h).le) u v
  rw [hp]
  exact length_pos hℓ p hne

@[instance_reducible]
noncomputable def metricSpace [Finite V] (hG : G.Connected)
    (hs : ∀ u v, ℓ u v = ℓ v u) (hℓ : ∀ u v, G.Adj u v → 0 < ℓ u v) :
    MetricSpace V where
  dist := graphDistance G ℓ
  dist_self := distance_self (fun i j h => (hℓ i j h).le)
  dist_comm := distance_symm hG hs (fun i j h => (hℓ i j h).le)
  dist_triangle := distance_triangle hG (fun i j h => (hℓ i j h).le)
  eq_of_dist_eq_zero := by
    intro x y he
    by_contra hne
    exact ne_of_gt (distance_pos hG hℓ hne) he

lemma edge_bound (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) {u v : V} (h : G.Adj u v) :
    graphDistance G ℓ u v ≤ ℓ u v := by
  simpa only [walkLength,add_zero] using distance_le_length hℓ (Walk.cons h Walk.nil)

/-- The literal predecessor used in the realization proof can be chosen with
strictly decreasing weighted root distance; no unit-edge shortcut is used. -/
lemma predecessor [Finite V] (hG : G.Connected) (hs : ∀ u v, ℓ u v = ℓ v u)
    (hℓ : ∀ u v, G.Adj u v → 0 < ℓ u v) (o v : V) (hne : v ≠ o) :
    ∃ u, G.Adj u v ∧ graphDistance G ℓ o u+ℓ u v = graphDistance G ℓ o v ∧
      graphDistance G ℓ o u < graphDistance G ℓ o v := by
  have hn := fun i j h => (hℓ i j h).le
  obtain ⟨p,_,hp⟩ := distance_attained hG hn v o
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons _ u _ h p =>
    have hpr := distance_le_length hn p
    have htri := distance_triangle hG hn v u o
    have hed := edge_bound hn h
    have he : graphDistance G ℓ v o = ℓ v u+graphDistance G ℓ u o := by
      change graphDistance G ℓ v o = ℓ v u+walkLength ℓ p at hp
      linarith
    rw [distance_symm hG hs hn v o,distance_symm hG hs hn u o,hs v u] at he
    refine ⟨u,h.symm,by linarith,?_⟩
    linarith [hℓ u v h.symm]


section ParentTree
variable (o : V) (f : V → V) (h : V → ℝ)
    (hf : ∀ v, v ≠ o → h (f v) < h v)

def parentGraph : SimpleGraph V where
  Adj u v := (v ≠ o ∧ f v = u) ∨ (u ≠ o ∧ f u = v)
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by
    intro v hv
    rcases hv with ⟨hne,he⟩ | ⟨hne,he⟩ <;>
      have hi := hf v hne <;> rw [he] at hi <;> exact hi.false⟩

lemma parent_adj {v : V} (hv : v ≠ o) : (parentGraph o f h hf).Adj (f v) v :=
  Or.inl ⟨hv,rfl⟩

lemma parent_connected [Finite V] : (parentGraph o f h hf).Connected := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨o,?_⟩
  intro v
  by_contra hv
  let S := Finset.univ.filter (fun x => ¬ (parentGraph o f h hf).Reachable o x)
  have hvS : v ∈ S := by simpa [S] using hv
  obtain ⟨w,hw,hm⟩ := Finset.exists_min_image S h ⟨v,hvS⟩
  have hnw : ¬ (parentGraph o f h hf).Reachable o w := (Finset.mem_filter.mp hw).2
  have hwo : w ≠ o := by rintro rfl; exact hnw (.refl _)
  have hnf : ¬ (parentGraph o f h hf).Reachable o (f w) := by
    intro hr
    exact hnw (hr.trans (parent_adj o f h hf hwo).reachable)
  have hfw : f w ∈ S := by simpa [S] using hnf
  exact (hf w hwo).not_ge (hm (f w) hfw)

lemma parent_tree [Finite V] : (parentGraph o f h hf).IsTree := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let T := parentGraph o f h hf
  have hT : T.Connected := parent_connected o f h hf
  let edge : {v : V // v ≠ o} → T.edgeSet :=
    fun v => ⟨s(f v.val,v.val),parent_adj o f h hf v.property⟩
  have he : Function.Surjective edge := by
    rintro ⟨e,he⟩
    induction e using Sym2.inductionOn with
    | hf u v =>
      rcases he with ⟨hv,hf⟩ | ⟨hu,hf⟩
      · refine ⟨⟨v,hv⟩,?_⟩
        apply Subtype.ext
        change s(f v,v) = s(u,v)
        rw [hf]
      · refine ⟨⟨u,hu⟩,?_⟩
        apply Subtype.ext
        change s(f u,u) = s(u,v)
        rw [hf,Sym2.eq_swap]
  have hc := Fintype.card_le_of_surjective edge he
  have hh : Fintype.card {v : V // v ≠ o} = Fintype.card V-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [hh] at hc
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨o⟩
  have hlo := hT.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at hlo
  apply (isTree_iff_connected_and_card).mpr
  refine ⟨hT,?_⟩
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  change Fintype.card T.edgeSet + 1 = Fintype.card V
  omega

lemma parent_walk [Finite V] {ℓ : V → V → ℝ} (ho : h o = 0)
    (hstep : ∀ v, v ≠ o → h (f v)+ℓ (f v) v = h v) (v : V) :
    ∃ p : (parentGraph o f h hf).Walk o v, walkLength ℓ p = h v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  by_contra hv
  let good := fun w => ∃ p : (parentGraph o f h hf).Walk o w, walkLength ℓ p = h w
  let S := Finset.univ.filter (fun x => ¬good x)
  have hvS : v ∈ S := by simpa [S,good] using hv
  obtain ⟨w,hw,hm⟩ := Finset.exists_min_image S h ⟨v,hvS⟩
  have hnw : ¬good w := (Finset.mem_filter.mp hw).2
  have hwo : w ≠ o := by
    rintro rfl
    exact hnw ⟨Walk.nil,ho.symm⟩
  have hfg : good (f w) := by
    by_contra hnf
    have hfw : f w ∈ S := by simpa [S] using hnf
    exact (hf w hwo).not_ge (hm (f w) hfw)
  obtain ⟨p,hp⟩ := hfg
  apply hnw
  refine ⟨p.append (Walk.cons (parent_adj o f h hf hwo) Walk.nil),?_⟩
  rw [length_append,hp]
  simpa only [walkLength,add_zero] using hstep w hwo

end ParentTree

/-- The weighted shortest-path spanning tree claimed at .
Its tree edges retain their arbitrary original positive lengths. -/
lemma shortest_path_tree [Finite V] (hG : G.Connected)
    (hs : ∀ u v, ℓ u v = ℓ v u)
    (hℓ : ∀ u v, G.Adj u v → 0 < ℓ u v) (o : V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
      (∀ v, ∃ p : T.Walk o v, walkLength ℓ p = graphDistance G ℓ o v) ∧
      (∀ u v, T.Adj u v → |graphDistance G ℓ o v-graphDistance G ℓ o u| = ℓ u v) := by
  classical
  let f : V → V := fun v => if hv : v = o then o else (predecessor hG hs hℓ o v hv).choose
  have hpred (v : V) (hv : v ≠ o) : G.Adj (f v) v ∧
      graphDistance G ℓ o (f v)+ℓ (f v) v = graphDistance G ℓ o v ∧
      graphDistance G ℓ o (f v) < graphDistance G ℓ o v := by
    simpa only [f,dite_eq_right hv] using (predecessor hG hs hℓ o v hv).choose_spec
  let h := graphDistance G ℓ o
  have hf : ∀ v, v ≠ o → h (f v) < h v := fun v hv => (hpred v hv).2.2
  let T := parentGraph o f h hf
  have hsub : T ≤ G := by
    intro u v huv
    rcases huv with ⟨hv,rfl⟩ | ⟨hu,rfl⟩
    · exact (hpred v hv).1
    · exact (hpred u hu).1.symm
  refine ⟨T,hsub,parent_tree o f h hf,?_,?_⟩
  · exact fun v => parent_walk o f h hf (distance_self (fun i j hi => (hℓ i j hi).le) o)
      (fun v hv => (hpred v hv).2.1) v
  · intro u v huv
    rcases huv with ⟨hv,rfl⟩ | ⟨hu,rfl⟩
    · rw [abs_of_pos (sub_pos.mpr (hpred v hv).2.2)]
      linarith [(hpred v hv).2.1]
    · rw [abs_of_neg (sub_neg.mpr (hpred u hu).2.2),hs u (f u)]
      linarith [(hpred u hu).2.1]

end PlanarL1.WeightedGraph




end

section

namespace PlanarL1
namespace Weighted
variable {V : Type} {G : SimpleGraph V} {l : V → V → ℝ}

lemma length_eq_sum_darts {u v : V} (p : G.Walk u v) :
    walkLength l p = (p.darts.map (fun d => l d.fst d.snd)).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [walkLength,SimpleGraph.Walk.darts_cons,List.map_cons,List.sum_cons,ih]

lemma length_nonneg (hl : ∀ u v, G.Adj u v → 0 ≤ l u v) {u v : V} (p : G.Walk u v) :
    0 ≤ walkLength l p := by
  induction p with
  | nil => exact le_rfl
  | cons h p ih => exact add_nonneg (hl _ _ h) ih

lemma length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkLength l (p.append q) = walkLength l p+walkLength l q := by
  simp only [length_eq_sum_darts,SimpleGraph.Walk.darts_append,List.map_append,List.sum_append]

lemma length_reverse (hs : ∀ u v, l u v=l v u) {u v : V} (p : G.Walk u v) :
    walkLength l p.reverse=walkLength l p := by
  simp only [length_eq_sum_darts,SimpleGraph.Walk.darts_reverse,List.map_reverse,List.map_map,List.sum_reverse]
  congr 2
  funext d
  exact hs d.snd d.fst

lemma length_bypass [DecidableEq V] (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (p : G.Walk u v) : walkLength l p.bypass ≤ walkLength l p := by
  rw [length_eq_sum_darts,length_eq_sum_darts]
  apply (p.darts_bypass_sublist_darts.map _).sum_le_sum
  intro a ha
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp ha
  exact hl d.fst d.snd d.adj

lemma length_eq_zero_iff (hl : ∀ u v, G.Adj u v → 0 < l u v)
    {u v : V} (p : G.Walk u v) : walkLength l p=0 ↔ p.Nil := by
  cases p with
  | nil => simp [walkLength]
  | cons h p =>
    have hpos : 0 < walkLength l (.cons h p) :=
      add_pos_of_pos_of_nonneg (hl _ _ h) (length_nonneg (fun u v h => (hl u v h).le) p)
    simp only [SimpleGraph.Walk.not_nil_cons,iff_false]
    exact ne_of_gt hpos

/-- Positivity permits deletion of repetitions, so the literal walk-infimum
is achieved by one of finitely many simple paths. No integral edge lengths
or approximation of the metric is used. -/
lemma exists_shortest [Fintype V] (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (hc : G.Reachable u v) :
    ∃ p : G.Path u v, ∀ q : G.Walk u v, walkLength l p.val ≤ walkLength l q := by
  classical
  obtain ⟨q⟩ := hc
  have he : (Finset.univ : Finset (G.Path u v)).Nonempty := ⟨q.toPath,Finset.mem_univ _⟩
  obtain ⟨p,_,hp⟩ := Finset.univ.exists_min_image (fun p : G.Path u v => walkLength l p.val) he
  refine ⟨p,fun q => ?_⟩
  exact (hp q.toPath (Finset.mem_univ _)).trans (length_bypass hl q)

lemma distance_eq_length [Fintype V] (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (hc : G.Reachable u v) :
    ∃ p : G.Path u v, graphDistance G l u v=walkLength l p.val ∧
      ∀ q : G.Walk u v, walkLength l p.val ≤ walkLength l q := by
  obtain ⟨p,hp⟩ := exists_shortest hl hc
  refine ⟨p,?_,hp⟩
  apply le_antisymm
  · exact csInf_le ⟨0,by rintro a ⟨q,rfl⟩; exact length_nonneg hl q⟩ ⟨p.val,rfl⟩
  · exact le_csInf ⟨walkLength l p.val,⟨p.val,rfl⟩⟩ (by rintro a ⟨q,rfl⟩; exact hp q)

lemma distance_le_walk (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (p : G.Walk u v) : graphDistance G l u v ≤ walkLength l p :=
  csInf_le ⟨0,by rintro a ⟨q,rfl⟩; exact length_nonneg hl q⟩ ⟨p,rfl⟩

lemma distance_nonneg (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (hc : G.Reachable u v) : 0 ≤ graphDistance G l u v := by
  obtain ⟨p⟩ := hc
  exact le_csInf ⟨walkLength l p,⟨p,rfl⟩⟩ (by rintro a ⟨q,rfl⟩; exact length_nonneg hl q)

lemma distance_self (hl : ∀ u v, G.Adj u v → 0 ≤ l u v) (u : V) :
    graphDistance G l u u=0 :=
  le_antisymm (distance_le_walk hl .nil) (distance_nonneg hl (.refl u))

lemma distance_symm [Fintype V] (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    (hs : ∀ u v, l u v=l v u) {u v : V} (hc : G.Reachable u v) :
    graphDistance G l u v=graphDistance G l v u := by
  have hb {u v : V} (hc : G.Reachable u v) : graphDistance G l v u ≤ graphDistance G l u v := by
    obtain ⟨p,he,_⟩ := distance_eq_length hl hc
    rw [he,← length_reverse hs p.val]
    exact distance_le_walk hl p.val.reverse
  exact le_antisymm (hb hc.symm) (hb hc)

lemma distance_triangle [Fintype V] (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    graphDistance G l u w ≤ graphDistance G l u v+graphDistance G l v w := by
  obtain ⟨p,hp,_⟩ := distance_eq_length hl huv
  obtain ⟨q,hq,_⟩ := distance_eq_length hl hvw
  rw [hp,hq,← length_append]
  exact distance_le_walk hl (p.val.append q.val)

lemma distance_eq_zero [Fintype V] (hl : ∀ u v, G.Adj u v → 0 < l u v)
    {u v : V} (hc : G.Reachable u v) : graphDistance G l u v=0 ↔ u=v := by
  constructor
  · intro hz
    obtain ⟨p,he,_⟩ := distance_eq_length (fun u v h => (hl u v h).le) hc
    have hp := (length_eq_zero_iff hl p.val).mp (he.symm.trans hz)
    exact hp.eq
  · rintro rfl
    exact distance_self (fun u v h => (hl u v h).le) u

/-- The exact source graph metric, on the original vertex type. -/
@[instance_reducible] noncomputable def metricSpace [Fintype V] (hc : G.Connected)
    (hs : ∀ u v, l u v=l v u) (hl : ∀ u v, G.Adj u v → 0 < l u v) : MetricSpace V where
  dist := graphDistance G l
  dist_self := distance_self (fun u v h => (hl u v h).le)
  dist_comm u v := distance_symm (fun u v h => (hl u v h).le) hs (hc.preconnected u v)
  dist_triangle u v w := distance_triangle (fun u v h => (hl u v h).le)
    (hc.preconnected u v) (hc.preconnected v w)
  eq_of_dist_eq_zero h := (distance_eq_zero hl (hc.preconnected _ _)).mp h

lemma edge_bound (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (h : G.Adj u v) : graphDistance G l u v ≤ l u v := by
  simpa only [walkLength,add_zero] using distance_le_walk hl (.cons h .nil)

lemma height_edge [Fintype V] (hc : G.Connected)
    (hs : ∀ u v, l u v=l v u) (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    (o : V) {u v : V} (h : G.Adj u v) :
    |graphDistance G l o u-graphDistance G l o v| ≤ l u v := by
  apply abs_le.mpr
  have h₁ := distance_triangle hl (hc.preconnected o u) (hc.preconnected u v)
  have h₂ := distance_triangle hl (hc.preconnected o v) (hc.preconnected v u)
  have h₃ := edge_bound hl h
  have h₄ := edge_bound hl h.symm
  rw [hs v u] at h₄
  constructor <;> linarith

/-- Each non-root vertex has a strictly lower predecessor on a genuine
weighted shortest path. This is the input to the shortest-path spanning tree
in ; positivity, not integral weights, supplies the descent. -/
lemma exists_predecessor [Fintype V] (hc : G.Connected)
    (hs : ∀ u v, l u v=l v u) (hl : ∀ u v, G.Adj u v → 0 < l u v)
    (o v : V) (hv : v ≠ o) : ∃ u, G.Adj u v ∧
      graphDistance G l o v=graphDistance G l o u+l u v ∧
      graphDistance G l o u < graphDistance G l o v := by
  have hn : ∀ u v, G.Adj u v → 0 ≤ l u v := fun u v h => (hl u v h).le
  obtain ⟨p,he,hp⟩ := distance_eq_length hn (hc.preconnected v o)
  cases hw : p.val with
  | nil => exact (hv rfl).elim
  | @cons v u o h q =>
    have htail : graphDistance G l u o=walkLength l q := by
      apply le_antisymm (distance_le_walk hn q)
      obtain ⟨r,hr,_⟩ := distance_eq_length hn (hc.preconnected u o)
      have hb := hp (.cons h r.val)
      rw [hw] at hb
      simp only [walkLength] at hb
      rw [hr]
      linarith
    have heq : graphDistance G l o v=graphDistance G l o u+l u v := by
      rw [distance_symm hn hs (hc.preconnected o v),he,hw,walkLength,
        ← htail,distance_symm hn hs (hc.preconnected u o),hs v u]
      ring
    exact ⟨u,h.symm,heq,by linarith [hl v u h,hs v u]⟩

end Weighted
end PlanarL1



end

section

/-! ## Shortest-path spanning tree . -/

namespace PlanarL1.Weighted
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}

/-- A predecessor system whose heights strictly decrease to its root. The
well-foundedness here uses finiteness, not any discretization of real lengths. -/
structure DescendingParents (V : Type*) where
  root : V
  height : V → ℝ
  parent : V → V
  at_root : parent root=root
  descent : ∀ v, v ≠ root → height (parent v)<height v

namespace DescendingParents
variable (D : DescendingParents V)

omit [Fintype V] in
lemma parent_ne (v : V) (hv : v ≠ D.root) : D.parent v ≠ v := by
  intro he
  have h := D.descent v hv
  rw [he] at h
  exact lt_irrefl _ h

noncomputable def graph : SimpleGraph V where
  Adj u v := (u ≠ D.root ∧ D.parent u=v) ∨ (v ≠ D.root ∧ D.parent v=u)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro v h
    rcases h with h | h <;> exact D.parent_ne v h.1 h.2⟩

omit [Fintype V] in
lemma child_adj (v : V) (hv : v ≠ D.root) : D.graph.Adj v (D.parent v) :=
  Or.inl ⟨hv,rfl⟩

lemma wellFounded : WellFounded (fun u v : V => D.height u<D.height v) := by
  let : IsTrans V (fun u v => D.height u<D.height v) := ⟨fun _ _ _ => lt_trans⟩
  let : Std.Irrefl (fun u v => D.height u<D.height v) := ⟨fun _ => lt_irrefl _⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

lemma reachable_root (v : V) : D.graph.Reachable v D.root := by
  induction v using D.wellFounded.induction with
  | h v ih =>
    by_cases hv : v=D.root
    · rw [hv]
    · exact (D.child_adj v hv).reachable.trans (ih (D.parent v) (D.descent v hv))

lemma connected : D.graph.Connected := by
  let : Nonempty V := ⟨D.root⟩
  exact ⟨fun u v => (D.reachable_root u).trans (D.reachable_root v).symm⟩

omit [Fintype V] in
lemma edge_injective : Set.InjOn (fun v => s(v,D.parent v)) ({D.root}ᶜ : Set V) := by
  intro u hu v hv he
  rcases Sym2.eq_iff.mp he with h | h
  · exact h.1
  · have hu' : u ≠ D.root := hu
    have hv' : v ≠ D.root := hv
    have hd₁ := D.descent u hu'
    have hd₂ := D.descent v hv'
    rw [h.2] at hd₁
    rw [← h.1] at hd₂
    exact False.elim ((not_lt_of_gt hd₁) hd₂)

lemma edgeFinset_eq : D.graph.edgeFinset = (Finset.univ.erase D.root).image
    (fun v => s(v,D.parent v)) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simp only [graph,Finset.mem_image,Finset.mem_erase,Finset.mem_univ,and_true,Sym2.eq_iff]
    constructor
    · rintro (⟨hu,he⟩ | ⟨hv,he⟩)
      · exact ⟨u,hu,Or.inl ⟨rfl,he⟩⟩
      · exact ⟨v,hv,Or.inr ⟨rfl,he⟩⟩
    · rintro ⟨w,hw,(⟨rfl,he⟩ | ⟨rfl,he⟩)⟩
      · exact Or.inl ⟨hw,he⟩
      · exact Or.inr ⟨hw,he⟩

lemma isTree : D.graph.IsTree := by
  classical
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨D.connected,?_⟩
  rw [Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card,D.edgeFinset_eq]
  rw [Finset.card_image_iff.mpr (by
    intro u hu v hv he
    exact D.edge_injective (Finset.mem_erase.mp hu).1 (Finset.mem_erase.mp hv).1 he)]
  rw [Finset.card_erase_add_one (Finset.mem_univ _),Finset.card_univ,Nat.card_eq_fintype_card]
end DescendingParents

noncomputable def shortestParents (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
    (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V) : DescendingParents V where
  root := o
  height := graphDistance G l o
  parent v := if hv : v=o then o else (exists_predecessor hc hs hl o v hv).choose
  at_root := by simp
  descent v hv := by
    rw [dite_eq_right hv]
    exact (exists_predecessor hc hs hl o v hv).choose_spec.2.2

namespace shortestParents
variable (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

lemma parent_step (v : V) (hv : v ≠ o) :
    G.Adj ((shortestParents hc hs hl o).parent v) v ∧
    graphDistance G l o v = graphDistance G l o ((shortestParents hc hs hl o).parent v)+
      l ((shortestParents hc hs hl o).parent v) v := by
  dsimp only [shortestParents]
  rw [dite_eq_right hv]
  exact ⟨(exists_predecessor hc hs hl o v hv).choose_spec.1,
    (exists_predecessor hc hs hl o v hv).choose_spec.2.1⟩

lemma graph_le : (shortestParents hc hs hl o).graph ≤ G := by
  intro u v h
  rcases h with ⟨hu,rfl⟩ | ⟨hv,rfl⟩
  · exact (parent_step hc hs hl o u hu).1.symm
  · exact (parent_step hc hs hl o v hv).1

lemma exists_root_walk (v : V) :
    ∃ p : (shortestParents hc hs hl o).graph.Walk o v,
      walkLength l p=graphDistance G l o v := by
  let D := shortestParents hc hs hl o
  induction v using D.wellFounded.induction with
  | h v ih =>
    by_cases hv : v=o
    · subst v
      exact ⟨.nil,(distance_self (fun u v h => (hl u v h).le) o).symm⟩
    · obtain ⟨p,hp⟩ := ih (D.parent v) (D.descent v hv)
      refine ⟨p.append (.cons (D.child_adj v hv).symm .nil),?_⟩
      rw [length_append,hp]
      simpa only [walkLength,add_zero] using (parent_step hc hs hl o v hv).2.symm

/-- The shortest-path spanning tree in : every root path has the
original weighted distance. No planarity or unit edge lengths is used. -/
lemma root_distance (v : V) :
    graphDistance (shortestParents hc hs hl o).graph l o v=graphDistance G l o v := by
  let D := shortestParents hc hs hl o
  have hn : ∀ u v, D.graph.Adj u v → 0 ≤ l u v :=
    fun u v h => (hl u v (graph_le hc hs hl o h)).le
  obtain ⟨p,hp⟩ := exists_root_walk hc hs hl o v
  apply le_antisymm
  · exact (distance_le_walk hn p).trans_eq hp
  · obtain ⟨q,hq,_⟩ := distance_eq_length hn (D.connected.preconnected o v)
    rw [hq]
    have hlen {u v : V} (q : D.graph.Walk u v) :
        walkLength l (q.mapLe (graph_le hc hs hl o))=walkLength l q := by
      induction q with
      | nil => rfl
      | cons h q ih => simpa only [Walk.mapLe,Walk.map,walkLength,SimpleGraph.Hom.ofLE_apply] using congrArg (l _ _ + ·) ih
    rw [← hlen q.val]
    exact distance_le_walk (fun u v h => (hl u v h).le) _
end shortestParents
end PlanarL1.Weighted



end

end OAI
