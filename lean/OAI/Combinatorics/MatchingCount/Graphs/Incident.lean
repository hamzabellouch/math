import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.HoleStrength

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open Finset

variable {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]

omit [Fintype V] [LinearOrder E] in
lemma totalDeletionCharge_eq_blocks [Fintype V] [LinearOrder E]
    (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (B Hu Hv lam : E → ℝ) (d : E → HoleBlocks (4*p)) :
    totalDeletionCharge u v p B Hu Hv lam d =
      ∏ e, blockCharge p (B e) (Hu e) (Hv e) (lam e) (d e) := by
  classical
  simp only [totalDeletionCharge,neutralPairs,consumedPairs,
    List.flatMap_def,List.map_flatten,List.prod_flatten,List.map_map,Function.comp_def,
    List.map_append,List.prod_append]
  simp only [neutralCharge,consumedCharge,ite_true,(huv _).symm,ite_false]
  simp only [Finset.prod_map_toList,blockCharge,Finset.prod_mul_distrib]
  ring

theorem deletionConstant_eq_charge (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 0 < B e) (hlam : ∀ e, 0 < lam e)
    (R₀ : Finset V) (U : E → Finset (Fin (4*p))) (b : E → Selection (4*p))
    (hb : FamilyHoles u v (4*p) R₀ U b)
    (d : E → HoleBlocks (4*p)) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hpar : ∀ e, (d e).Parity) :
    deletionConstant U b (pathActivity p B Hu Hv lam) (fun e => pathConstant p (B e) (Hu e) (Hv e)) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * totalDeletionCharge u v p B Hu Hv lam d := by
  rw [totalDeletionCharge_eq_blocks u v huv,← Finset.prod_mul_distrib]
  unfold deletionConstant
  apply Finset.prod_congr rfl
  intro e _
  exact forcing_weight_charge p (B e) (Hu e) (Hv e) (lam e) (hB e) (hlam e)
    (U e) (b e) (hb.1 e) (d e) (he e) (hpar e)

theorem real_partition_charge_identity (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 0 < B e) (hlam : ∀ e, 0 < lam e)
    (R₀ : Finset V) (U : E → Finset (Fin (4*p))) (b : E → Selection (4*p))
    (hb : FamilyHoles u v (4*p) R₀ U b)
    (d : E → HoleBlocks (4*p)) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hpar : ∀ e, (d e).Parity) :
    realHolePartition u v (4*p) R₀ U (pathActivity p B Hu Hv lam) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * totalDeletionCharge u v p B Hu Hv lam d *
      logicalHolePartition u v (residualHoles u v R₀ U b) (broken U) lam := by
  classical
  have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
    u v R₀ U b hb (pathActivity p B Hu Hv lam)
    (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
    (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) lam
    (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (lam e))
  simp only [List.prod_reverse,List.prod_ofFn] at hid
  change realHolePartition _ _ _ _ _ _ =
    deletionConstant U b (pathActivity p B Hu Hv lam)
      (fun e => pathConstant p (B e) (Hu e) (Hv e)) * _ at hid
  rw [hid,deletionConstant_eq_charge u v huv p B Hu Hv lam hB hlam R₀ U b hb d he hpar]

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.Representation

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.Enlargement
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

abbrev Incident (e : LogicalEdge V) (x : V) := source e=x ∨ target e=x

noncomputable def other (e : LogicalEdge V) (x : V) : V :=
  if source e=x then target e else source e

omit [Fintype V] in
@[simp] lemma other_source (e : LogicalEdge V) : other e (source e)=target e := by simp [other]
@[simp] lemma other_target (e : LogicalEdge V) : other e (target e)=source e := by
  simp [other,source_ne_target e]

lemma other_incident (e : LogicalEdge V) (x : V) (hx : Incident e x) :
    Incident e (other e x) := by
  rcases hx with rfl | rfl <;> simp only [other_source,other_target] <;> tauto

lemma other_ne (e : LogicalEdge V) (x : V) (hx : Incident e x) : other e x ≠ x := by
  rcases hx with rfl | rfl <;> simp [source_ne_target e,(source_ne_target e).symm]

lemma other_other (e : LogicalEdge V) (x : V) (hx : Incident e x) :
    other e (other e x)=x := by rcases hx with rfl | rfl <;> simp

lemma edge_eq_of_inc_other {e f : LogicalEdge V} (h : Incident f (source e))
    (ho : other f (source e)=target e) : f=e := by
  rcases h with h | h
  · have ht : target f=target e := by simpa only [← h,other_source] using ho
    exact Subtype.ext (Prod.ext h ht)
  · have hs : source f=target e := by simpa only [← h,other_target] using ho
    have hf := f.property
    have he := e.property
    change source f < target f at hf
    change source e < target e at he
    rw [hs,h] at hf
    exact False.elim ((lt_asymm he hf))

variable (R : Finset V) (s : LogicalEdge V → Bool)
    (hs : LogicalHoles source target R ∅ s)

include hs in
omit [Fintype V] in
lemma selected_not_hole [Fintype V] (e : LogicalEdge V) (he : s e=true) (x : V) (hx : Incident e x) :
    x ∉ R := by
  intro hxR
  exact hs.2.1 x hxR e ⟨he,hx⟩

noncomputable def chosen (x : V) (hx : x ∉ R) : LogicalEdge V :=
  (hs.2.2 x hx).exists.choose

omit [Fintype V] in
lemma chosen_spec [Fintype V] (x : V) (hx : x ∉ R) :
    s (chosen R s hs x hx)=true ∧ Incident (chosen R s hs x hx) x :=
  (hs.2.2 x hx).exists.choose_spec

lemma chosen_eq (x : V) (hx : x ∉ R) (e : LogicalEdge V)
    (he : s e=true) (hi : Incident e x) : chosen R s hs x hx=e := by
  exact (hs.2.2 x hx).unique (chosen_spec R s hs x hx) ⟨he,hi⟩

noncomputable def mateFun (x : V) : V :=
  if h : x ∈ R then x else other (chosen R s hs x h) x

omit [Fintype V] in
lemma mateFun_hole [Fintype V] (x : V) (hx : x ∈ R) : mateFun R s hs x=x := by simp [mateFun,hx]

lemma mateFun_selected (e : LogicalEdge V) (he : s e=true) (x : V) (hx : Incident e x) :
    mateFun R s hs x=other e x := by
  have hn := selected_not_hole R s hs e he x hx
  simp only [mateFun,dite_eq_right hn]
  rw [chosen_eq R s hs x hn e he hx]

lemma mateFun_involutive : Function.Involutive (mateFun R s hs) := by
  intro x
  by_cases hx : x ∈ R
  · rw [mateFun_hole R s hs x hx,mateFun_hole R s hs x hx]
  · let e := chosen R s hs x hx
    have he := chosen_spec R s hs x hx
    have hx' : mateFun R s hs x=other e x := mateFun_selected R s hs e he.1 x he.2
    rw [hx',mateFun_selected R s hs e he.1 _ (other_incident e x he.2),other_other e x he.2]

noncomputable def asMate : Mate V := ⟨mateFun R s hs,mateFun_involutive R s hs⟩

lemma asMate_holes : HasHoles (asMate R s hs) R := by
  intro x
  change mateFun R s hs x=x ↔ x ∈ R
  by_cases hx : x ∈ R
  · simp [hx,mateFun_hole R s hs x hx]
  · simp only [hx,iff_false]
    change mateFun R s hs x ≠ x
    rw [mateFun_selected R s hs _ (chosen_spec R s hs x hx).1 x (chosen_spec R s hs x hx).2]
    exact other_ne _ x (chosen_spec R s hs x hx).2

lemma asMate_selected (e : LogicalEdge V) :
    (asMate R s hs).val (source e)=target e ↔ s e=true := by
  constructor
  · intro hm
    have hx : source e ∉ R := by
      intro hx
      have hh := mateFun_hole R s hs _ hx
      change mateFun R s hs (source e)=target e at hm
      exact source_ne_target e (hh.symm.trans hm)
    let f := chosen R s hs (source e) hx
    have hf := chosen_spec R s hs (source e) hx
    have ho : other f (source e)=target e := by
      rw [← mateFun_selected R s hs f hf.1 _ hf.2]
      exact hm
    have hfe : f=e := edge_eq_of_inc_other hf.2 ho
    exact hfe ▸ hf.1
  · intro he
    exact (mateFun_selected R s hs e he (source e) (Or.inl rfl)).trans (other_source e)

variable {R s hs}

noncomputable def select (m : Mate V) (e : LogicalEdge V) : Bool :=
  decide (m.val (source e)=target e)

omit [Fintype V] in
@[simp] lemma select_eq_true [Fintype V] (m : Mate V) (e : LogicalEdge V) :
    select m e=true ↔ m.val (source e)=target e := by simp [select]

lemma select_mate_other (m : Mate V) (e : LogicalEdge V)
    (he : select m e=true) (x : V) (hx : Incident e x) : m.val x=other e x := by
  have ht := (select_eq_true m e).mp he
  rcases hx with rfl | rfl
  · simpa only [other_source] using ht
  · simp only [other_target]
    rw [← ht,mate_mate]

lemma edge_eq_of_selected_inc (m : Mate V) {e f : LogicalEdge V}
    (he : select m e=true) (hf : select m f=true)
    (x : V) (hex : Incident e x) (hfx : Incident f x) : e=f := by
  have hh : other e x=other f x := (select_mate_other m e he x hex).symm.trans
    (select_mate_other m f hf x hfx)
  rcases hex with rfl | rfl
  · exact (edge_eq_of_inc_other hfx (hh.symm.trans (other_source e))).symm
  · have hy : Incident f (source e) := by
      rw [other_target] at hh
      rw [hh]
      exact other_incident f _ hfx
    apply (edge_eq_of_inc_other hy ?_).symm
    rw [other_target] at hh
    rw [hh,other_other f _ hfx]

lemma select_holes (m : Mate V) (hm : HasHoles m R) :
    LogicalHoles source target R ∅ (select m) := by
  classical
  refine ⟨by simp,?_,?_⟩
  · intro x hx e he
    have hh := select_mate_other m e he.1 x he.2
    rw [(hm x).mpr hx] at hh
    exact other_ne e x he.2 hh.symm
  · intro x hx
    have hmx : m.val x ≠ x := fun h => hx ((hm x).mp h)
    have hex : ∃ e : LogicalEdge V, select m e=true ∧ Incident e x := by
      rcases lt_or_gt_of_ne hmx.symm with h | h
      · exact ⟨⟨(x,m.val x),h⟩,by simp [select,source,target],Or.inl rfl⟩
      · exact ⟨⟨(m.val x,x),h⟩,by simp [select,source,target],Or.inr rfl⟩
    obtain ⟨e,he⟩ := hex
    refine ⟨e,he,?_⟩
    intro f hf
    exact edge_eq_of_selected_inc m hf.1 he.1 x hf.2 he.2

@[simp] lemma select_asMate : select (asMate R s hs)=s := by
  funext e
  apply Bool.eq_iff_iff.mpr
  exact (select_eq_true _ e).trans (asMate_selected R s hs e)

lemma asMate_select (m : Mate V) (hm : HasHoles m R) :
    asMate R (select m) (select_holes m hm)=m := by
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ R
  · exact (mateFun_hole R _ _ x hx).trans ((hm x).mpr hx).symm
  · let h := select_holes m hm
    let e := chosen R (select m) h x hx
    have he := chosen_spec R (select m) h x hx
    exact (mateFun_selected R _ h e he.1 x he.2).trans
      (select_mate_other m e he.1 x he.2).symm

noncomputable def matchingEquiv (R : Finset V) :
    {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s} ≃
    {m : Mate V // HasHoles m R} where
  toFun s := ⟨asMate R s.val s.property,asMate_holes R s.val s.property⟩
  invFun m := ⟨select m.val,select_holes m.val m.property⟩
  left_inv _selection := Subtype.ext select_asMate
  right_inv m := Subtype.ext (asMate_select m.val m.property)

lemma selection_weight (w : V → V → ℝ) (m : Mate V) :
    (∏ e : LogicalEdge V, if select m e then logicalActivity w e else 1)=weight w m := by
  classical
  unfold weight
  rw [← Finset.prod_filter,← Finset.prod_filter]
  apply Finset.prod_bij (fun e _ => source e)
  · intro e he
    have hh := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hh]
    exact e.property
  · intro e he f hf h
    have he' := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    have hf' := (select_eq_true m f).mp (Finset.mem_filter.mp hf).2
    exact Subtype.ext (Prod.ext h (he'.symm.trans ((congrArg m.val h).trans hf')))
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    refine ⟨⟨(x,m.val x),hx'⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [select,source,target]⟩
  · intro e he
    have he' := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    simp only [logicalActivity,edgeActivity,show source e < target e from e.property,ite_true,he']

lemma asMate_weight (w : V → V → ℝ) :
    (∏ e : LogicalEdge V, if s e then logicalActivity w e else 1)=weight w (asMate R s hs) := by
  rw [← selection_weight,select_asMate]

theorem logical_partition_eq (w : V → V → ℝ) (R : Finset V) :
    logicalHolePartition source target R ∅ (logicalActivity w)=partition w R := by
  classical
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s}
  let := Fintype.ofFinite {m : Mate V // HasHoles m R}
  unfold logicalHolePartition partition
  rw [Finset.sum_subtype (matchings R) (fun m => mem_matchings m R)]
  apply Fintype.sum_equiv (matchingEquiv R)
  intro s
  exact asMate_weight w

theorem logical_partition_forbidden_le (w : V → V → ℝ) (hw : ∀ a b, 0 ≤ w a b)
    (R : Finset V) (forbidden : Finset (LogicalEdge V)) :
    logicalHolePartition source target R forbidden (logicalActivity w) ≤ partition w R := by
  classical
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R forbidden s}
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s}
  rw [← logical_partition_eq]
  unfold logicalHolePartition
  let f : {s : LogicalEdge V → Bool // LogicalHoles source target R forbidden s} →
      {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s} :=
    fun s => ⟨s.val,⟨by simp,s.property.2⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg
      (fun z : {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s} => z.val) hab)
  let g := fun s : {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s} =>
    ∏ e, if s.val e then logicalActivity w e else 1
  calc
    _ = ∑ y ∈ Finset.univ.image f, g y := by
      rw [Finset.sum_image hf.injOn]
    _ ≤ ∑ y, g y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro s _ _
      apply Finset.prod_nonneg
      intro e _
      split_ifs
      · unfold logicalActivity edgeActivity
        split_ifs <;> exact hw _ _
      · norm_num

end MatchingFPRAS.Representation

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Representation
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma pathConstant_pos (p : ℕ) (B Hu Hv : ℝ) (hB : 0 < B) :
    0 < pathConstant p B Hu Hv := by
  apply mul_pos <;> apply Finset.prod_pos <;> intro i hi <;> exact hB.trans_le (le_max_left _ _)

lemma intact_family (p : ℕ) (m : Mate V) (hm : HasHoles m ∅) :
    FamilyHoles source target (4*p) ∅ (fun _ => ∅)
      (fun e i => alternating (select m e) i.val) := by
  have hs := select_holes m hm
  refine ⟨fun e => alternating_valid _ _,by simp,?_⟩
  intro x hx
  have hi (e : LogicalEdge V) :
      Uses source target (fun (e : LogicalEdge V) (i : Fin (4*p+1)) => alternating (select m e) i.val) e x ↔
        select m e=true ∧ Incident e x := by
    rw [intact_uses (show Even (4*p) from ⟨2*p,by omega⟩) source target _ e x
      (alternating_valid _ _)]
    simp only [Fin.val_zero,alternating,Nat.zero_mod,ite_true]
  simpa only [hi] using hs.2.2 x hx

theorem intact_partition_identity (w : V → V → ℝ) (hz : 0 < partition w ∅)
    (p : ℕ) (B Hu Hv : LogicalEdge V → ℝ) :
    realHolePartition source target (4*p) ∅ (fun _ => ∅)
      (pathActivity p B Hu Hv (logicalActivity w)) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * partition w ∅ := by
  classical
  have hn : (matchings (∅ : Finset V)).Nonempty := by
    by_contra hn
    have hz0 : partition w ∅=0 := by
      simp [partition,Finset.not_nonempty_iff_eq_empty.mp hn]
    linarith
  obtain ⟨m,hm⟩ := hn
  let b := fun (e : LogicalEdge V) (i : Fin (4*p+1)) => alternating (select m e) i.val
  have hb := intact_family p m ((mem_matchings m ∅).mp hm)
  have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
    source target ∅ (fun _ => ∅) b hb (pathActivity p B Hu Hv (logicalActivity w))
    (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
    (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) _
    (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (logicalActivity w e))
  simpa [residualHoles,broken,deletionConstant,List.prod_ofFn,pathConstant,
    logical_partition_eq] using hid

theorem lifted_hole_bound_feasible (hn : 2 ≤ Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ a b, 0 < w a b) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/4 ≤ rowMax hn w a) (hrhi : ∀ a, rowMax hn w a ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (Hu Hv : LogicalEdge V → ℝ)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e)
    (R₀ : Finset V) (U : LogicalEdge V → Finset (Fin (4*p)))
    (b : LogicalEdge V → Selection (4*p)) (hb : FamilyHoles source target (4*p) R₀ U b)
    (hH : Even (enlargedHoles (4*p) R₀ U).card) :
    realHolePartition source target (4*p) R₀ U
        (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)) /
      realHolePartition source target (4*p) ∅ (fun _ => ∅)
        (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)) *
      pairingCapacity (realBottleneck source target p
        (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w))
        (enlargedHoles (4*p) R₀ U) hH ≤
      2 * holeScale V ^ ((enlargedHoles (4*p) R₀ U).card/2) := by
  classical
  choose d he hpar using (fun e => hole_blocks_exist (hb.1 e))
  let B := fun e : LogicalEdge V => bottleneck w (source e) (target e)
  let R := residualHoles source target R₀ U b
  let F := totalDeletionCharge source target p B Hu Hv (logicalActivity w) d
  let C := ∏ e, pathConstant p (B e) (Hu e) (Hv e)
  let Zf := logicalHolePartition source target R (broken U) (logicalActivity w)
  have hB : ∀ e, 0 < B e := fun e => lt_of_lt_of_le zero_lt_one (one_le_bottleneck _ _ _)
  have hlam : ∀ e, 0 < logicalActivity w e := by
    intro e
    unfold logicalActivity edgeActivity
    split_ifs <;> exact hw _ _
  have hC : 0 < C := Finset.prod_pos (fun e _ => pathConstant_pos p _ _ _ (hB e))
  have htrace := deletion_charge_trace source target source_ne_target p hp B Hu Hv (logicalActivity w)
    (fun e => one_le_bottleneck w _ _) hHu hHv (fun e => (hlam e).le)
    (fun e => edgeActivity_le_bottleneck w _ _ (source_ne_target e)) R₀ U b hb d he hpar
  have hF : 0 ≤ F := htrace.factor_nonneg
  have hcard : R.card ≤ (enlargedHoles (4*p) R₀ U).card := by
    simpa using htrace.card_le
  obtain ⟨hR,hcap⟩ := deletion_capacity_bound w hw p hp Hu Hv hHu hHv R₀ U b hb d he hpar hH
  have hZf : 0 ≤ Zf := by
    unfold Zf logicalHolePartition
    apply Finset.sum_nonneg
    intro s _
    apply Finset.prod_nonneg
    intro e _
    split_ifs <;> first | exact (hlam e).le | norm_num
  have hZf_le : Zf ≤ partition w R := logical_partition_forbidden_le w (fun a b => (hw a b).le) R _
  rw [real_partition_charge_identity source target source_ne_target p B Hu Hv (logicalActivity w)
    hB hlam R₀ U b hb d he hpar,intact_partition_identity w hz p B Hu Hv]
  change (C * F * Zf) / (C * partition w ∅) * _ ≤ _
  calc
    _ = (Zf / partition w ∅) * (pairingCapacity (realBottleneck source target p B Hu Hv (logicalActivity w))
      (enlargedHoles (4*p) R₀ U) hH * F) := by field_simp [hC.ne',hz.ne']; ring
    _ ≤ (Zf / partition w ∅) * pairingCapacity (bottleneck w) R hR :=
      mul_le_mul_of_nonneg_left hcap (div_nonneg hZf hz.le)
    _ ≤ (partition w R / partition w ∅) * pairingCapacity (bottleneck w) R hR :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hZf_le hz.le)
        (pairingCapacity_nonneg _ (fun a b => zero_le_one.trans (one_le_bottleneck w a b)) R hR)
    _ ≤ 2 * holeScale V ^ (R.card/2) := logical_hole_bound hn w (fun a b => (hw a b).le) hz hrlo hrhi R hR
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pow_le_pow_right₀ _ (Nat.div_le_div_right hcard)
      unfold holeScale
      have hN : (1:ℝ) ≤ (Fintype.card V : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) (Fintype.card V); linarith
      have hp4 := one_le_pow₀ hN (n := 4)
      linarith

theorem lifted_hole_bound (hn : 2 ≤ Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ a b, 0 < w a b) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/4 ≤ rowMax hn w a) (hrhi : ∀ a, rowMax hn w a ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (Hu Hv : LogicalEdge V → ℝ)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e)
    (R₀ : Finset V) (U : LogicalEdge V → Finset (Fin (4*p)))
    (hH : Even (enlargedHoles (4*p) R₀ U).card) :
    realHolePartition source target (4*p) R₀ U
        (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)) /
      realHolePartition source target (4*p) ∅ (fun _ => ∅)
        (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)) *
      pairingCapacity (realBottleneck source target p
        (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w))
        (enlargedHoles (4*p) R₀ U) hH ≤
      2 * holeScale V ^ ((enlargedHoles (4*p) R₀ U).card/2) := by
  classical
  by_cases h : ∃ b, FamilyHoles source target (4*p) R₀ U b
  · obtain ⟨b,hb⟩ := h
    exact lifted_hole_bound_feasible hn w hw hz hrlo hrhi p hp Hu Hv hHu hHv R₀ U b hb hH
  · have hempty : IsEmpty {b : LogicalEdge V → Selection (4*p) //
        FamilyHoles source target (4*p) R₀ U b} := ⟨fun b => h ⟨b.val,b.property⟩⟩
    have hzero : realHolePartition source target (4*p) R₀ U
        (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w)) = 0 := by
      let := hempty
      unfold realHolePartition
      exact Finset.sum_eq_zero (fun b _ => isEmptyElim b)
    rw [hzero,zero_div,zero_mul]
    unfold holeScale
    positivity

end MatchingFPRAS.Enlargement

end OAI
