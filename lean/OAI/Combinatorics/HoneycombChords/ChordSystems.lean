import OAI.Combinatorics.HoneycombChords.BoundarySystems
import OAI.Combinatorics.HoneycombChords.ArchContinuation

namespace OAI

/-! Chord systems for critical honeycomb strips.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations

lemma BoundaryChord.first_edge {W H : ℕ} (c : BoundaryChord W H) : c.path.edge 0=c.source.wire :=
  ofChord_first_edge c.chord c.distinct
lemma BoundaryChord.last_edge {W H : ℕ} (c : BoundaryChord W H) :
    c.path.edge (Fin.last c.chord.val.length)=c.target.wire := ofChord_last_edge c.chord c.distinct

lemma SelectedSystem.source_selected {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs)
    {c : BoundaryChord W H} (hc : c∈cs) : assignmentSpins x c.source.wire≠1 := by
  apply (h.edge_union _).mpr
  exact ⟨c,hc,⟨0,c.first_edge⟩⟩
lemma SelectedSystem.target_selected {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs)
    {c : BoundaryChord W H} (hc : c∈cs) : assignmentSpins x c.target.wire≠1 := by
  apply (h.edge_union _).mpr
  exact ⟨c,hc,⟨Fin.last c.chord.val.length,c.last_edge⟩⟩

lemma SelectedSystem.sources_nodup {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs) : (cs.map BoundaryChord.source).Nodup := by
  induction h with
  | nil => simp
  | cons x c cs hs hn hr ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hm
    obtain ⟨d,hd,he⟩:=List.mem_map.mp hm
    have hp:=hr.source_selected hd
    rw [he,←c.first_edge,eraseAssignment_spins,CenterPath.erase,ite_eq_left (Set.mem_range_self 0)] at hp
    exact hp rfl

lemma SelectedSystem.length_le_width {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs)
    (hw : ∀ j,assignmentSpins x (westPort W H j).wire=1)
    (he : ∀ j,assignmentSpins x (eastPort W H j).wire=1) : cs.length≤2*(W+1) := by
  classical
  let bs := Finset.univ.image (southPort W H)
  let ts := Finset.univ.image (northPort W H)
  have hsub : (cs.map BoundaryChord.source).toFinset⊆bs∪ts := by
    intro a ha
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
    have hs:=h.source_selected hc
    rcases port_exhaustive c.source with ⟨i,hh⟩|⟨i,hh⟩|⟨i,hh⟩|⟨i,hh⟩
    · exact (hs (hh ▸ hw i)).elim
    · exact (hs (hh ▸ he i)).elim
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hh.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hh.symm⟩)
  have hc:=(Finset.card_mono hsub).trans (Finset.card_union_le _ _)
  have hb : bs.card≤W+1 := (Finset.card_image_le).trans_eq (by simp)
  have ht : ts.card≤W+1 := (Finset.card_image_le).trans_eq (by simp)
  rw [List.toFinset_card_of_nodup h.sources_nodup,List.length_map] at hc
  omega
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations

noncomputable def BoundaryChord.code {W H : ℕ} (c : BoundaryChord W H) :=
  (c.source,c.target,restrictAssignment (W:=W+1) (H:=H+1) c.path.spins)
lemma BoundaryChord.spins_restrict {W H : ℕ} (c : BoundaryChord W H) :
    assignmentSpins (restrictAssignment (W:=W+1) (H:=H+1) c.path.spins)=c.path.spins :=
  path_spins_restrict c.path (chord_length_pos c.chord) (ofChord_center_mem c.chord c.distinct)
lemma BoundaryChord.code_injective (W H : ℕ) : Function.Injective (BoundaryChord.code (W:=W) (H:=H)) := by
  rintro ⟨a,b,hab,γ⟩ ⟨a',b',hab',δ⟩ he
  have ha:=congrArg Prod.fst he
  change a=a' at ha
  subst a'
  have hb:=congrArg (fun z=>z.2.1) he
  change b=b' at hb
  subst b'
  have he':=congrArg (fun z=>assignmentSpins z.2.2) he
  rw [BoundaryChord.code,BoundaryChord.code] at he'
  change assignmentSpins (restrictAssignment (ofChord γ hab).spins)=
    assignmentSpins (restrictAssignment (ofChord δ hab').spins) at he'
  rw [show assignmentSpins (restrictAssignment (ofChord γ hab).spins)=(ofChord γ hab).spins from
    (⟨a,b,hab,γ⟩ : BoundaryChord W H).spins_restrict,
    show assignmentSpins (restrictAssignment (ofChord δ hab').spins)=(ofChord δ hab').spins from
    (⟨a,b,hab',δ⟩ : BoundaryChord W H).spins_restrict] at he'
  have hγ:=chord_eq_of_selected_eq γ δ hab (congrArg selected he')
  subst δ
  rfl
noncomputable instance boundaryChordFintype (W H : ℕ) : Fintype (BoundaryChord W H) :=
  Fintype.ofInjective BoundaryChord.code (BoundaryChord.code_injective W H)

def EndPort {W H : ℕ} (p : Port (domain (W+1) (H+1) : Set Center)) : Prop :=
  (∃ i,p=southPort W H i) ∨ (∃ i,p=northPort W H i)
def HardChord (W H : ℕ) := {c : BoundaryChord W H // EndPort c.source ∧ EndPort c.target}
noncomputable instance hardChordFintype (W H : ℕ) : Fintype (HardChord W H) := by
  classical
  unfold HardChord
  infer_instance
noncomputable def singleSystemMass (W H : ℕ) : ℝ := ∑ c : HardChord W H,kappa^c.val.chord.val.length

lemma endPort_of_selected {W H : ℕ} {x : Assignment (W+1) (H+1)}
    (hw : ∀ j,assignmentSpins x (westPort W H j).wire=1)
    (he : ∀ j,assignmentSpins x (eastPort W H j).wire=1)
    {a : Port (domain (W+1) (H+1) : Set Center)} (ha : assignmentSpins x a.wire≠1) : EndPort a := by
  rcases port_exhaustive a with ⟨i,hh⟩|⟨i,hh⟩|⟨i,hh⟩|⟨i,hh⟩
  · exact (ha (hh ▸ hw i)).elim
  · exact (ha (hh ▸ he i)).elim
  · exact Or.inl ⟨i,hh⟩
  · exact Or.inr ⟨i,hh⟩
lemma SelectedSystem.hard_endpoints {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs)
    (hw : ∀ j,assignmentSpins x (westPort W H j).wire=1)
    (he : ∀ j,assignmentSpins x (eastPort W H j).wire=1)
    {c : BoundaryChord W H} (hc : c∈cs) : EndPort c.source ∧ EndPort c.target :=
  ⟨endPort_of_selected hw he (h.source_selected hc),endPort_of_selected hw he (h.target_selected hc)⟩
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation

lemma endPort_inside_injective {W H : ℕ} {a b : Port (domain (W+1) (H+1) : Set Center)}
    (ha : EndPort a) (hb : EndPort b) (he : a.inside=b.inside) : a=b := by
  rcases ha with ⟨i,rfl⟩|⟨i,rfl⟩ <;> rcases hb with ⟨j,rfl⟩|⟨j,rfl⟩ <;>
    simp only [southPort,northPort,cellCenter,up,down,Prod.mk.injEq,Bool.true_eq_false,
      Bool.false_eq_true,and_false,and_true] at he
  all_goals first
    | exact he.elim
    | have he' : i=j := by apply Fin.ext;omega
      subst j;rfl
lemma HardChord.trace_injective (W H : ℕ) :
    Function.Injective (fun c : HardChord W H=>c.val.chord.val) := by
  intro c d he
  have hs : c.val.source=d.val.source := endPort_inside_injective c.property.1 d.property.1
    (Option.some.inj (c.val.chord.property.2.1.symm.trans ((congrArg List.head? he).trans d.val.chord.property.2.1)))
  have ht : c.val.target=d.val.target := endPort_inside_injective c.property.2 d.property.2
    (Option.some.inj (c.val.chord.property.2.2.symm.trans ((congrArg List.getLast? he).trans d.val.chord.property.2.2)))
  apply Subtype.ext
  rcases c with ⟨⟨a,b,hab,γ⟩,hc⟩
  rcases d with ⟨⟨a',b',hab',δ⟩,hd⟩
  dsimp at hs ht he
  subst a';subst b'
  have hh : γ=δ:=Subtype.ext he
  subst δ
  rfl

lemma boundaryChord_to_halfRect {W H : ℕ} (c : BoundaryChord W H) :
    IsTrace (halfRect (W+1)) c.chord.val := by
  refine ⟨c.chord.property.1.1,c.chord.property.1.2.1,?_⟩
  intro v hv
  obtain ⟨hx,hW,hy,hH⟩:=domain_coord_bounds (c.chord.property.1.2.2 v hv)
  exact ⟨hx,hW,hy⟩
noncomputable def bottomArchOf {W H : ℕ} (c : BoundaryChord W H) (i j : Fin (W+1))
    (hs : c.source=southPort W H i) (ht : c.target=southPort W H j) : BottomArch W i j :=
  ⟨c.chord.val,boundaryChord_to_halfRect c,by simpa only [hs,southPort,cellCenter,up,Fin.val_zero,Nat.cast_zero] using c.chord.property.2.1,
    by simpa only [ht,southPort,cellCenter,up,Fin.val_zero,Nat.cast_zero] using c.chord.property.2.2⟩
lemma bottomEnds_distinct {W H : ℕ} (c : BoundaryChord W H) (i j : Fin (W+1))
    (hs : c.source=southPort W H i) (ht : c.target=southPort W H j) : i≠j := by
  intro hh;apply c.distinct;rw [hs,ht,hh]

lemma topTurn_involution (W H : ℕ) (v : Center) : topTurn W H (topTurn W H v)=v := by
  rcases v with ⟨i,j,b⟩
  simp [topTurn]
lemma topTurn_trace {W H : ℕ} (c : BoundaryChord W H) :
    IsTrace (halfRect (W+1)) (c.chord.val.map (topTurn W H)) := by
  refine ⟨c.chord.property.1.1.map (topTurn_injective W H),?_,?_⟩
  · apply (List.isChain_map _).mpr
    exact c.chord.property.1.2.1.imp (fun v w h=>(topTurn_adj W H v w).mpr h)
  · intro v hv
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
    obtain ⟨hx,hW,hy,hH⟩:=domain_coord_bounds (c.chord.property.1.2.2 w hw)
    change 0≤(W:ℤ)-w.1 ∧ (W:ℤ)-w.1<(W+1:ℕ) ∧ 0≤(H:ℤ)-w.2.1
    omega
lemma topTurn_north (W H : ℕ) (i : Fin (W+1)) :
    topTurn W H (northPort W H i).inside=up i.rev.val 0 := by
  simp [topTurn,northPort,cellCenter,up,Fin.rev]
  omega
noncomputable def topArchOf {W H : ℕ} (c : BoundaryChord W H) (i j : Fin (W+1))
    (hs : c.source=northPort W H i) (ht : c.target=northPort W H j) : BottomArch W i.rev j.rev :=
  ⟨c.chord.val.map (topTurn W H),topTurn_trace c,by
    rw [List.head?_map,c.chord.property.2.1,hs];simp only [Option.map_some,topTurn_north],by
    rw [List.getLast?_map,c.chord.property.2.2,ht];simp only [Option.map_some,topTurn_north]⟩
lemma topEnds_distinct {W H : ℕ} (c : BoundaryChord W H) (i j : Fin (W+1))
    (hs : c.source=northPort W H i) (ht : c.target=northPort W H j) : i.rev≠j.rev := by
  intro hh
  have hij : i=j := by simpa using congrArg Fin.rev hh
  apply c.distinct;rw [hs,ht,hij]

lemma boundaryChord_to_rect {W H : ℕ} (c : BoundaryChord W H) :
    IsTrace (rect (W+1) (H+1)) c.chord.val := by
  refine ⟨c.chord.property.1.1,c.chord.property.1.2.1,?_⟩
  intro v hv
  exact domain_coord_bounds (c.chord.property.1.2.2 v hv)

noncomputable def upBridgeOf {W H : ℕ} (c : BoundaryChord W H) (i j : Fin (W+1))
    (hs : c.source=southPort W H i) (ht : c.target=northPort W H j) : RectBridge W H i :=
  ⟨c.chord.val,boundaryChord_to_rect c,by simpa only [hs,southPort,cellCenter,up,Fin.val_zero,Nat.cast_zero] using c.chord.property.2.1,
    ⟨j,by simpa only [ht,northPort,cellCenter,down,Fin.val_last] using c.chord.property.2.2⟩⟩
noncomputable def downBridgeOf {W H : ℕ} (c : BoundaryChord W H) (i j : Fin (W+1))
    (hs : c.source=northPort W H i) (ht : c.target=southPort W H j) : RectBridge W H j :=
  ⟨c.chord.val.reverse,⟨List.nodup_reverse.mpr c.chord.property.1.1,
    reverse_chain c.chord.property.1.2.1,by
    intro v hv;exact domain_coord_bounds (c.chord.property.1.2.2 v (List.mem_reverse.mp hv))⟩,by
    simpa only [List.head?_reverse,ht,southPort,cellCenter,up,Fin.val_zero,Nat.cast_zero] using c.chord.property.2.2,
    ⟨i,by simpa only [List.getLast?_reverse,hs,northPort,cellCenter,down,Fin.val_last] using c.chord.property.2.1⟩⟩

abbrev ArchPool (W : ℕ) := Σ a : ArchEnds W,BottomArch W a.first a.last
abbrev BridgePool (W H : ℕ) := Σ i : Fin (W+1),RectBridge W H i
abbrev OnePathPool (W H : ℕ) := (ArchPool W ⊕ ArchPool W) ⊕ (BridgePool W H ⊕ BridgePool W H)

noncomputable def HardChord.encode {W H : ℕ} (c : HardChord W H) : OnePathPool W H := by
  classical
  exact if hs : ∃ i,c.val.source=southPort W H i then
    if ht : ∃ j,c.val.target=southPort W H j then
      .inl (.inl ⟨⟨hs.choose,ht.choose,bottomEnds_distinct c.val _ _ hs.choose_spec ht.choose_spec⟩,
        bottomArchOf c.val _ _ hs.choose_spec ht.choose_spec⟩)
    else
      let hnt := c.property.2.resolve_left ht
      .inr (.inl ⟨hs.choose,upBridgeOf c.val _ _ hs.choose_spec hnt.choose_spec⟩)
    else
      let hns := c.property.1.resolve_left hs
      if ht : ∃ j,c.val.target=southPort W H j then
        .inr (.inr ⟨ht.choose,downBridgeOf c.val _ _ hns.choose_spec ht.choose_spec⟩)
      else
        let hnt := c.property.2.resolve_left ht
        .inl (.inr ⟨⟨hns.choose.rev,hnt.choose.rev,
          topEnds_distinct c.val _ _ hns.choose_spec hnt.choose_spec⟩,
          topArchOf c.val _ _ hns.choose_spec hnt.choose_spec⟩)

noncomputable def poolTrace {W H : ℕ} : OnePathPool W H→List Center
  | .inl (.inl a)=>a.2.val
  | .inl (.inr a)=>a.2.val
  | .inr (.inl a)=>a.2.val
  | .inr (.inr a)=>a.2.val
noncomputable def recoverTrace {W H : ℕ} : OnePathPool W H→List Center
  | .inl (.inl a)=>a.2.val
  | .inl (.inr a)=>a.2.val.map (topTurn W H)
  | .inr (.inl a)=>a.2.val
  | .inr (.inr a)=>a.2.val.reverse
lemma HardChord.recover_encode {W H : ℕ} (c : HardChord W H) : recoverTrace c.encode=c.val.chord.val := by
  classical
  unfold HardChord.encode
  split_ifs <;> simp only [recoverTrace,bottomArchOf,topArchOf,upBridgeOf,downBridgeOf,
    List.map_map,List.reverse_reverse]
  have hh : topTurn W H ∘ topTurn W H = id := funext (topTurn_involution W H)
  rw [hh,List.map_id]
lemma HardChord.encode_injective (W H : ℕ) : Function.Injective (HardChord.encode (W:=W) (H:=H)) := by
  intro c d he
  apply HardChord.trace_injective W H
  change c.val.chord.val=d.val.chord.val
  exact c.recover_encode.symm.trans ((congrArg recoverTrace he).trans d.recover_encode)
lemma HardChord.encode_length {W H : ℕ} (c : HardChord W H) : (poolTrace c.encode).length=c.val.chord.val.length := by
  classical
  unfold HardChord.encode
  split_ifs <;> simp [poolTrace,bottomArchOf,topArchOf,upBridgeOf,downBridgeOf]
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open Filter Topology

noncomputable instance archEndsFintype (W : ℕ) : Fintype (ArchEnds W) :=
  Fintype.ofInjective (fun a : ArchEnds W=>(a.first,a.last)) (by
    rintro ⟨i,j,h⟩ ⟨i',j',h'⟩ he
    obtain ⟨rfl,rfl⟩:=Prod.mk.inj he
    rfl)

noncomputable def archPoolWeight {W : ℕ} (a : ArchPool W) : ℝ := kappa^a.2.val.length
noncomputable def bridgePoolWeight {W H : ℕ} (a : BridgePool W H) : ℝ := kappa^a.2.val.length
noncomputable def poolWeight {W H : ℕ} (a : OnePathPool W H) : ℝ := kappa^(poolTrace a).length
noncomputable def archPoolMass (W : ℕ) : ℝ := ∑' a : ArchPool W,archPoolWeight a
noncomputable def bridgePoolMass (W H : ℕ) : ℝ := ∑ a : BridgePool W H,bridgePoolWeight a
noncomputable def poolMass (W H : ℕ) : ℝ := ∑' a : OnePathPool W H,poolWeight a

lemma archPool_summable (W : ℕ) : Summable (archPoolWeight (W:=W)) := by
  apply summable_sigma_of_nonneg (fun a=>(pow_pos kappa_positive _).le) |>.mpr
  refine ⟨?_,?_⟩
  · intro a;exact bottom_arch_summable a.distinct
  · exact (hasSum_fintype _).summable
lemma pool_hasSum (W H : ℕ) : HasSum (poolWeight (W:=W) (H:=H))
    ((archPoolMass W+archPoolMass W)+(bridgePoolMass W H+bridgePoolMass W H)) := by
  apply HasSum.sum
  · apply HasSum.sum
    · exact (archPool_summable W).hasSum
    · exact (archPool_summable W).hasSum
  · apply HasSum.sum
    · exact hasSum_fintype _
    · exact hasSum_fintype _
lemma pool_summable (W H : ℕ) : Summable (poolWeight (W:=W) (H:=H)) :=
  (pool_hasSum W H).summable
lemma poolWeight_nonnegative {W H : ℕ} (a : OnePathPool W H) : 0≤poolWeight a :=
  (pow_pos kappa_positive _).le
lemma bridgePoolMass_eq (W H : ℕ) : bridgePoolMass W H=∑ i : Fin (W+1),crossingMass W H i := by
  rw [bridgePoolMass,Fintype.sum_sigma]
  rfl
lemma poolMass_eq (W H : ℕ) : poolMass W H=2*archPoolMass W+2*bridgePoolMass W H := by
  change (∑' a : OnePathPool W H,poolWeight a)=_
  rw [(pool_hasSum W H).tsum_eq]
  ring
lemma bridgePoolMass_limit (W : ℕ) : Tendsto (bridgePoolMass W) atTop (𝓝 0) := by
  change Tendsto (fun H=>bridgePoolMass W H) atTop (𝓝 0)
  simp_rw [bridgePoolMass_eq]
  have hh:=tendsto_finsetSum Finset.univ (fun i hi=>crossing_tendsto_zero W i)
  simpa using hh
lemma poolMass_limit (W : ℕ) : Tendsto (poolMass W) atTop (𝓝 (2*archPoolMass W)) := by
  change Tendsto (fun H=>poolMass W H) atTop (𝓝 (2*archPoolMass W))
  simp_rw [poolMass_eq]
  simpa using tendsto_const_nhds.add ((bridgePoolMass_limit W).const_mul 2)

lemma singleSystemMass_le (W H : ℕ) : singleSystemMass W H≤poolMass W H := by
  classical
  calc
    _ = ∑ c : HardChord W H,poolWeight c.encode := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [poolWeight,c.encode_length]
    _ = ∑ a∈Finset.univ.image (HardChord.encode (W:=W) (H:=H)),poolWeight a :=
      (Finset.sum_image (HardChord.encode_injective W H).injOn).symm
    _ ≤ _ := (pool_summable W H).sum_le_tsum _ (fun a ha=>poolWeight_nonnegative a)
end CriticalHoneycomb.Transfer.RasterGrid

end

end OAI
