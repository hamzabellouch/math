import OAI.Combinatorics.VariableWL.Coordinates

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.Subcubic
open VariableWL.Affine VariableWL.Blocks VariableWL.PrefixParts VariableWL.PrefixParts.Wiring
open VariableWL.BlockCoordinates
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} [Fintype P] [Fintype E]
  (J : ProductImages.Instance r P E) [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)] [FiniteNumbering (Block (n := n) J)] (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
  [FiniteNumbering (SortTag (data (n := n) J hr hn marked))]

noncomputable abbrev Vertex (ε : Bit) := UncoloredVertex (data (n := n) J hr hn marked) ε
noncomputable abbrev graph (ε : Bit) := uncolored (data (n := n) J hr hn marked) (wiring J hr hn marked) ε
noncomputable abbrev finiteGraph (ε : Bit) := TypedGame.numbered (graph J hr hn marked ε)

noncomputable def translation (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) :
    Vertex J hr hn marked 0 ≃ Vertex J hr hn marked 1 :=
  uncoloredTranslation (data J hr hn marked) (encodeList J hr hn marked ξ)

noncomputable def numberedTranslation (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) :
    Fin (finiteGraph J hr hn marked 0).order ≃ Fin (finiteGraph J hr hn marked 1).order :=
  (Fintype.equivFin _).symm.trans ((translation J hr hn marked ξ).trans (Fintype.equivFin _))

noncomputable def numberedPart (v : Fin (finiteGraph J hr hn marked 0).order) : Block (n := n) J :=
  ((Fintype.equivFin (Vertex J hr hn marked 0)).symm v).owner.1

theorem numberedTranslation_local (ξ η : ∀ b : Block (n := n) J, Valuation J marked 1 b)
    (v : Fin (finiteGraph J hr hn marked 0).order)
    (h : ξ (numberedPart J hr hn marked v)=η (numberedPart J hr hn marked v)) :
    numberedTranslation J hr hn marked ξ v=numberedTranslation J hr hn marked η v := by
  apply congrArg (Fintype.equivFin (Vertex J hr hn marked 1))
  apply uncoloredTranslation_local
  exact congrArg (valuationEquiv J hr hn marked _ 1) h

theorem winning_of_witness (hr3 : 3 ≤ r) (hlarge : r+1 < n+1) (Q : J.Witness) :
    Game.Winning (fun _ : Fin (r+1) => none :
      Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) (r+1)) := by
  classical
  apply Game.winning_of_block_families (numberedPart J hr hn marked)
    (numberedTranslation J hr hn marked) (numberedTranslation_local J hr hn marked)
    (GlobalPool J marked hr3 hn Q)
  · exact globalPool_nonempty J marked hr3 hn hlarge Q ∅ (by simp)
  · exact globalPool_down J marked hr3 hn hlarge Q
  · exact globalPool_extend J marked hr3 hn hlarge Q
  · intro U ξ hξ v w hv hw
    let x := (Fintype.equivFin (Vertex J hr hn marked 0)).symm v
    let y := (Fintype.equivFin (Vertex J hr hn marked 0)).symm w
    have hag : General.Agree J marked ⟨x.owner.1,ξ x.owner.1⟩ ⟨y.owner.1,ξ y.owner.1⟩ := by
      intro a ha hb
      exact offsetLists_agree J hr3 hn marked Q U hξ ⟨x.owner.1,hv⟩ ⟨y.owner.1,hw⟩ a ha hb
    have hh := (uncoloredTranslation_adj (data J hr hn marked) (wiring J hr hn marked)
      (encodeList J hr hn marked ξ) x y (compatible_of_agree J hr hn marked ξ hag)).symm
    change (graph J hr hn marked 0).Adj x y ↔
      (graph J hr hn marked 1).Adj
        ((Fintype.equivFin (Vertex J hr hn marked 1)).symm
          ((Fintype.equivFin (Vertex J hr hn marked 1)) (translation J hr hn marked ξ x)))
        ((Fintype.equivFin (Vertex J hr hn marked 1)).symm
          ((Fintype.equivFin (Vertex J hr hn marked 1)) (translation J hr hn marked ξ y)))
    simpa only [Equiv.symm_apply_apply,graph,translation] using hh

end VariableWL.Subcubic

namespace VariableWL.Subcubic
open VariableWL.Affine VariableWL.Blocks VariableWL.PrefixParts VariableWL.PrefixParts.Wiring
open VariableWL.BlockCoordinates
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} [Fintype P] [Fintype E]
  (J : ProductImages.Instance r P E) [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)] [FiniteNumbering (Block (n := n) J)] (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
  [FiniteNumbering (SortTag (data (n := n) J hr hn marked))]

abbrev Response (b : Block (n := n) J) := Valuation J marked 1 b × Fin 3

noncomputable def zeroQuery (b : Block (n := n) J) : Fin (finiteGraph J hr hn marked 0).order :=
  Fintype.equivFin _ (Wiring.query (data J hr hn marked) b)

noncomputable def valuationQuery (b : Block (n := n) J) (z : Response J marked b) :
    Fin (finiteGraph J hr hn marked 1).order :=
  Fintype.equivFin _ (Wiring.response (data J hr hn marked)
    ⟨b,valuationEquiv J hr hn marked b 1 z.1,z.2⟩)

theorem valuationQuery_injective (b : Block (n := n) J) :
    Function.Injective (valuationQuery J hr hn marked b) := by
  intro z w he
  have h0 := (Fintype.equivFin (Vertex J hr hn marked 1)).injective he
  have ho := congrArg SubcubicRealization.Vertex.owner h0
  have hv := eq_of_heq (Sigma.mk.inj_iff.mp ho).2
  have hz : valuationEquiv J hr hn marked b 1 z.1=valuationEquiv J hr hn marked b 1 w.1 :=
    congrArg Prod.snd (Sum.inl.inj (Sum.inr.inj hv))
  have hp : z.2=w.2 := congrArg SubcubicRealization.Vertex.port h0
  exact Prod.ext ((valuationEquiv J hr hn marked b 1).injective hz) hp

theorem decode_winning {q : ℕ}
    {p : Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) q}
    (hp : Game.Winning p) :
    TypedGame.Winning (graph J hr hn marked 0) (graph J hr hn marked 1) (TypedGame.decode p) := by
  change Game.Winning (G := finiteGraph J hr hn marked 0)
    (H := finiteGraph J hr hn marked 1) (TypedGame.encode (TypedGame.decode p))
  rw [TypedGame.encode_decode]
  exact hp

theorem zeroQuery_recognized {q : ℕ} (hq : 3 ≤ q)
    {p : Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) q}
    (hp : Game.Winning p) {i : Fin q} {b : Block (n := n) J} {w : Fin (finiteGraph J hr hn marked 1).order}
    (hi : p i=some (zeroQuery J hr hn marked b,w)) :
    ∃ z : Response J marked b, w=valuationQuery J hr hn marked b z := by
  have hi' : TypedGame.decode p i=some (Wiring.query (data J hr hn marked) b,
      (Fintype.equivFin (Vertex J hr hn marked 1)).symm w) := by
    simp only [TypedGame.decode,hi,Option.map_some,zeroQuery,Equiv.symm_apply_apply]
  obtain ⟨z,hz⟩ := winning_query_recognized (data J hr hn marked) (wiring J hr hn marked)
    hq (decode_winning J hr hn marked hp) hi'
  refine ⟨((valuationEquiv J hr hn marked b 1).symm z.1,z.2),?_⟩
  apply (Fintype.equivFin (Vertex J hr hn marked 1)).symm.injective
  simpa only [valuationQuery,Equiv.symm_apply_apply,Equiv.apply_symm_apply] using hz

theorem zeroQuery_agree {q : ℕ} (hq : 3 ≤ q)
    {p : Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) q}
    (hp : Game.Winning p) {i j : Fin q} {b c : Block (n := n) J}
    {z : Response J marked b} {w : Response J marked c}
    (hi : p i=some (zeroQuery J hr hn marked b,valuationQuery J hr hn marked b z))
    (hj : p j=some (zeroQuery J hr hn marked c,valuationQuery J hr hn marked c w)) :
    General.Agree J marked ⟨b,z.1⟩ ⟨c,w.1⟩ := by
  intro a hb hc
  by_cases hbc : b=c
  · subst c
    have hzw := valuationQuery_injective J hr hn marked b ((hp.partialIso i j _ _ hi hj).1.mp rfl)
    exact congrArg (fun t : Response J marked b => readout J t.1.val hb) hzw
  · have hi' : TypedGame.decode p i=some (Wiring.query (data J hr hn marked) b,
        Wiring.response (data J hr hn marked) ⟨b,valuationEquiv J hr hn marked b 1 z.1,z.2⟩) := by
      simp only [TypedGame.decode,hi,Option.map_some,zeroQuery,valuationQuery,Equiv.symm_apply_apply]
    have hj' : TypedGame.decode p j=some (Wiring.query (data J hr hn marked) c,
        Wiring.response (data J hr hn marked) ⟨c,valuationEquiv J hr hn marked c 1 w.1,w.2⟩) := by
      simp only [TypedGame.decode,hj,Option.map_some,zeroQuery,valuationQuery,Equiv.symm_apply_apply]
    let d : Proper J b := ⟨⟨c,Ne.symm hbc⟩,a,hb,hc⟩
    let e : Proper J c := ⟨⟨b,hbc⟩,a,hc,hb⟩
    have test := winning_readout (data J hr hn marked) (wiring J hr hn marked)
      hq (decode_winning J hr hn marked hp) (channelEquiv J hr hn marked ⟨b,d⟩)
    rw [mate_channel] at test
    have he := test (valuationEquiv J hr hn marked b 1 z.1,z.2)
      (valuationEquiv J hr hn marked c 1 w.1,w.2) hi' hj'
    change pad (Data.truncate ((data J hr hn marked b).root (properNumber J b d).val)
      ((valuationEquiv J hr hn marked b 1 z.1).val ∘
        (data J hr hn marked b).order (properNumber J b d).val)) =
      pad (Data.truncate ((data J hr hn marked c).root (properNumber J c e).val)
      ((valuationEquiv J hr hn marked c 1 w.1).val ∘
        (data J hr hn marked c).order (properNumber J c e).val)) at he
    rw [data_prefix,data_prefix] at he
    exact (readoutEquiv J a).injective (pad_injective he)

end VariableWL.Subcubic

namespace VariableWL.Subcubic
open VariableWL.Affine VariableWL.Blocks VariableWL.PrefixParts VariableWL.PrefixParts.Wiring
open VariableWL.BlockCoordinates
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} [Fintype P] [Fintype E]
  (J : ProductImages.Instance r P E) [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)] [FiniteNumbering (Block (n := n) J)] (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
  [FiniteNumbering (SortTag (data (n := n) J hr hn marked))]

noncomputable def attainedRings
    (hwin : Game.Winning (fun _ : Fin (r+1) => none :
      Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) (r+1))) :
    RingSystem J marked (n := n) := by
  let query := zeroQuery J hr hn marked
  let response := fun v : Σ b : Block (n := n) J, Response J marked b =>
    valuationQuery J hr hn marked v.1 v.2
  let decode := fun (b : Block (n := n) J) (z : Response J marked b) => z.1
  have recognize : ∀ p : Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) (r+1),
      Game.Winning p → ∀ i b w, p i=some (query b,w) → ∃ z : Response J marked b, w=response ⟨b,z⟩ :=
    fun p hp i b w hi => zeroQuery_recognized J hr hn marked (by omega) hp hi
  have agreement : ∀ p : Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) (r+1),
      Game.Winning p → ∀ i j v w, p i=some (query v.1,response v) → p j=some (query w.1,response w) →
        General.Agree J marked (Game.decodeSigma decode v) (Game.decodeSigma decode w) := by
    intro p hp i j v w hi hj
    exact zeroQuery_agree J hr hn marked (by omega) hp hi hj
  exact {
    lists := Game.RingLists query response decode
    nonempty := Game.ringLists_nonempty query response decode recognize hwin
    compatible := fun b y hy i j => Game.ringLists_compatible query response decode (General.Agree J marked) agreement hy i j
    transfer := fun b y hy c => Game.ringLists_transfer query response decode recognize (General.Agree J marked) agreement hy c }

theorem consistent_of_winning
    (hwin : Game.Winning (fun _ : Fin (r+1) => none :
      Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) (r+1))) :
    J.Consistent := ⟨extractedWitness J marked hr hn (attainedRings J hr hn marked hwin)⟩

omit [Fintype P] [Fintype E] in
include marked in
theorem block_nonempty [Nonempty P] : Nonempty (Block (n := n) J) := by
  obtain ⟨p⟩ := ‹Nonempty P›
  exact ⟨siteRing (n := n) J (.inl p) (realAddress J p (fun _ => false)) marked⟩

theorem positive_order [Nonempty P] (ε : Bit) : 0 < (finiteGraph J hr hn marked ε).order := by
  classical
  let : Nonempty (Block (n := n) J) := block_nonempty J marked
  obtain ⟨b⟩ := ‹Nonempty (Block (n := n) J)›
  exact Fintype.card_pos_iff.mpr ⟨SubcubicRealization.Vertex.triangle (anchor (data J hr hn marked) ε b) 0⟩

theorem connected [Nonempty P] (ε : Bit) : (finiteGraph J hr hn marked ε).graph.Connected := by
  let : Nonempty (Block (n := n) J) := block_nonempty J marked
  exact (TypedGame.numbering (graph J hr hn marked ε)).connected_iff.mp
    (uncolored_connected (data J hr hn marked) (wiring J hr hn marked) ε)

theorem degree_le_three (ε : Bit) : VariableWL.Subcubic (finiteGraph J hr hn marked ε) := by
  classical
  intro v
  let e := TypedGame.numbering (graph J hr hn marked ε)
  have h := uncolored_subcubic (data J hr hn marked) (wiring J hr hn marked) ε (e.symm v)
  have he : (graph J hr hn marked ε).degree (e.symm v)=
      (finiteGraph J hr hn marked ε).graph.degree v := by
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr (e.symm.mapNeighborSet v).symm
  exact he ▸ h

theorem equal_order : (finiteGraph J hr hn marked 0).order=(finiteGraph J hr hn marked 1).order :=
  Wiring.equal_order (data J hr hn marked)

theorem promise [Nonempty P] :
    0 < (finiteGraph J hr hn marked 0).order ∧
    (finiteGraph J hr hn marked 0).order=(finiteGraph J hr hn marked 1).order ∧
    (finiteGraph J hr hn marked 0).graph.Connected ∧
    (finiteGraph J hr hn marked 1).graph.Connected ∧
    VariableWL.Subcubic (finiteGraph J hr hn marked 0) ∧
    VariableWL.Subcubic (finiteGraph J hr hn marked 1) :=
  ⟨positive_order J hr hn marked 0,equal_order J hr hn marked,
    connected J hr hn marked 0,connected J hr hn marked 1,
    degree_le_three J hr hn marked 0,degree_le_three J hr hn marked 1⟩

theorem equivalent_iff_consistent [Nonempty P] (hr3 : 3 ≤ r) (hlarge : r+1 < n+1) :
    Equivalent (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) r ↔ J.Consistent := by
  rw [Game.equivalent_iff_winning hr (positive_order J hr hn marked 0)]
  exact ⟨consistent_of_winning J hr hn marked,
    fun ⟨Q⟩ => winning_of_witness J hr hn marked hr3 hlarge Q⟩

end VariableWL.Subcubic

end OAI
