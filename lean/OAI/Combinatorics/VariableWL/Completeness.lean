import OAI.Combinatorics.VariableWL.MachineCellular

namespace OAI

universe uVariable1 uVariable2

namespace VariableWL.AffineCatalog
open Blocks BlockCoordinates Descriptor VariableWL.Affine
attribute [local instance] Classical.propDecidable
namespace Data
 def resign (D : Data) (ε : Bit) : Data := {D with epsilon:=ε.val}
 noncomputable def descriptor (D : Data) (ε : Bit) : Descriptor.Data :=
   (D.resign ε).core.toPrefix.portData.expanded
end Data
theorem sortPredicate_congr {X Y : PrefixDescriptor.Data}
    (hv : X.validBlock=Y.validBlock) (hc : X.channelBound=Y.channelBound)
    (hd : X.dimension=Y.dimension) (hch : X.channels=Y.channels)
    (hr : X.root=Y.root) : X.sortPredicate=Y.sortPredicate := by
  cases X
  cases Y
  dsimp only at hv hc hd hch hr
  cases hv
  cases hc
  cases hd
  cases hch
  cases hr
  rfl
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} [Fintype P] [Fintype E]
variable (PP : Presentation P) (PE : Presentation E) (J : ProductImages.Instance r P E)
variable (hr : 2≤r) (hn : 0<n) (marked : Fin r) {D : Data} {ε₀ : Bit}
variable (h : Good (n := n) PP PE J marked ε₀ D)
omit [Fintype P] [Fintype E] in
include h in
 theorem resign_good (ε : Bit) : Good (n := n) PP PE J marked ε (D.resign ε) := by
  exact ⟨h.toGood,h.realDimension,h.leftForm,h.rightForm,h.leftConstant,h.rightConstant,h.marked,rfl⟩
noncomputable def blockPresentation := BlockCatalog.block PP PE J h.toGood
noncomputable def readPresentation := BlockCatalog.readout (r := r) (n := n) PP PE
omit [Fintype P] [Fintype E] in
theorem coordinateBound : ∀b : Block (n := n) J,
    Fintype.card (BlockCoordinates.Coordinate J b.val)≤6 :=
  fun b => RealizationSize.coordinate_card J b.val
omit [Fintype P] [Fintype E] in
include h in
 theorem core_resign_good (ε : Bit) :
    BlockDescriptor.Good J hr hn marked (blockPresentation PP PE J marked h)
      (readPresentation (r := r) (n := n) PP PE) (coordinateBound (n := n) J) ε (D.resign ε).core :=
    core_good PP PE J marked ε (resign_good PP PE J marked h ε) hr hn
@[instance_reducible] noncomputable def properNumbering : ∀b : Block (n := n) J, FiniteNumbering (Proper J b) :=
  BlockDescriptor.properNumberings J hr hn marked (blockPresentation PP PE J marked h)
    (readPresentation (r := r) (n := n) PP PE) (coordinateBound (n := n) J) 0
    (core_resign_good PP PE J hr hn marked h 0)
include h in
 theorem properNumbering_eq (ε : Bit) :
    BlockDescriptor.properNumberings J hr hn marked (blockPresentation PP PE J marked h)
      (readPresentation (r := r) (n := n) PP PE) (coordinateBound (n := n) J) ε
      (core_resign_good PP PE J hr hn marked h ε)=properNumbering PP PE J hr hn marked h := rfl
include h in
 theorem prefix_resign_good (ε : Bit) :
    let _ := properNumbering PP PE J hr hn marked h
    PrefixDescriptor.Good (blockPresentation PP PE J marked h) (data J hr hn marked)
      (coordinateBound (n := n) J) ε (D.resign ε).core.toPrefix := by
  have ht := BlockDescriptor.prefix_good J hr hn marked (blockPresentation PP PE J marked h)
    (readPresentation (r := r) (n := n) PP PE) (coordinateBound (n := n) J) ε
    (core_resign_good PP PE J hr hn marked h ε)
  rw [properNumbering_eq PP PE J hr hn marked h ε] at ht
  exact ht
include h in
 theorem matching_resign_good (ε : Bit) :
    let _ := properNumbering PP PE J hr hn marked h
    PrefixDescriptor.MatchingGood (blockPresentation PP PE J marked h) (data J hr hn marked)
      (D.resign ε).core.toPrefix (wiring J hr hn marked) := by
  have ht := BlockDescriptor.matching_good J hr hn marked (blockPresentation PP PE J marked h)
    (readPresentation (r := r) (n := n) PP PE) (coordinateBound (n := n) J) ε
    (core_resign_good PP PE J hr hn marked h ε)
  rw [properNumbering_eq PP PE J hr hn marked h ε] at ht
  exact ht
include hr hn h in
 theorem descriptor_sound (ε : Bit) : (D.descriptor ε).Sound := by
  let : ∀b : Block (n := n) J,FiniteNumbering (Proper J b) := properNumbering PP PE J hr hn marked h
  exact Descriptor.PortData.sound_expanded _
    (PrefixDescriptor.port_sound (blockPresentation PP PE J marked h) (data J hr hn marked)
      (coordinateBound (n := n) J) ε (prefix_resign_good PP PE J hr hn marked h ε)
      (wiring J hr hn marked) (matching_resign_good PP PE J hr hn marked h ε))
noncomputable def sortPresentation :
    let _ := properNumbering PP PE J hr hn marked h
    Presentation (PrefixParts.Wiring.SortTag (data J hr hn marked)) := by
  letI : ∀b : Block (n := n) J,FiniteNumbering (Proper J b) := properNumbering PP PE J hr hn marked h
  exact Classical.choose (PrefixDescriptor.sortPresentation (blockPresentation PP PE J marked h)
    (data J hr hn marked) (coordinateBound (n := n) J) 0 (prefix_resign_good PP PE J hr hn marked h 0))
 theorem core_proper_resign (ε : Bit) :
    (D.resign ε).core.proper=(D.resign 0).core.proper := by
  funext b i
  rfl
 theorem core_channels_resign (ε : Bit) :
    (D.resign ε).core.channels=(D.resign 0).core.channels := by
  funext b
  simp only [BlockDescriptor.Core.channels,core_proper_resign]
  rfl
 theorem core_dimension_resign (ε : Bit) :
    (D.resign ε).core.dimension=(D.resign 0).core.dimension := by
  funext b
  rfl
 theorem core_readDimension_resign (ε : Bit) :
    (D.resign ε).core.readDimension=(D.resign 0).core.readDimension := by
  funext b
  rfl
 theorem core_root_resign (ε : Bit) :
    (D.resign ε).core.root=(D.resign 0).core.root := by
  funext b c
  simp only [BlockDescriptor.Core.root,BlockDescriptor.Core.readout,
    BlockDescriptor.Core.select,core_readDimension_resign,core_proper_resign]
  rfl
 theorem prefix_channelBound_resign (ε : Bit) :
    (D.resign ε).core.toPrefix.channelBound=(D.resign 0).core.toPrefix.channelBound := by
  simp only [BlockDescriptor.Core.toPrefix,BlockDescriptor.Core.channelBound,
    BlockDescriptor.Core.properBound,Data.core,Data.resign]
 theorem prefix_sortPredicate_resign (ε : Bit) :
    (D.resign ε).core.toPrefix.sortPredicate=(D.resign 0).core.toPrefix.sortPredicate := by
  exact sortPredicate_congr (X := (D.resign ε).core.toPrefix)
    (Y := (D.resign 0).core.toPrefix) rfl (prefix_channelBound_resign (D := D) ε)
    (core_dimension_resign (D := D) ε)
    (core_channels_resign (D := D) ε) (core_root_resign (D := D) ε)
 theorem prefix_tag_resign (ε : Bit) :
    (D.resign ε).core.toPrefix.tag=(D.resign 0).core.toPrefix.tag := by
  funext x
  simp only [PrefixDescriptor.Data.tag,BlockDescriptor.Core.toPrefix,
    BlockDescriptor.Core.channelBound,BlockDescriptor.Core.properBound,Data.core,Data.resign]
include h in
 theorem sort_spec :
    let _ := properNumbering PP PE J hr hn marked h
    let S := sortPresentation PP PE J hr hn marked h
    let X := (D.resign 0).core.toPrefix
    S.bound=X.sortBound ∧ S.valid=X.sortPredicate ∧
      ∀s,S.encode s=X.tag (PrefixDescriptor.sortRaw (blockPresentation PP PE J marked h) (data J hr hn marked) s) := by
  let : ∀b : Block (n := n) J,FiniteNumbering (Proper J b) := properNumbering PP PE J hr hn marked h
  exact Classical.choose_spec (PrefixDescriptor.sortPresentation (blockPresentation PP PE J marked h)
    (data J hr hn marked) (coordinateBound (n := n) J) 0 (prefix_resign_good PP PE J hr hn marked h 0))
include h in
 theorem sort_valid (ε : Bit) :
    (sortPresentation PP PE J hr hn marked h).valid=(D.resign ε).core.toPrefix.sortPredicate := by
  rw [prefix_sortPredicate_resign]
  exact (sort_spec PP PE J hr hn marked h).2.1
include h in
 theorem sort_encode (ε : Bit) :
    let _ := properNumbering PP PE J hr hn marked h
    ∀s,(sortPresentation PP PE J hr hn marked h).encode s=
      (D.resign ε).core.toPrefix.tag (PrefixDescriptor.sortRaw (blockPresentation PP PE J marked h) (data J hr hn marked) s) := by
  intro _ s
  rw [prefix_tag_resign]
  exact (sort_spec PP PE J hr hn marked h).2.2 s
noncomputable def descriptor_iso (ε : Bit) :
    let _ := properNumbering PP PE J hr hn marked h
    let _ : FiniteNumbering (Block (n := n) J) := (blockPresentation PP PE J marked h).numbering
    let _ : FiniteNumbering (PrefixParts.Wiring.SortTag (data J hr hn marked)) := (sortPresentation PP PE J hr hn marked h).numbering
    ((D.descriptor ε).graph (descriptor_sound PP PE J hr hn marked h ε)).graph ≃g
      (Subcubic.finiteGraph J hr hn marked ε).graph := by
  letI : ∀b : Block (n := n) J,FiniteNumbering (Proper J b) := properNumbering PP PE J hr hn marked h
  letI : FiniteNumbering (Block (n := n) J) := (blockPresentation PP PE J marked h).numbering
  letI : FiniteNumbering (PrefixParts.Wiring.SortTag (data J hr hn marked)) := (sortPresentation PP PE J hr hn marked h).numbering
  exact (PrefixDescriptor.uncoloredIso (blockPresentation PP PE J marked h) (data J hr hn marked)
    (coordinateBound (n := n) J) ε (prefix_resign_good PP PE J hr hn marked h ε)
    (wiring J hr hn marked) (matching_resign_good PP PE J hr hn marked h ε)
    (sortPresentation PP PE J hr hn marked h) (sort_valid PP PE J hr hn marked h ε)
    (sort_encode PP PE J hr hn marked h ε)).trans (TypedGame.numbering (Subcubic.graph J hr hn marked ε))
include hr hn h in
 theorem compiler_correct [Nonempty P] (hr3 : 3≤r) (hlarge : r+1<n+1) :
    ∃h0 : (D.descriptor 0).Sound,∃h1 : (D.descriptor 1).Sound,
      let G := (D.descriptor 0).graph h0
      let H := (D.descriptor 1).graph h1
      0<G.order ∧ G.order=H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧
        VariableWL.Subcubic G ∧ VariableWL.Subcubic H ∧ (Equivalent G H r ↔ J.Consistent) := by
  let : ∀b : Block (n := n) J,FiniteNumbering (Proper J b) := properNumbering PP PE J hr hn marked h
  let : FiniteNumbering (Block (n := n) J) := (blockPresentation PP PE J marked h).numbering
  let : FiniteNumbering (PrefixParts.Wiring.SortTag (data J hr hn marked)) := (sortPresentation PP PE J hr hn marked h).numbering
  have hsound := descriptor_sound PP PE J hr hn marked h
  let iso := descriptor_iso PP PE J hr hn marked h
  refine ⟨hsound 0,hsound 1,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [order_eq_of_iso (iso 0)]
    exact Subcubic.positive_order J hr hn marked 0
  · rw [order_eq_of_iso (iso 0),order_eq_of_iso (iso 1)]
    exact Subcubic.equal_order J hr hn marked
  · exact (iso 0).connected_iff.mpr (Subcubic.connected J hr hn marked 0)
  · exact (iso 1).connected_iff.mpr (Subcubic.connected J hr hn marked 1)
  · exact (subcubic_iso_iff (iso 0)).mpr (Subcubic.degree_le_three J hr hn marked 0)
  · exact (subcubic_iso_iff (iso 1)).mpr (Subcubic.degree_le_three J hr hn marked 1)
  · exact (equivalent_iso_iff (iso 0) (iso 1) r).trans
      (Subcubic.equivalent_iff_consistent J hr hn marked hr3 hlarge)
end VariableWL.AffineCatalog

namespace VariableWL.AffineCatalog.Program.Listing
open Computation.Stack.PolyRecipe
variable {n : ℕ} (D : Listing n)
noncomputable def graph : GraphListing n := D.core.toPrefix.portListing.expanded
 theorem graph_eval (v : Computation.Stack.Recipe.Env n) :
    D.graph.eval v=(D.eval v).core.toPrefix.portData.expanded := by
  rw [graph,PortListing.expanded_eval,PrefixDescriptor.Program.Listing.portListing_eval,
    BlockDescriptor.Program.Listing.prefix_eval,core_eval]
end VariableWL.AffineCatalog.Program.Listing
namespace VariableWL.CellularCatalog.Program.Listing
open Computation.Stack.PolyRecipe
variable {n : ℕ} (D : Listing n)
noncomputable def graph : GraphListing n := D.catalog.affine.graph
 theorem graph_eval (v : Computation.Stack.Recipe.Env n) :
    D.graph.eval v=(D.eval v).catalog.affine.core.toPrefix.portData.expanded := by
  rw [graph,AffineCatalog.Program.Listing.graph_eval,CircuitCatalog.Program.Listing.affine_eval,catalog_eval]
end VariableWL.CellularCatalog.Program.Listing
namespace VariableWL.CellularCatalog.Data
 def resign (D : Data) (ε : Affine.Bit) : Data := {D with epsilon:=ε.val}
 theorem ext_fields {D E : Data}
    (h1 : D.bits=E.bits) (h2 : D.inputLength=E.inputLength) (h3 : D.letters=E.letters)
    (h4 : D.internal=E.internal) (h5 : D.rule=E.rule) (h6 : D.input=E.input)
    (h7 : D.blank=E.blank) (h8 : D.accepting=E.accepting) (h9 : D.marked=E.marked)
    (h10 : D.epsilon=E.epsilon) : D=E := by
  cases D; cases E; congr
 theorem resign_affine (D : Data) (ε : Affine.Bit) :
    (D.resign ε).catalog.affine=D.catalog.affine.resign ε := rfl
end VariableWL.CellularCatalog.Data
namespace VariableWL.MachineCellular
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable (M : Machine) (c d : ℕ)
 theorem listing_eval_resign (v : Env 1) (ε : Affine.Bit) :
    (listing M c d ε).eval v=((listing M c d 0).eval v).resign ε := by
  apply CellularCatalog.Data.ext_fields <;> try rfl
  exact numeral_number _ _
noncomputable def graphListing (ε : Affine.Bit) : GraphListing 1 := (listing M c d ε).graph
noncomputable def base (v : Env 1) : AffineCatalog.Data := ((listing M c d 0).eval v).catalog.affine
 theorem graphListing_eval (v : Env 1) (ε : Affine.Bit) :
    (graphListing M c d ε).eval v=(base M c d v).descriptor ε := by
  rw [graphListing,CellularCatalog.Program.Listing.graph_eval,listing_eval_resign,
    CellularCatalog.Data.resign_affine]
  rfl
end VariableWL.MachineCellular

namespace VariableWL.MachineCellular
open Descriptor Computation.Stack.PolyRecipe Computation.Stack.Recipe
attribute [local instance] Classical.propDecidable
variable (M : Machine) (c d : ℕ)
noncomputable def realPresentation (w : Word) : Presentation (MachineReduction.Real M c d w) :=
  CircuitCatalog.real (presentation M) (CellularCatalog.ands (presentation M))
    (CellularCatalog.edge (d := MachineReduction.bits M c d w) (presentation M))
noncomputable def comparisonPresentation (w : Word) : Presentation (MachineReduction.Comparison M c d w) :=
  CircuitCatalog.comparison (CellularCatalog.edge (d := MachineReduction.bits M c d w) (presentation M))
    (CellularCatalog.request (presentation M) (MachineReduction.circuit M c d w))
 theorem base_good (w : Word) :
    AffineCatalog.Good (n := MachineReduction.internal M c d w)
      (realPresentation M c d w) (comparisonPresentation M c d w)
      (MachineReduction.imageInstance M c d w) (MachineReduction.marked M c d w) 0
      (base M c d (fun _=>w.reverse)) := by
  have hC := CellularCatalog.catalog_good (presentation M) (MachineReduction.circuit M c d w)
    (MachineReduction.marked M c d w) 0 (listing_good M c d w 0)
  exact CircuitCatalog.affine_good (presentation M) (CellularCatalog.ands (presentation M))
    (CellularCatalog.edge (d := MachineReduction.bits M c d w) (presentation M))
    (CellularCatalog.request (presentation M) (MachineReduction.circuit M c d w))
    (MachineReduction.circuit M c d w).description (MachineReduction.marked M c d w) 0 hC
 theorem compiled_correct (w : Word) :
    ∃h0 : ((graphListing M c d 0).eval (fun _=>w.reverse)).Sound,
    ∃h1 : ((graphListing M c d 1).eval (fun _=>w.reverse)).Sound,
      let G := ((graphListing M c d 0).eval (fun _=>w.reverse)).graph h0
      let H := ((graphListing M c d 1).eval (fun _=>w.reverse)).graph h1
      0<G.order ∧ G.order=H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧
        VariableWL.Subcubic G ∧ VariableWL.Subcubic H ∧
        (Equivalent G H (MachineReduction.dimension M c d w) ↔ (MachineReduction.imageInstance M c d w).Consistent) := by
  have hr := MachineReduction.dimension_large M c d w
  have h := AffineCatalog.compiler_correct (realPresentation M c d w) (comparisonPresentation M c d w)
    (MachineReduction.imageInstance M c d w) (by omega) (MachineReduction.internal_pos M c d w)
    (MachineReduction.marked M c d w) (base_good M c d w) (by omega) (MachineReduction.enough_links M c d w)
  rw [graphListing_eval M c d (fun _=>w.reverse) 0,graphListing_eval M c d (fun _=>w.reverse) 1]
  exact h
noncomputable def dimensionProgram : Expr 1 := add (bitProgram M c d) (bitProgram M c d)
 theorem dimensionProgram_number (w : Word) :
    (dimensionProgram M c d).number (fun _=>w.reverse)=MachineReduction.dimension M c d w := by
  rw [dimensionProgram,add_number,bitProgram_number,List.length_reverse]
  rfl
noncomputable def pairProgram : Expr 1 := append (graphListing M c d 0).code
  (append (graphListing M c d 1).code (integerEncode (dimensionProgram M c d)))
 theorem pairProgram_value (w : Word)
    (h0 : ((graphListing M c d 0).eval (fun _=>w.reverse)).Sound)
    (h1 : ((graphListing M c d 1).eval (fun _=>w.reverse)).Sound) :
    (pairProgram M c d).value (fun _=>w.reverse)=
      pairCode (((graphListing M c d 0).eval (fun _=>w.reverse)).graph h0)
        (((graphListing M c d 1).eval (fun _=>w.reverse)).graph h1) (MachineReduction.dimension M c d w) := by
  rw [pairProgram,append_value,append_value,GraphListing.code_correct _ _ h0,
    GraphListing.code_correct _ _ h1,integerEncode_value,dimensionProgram_number]
  exact (List.append_assoc _ _ _).symm
 theorem reduction_correct (w : Word) (b : Bool)
    (h : OutputsWithin M w [b] (2^(c*(w.length+1)^d))) :
    ((pairProgram M c d).value (fun _=>w.reverse)∈WL ↔ b=true) ∧
    ((pairProgram M c d).value (fun _=>w.reverse)∈SubWL ↔ b=true) := by
  obtain ⟨h0,h1,hpos,horder,hconn0,hconn1,hdeg0,hdeg1,heq⟩ := compiled_correct M c d w
  have hd := MachineReduction.dimension_large M c d w
  have hr : 2≤MachineReduction.dimension M c d w := by omega
  have hc := MachineReduction.consistent_iff_output M c d w b h
  rw [pairProgram_value M c d w h0 h1,Encoding.pair_mem_WL,Encoding.pair_mem_SubWL]
  constructor
  · exact (and_iff_right hr).trans (heq.trans hc)
  · constructor
    · intro hp
      exact (heq.trans hc).mp hp.2.2.2.2.2.2.2
    · intro hb
      exact ⟨hr,hpos,horder,hconn0,hconn1,hdeg0,hdeg1,(heq.trans hc).mpr hb⟩
end VariableWL.MachineCellular
namespace VariableWL
 theorem general_hard : ∀R : Language, InEXPTIME R → PolytimeReduces R WL := by
  rintro R ⟨M,c,d,hM⟩
  apply Computation.Stack.PolyRecipe.reduces (MachineCellular.pairProgram M c d) R WL
  intro w
  obtain ⟨b,hb,ho⟩ := hM w
  exact hb.symm.trans (MachineCellular.reduction_correct M c d w b ho).1.symm
 theorem subcubic_hard : ∀R : Language, InEXPTIME R → PolytimeReduces R SubWL := by
  rintro R ⟨M,c,d,hM⟩
  apply Computation.Stack.PolyRecipe.reduces (MachineCellular.pairProgram M c d) R SubWL
  intro w
  obtain ⟨b,hb,ho⟩ := hM w
  exact hb.symm.trans (MachineCellular.reduction_correct M c d w b ho).2.symm
 theorem main : EXPTIMEComplete WL ∧ EXPTIMEComplete SubWL :=
  ⟨⟨Computation.Stack.ExponentialRecipe.general_upper,general_hard⟩,
    ⟨Computation.Stack.ExponentialRecipe.subcubic_upper,subcubic_hard⟩⟩
end VariableWL

end OAI
