import OAI.Computability.DegreeRigidity.Representation.GenericTopology
import OAI.Computability.DegreeRigidity.Representation.GenericIdentity
import OAI.Computability.DegreeRigidity.Representation.PairGenericSelection
import Mathlib.Topology.Baire.BaireMeasurable

namespace OAI

namespace TuringRigidity.GenericTruth
open FiniteShuffle ShuffleRequirements GenericTopology Set Filter Encodable

def CylinderIn (U : Set Oracle) (s : List Bool) : Prop := ∀ G, Realizes s G → G ∈ U

theorem cylinderIn_denseOpen (U : Set Oracle) (ho : IsOpen U) (hd : Dense U) :
    DenseOpen (CylinderIn U) := by
  constructor
  · intro s
    obtain ⟨H,hs,hHU⟩ := hd.inter_open_nonempty {G | Realizes s G} (realizes_isOpen s)
      ⟨fun i => s.getD i false,realizes_default s⟩
    obtain ⟨n,hn⟩ := cylinder_basis U ho H hHU
    refine ⟨initial H (max n s.length),?_,?_⟩
    · rw [←prefix_default s]
      simpa only [prefix_length] using initial_prefix (n := s.length) (m := max n s.length) (le_max_right _ _) hs
    · intro G hG
      exact hn G (((realizes_initial H G _).mp hG).mono (le_max_left _ _))
  · intro s t hst hs G hG
    exact hs G (realizes_mono hst hG)

theorem generic_subset_of_residual (S : Set Oracle) (hS : S ∈ residual Oracle) :
    ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
      ∀ G, GenericFor D G → G ∈ S := by
  classical
  obtain ⟨T,hTo,hTd,hTc,hsub⟩ := mem_residual_iff.mp hS
  let : Countable T := hTc.to_subtype
  let : Encodable T := Encodable.ofCountable T
  let V : ℕ → Set Oracle := fun n => ((decode (α := T) n).map Subtype.val).getD univ
  have hV (n : ℕ) : IsOpen (V n) ∧ Dense (V n) := by
    cases he : decode (α := T) n with
    | none => simp [V,he]
    | some t => simpa [V,he] using And.intro (hTo t.val t.property) (hTd t.val t.property)
  refine ⟨fun n => CylinderIn (V n),fun n => cylinderIn_denseOpen _ (hV n).1 (hV n).2,?_⟩
  intro G hG
  apply hsub
  intro t ht
  let k : T := ⟨t,ht⟩
  obtain ⟨s,hs,hGs⟩ := hG (encode k)
  have hh := hs G hGs
  simpa [V,k] using hh

theorem borel_generic_truth (S : Set Oracle) (hS : MeasurableSet S) :
    ∃ U : Set Oracle, IsOpen U ∧ ∃ D : ℕ → List Bool → Prop,
      (∀ n, DenseOpen (D n)) ∧ ∀ G, GenericFor D G → (G ∈ S ↔ G ∈ U) := by
  obtain ⟨U,hU,hSU⟩ := hS.residualEq_isOpen
  obtain ⟨D,hD,hDS⟩ := generic_subset_of_residual {G | G ∈ S ↔ G ∈ U}
    (Filter.eventuallyEqSet_iff.mp hSU)
  exact ⟨U,hU,D,hD,hDS⟩

def triple (G : Oracle) : Oracle × Oracle × Oracle :=
  (PairGenericSelection.column false G,
    PairGenericSelection.column false (PairGenericSelection.column true G),
    PairGenericSelection.column true (PairGenericSelection.column true G))

theorem triple_measurable : Measurable triple :=
  (PairGenericSelection.column_measurable false).prodMk
    (((PairGenericSelection.column_measurable false).comp (PairGenericSelection.column_measurable true)).prodMk
      ((PairGenericSelection.column_measurable true).comp (PairGenericSelection.column_measurable true)))

theorem sourceEquation_generic_truth (p : OracleCode) (P : Oracle) :
    ∃ U : Set Oracle, IsOpen U ∧ ∃ D : ℕ → List Bool → Prop,
      (∀ n, DenseOpen (D n)) ∧ ∀ G, GenericFor D G →
        (GenericIdentity.SourceEquation p P (triple G) ↔ G ∈ U) :=
  borel_generic_truth _ ((GenericIdentity.sourceEquation_measurable p P).preimage triple_measurable)

end TuringRigidity.GenericTruth

end OAI
