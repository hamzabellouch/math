import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.NormalizationMachine
import OAI.Combinatorics.KMedianRecovery.Recovery.FinImages

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalizeInput
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace P
noncomputable def clients : List Bool→List Bool := BinaryMaskParser.run ∘ BinaryInputParser.Metric.clients
noncomputable def clients_computes : PolyComputes clients := BinaryInputParser.Metric.clients_computes.comp BinaryMaskParser.run_computes
noncomputable def facilities : List Bool→List Bool := BinaryMaskParser.run ∘ BinaryInputParser.Metric.facilities
noncomputable def facilities_computes : PolyComputes facilities := BinaryInputParser.Metric.facilities_computes.comp BinaryMaskParser.run_computes
noncomputable def points : List Bool→List Bool := RawUnary.run ∘ BinaryInputParser.Metric.clients
noncomputable def points_computes : PolyComputes points := BinaryInputParser.Metric.clients_computes.comp RawUnary.run_computes
lemma clients_bits (I : RationalMetricInput) : clients I.bits=BinaryFinSet.encode I.clients := by
  rw [clients,Function.comp_apply,BinaryInputParser.Metric.clients_bits,BinaryMaskParser.run_mask]
lemma facilities_bits (I : RationalMetricInput) : facilities I.bits=BinaryFinSet.encode I.facilities := by
  rw [facilities,Function.comp_apply,BinaryInputParser.Metric.facilities_bits,BinaryMaskParser.run_mask]
lemma points_bits (I : RationalMetricInput) : points I.bits=List.replicate I.pointCount true := by
  rw [points,Function.comp_apply,BinaryInputParser.Metric.clients_bits,RawUnary.run,BinaryInputParser.Metric.mask_length]
end P
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.matrix BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
noncomputable def raw (x : List Bool) : List Bool := extractPrefix x
noncomputable def raw_computes : PolyComputes raw := extractPrefix_computes
noncomputable def matrix (x : List Bool) : List Bool := BinaryInputParser.Metric.matrix (raw x)
noncomputable def matrix_computes : PolyComputes matrix := raw_computes.comp BinaryInputParser.Metric.matrix_computes
noncomputable def points (x : List Bool) : List Bool := P.points (raw x)
noncomputable def points_computes : PolyComputes points := raw_computes.comp P.points_computes
noncomputable def clients (x : List Bool) : List Bool := P.clients (raw x)
noncomputable def clients_computes : PolyComputes clients := raw_computes.comp P.clients_computes
noncomputable def clientCount (x : List Bool) : List Bool := Count.run (clients x)
noncomputable def clientCount_computes : PolyComputes clientCount := clients_computes.comp Count.run_computes
noncomputable def count (x : List Bool) : List Bool := BinaryInputParser.Metric.count (raw x)
noncomputable def count_computes : PolyComputes count := raw_computes.comp BinaryInputParser.Metric.count_computes
noncomputable def plainFacilities (x : List Bool) : List Bool := P.facilities (raw x)
noncomputable def plainFacilities_computes : PolyComputes plainFacilities := raw_computes.comp P.facilities_computes
noncomputable def facilitiesInput (x : List Bool) : List Bool := pairBits (count x,plainFacilities x)
noncomputable def facilitiesInput_computes : PolyComputes facilitiesInput := count_computes.pair plainFacilities_computes
noncomputable def facilities (x : List Bool) : List Bool := BinaryTaggedSets.shift (facilitiesInput x)
noncomputable def facilities_computes : PolyComputes facilities := facilitiesInput_computes.comp BinaryTaggedSets.shift_computes
noncomputable def prep (x : List Bool) : List Bool := encode [matrix x,points x,clientCount x,discardPrefix x]
noncomputable def prep_computes : PolyComputes prep := list_computes [matrix,points,clientCount,discardPrefix] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl
  · exact ⟨matrix_computes⟩
  · exact ⟨points_computes⟩
  · exact ⟨clientCount_computes⟩
  · exact ⟨discardPrefix_computes⟩)
noncomputable def rounded (x : List Bool) : List Bool := BinaryNormalization.run (prep x)
noncomputable def rounded_computes : PolyComputes rounded := prep_computes.comp BinaryNormalization.run_computes
noncomputable def twice (x : List Bool) : List Bool := BinaryDuplicateMatrix.twice (points x)
noncomputable def twice_computes : PolyComputes twice := points_computes.comp BinaryDuplicateMatrix.twice_computes
noncomputable def budget (x : List Bool) : List Bool := BinaryInputParser.Metric.budget (raw x)
noncomputable def budget_computes : PolyComputes budget := raw_computes.comp BinaryInputParser.Metric.budget_computes
noncomputable def mesh (x : List Bool) : List Bool := BinaryNormalization.mesh (prep x)
noncomputable def mesh_computes : PolyComputes mesh := prep_computes.comp BinaryNormalization.mesh_computes
noncomputable def cap (x : List Bool) : List Bool := BinaryNormalization.cap (prep x)
noncomputable def cap_computes : PolyComputes cap := prep_computes.comp BinaryNormalization.cap_computes
noncomputable def run (x : List Bool) : List Bool := encode [rounded x,twice x,clients x,facilities x,budget x,mesh x,cap x]
noncomputable def run_computes : PolyComputes run := list_computes [rounded,twice,clients,facilities,budget,mesh,cap] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨rounded_computes⟩
  · exact ⟨twice_computes⟩
  · exact ⟨clients_computes⟩
  · exact ⟨facilities_computes⟩
  · exact ⟨budget_computes⟩
  · exact ⟨mesh_computes⟩
  · exact ⟨cap_computes⟩)
lemma prep_bits (I : RationalMetricInput) (M : ℚ) :
    prep (pairBits (I.bits,BinaryRational.encode M))=BinaryNormalization.pack I.distance I.clients.card M := by
  simp only [prep,matrix,points,clientCount,clients,raw,extractPrefix_pairBits,discardPrefix_pairBits,BinaryInputParser.Metric.matrix_bits,P.points_bits,
    P.clients_bits,BinaryFinSet.encode_eq,Count.run_encode,List.length_map,Finset.length_sort,BinaryNormalization.pack]
  rfl
lemma facilities_bits (I : RationalMetricInput) (M : ℚ) :
    facilities (pairBits (I.bits,BinaryRational.encode M))=BinaryFinSet.encode (I.facilities.image BinaryTaggedSets.right) := by
  simp only [facilities,facilitiesInput,count,plainFacilities,raw,extractPrefix_pairBits,BinaryInputParser.Metric.count_bits,P.facilities_bits,BinaryTaggedSets.shift_encode]
lemma run_bits (I : RationalMetricInput) (M : ℚ) :
    run (pairBits (I.bits,BinaryRational.encode M))=encode
      [RationalMatrix.encode (BinaryRoundingMatrix.round (BinaryDuplicateMatrix.duplicate I.distance)
          ((IntegralAssembly.gammaRat/16)*M/I.clients.card) (Rounding.cap I.clients.card (IntegralAssembly.gamma/16))),
        List.replicate (I.pointCount+I.pointCount) true,BinaryFinSet.encode (I.clients.image BinaryTaggedSets.left),
        BinaryFinSet.encode (I.facilities.image BinaryTaggedSets.right),I.budget.bits,
        BinaryRational.encode ((IntegralAssembly.gammaRat/16)*M/I.clients.card),
        (Rounding.cap I.clients.card (IntegralAssembly.gamma/16)).bits] := by
  rw [run,rounded,twice,mesh,cap,prep_bits,BinaryNormalization.run_pack,BinaryNormalization.mesh_pack,BinaryNormalization.cap_pack,facilities_bits]
  simp only [clients,points,budget,raw,extractPrefix_pairBits,P.points_bits,P.clients_bits,BinaryInputParser.Metric.budget_bits,
    BinaryDuplicateMatrix.twice,←List.replicate_add,BinaryTaggedSets.left_encode]
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
