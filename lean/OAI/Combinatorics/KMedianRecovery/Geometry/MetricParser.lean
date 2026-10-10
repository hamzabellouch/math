import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalStream
import OAI.Combinatorics.KMedianRecovery.Encoding.MatrixRows
import OAI.Combinatorics.KMedianRecovery.Recovery.RawUnary

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric
open WordOperations WordList
attribute [local irreducible] nat RawTake.run RawDrop.run Stream.run Rows.run RawUnary.run
noncomputable def header (x : List Bool) : List Bool := nat x
noncomputable def count (x : List Bool) : List Bool := extractPrefix (header x)
noncomputable def tailHeader (x : List Bool) : List Bool := nat (discardPrefix (header x))
noncomputable def budget (x : List Bool) : List Bool := extractPrefix (tailHeader x)
noncomputable def masks (x : List Bool) : List Bool := discardPrefix (tailHeader x)
noncomputable def clients (x : List Bool) : List Bool := RawTake.run (pairBits (count x,masks x))
noncomputable def afterClients (x : List Bool) : List Bool := RawDrop.run (pairBits (count x,masks x))
noncomputable def facilities (x : List Bool) : List Bool := RawTake.run (pairBits (count x,afterClients x))
noncomputable def rawMatrix (x : List Bool) : List Bool := RawDrop.run (pairBits (count x,afterClients x))
attribute [local irreducible] header count tailHeader budget masks clients afterClients facilities rawMatrix
noncomputable def header_computes : PolyComputes header := by
  unfold header
  exact nat_computes
noncomputable def count_computes : PolyComputes count := by
  unfold count
  exact header_computes.comp extractPrefix_computes
noncomputable def tailHeader_computes : PolyComputes tailHeader := by
  unfold tailHeader
  exact (header_computes.comp discardPrefix_computes).comp nat_computes
noncomputable def budget_computes : PolyComputes budget := by
  unfold budget
  exact tailHeader_computes.comp extractPrefix_computes
noncomputable def masks_computes : PolyComputes masks := by
  unfold masks
  exact tailHeader_computes.comp discardPrefix_computes
noncomputable def clients_computes : PolyComputes clients := by
  unfold clients
  exact (count_computes.pair masks_computes).comp RawTake.run_computes
noncomputable def afterClients_computes : PolyComputes afterClients := by
  unfold afterClients
  exact (count_computes.pair masks_computes).comp RawDrop.run_computes
noncomputable def facilities_computes : PolyComputes facilities := by
  unfold facilities
  exact (count_computes.pair afterClients_computes).comp RawTake.run_computes
noncomputable def rawMatrix_computes : PolyComputes rawMatrix := by
  unfold rawMatrix
  exact (count_computes.pair afterClients_computes).comp RawDrop.run_computes
noncomputable def matrix (x : List Bool) : List Bool := Rows.run (pairBits (RawUnary.run (clients x),Stream.run (rawMatrix x)))
noncomputable def matrix_computes : PolyComputes matrix := by
  unfold matrix
  exact ((clients_computes.comp RawUnary.run_computes).pair (rawMatrix_computes.comp Stream.run_computes)).comp Rows.run_computes
attribute [local irreducible] matrix
noncomputable def run (x : List Bool) : List Bool := WordList.encode [count x,budget x,clients x,facilities x,matrix x]
noncomputable def run_computes : PolyComputes run := by
  unfold run
  exact cons_computes count_computes (cons_computes budget_computes (cons_computes clients_computes
    (cons_computes facilities_computes (cons_computes matrix_computes (const_computes [])))))
def mask {n : ℕ} (S : Finset (Fin n)) : List Bool := List.ofFn (fun i=>decide (i∈S))
def flat (I : RationalMetricInput) : List ℚ := (List.ofFn (fun i=>List.ofFn (I.distance i))).flatten
lemma bits_eq (I : RationalMetricInput) : I.bits=RationalMetricInput.natBits I.pointCount++RationalMetricInput.natBits I.budget++
    mask I.clients++mask I.facilities++Stream.raw (flat I) := by
  unfold RationalMetricInput.bits mask Stream.raw flat
  congr 1
  rw [List.map_flatten,List.flatten_flatten]
  simp only [List.map_ofFn,Function.comp_def]
lemma header_bits (I : RationalMetricInput) : header I.bits=pairBits (I.pointCount.bits,
    RationalMetricInput.natBits I.budget++mask I.clients++mask I.facilities++Stream.raw (flat I)) := by
  rw [header,bits_eq]
  simp only [List.append_assoc,nat_code]
lemma count_bits (I : RationalMetricInput) : count I.bits=I.pointCount.bits := by rw [count,header_bits,extractPrefix_pairBits]
lemma tailHeader_bits (I : RationalMetricInput) : tailHeader I.bits=pairBits (I.budget.bits,
    mask I.clients++mask I.facilities++Stream.raw (flat I)) := by
  rw [tailHeader,header_bits,discardPrefix_pairBits]
  simp only [List.append_assoc,nat_code]
lemma budget_bits (I : RationalMetricInput) : budget I.bits=I.budget.bits := by rw [budget,tailHeader_bits,extractPrefix_pairBits]
lemma masks_bits (I : RationalMetricInput) : masks I.bits=mask I.clients++mask I.facilities++Stream.raw (flat I) := by
  rw [masks,tailHeader_bits,discardPrefix_pairBits]
lemma mask_length {n : ℕ} (S : Finset (Fin n)) : (mask S).length=n := List.length_ofFn
lemma clients_bits (I : RationalMetricInput) : clients I.bits=mask I.clients := by
  rw [clients,count_bits,masks_bits,RawTake.run_pack,List.append_assoc]
  simpa only [mask_length] using (show (mask I.clients++(mask I.facilities++Stream.raw (flat I))).take (mask I.clients).length=mask I.clients from List.take_left)
lemma afterClients_bits (I : RationalMetricInput) : afterClients I.bits=mask I.facilities++Stream.raw (flat I) := by
  rw [afterClients,count_bits,masks_bits,RawDrop.run_encode,List.append_assoc]
  simpa only [mask_length] using (show (mask I.clients++(mask I.facilities++Stream.raw (flat I))).drop (mask I.clients).length=mask I.facilities++Stream.raw (flat I) from List.drop_left)
lemma facilities_bits (I : RationalMetricInput) : facilities I.bits=mask I.facilities := by
  rw [facilities,count_bits,afterClients_bits,RawTake.run_pack]
  simpa only [mask_length] using (show (mask I.facilities++Stream.raw (flat I)).take (mask I.facilities).length=mask I.facilities from List.take_left)
lemma rawMatrix_bits (I : RationalMetricInput) : rawMatrix I.bits=Stream.raw (flat I) := by
  rw [rawMatrix,count_bits,afterClients_bits,RawDrop.run_encode]
  simpa only [mask_length] using (show (mask I.facilities++Stream.raw (flat I)).drop (mask I.facilities).length=Stream.raw (flat I) from List.drop_left)
lemma matrix_bits (I : RationalMetricInput) : matrix I.bits=Rectangular.encode I.distance := by
  rw [matrix,clients_bits,rawMatrix_bits,Stream.run_code,RawUnary.run,mask_length]
  unfold Stream.codes flat
  rw [List.map_flatten]
  simp only [List.map_ofFn,Function.comp_def]
  rw [Rows.run_matrix]
  simp only [Rectangular.encode,RationalMatrix.rowEncode_eq]
lemma run_bits (I : RationalMetricInput) : run I.bits=WordList.encode
    [I.pointCount.bits,I.budget.bits,mask I.clients,mask I.facilities,Rectangular.encode I.distance] := by
  rw [run,count_bits,budget_bits,clients_bits,facilities_bits,matrix_bits]
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

end OAI
