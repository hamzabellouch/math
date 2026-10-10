import Mathlib
import OAI.Combinatorics.KMedian.Process.TaperAllProgram
import OAI.Combinatorics.KMedian.Programs.GraphLawProgram

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
abbrev Row := List ℚ
abbrev BRow := List Bool
abbrev Raw := ((ℚ × ℚ) × ℕ) × List (Row × BRow)

structure Input where
  n : ℕ
  d : Fin n → Fin n → ℚ
  own : Fin n → Finset (Fin n)
  g : ℚ
  P : ℚ
  Δ : ℕ
  positive : 0<P

def Input.raw (x : Input) : Raw :=
  (((x.g,x.P),x.Δ),List.ofFn fun i => (List.ofFn (x.d i),List.ofFn fun h => decide (h∈x.own i)))
abbrev Input.encode (x : Input) := enc x.raw

 theorem marginal_unit (P d r : ℚ) (hP : 0<P) :
    0≤Taper.rationalMarginal P d r ∧ Taper.rationalMarginal P d r≤1 := by
  unfold Taper.rationalMarginal
  exact ⟨le_min (by norm_num) (div_nonneg (le_max_right _ _) hP.le), min_le_left _ _⟩
 theorem source_unit {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) (hP : 0<P) (i : Fin n) :
    0≤Taper.sourceMarginals g P d own Δ i ∧ Taper.sourceMarginals g P d own Δ i≤1 := by
  unfold Taper.sourceMarginals
  split_ifs
  · unfold Taper.zeroMarginal; split_ifs <;> norm_num
  · exact marginal_unit _ _ _ hP

def Input.qInput (x : Input) : SparseGraph.Program.QInput :=
  ⟨x.n,x.n,(fun h i => Taper.sourceMarginals x.g x.P (x.d i) (x.own i) x.Δ h),
    fun h i => source_unit x.g x.P (x.d i) (x.own i) x.Δ x.positive h⟩
def rawQ (x : Raw) : List Unit × List Row :=
  (x.2.map (fun _ => ()),x.2.map (fun col => Taper.ListOperation.sourceRow (((x.1.1,col.1),col.2),x.1.2)))
@[fun_prop] theorem rawQ_poly : Poly rawQ := by
  unfold rawQ
  apply Poly.pair
  · apply list_map <;> fun_prop
  · apply list_map <;> fun_prop

 theorem rawQ_input (x : Input) : rawQ x.raw=x.qInput.raw := by
  simp only [rawQ,Input.raw,List.map_ofFn,Function.comp_def,Taper.ListOperation.sourceRow_list,
    SparseGraph.Program.QInput.raw,Input.qInput,List.ofFn_const]

noncomputable def qInputProgram : PolyProgram Input.encode SparseGraph.Program.QInput.encode Input.qInput :=
  rawQ_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (rawQ_input x))
noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.et)
    (fun x : Input => x.qInput.result) := qInputProgram.comp SparseGraph.Program.lawProgram
end MetricKMedian.TaperGraphProgram
end

end OAI
