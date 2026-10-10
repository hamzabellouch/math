import Mathlib
import OAI.Combinatorics.KMedian.Programs.BundlesProgram
import OAI.Combinatorics.KMedian.Preparation.PreparedDataOperations

namespace OAI


                                             
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

def KernelInput.bundles (x : KernelInput) : SparseBundles.Program.QInput :=
  ⟨x.f,x.n,SparseRescaledInner.piece x.P x.y x.p (total x.D x.q x.Δ x.z),
    SparseRescaledInner.piece_nonnegative x.P x.y x.p _ x.hy x.hp⟩
def bundleData (x : KernelRaw) : List Unit × List (List ℚ) := (x.1.2.2.2.1.map (fun _ => ()),pieces x)
@[fun_prop] theorem bundleData_poly : Poly bundleData := by
  unfold bundleData; apply Binary.Automatic.Poly.pair
  · apply list_map <;> fun_prop
  · exact pieces_poly
noncomputable def bundleInputProgram : PolyProgram KernelInput.encode SparseBundles.Program.QInput.encode KernelInput.bundles :=
  bundleData_poly.program.recode KernelInput.raw (fun _ => rfl) (fun x => by
    unfold bundleData
    rw [pieces_view]
    simp only [KernelInput.raw,KernelInput.base,List.map_const',List.length_ofFn,
      SparseBundles.Program.QInput.encode,SparseBundles.Program.QInput.raw,KernelInput.bundles]
    rfl)
abbrev PreparedRaw := StateRaw × SparseCounts.ListOperation.Table
def attach (x : StateRaw × Data SparseCounts.ListOperation.Table) : Data PreparedRaw :=
  (x.2.1,x.2.2.map (fun G => (x.1,G)))
@[fun_prop] theorem attach_poly : Poly attach := by
  unfold attach; apply Binary.Automatic.Poly.pair
  · fun_prop
  · apply list_map <;> fun_prop

def view {n m f : ℕ} (s : SparseSignedPreparation.State n m × SparseCounts.Table f n) : PreparedRaw :=
  (SparseSignedPreparation.Program.view s.1,SparseCounts.ListOperation.view s.2)
def KernelInput.result (x : KernelInput) : Data PreparedRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (kernel x.D x.q x.Δ x.P x.y x.p x.z)).1,
    (kernel x.D x.q x.Δ x.P x.y x.p x.z).states.toList.map view)
theorem kernel_result (x : KernelInput) :
    attach (SparseSignedPreparation.Program.view x.z,SparseBundles.Program.QInput.result x.bundles)=x.result := by
  simp only [attach,KernelInput.result,kernel,SparseIntegerLaw.map,SparseIntegerLaw.BinarySparse.raw,
    SparseBundles.Program.QInput.result,KernelInput.bundles,Vector.toList_map,List.map_map,Function.comp_def,view]
noncomputable def kernelProgram : PolyProgram KernelInput.encode (enc : Data PreparedRaw → List Bool) KernelInput.result := by
  let z : PolyProgram KernelInput.encode enc (fun x => SparseSignedPreparation.Program.view x.z) :=
    (snd enc enc).recode KernelInput.raw (fun _ => rfl) (fun _ => rfl)
  exact (z.fanout (bundleInputProgram.comp SparseBundles.Program.lawProgram) |>.comp attach_poly.program).congr _ kernel_result
end MetricKMedian.SparsePrepared.Program
end

end OAI
