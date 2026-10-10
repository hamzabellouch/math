import Mathlib
import OAI.Combinatorics.KMedian.Machines.ListCompiler
import OAI.Combinatorics.KMedian.Machines.RawRotation

namespace OAI

section Inline_PCPBlockRotation
namespace MetricKMedian.PCP.Compiler.RotationTable
open scoped Classical

variable {D B : Type} [Fintype D] [Inhabited D] [Fintype B] [Inhabited B]
noncomputable def blockRows (N : ℕ) (f : ℕ → B → D → ℕ × D) : RotationTable D :=
  (List.range N).flatMap (fun v => (ports (D := B)).map (fun b => (ports (D := D)).map (f v b)))
omit [Inhabited B] in
lemma lookup_blockRows (N : ℕ) (f : ℕ → B → D → ℕ × D)
    (v : ℕ) (hv : v<N) (b : B) (d : D) :
    lookup (blockRows N f) (v*Fintype.card B+(Fintype.equivFin B b).val) d=f v b d := by
  unfold lookup blockRows
  rw [getElem?_flatMap_uniform _ _ (Fintype.card B)
    (by intro u hu; simp only [List.length_map,ports_length]) v
    (by simpa only [List.length_range] using hv) _ (Fintype.equivFin B b).isLt]
  simp only [List.getElem_range,List.getElem?_map,ports,List.getElem?_ofFn,
    Fin.isLt,↓reduceDIte,Option.map_some,Option.getD_some,Fin.eta,Equiv.symm_apply_apply]
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPBlockRotation

end OAI
