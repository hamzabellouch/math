import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.BitsInjective

namespace OAI

namespace MetricKMedianRecovery
namespace RationalMetricInput

lemma decodeOutput_mask (I : RationalMetricInput) (S : Finset (Fin I.pointCount))
    (hS : S ⊆ I.facilities) :
    I.decodeOutput (List.ofFn (fun i => decide (i ∈ S))) = S := by
  ext i
  simp only [decodeOutput,Finset.mem_filter,List.getElem?_ofFn,dite_eq_left i.isLt,
    Option.getD_some,decide_eq_true_eq]
  exact ⟨And.right,fun h => ⟨hS h,h⟩⟩

end RationalMetricInput

noncomputable def rawRun (P : Polynomial ℕ)
    (out : (I : RationalMetricInput) → (Fin (P.eval I.bits.length) → Bool) → Finset (Fin I.pointCount))
    (pair : List Bool × List Bool) : List Bool :=
  match RationalMetricInput.decodeInput pair.1 with
  | none => []
  | some I => List.ofFn (fun i : Fin I.pointCount =>
      decide (i ∈ out I (fun j => pair.2[j.val]?.getD false)))

lemma rawRun_code (P : Polynomial ℕ)
    (out : (I : RationalMetricInput) → (Fin (P.eval I.bits.length) → Bool) → Finset (Fin I.pointCount))
    (I : RationalMetricInput) (bits : Fin (P.eval I.bits.length) → Bool) :
    rawRun P out (I.bits,List.ofFn bits) = List.ofFn (fun i => decide (i ∈ out I bits)) := by
  simp only [rawRun,RationalMetricInput.decodeInput_code]
  congr 1
  funext i
  congr 2
  apply congrArg (out I)
  funext j
  simp only [List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some]

lemma rawRun_output (P : Polynomial ℕ)
    (out : (I : RationalMetricInput) → (Fin (P.eval I.bits.length) → Bool) → Finset (Fin I.pointCount))
    (I : RationalMetricInput) (bits : Fin (P.eval I.bits.length) → Bool)
    (h : I.Feasible (out I bits)) :
    I.decodeOutput (rawRun P out (I.bits,List.ofFn bits)) = out I bits := by
  rw [rawRun_code]
  exact I.decodeOutput_mask _ h.1

end MetricKMedianRecovery

end OAI
