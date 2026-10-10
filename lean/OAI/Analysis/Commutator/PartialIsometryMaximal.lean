import Mathlib
import OAI.Analysis.Commutator.PartialIsometryOrder
import OAI.Analysis.Commutator.PolarExtension
import OAI.Analysis.Commutator.WeakOperatorAlgebra
import OAI.Analysis.Commutator.WeakOperatorLimit

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) {e f : H →L[ℂ] H}

variable (he : IsStarProjection e) (hf : IsStarProjection f)

include he hf

theorem chain_has_upper (c : Set (Link M e f)) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
    BddAbove c := by
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := hc.directedOn.isDirectedOrder
  let ω : Ultrafilter c := Ultrafilter.of atTop
  have hω : (ω : Filter c)≤atTop := Ultrafilter.of_le atTop
  obtain ⟨W,hnW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω (fun v : c => v.val.val)
    1 zero_le_one (fun v => v.val.norm_le_one)
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Filter.Eventually.of_forall fun v => v.val.mem)
  have hWe : W*e=W := by
    have h := WeakOperatorLimit.intertwine hlim e 1 (Filter.Eventually.of_forall
      fun v => by simpa only [one_mul] using v.val.mul_source he)
    simpa only [one_mul] using h
  have hfW : f*W=W := by
    have h := WeakOperatorLimit.intertwine hlim 1 f (Filter.Eventually.of_forall
      fun v => by simpa only [mul_one] using (v.val.target_mul hf).symm)
    simpa only [mul_one] using h.symm
  let u : Link M e f :=
    { val := Polar.partialIsometry W
      mem := Polar.partialIsometry_mem_vonNeumann M hWM
      triple := Polar.partialIsometry_triple W
      source_le := by rw [Polar.partialIsometry_initial]; exact Polar.rightSupport_le W e he hWe
      target_le := Polar.leftSupport_le W f hf hfW }
  refine ⟨u,?_⟩
  intro v hv
  have hev : ∀ᶠ w : c in (ω : Filter c), v≤w.val :=
    (Filter.eventually_ge_atTop (⟨v,hv⟩ : c)).filter_mono hω
  have hWv : W*v.initial=v.val := WeakOperatorLimit.right_eq hlim v.initial v.val
    (hev.mono fun w hw => (Link.le_def v w.val).mp hw |>.2)
  have hExt := Polar.partialIsometry_extends hnW v.triple hWv
  apply (Link.le_def v u).mpr
  constructor
  · change v.initial ≤ star (Polar.partialIsometry W)*Polar.partialIsometry W
    rw [Polar.partialIsometry_initial]
    exact hExt.2
  · exact hExt.1

theorem exists_maximal : ∃ v : Link M e f, IsMax v := by
  let v0 : Link M e f :=
    { val := 0
      mem := M.zero_mem
      triple := by simp
      source_le := by simpa using he.nonneg
      target_le := by simpa using hf.nonneg }
  let : Nonempty (Link M e f) := ⟨v0⟩
  exact zorn_le_nonempty (fun c hc hn => chain_has_upper M he hf c hc hn)

end Kadison.PartialIsometryOrder

end

end
end

end OAI
