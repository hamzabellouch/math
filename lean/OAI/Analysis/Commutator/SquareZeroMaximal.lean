import Mathlib
import OAI.Analysis.Commutator.PolarExtension
import OAI.Analysis.Commutator.SquareZeroPolar
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

abbrev SquareZeroLink (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) :=
  {v : Link M e e // v.val*v.val=0}

variable (M : VonNeumannAlgebra H) {e : H →L[ℂ] H} (he : IsStarProjection e)

include he

lemma squareZero_chain_has_upper (c : Set (SquareZeroLink M e)) (hc : IsChain (·≤·) c)
    (hne : c.Nonempty) : BddAbove c := by
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := hc.directedOn.isDirectedOrder
  let ω : Ultrafilter c := Ultrafilter.of atTop
  have hω : (ω : Filter c)≤atTop := Ultrafilter.of_le atTop
  obtain ⟨W,hnW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω (fun v : c => v.val.val.val)
    1 zero_le_one (fun v => v.val.val.norm_le_one)
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Filter.Eventually.of_forall fun v => v.val.val.mem)
  have hWe : W*e=W := by
    have h := WeakOperatorLimit.intertwine hlim e 1 (Filter.Eventually.of_forall
      fun v => by simpa only [one_mul] using v.val.val.mul_source he)
    simpa only [one_mul] using h
  have heW : e*W=W := by
    have h := WeakOperatorLimit.intertwine hlim 1 e (Filter.Eventually.of_forall
      fun v => by simpa only [mul_one] using (v.val.val.target_mul he).symm)
    simpa only [mul_one] using h.symm
  have hWv (v : c) : W*v.val.val.val=0 := by
    have hev : ∀ᶠ w : c in (ω : Filter c), v.val≤w.val :=
      (Filter.eventually_ge_atTop v).filter_mono hω
    apply WeakOperatorLimit.right_eq hlim v.val.val.val 0
    filter_upwards [hev] with w hw
    have hfix := (Link.le_def v.val.val w.val.val).mp hw |>.2
    calc
      _=w.val.val.val*(w.val.val.val*v.val.val.initial) := by rw [hfix]
      _=0 := by rw [←mul_assoc,w.val.property,zero_mul]
  have hWW : W*W=0 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    have hs : ∀ v : c, inner ℂ (v.val.val.val x) (star W y)=0 := by
      intro v
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      simpa only [mul_apply_eq_comp,zero_apply,inner_zero_left] using
        congrArg (fun U : H →L[ℂ] H => inner ℂ (U x) y) (hWv v)
    have hl := hlim x (star W y)
    simp only [hs] at hl
    have h := tendsto_nhds_unique hl tendsto_const_nhds
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
      mul_apply_eq_comp,zero_apply,inner_zero_left] using h
  let u : Link M e e :=
    { val := Polar.partialIsometry W
      mem := Polar.partialIsometry_mem_vonNeumann M hWM
      triple := Polar.partialIsometry_triple W
      source_le := by rw [Polar.partialIsometry_initial]; exact Polar.rightSupport_le W e he hWe
      target_le := Polar.leftSupport_le W e he heW }
  let u' : SquareZeroLink M e := ⟨u,Polar.partialIsometry_square_zero W hWW⟩
  refine ⟨u',?_⟩
  intro v hv
  have hev : ∀ᶠ w : c in (ω : Filter c), v≤w.val :=
    (Filter.eventually_ge_atTop (⟨v,hv⟩ : c)).filter_mono hω
  have hWext : W*v.val.initial=v.val.val := WeakOperatorLimit.right_eq hlim v.val.initial v.val.val
    (hev.mono fun w hw => (Link.le_def v.val w.val.val).mp hw |>.2)
  have hExt := Polar.partialIsometry_extends hnW v.val.triple hWext
  change v.val≤u
  apply (Link.le_def v.val u).mpr
  constructor
  · change v.val.initial ≤ star (Polar.partialIsometry W)*Polar.partialIsometry W
    rw [Polar.partialIsometry_initial]
    exact hExt.2
  · exact hExt.1

theorem exists_maximal_squareZero : ∃ v : SquareZeroLink M e, IsMax v := by
  let v0 : Link M e e :=
    { val := 0
      mem := M.zero_mem
      triple := by simp
      source_le := by simpa using he.nonneg
      target_le := by simpa using he.nonneg }
  let : Nonempty (SquareZeroLink M e) := ⟨⟨v0,by simp [v0]⟩⟩
  exact zorn_le_nonempty (squareZero_chain_has_upper M he)

end Kadison.PartialIsometryOrder

end

end
end

end OAI
