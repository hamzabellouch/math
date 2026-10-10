import Mathlib
import OAI.Analysis.BrownMeasure.Atomic

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology
namespace PolarStructure
variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}

theorem jointPurePoint_of_countable_levels
    (A : ι → (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) (r : Ω → ι → ℝ)
    (hr : Measurable r)
    (hA : ∀ i u,A i u =ᵐ[μ] fun x=>(r x i:ℂ)*u x)
    (S : Set (ι → ℝ)) (hS : S.Countable) (hmem : ∀ᵐ x ∂μ,r x∈S) : JointPurePoint A := by
  let K := (Submodule.span ℂ {x | ∃ t : ι → ℝ,x∈jointSpace A t}).topologicalClosure
  have hK : Kᗮ=⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro u hu
    have hz (t : ι → ℝ) : ∀ᵐ x ∂μ,r x=t → u x=0 := by
      let E := r ⁻¹' {t}
      have hE : MeasurableSet E := hr (measurableSet_singleton t)
      let hv := (Lp.memLp u).indicator hE
      let v : Lp ℂ 2 μ := hv.toLp (E.indicator u)
      have hvE : v =ᵐ[μ] E.indicator u := hv.coeFn_toLp
      have hvj : v∈jointSpace A t := by
        intro i
        apply Lp.ext
        filter_upwards [hA i v,hvE,Lp.coeFn_smul (t i:ℂ) v] with x hx hxe hxs
        rw [hx,hxs]
        by_cases hxE : x∈E
        · have he : r x=t := hxE
          simp [he]
        · have h0 : v x=0 := by rw [hxe,Set.indicator_of_notMem hxE]
          simp [h0]
      have hvK : v∈K := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t,hvj⟩)
      have hi : inner ℂ v u=0 := (Submodule.mem_orthogonal _ u).mp hu v hvK
      have he : inner ℂ v v=inner ℂ v u := by
        rw [L2.inner_def,L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hvE] with x hx
        rw [hx]
        by_cases hxE : x∈E <;> simp [Set.indicator_of_mem,Set.indicator_of_notMem,hxE]
      have hv0 : v=0 := inner_self_eq_zero.mp (he.trans hi)
      filter_upwards [hvE,Lp.coeFn_zero ℂ 2 μ] with x hx hx0 hxt
      have hxE : x∈E := hxt
      rw [Set.indicator_of_mem hxE,hv0,hx0] at hx
      exact hx.symm
    have hall : ∀ᵐ x ∂μ,∀ t∈S,r x=t → u x=0 := (ae_ball_iff hS).mpr (fun t _=>hz t)
    have hu0 : u=0 := by
      apply Lp.ext
      filter_upwards [hall,hmem,Lp.coeFn_zero ℂ 2 μ] with x hx hxm hx0
      exact (hx (r x) hxm rfl).trans hx0.symm
    simp only [hu0]
  exact Submodule.orthogonal_eq_bot_iff.mp hK
end PolarStructure
end

end OAI
