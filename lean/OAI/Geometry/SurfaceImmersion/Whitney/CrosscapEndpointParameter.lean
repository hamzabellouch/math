import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapArcEndpoint
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisCoordinates
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! A whole initial segment of the chosen embedded double arc is traced
by the explicit pair of opposite kernel-axis curves, in one orientation. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem crosscap_endpoint_parameter (c : SurfaceCrosscapCoordinates f p)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ (ε s d : ℝ), 0 < ε ∧ ε < 1/3 ∧ (s = 1 ∨ s = -1) ∧ 0 < d ∧
      (fun t => (c.axisCurve (s*t),c.axisCurve (-(s*t)))) '' Icc 0 d =
        Γ '' {t : I | (t:ℝ) ≤ ε} ∧
      (∀ t ∈ Icc 0 d, crosscapAxis (s*t) ∈ c.source.target ∧
        crosscapAxis (-(s*t)) ∈ c.source.target) ∧
      (∀ u : I, (u:ℝ) = ε → (c.axisCurve (s*d),c.axisCurve (-(s*d))) = Γ u) := by
  obtain ⟨ε,hε,hεsmall,hcoords⟩ := crosscap_arc_endpoint c hΓ hzero heq hne
  have hε1 : ε < 1 := hεsmall.trans (by norm_num)
  let θ : ℝ → I := projIcc 0 1 zero_le_one
  let A : ℝ → M × M := Γ ∘ θ
  let v : ℝ → ℝ := fun t => c.source (A t).1 1
  have hθ : Continuous θ := continuous_projIcc
  have hA : Continuous A := hΓ.comp hθ
  have hθval : ∀ t ∈ Icc 0 ε, (θ t : ℝ) = t := by
    intro t ht
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨ht.1,ht.2.trans hε1.le⟩)
  have hdata : ∀ t ∈ Icc 0 ε,
      (A t).1 ∈ c.source.source ∧ (A t).2 ∈ c.source.source ∧
      c.source (A t).1 0 = 0 ∧ c.source (A t).2 0 = 0 ∧
      c.source (A t).1 1 = -c.source (A t).2 1 := by
    intro t ht
    have h := hcoords (θ t) (by rw [hθval t ht]; exact ht.2)
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩
  have hAi : InjOn A (Icc 0 ε) := by
    intro t ht u hu he
    have hh := congrArg Subtype.val (hinj he)
    change (θ t:ℝ) = (θ u:ℝ) at hh
    rwa [hθval t ht,hθval u hu] at hh
  have hvi : InjOn v (Icc 0 ε) := c.axis_parameter_injective hAi
    (fun t ht => ⟨(hdata t ht).1,(hdata t ht).2.1⟩)
    (fun t ht => ⟨(hdata t ht).2.2.1,(hdata t ht).2.2.2.1,(hdata t ht).2.2.2.2⟩)
  have hvc : ContinuousOn v (Icc 0 ε) := (continuous_apply 1).comp_continuousOn
    (c.source.continuousOn.comp hA.fst.continuousOn (fun t ht => (hdata t ht).1))
  have hv0 : v 0 = 0 := by
    have hz : θ 0 = 0 := Subtype.ext (hθval 0 (left_mem_Icc.mpr hε.le))
    change c.source (Γ (θ 0)).1 1 = 0
    rw [hz,hzero]
    exact congrFun c.source_center 1
  have hs : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ StrictMonoOn (fun t => s*v t) (Icc 0 ε) := by
    rcases hvc.strictMonoOn_of_injOn_Icc' hε.le hvi with hm | hm
    · exact ⟨1,Or.inl rfl,by simpa only [one_mul] using hm⟩
    · refine ⟨-1,Or.inr rfl,?_⟩
      intro x hx y hy hxy
      simpa only [neg_one_mul,neg_lt_neg_iff] using hm hx hy hxy
  obtain ⟨s,hs,hm⟩ := hs
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  let d := s*v ε
  have hd : 0 < d := by
    have h := hm (left_mem_Icc.mpr hε.le) (right_mem_Icc.mpr hε.le) hε
    simpa only [hv0,mul_zero] using h
  have himage : (fun t => s*v t) '' Icc 0 ε = Icc 0 d := by
    have hc : ContinuousOn (fun t => s*v t) (Icc 0 ε) := continuousOn_const.mul hvc
    simpa only [hv0,mul_zero] using hc.image_Icc_of_monotoneOn hε.le hm.monotoneOn
  have hpair : ∀ t ∈ Icc 0 ε, A t = (c.axisCurve (v t),c.axisCurve (-(v t))) := by
    intro t ht
    exact c.axis_pair_coordinates (hdata t ht).1 (hdata t ht).2.1
      (hdata t ht).2.2.1 (hdata t ht).2.2.2.1 (hdata t ht).2.2.2.2
  have hAiimage : A '' Icc 0 ε = Γ '' {t : I | (t:ℝ) ≤ ε} := by
    apply Set.Subset.antisymm
    · rintro y ⟨t,ht,rfl⟩
      refine ⟨θ t,?_,rfl⟩
      change (θ t:ℝ) ≤ ε
      rw [hθval t ht]
      exact ht.2
    · rintro y ⟨t,ht,rfl⟩
      refine ⟨(t:ℝ),⟨t.property.1,ht⟩,?_⟩
      change Γ (θ (t:ℝ)) = Γ t
      congr 1
      exact Subtype.ext (hθval t ⟨t.property.1,ht⟩)
  refine ⟨ε,s,d,hε,hεsmall,hs,hd,?_,?_,?_⟩
  · rw [← hAiimage]
    apply Set.Subset.antisymm
    · rintro y ⟨t,ht,rfl⟩
      obtain ⟨u,hu,rfl⟩ := himage.symm.subset ht
      refine ⟨u,hu,?_⟩
      dsimp only
      rw [← mul_assoc,hss,one_mul]
      exact hpair u hu
    · rintro y ⟨u,hu,rfl⟩
      refine ⟨s*v u,himage.subset ⟨u,hu,rfl⟩,?_⟩
      dsimp only
      rw [← mul_assoc,hss,one_mul]
      exact (hpair u hu).symm
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := himage.symm.subset ht
    dsimp only
    rw [← mul_assoc,hss,one_mul]
    have hx : crosscapAxis (v u) = c.source (A u).1 := by
      rw [crosscapAxis_apply]
      ext i
      fin_cases i
      · exact (hdata u hu).2.2.1.symm
      · rfl
    have hy : crosscapAxis (-(v u)) = c.source (A u).2 := by
      rw [crosscapAxis_apply]
      ext i
      fin_cases i
      · exact (hdata u hu).2.2.2.1.symm
      · have h := (hdata u hu).2.2.2.2
        change -(c.source (A u).1 1) = c.source (A u).2 1
        linarith
    rw [hx,hy]
    exact ⟨c.source.map_source (hdata u hu).1,c.source.map_source (hdata u hu).2.1⟩

  · intro u hu
    change (c.axisCurve (s*(s*v ε)),c.axisCurve (-(s*(s*v ε)))) = Γ u
    rw [← mul_assoc,hss,one_mul,← hpair ε (right_mem_Icc.mpr hε.le)]
    change Γ (θ ε) = Γ u
    apply congrArg Γ
    apply Subtype.ext
    exact (hθval ε (right_mem_Icc.mpr hε.le)).trans hu.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
