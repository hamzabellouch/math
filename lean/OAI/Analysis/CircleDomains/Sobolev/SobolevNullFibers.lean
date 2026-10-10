import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevGraphNull
import OAI.Analysis.CircleDomains.Sobolev.LipschitzLengthFiberMajorant

namespace OAI

/-! The graph-null theorem removes exceptional scalar fibers for the
actual continuous local Sobolev representative. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma physical_graph_null_fibers (u : EuclideanPlane → ℝ) (E : Set EuclideanPlane)
    (hG : (μH[2] : Measure GraphSpace) (sobolevGraph u '' E) = 0) :
    ∀ᵐ t, (μH[1] : Measure EuclideanPlane) (E ∩ u ⁻¹' {t}) = 0 := by
  let G := sobolevGraph u '' E
  obtain ⟨H,hH,hbound,hint⟩ := exists_exact_lipschitz_length_fiber_majorant G
    (by rw [hG]; exact ENNReal.zero_lt_top) 1 Prod.snd LipschitzWith.prod_snd
  have hzero : (∫⁻ t, H t) = 0 := by
    apply le_antisymm _ bot_le
    simpa only [bot_eq_zero,G,hG,mul_zero] using hint
  let P : GraphSpace → EuclideanPlane := euclideanPlaneCoordinates.symm ∘ Prod.fst
  have hp := euclideanPlaneCoordinates.symm.lipschitzWith.comp
    (LipschitzWith.prod_fst (α := ℝ × ℝ) (β := ℝ))
  filter_upwards [(lintegral_eq_zero_iff hH).mp hzero] with t ht
  have hset : P '' (G ∩ Prod.snd ⁻¹' {t}) = E ∩ u ⁻¹' {t} := by
    ext x
    constructor
    · rintro ⟨z,⟨⟨y,hy,rfl⟩,hty⟩,rfl⟩
      simpa only [P,comp_apply,sobolevGraph,Prod.fst,Prod.snd,
        ContinuousLinearEquiv.symm_apply_apply,mem_inter_iff,mem_preimage,mem_singleton_iff]
        using And.intro hy hty
    · intro hx
      refine ⟨sobolevGraph u x,⟨⟨x,hx.1,rfl⟩,hx.2⟩,?_⟩
      exact euclideanPlaneCoordinates.symm_apply_apply x
  apply le_antisymm _ bot_le
  rw [← hset]
  have hm : (μH[1] : Measure GraphSpace) (G ∩ Prod.snd ⁻¹' {t}) = 0 := by
    apply le_antisymm _ bot_le
    simpa only [bot_eq_zero,ht,Pi.zero_apply] using hbound t
  have hh := hp.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1) (G ∩ Prod.snd ⁻¹' {t})
  simpa only [bot_eq_zero,hm,mul_zero] using hh

lemma locally_sobolev_null_fibers {u : EuclideanPlane → ℝ} (hu : Continuous u)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (hnull : volume E = 0) :
    ∀ᵐ t, (μH[1] : Measure EuclideanPlane) (E ∩ u ⁻¹' {t}) = 0 :=
  physical_graph_null_fibers u E (locally_sobolev_graph_null hu hw hLp hE hEb hnull)

end CircleDomainRigidity

end

end OAI
