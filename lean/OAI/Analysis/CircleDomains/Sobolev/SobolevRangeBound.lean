import OAI.Analysis.CircleDomains.Sobolev.BoundedSobolevChain
import OAI.Analysis.CircleDomains.Sobolev.ZeroWeakGradient
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

/-! The weak gradient cannot support an excess range hidden on a set
where that gradient vanishes. This will identify values on point dust. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem ae_le_of_compact_sobolev_gradient_zero_above
    {u : EuclideanPlane → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u univ)
    (hs : HasCompactSupport u) (hu : ∀ x, u x ∈ Icc 0 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hg : ∀ i : Fin 2, ∀ᵐ x ∂volume, b < u x → hw.weakGrad x i = 0) :
    ∀ᵐ x ∂volume, u x ≤ b := by
  let F : ℝ → ℝ := fun t => Real.smoothTransition (t - b)
  have hF : ContDiff ℝ 1 F := Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have hF0 : F 0 = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  have hFs : HasCompactSupport (F ∘ u) := hs.comp_left hF0
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hm : AEStronglyMeasurable (F ∘ u) volume :=
    hF.continuous.comp_aestronglyMeasurable huL.aestronglyMeasurable
  have hL : MemLp (F ∘ u) 2 volume := by
    let K := tsupport (F ∘ u)
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hFs.isCompact.measure_lt_top.ne
    have ht : MemLp (F ∘ u) 2 (volume.restrict K) :=
      MemLp.of_bound hm.restrict 1 (Eventually.of_forall fun x => by
        change ‖Real.smoothTransition (u x - b)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _)
    have he : K.indicator (F ∘ u) = F ∘ u := by
      funext x
      by_cases hx : x ∈ K
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx]
        exact (image_eq_zero_of_notMem_tsupport hx).symm
    rw [← he]
    exact (memLp_indicator_iff_restrict hFs.isCompact.isClosed.measurableSet).mpr ht
  have hd (t : ℝ) (ht : t ≤ b) : deriv F t = 0 := by
    apply IsLocalMin.deriv_eq_zero
    apply Eventually.of_forall
    intro y
    change F t ≤ F y
    have hz : F t = 0 := Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht)
    rw [hz]
    exact Real.smoothTransition.nonneg _
  have hgrad (i : Fin 2) :
      (fun x => deriv F (u x) * hw.weakGrad x i) =ᵐ[volume] 0 := by
    filter_upwards [hg i] with x hx
    by_cases ht : b < u x
    · simp only [hx ht, mul_zero, Pi.zero_apply]
    · simp only [hd _ (le_of_not_gt ht), zero_mul, Pi.zero_apply]
  let hW : DeGiorgi.MemW1pWitness 2 (F ∘ u) univ := {
    memLp := by simpa only [Measure.restrict_univ] using hL
    weakGrad := 0
    weakGrad_component_memLp := by
      intro i
      simp
    isWeakGrad := by
      intro i φ hφ hφs hφsub
      have ht := bounded_sobolev_chain_rule hw hs hu hF i φ hφ hφs hφsub
      have hi : (∫ x in univ, deriv F (u x) * hw.weakGrad x i * φ x) = 0 := by
        simp only [Measure.restrict_univ]
        apply integral_eq_zero_of_ae
        filter_upwards [hgrad i] with x hx
        change deriv F (u x) * hw.weakGrad x i = 0 at hx
        simp only [hx, zero_mul, Pi.zero_apply]
      rw [hi, neg_zero] at ht
      simpa using ht }
  have hz := zero_of_compact_support_zero_weak_gradient hW hFs
    (fun _ => Eventually.of_forall fun _ => rfl)
  filter_upwards [hz] with x hx
  exact sub_nonpos.mp (Real.smoothTransition.zero_iff_nonpos.mp hx)

end CircleDomainRigidity

end

end OAI
