import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


namespace WeakHessianFunctional
open Set Filter
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma dualTransport_pairing_le
    {q ρ A : ℝ → E} {e : ℝ → ℝ} {a b α M : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α)
    (hq : ContinuousOn q (Icc a b)) (hρ : ContinuousOn ρ (Icc a b))
    (hyoung : ∀ t ∈ Ico a b, -α*e t + ⟪q t,A t⟫_ℝ ≤ M)
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt ρ (A t) (Ici t) t)
    (hinc : ∀ t ∈ Ico a b, ∀ s ∈ Ioc t b,
      ⟪q s-q t,ρ t⟫_ℝ ≤ -(s-t)*t/s*α*e t) :
    ⟪q b,ρ b⟫_ℝ - ⟪q a,ρ a⟫_ℝ ≤ (b-a)*M := by
  let J : ℝ → ℝ := fun t => ⟪q t,ρ t⟫_ℝ
  have hJ : ContinuousOn J (Icc a b) := hq.inner hρ
  have HB : ∀ t, HasDerivAt (fun s => J a + M*(s-a)) M t := by
    intro t
    simpa only [mul_one, id_eq] using! (((hasDerivAt_id t).sub_const a).const_mul M).const_add (J a)
  have hbound : ∀ t ∈ Ico a b, ∀ r : ℝ, M < r →
      ∃ᶠ s in 𝓝[>] t, slope J t s < r := by
    intro t ht r hr
    have ht0 : 0 < t := ha.trans_le ht.1
    have hqs : Tendsto q (𝓝[>] t) (𝓝 (q t)) :=
      (hq t (Ico_subset_Icc_self ht)).mono_left
        (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ht))
    have hρs : Tendsto (slope ρ t) (𝓝[>] t) (𝓝 (A t)) :=
      (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp (hderiv t ht).Ioi_of_Ici
    have hl : Tendsto (fun s : ℝ => -t/s*α*e t + ⟪q s,slope ρ t s⟫_ℝ)
        (𝓝[>] t) (𝓝 (-α*e t + ⟪q t,A t⟫_ℝ)) := by
      have hrat : Tendsto (fun s : ℝ => -t/s*α*e t)
          (𝓝[>] t) (𝓝 (-α*e t)) := by
        have H : Tendsto (fun s : ℝ => -t/s*α*e t)
            (𝓝[>] t) (𝓝 (-t/t*α*e t)) :=
          (((tendsto_const_nhds.div (tendsto_id.mono_left nhdsWithin_le_nhds) ht0.ne').mul_const α).mul_const
            (e t))
        simpa [ht0.ne'] using H
      exact hrat.add (hqs.inner hρs)
    have hy : -α*e t + ⟪q t,A t⟫_ℝ ≤ M := hyoung t ht
    have hev : ∀ᶠ s in 𝓝[>] t, slope J t s < r := by
      filter_upwards [hl.eventually_lt_const (hy.trans_lt hr), Ioc_mem_nhdsGT ht.2] with s hs hsI
      apply lt_of_le_of_lt _ hs
      have hi := (div_le_div_of_nonneg_right (hinc t ht s hsI) (sub_nonneg.mpr hsI.1.le))
      have heq : slope J t s = ⟪q s-q t,ρ t⟫_ℝ/(s-t) + ⟪q s,slope ρ t s⟫_ℝ := by
        simp only [slope_def_field, slope_def_module, real_inner_smul_right, inner_sub_left,
          inner_sub_right, J]
        ring
      rw [heq]
      have he : (-(s-t)*t/s*α*e t)/(s-t) =
          -t/s*α*e t := by
        field_simp [sub_ne_zero.mpr hsI.1.ne']
      rw [he] at hi
      linarith
    exact hev.frequently
  have H := image_le_of_liminf_slope_right_le_deriv_boundary hJ
    (show J a ≤ J a+M*(a-a) by simp)
    (by fun_prop : ContinuousOn (fun s => J a+M*(s-a)) (Icc a b))
    (fun t _ => (HB t).hasDerivWithinAt) hbound (right_mem_Icc.mpr hab)
  calc
    _ ≤ M*(b-a) := by change J b-J a ≤ M*(b-a); linarith
    _ = _ := by ring

end WeakHessianFunctional

end

end OAI
