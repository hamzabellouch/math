import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.FiniteNonnegativeWeight

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {P E : Type*} [TopologicalSpace P] [CompactSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [Nonempty ι]

lemma uniform_finite_transverse_quadratic_growth
    (w : P → ι → ℝ) (L : P → ι → E →L[ℝ] ℝ)
    (B : P → ι → E →L[ℝ] E →L[ℝ] ℝ)
    (hw : ∀ a i, 0 ≤ w a i) (hsum : ∀ a, ∑ i, w a i = 1)
    (hmean : ∀ a v, ∑ i, w a i * L a i v = 0)
    (hwc : ∀ i, Continuous (fun a => w a i))
    (hLc : ∀ i, Continuous (fun a => L a i))
    (hBc : ∀ i, Continuous (fun a => B a i))
    (hpos : ∀ a v, ‖v‖ = 1 → (∀ i, L a i v ≤ 0) →
      0 < ∑ i, w a i * B a i v v) :
    ∃ b > 0, ∀ᶠ h : E in 𝓝 0, ∀ a : P, ∃ i,
      b * ‖h‖ ^ 2 ≤ L a i h + B a i h h := by
  let Q : P × E → ℝ := fun z => ∑ i, w z.1 i * B z.1 i z.2 z.2
  have hQ : Continuous Q := by
    apply continuous_finsetSum
    intro i _
    exact ((hwc i).comp continuous_fst).mul
      (((hBc i).comp continuous_fst).clm_apply continuous_snd |>.clm_apply continuous_snd)
  have hL : ∀ i, Continuous (fun z : P × E => L z.1 i z.2) :=
    fun i => ((hLc i).comp continuous_fst).clm_apply continuous_snd
  let C : Set (P × E) := univ ×ˢ Metric.sphere (0:E) 1
  have hC : IsCompact C := isCompact_univ.prod (isCompact_sphere (0:E) 1)
  let K : Set (P × E) := C ∩ {z | ∀ i, L z.1 i z.2 ≤ 0}
  have hK : IsCompact K := by
    apply hC.inter_right
    simpa only [Set.ofPred_forall] using
      isClosed_iInter (fun i => isClosed_le (hL i) continuous_const)
  obtain ⟨b,hb,hbK⟩ : ∃ b > 0, ∀ z ∈ K, b < Q z := by
    by_cases hne : K.Nonempty
    · obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne hQ.continuousOn
      have hp : 0 < Q z := hpos z.1 z.2
        (by simpa only [Metric.mem_sphere,dist_zero_right] using hz.1.2) hz.2
      exact ⟨Q z / 2,half_pos hp,fun y hy => (half_lt_self hp).trans_le (hmin hy)⟩
    · exact ⟨1,zero_lt_one,fun z hz => (hne ⟨z,hz⟩).elim⟩
  have hloc : ∀ z ∈ C, ∀ᶠ q : ℝ × (P × E) in 𝓝 (0,z),
      0 ≤ q.1 → ∃ i, q.1 * b ≤ L q.2.1 i q.2.2 + q.1 * B q.2.1 i q.2.2 q.2.2 := by
    intro z hz
    by_cases hlin : ∃ i, 0 < L z.1 i z.2
    · obtain ⟨i,hi⟩ := hlin
      have hc : Continuous (fun q : ℝ × (P × E) =>
          L q.2.1 i q.2.2 + q.1 * (B q.2.1 i q.2.2 q.2.2 - b)) := by
        exact ((hL i).comp continuous_snd).add
          (continuous_fst.mul (((((hBc i).comp (continuous_fst.comp continuous_snd)).clm_apply
            (continuous_snd.comp continuous_snd)).clm_apply
              (continuous_snd.comp continuous_snd)).sub continuous_const))
      have he : ∀ᶠ q : ℝ × (P × E) in 𝓝 (0,z),
          0 < L q.2.1 i q.2.2 + q.1 * (B q.2.1 i q.2.2 q.2.2 - b) :=
        hc.continuousAt.eventually (Ioi_mem_nhds (by simpa using hi))
      filter_upwards [he] with q hq _
      exact ⟨i,by nlinarith⟩
    · have hzK : z ∈ K := ⟨hz,fun i => le_of_not_gt (fun h => hlin ⟨i,h⟩)⟩
      have he : ∀ᶠ q : ℝ × (P × E) in 𝓝 (0,z), b < Q q.2 :=
        (hQ.comp continuous_snd).continuousAt.eventually (Ioi_mem_nhds (hbK z hzK))
      filter_upwards [he] with q hq hr
      apply finite_nonnegative_weight_exists_ge (w q.2.1)
        (fun i => L q.2.1 i q.2.2 + q.1 * B q.2.1 i q.2.2 q.2.2)
        (hw q.2.1) (hsum q.2.1)
      have heq : (∑ i, w q.2.1 i *
          (L q.2.1 i q.2.2 + q.1 * B q.2.1 i q.2.2 q.2.2)) = q.1 * Q q.2 := by
        simp only [mul_add,Finset.sum_add_distrib,hmean,zero_add,Q]
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hq.le hr
  have he : ∀ᶠ r : ℝ in 𝓝 0, ∀ z ∈ C, 0 ≤ r → ∃ i,
      r * b ≤ L z.1 i z.2 + r * B z.1 i z.2 z.2 :=
    hC.eventually_forall_of_forall_eventually hloc
  have hnorm : Tendsto (fun h : E => ‖h‖) (𝓝 0) (𝓝 (0:ℝ)) := by
    simpa only [norm_zero] using continuous_norm.tendsto (0:E)
  refine ⟨b,hb,?_⟩
  filter_upwards [hnorm.eventually he] with h hh
  intro a
  by_cases hz : h = 0
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i,by simp [hz]⟩
  · let v := ‖h‖⁻¹ • h
    have hn : 0 < ‖h‖ := norm_pos_iff.mpr hz
    have hv : v ∈ Metric.sphere (0:E) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,v,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    obtain ⟨i,hi⟩ := hh (a,v) ⟨mem_univ _,hv⟩ hn.le
    have hv' : ‖h‖ • v = h := by simp [v,smul_smul,hn.ne']
    have hil := mul_le_mul_of_nonneg_left hi hn.le
    refine ⟨i,?_⟩
    have hL' : L a i h = ‖h‖ * L a i v := by
      calc _ = L a i (‖h‖ • v) := congrArg (L a i) hv'.symm
           _ = _ := by simp only [map_smul,smul_eq_mul]
    have hB' : B a i h h = ‖h‖ * (‖h‖ * B a i v v) := by
      calc _ = B a i (‖h‖ • v) (‖h‖ • v) := by rw [hv']
           _ = _ := by simp only [map_smul,_root_.smul_apply,smul_eq_mul]
    rw [hL',hB']
    nlinarith

end WeakMTWTransport

end

end OAI
