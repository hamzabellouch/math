import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma finite_positive_weight_exists_ge {ι : Type*} [Fintype ι] [Nonempty ι]
    (w f : ι → ℝ) (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1) {a : ℝ}
    (ha : a≤∑ i, w i*f i) : ∃ i, a≤f i := by
  by_contra! h
  have hh : (∑ i, w i*f i)<∑ i, w i*a := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (mul_lt_mul_of_pos_left (h i) (hw i)).le
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨i,Finset.mem_univ i,mul_lt_mul_of_pos_left (h i) (hw i)⟩
  rw [←Finset.sum_mul,hsum,one_mul] at hh
  exact (not_lt_of_ge ha) hh

lemma finite_positive_weight_zero {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0<w i) (hf : ∀ i, f i≤0)
    (hsum : ∑ i, w i*f i=0) : ∀ i, f i=0 := by
  intro i
  apply le_antisymm (hf i)
  by_contra! hh
  have hs : (∑ j, w j*f j)<∑ j ∈ (Finset.univ : Finset ι), (0:ℝ) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_nonpos_of_nonneg_of_nonpos (hw j).le (hf j)
    · exact ⟨i,Finset.mem_univ i,mul_neg_of_pos_of_neg (hw i) hh⟩
  simp [hsum] at hs

lemma finite_transverse_quadratic_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → E →L[ℝ] ℝ) (B : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmean : ∀ v, ∑ i, w i*L i v=0)
    (hpos : ∀ v : E, v≠0 → (∀ i, L i v=0) → 0<∑ i, w i*B i v v) :
    ∃ b>0, ∀ᶠ h : E in 𝓝 0, ∃ i, b*‖h‖^2≤L i h+B i h h := by
  let Q : E → ℝ := fun v => ∑ i, w i*B i v v
  have hQ : Continuous Q := by
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul ((B i).continuous.clm_apply continuous_id))
  let K : Set E := {v | ‖v‖=1 ∧ ∀ i, L i v=0}
  have hK : IsCompact K := by
    have hc : IsClosed {v : E | ∀ i, L i v=0} := by
      simpa only [Set.ofPred_forall] using
        isClosed_iInter (fun i => isClosed_eq (L i).continuous (continuous_const (y := (0:ℝ))))
    exact (isCompact_sphere (0:E) 1).inter_right hc |>.of_isClosed_subset
      (isClosed_eq continuous_norm continuous_const |>.inter hc) (by
        intro v hv
        exact ⟨by simpa [Metric.mem_sphere,dist_zero_right] using hv.1,hv.2⟩)
  obtain ⟨b,hb,hbK⟩ : ∃ b>0, ∀ v ∈ K, b<Q v := by
    by_cases hne : K.Nonempty
    · obtain ⟨u,hu,hmin⟩ := hK.exists_isMinOn hne hQ.continuousOn
      have hp : 0<Q u := hpos u (by intro hz; simp [K,hz] at hu) hu.2
      refine ⟨Q u/2,by positivity,?_⟩
      intro v hv
      exact (half_lt_self hp).trans_le (hmin hv)
    · exact ⟨1,zero_lt_one,fun v hv => (hne ⟨v,hv⟩).elim⟩
  have hloc : ∀ u ∈ Metric.sphere (0:E) 1, ∀ᶠ z : ℝ × E in 𝓝 (0,u),
      0≤z.1 → ∃ i, z.1*b≤L i z.2+z.1*B i z.2 z.2 := by
    intro u hu
    by_cases hlin : ∃ i, 0<L i u
    · obtain ⟨i,hi⟩ := hlin
      have hc : Continuous (fun z : ℝ × E => L i z.2+z.1*(B i z.2 z.2-b)) := by
        exact ((L i).continuous.comp continuous_snd).add
          (continuous_fst.mul (((B i).continuous.comp continuous_snd).clm_apply continuous_snd |>.sub continuous_const))
      have he : ∀ᶠ z : ℝ × E in 𝓝 (0,u), 0<L i z.2+z.1*(B i z.2 z.2-b) :=
        hc.continuousAt.eventually (Ioi_mem_nhds (by simpa using hi))
      filter_upwards [he] with z hz _
      exact ⟨i,by nlinarith⟩
    · have hall : ∀ i, L i u=0 := finite_positive_weight_zero w (fun i => L i u) hw
        (by simpa only [not_exists,not_lt] using hlin) (hmean u)
      have huK : u ∈ K := ⟨by simpa [Metric.mem_sphere,dist_zero_right] using hu,hall⟩
      have he : ∀ᶠ z : ℝ × E in 𝓝 (0,u), b<Q z.2 :=
        (hQ.comp continuous_snd).continuousAt.eventually (Ioi_mem_nhds (hbK u huK))
      filter_upwards [he] with z hz hr
      apply finite_positive_weight_exists_ge w (fun i => L i z.2+z.1*B i z.2 z.2) hw hsum
      have heq : (∑ i, w i*(L i z.2+z.1*B i z.2 z.2))=z.1*Q z.2 := by
        simp only [mul_add,Finset.sum_add_distrib,hmean,zero_add,Q]
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hz.le hr
  have he : ∀ᶠ r : ℝ in 𝓝 0, ∀ u ∈ Metric.sphere (0:E) 1,
      0≤r → ∃ i, r*b≤L i u+r*B i u u :=
    (isCompact_sphere (0:E) 1).eventually_forall_of_forall_eventually hloc
  have hnorm : Tendsto (fun h : E => ‖h‖) (𝓝 0) (𝓝 (0:ℝ)) := by simpa only [norm_zero] using (continuous_norm.tendsto (0:E))
  refine ⟨b,hb,?_⟩
  filter_upwards [hnorm.eventually he] with h hh
  by_cases hz : h=0
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i,by simp [hz]⟩
  · let u := ‖h‖⁻¹ • h
    have hn : 0<‖h‖ := norm_pos_iff.mpr hz
    have hu : u ∈ Metric.sphere (0:E) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,u,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    obtain ⟨i,hi⟩ := hh u hu hn.le
    have hv : ‖h‖ • u=h := by simp [u,smul_smul,hn.ne']
    have hil := mul_le_mul_of_nonneg_left hi hn.le
    refine ⟨i,?_⟩
    calc
      b*‖h‖^2≤‖h‖*(L i u+‖h‖*B i u u) := by nlinarith [hil]
      _ = L i h+B i h h := by
        have hL : L i h=‖h‖*L i u := by
          calc _ = L i (‖h‖ • u) := congrArg (L i) hv.symm
               _ = _ := by simp only [map_smul,smul_eq_mul]
        have hB : B i h h=‖h‖*(‖h‖*B i u u) := by
          calc _ = B i (‖h‖ • u) (‖h‖ • u) := by rw [hv]
               _ = _ := by simp only [map_smul,smul_apply,smul_eq_mul]
        rw [hL,hB]
        ring
end WeakMTWTransport

end

end OAI
