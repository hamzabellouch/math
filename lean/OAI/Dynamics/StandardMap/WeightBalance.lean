import OAI.Dynamics.StandardMap.CappedPrelimit

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma affine_cap_cover : affineLocus ⊆ slowCapOpen∪(⋃q:{q:ℚ // 0<q},middleCapOpen (q.val:ℝ))∪{unitAffine} := by
  rintro d ⟨w,rfl⟩
  by_cases hw:w.val≤999/1000
  · exact Or.inl (Or.inl (affine_mem_slowOpen w hw))
  by_cases hw1:w.val<1
  · obtain ⟨q,hq,hqw⟩:=exists_rat_btwn (sub_pos.mpr hw1)
    have hq':0<q := by exact_mod_cast hq
    exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨q,hq'⟩,affine_mem_middleOpen w (lt_of_not_ge hw) hqw hw1⟩))
  · have he:w=⟨1,by norm_num⟩ := Subtype.ext (le_antisymm w.property.2 (le_of_not_gt hw1))
    exact Or.inr (by rw [he]; rfl)
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma weight_affine_null {α:ℝ} (hα:0≤α) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f) :
    Q.law affineLocus=0 := by
  apply measure_mono_null affine_cap_cover
  apply measure_union_null
  · apply measure_union_null (Q.slow_null h0 hb)
    apply measure_iUnion_null
    intro q
    exact S.weight_middle_null L f hf h0 hb Q (by exact_mod_cast q.property)
  · exact S.weight_unit_null L hα f hf h0 hb Q
lemma cap_dominated_tendsto {α:ℝ} (hα:0≤α) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) :
    Tendsto (fun i => ∫d,f d ∂S.multiLaw i) (L.filter:Filter ℕ) (𝓝 (∫d:NonAffineArray,f d.val ∂L.multi)) := by
  obtain ⟨C,hC,hcap⟩:=capG_bound α
  obtain ⟨D,hD⟩:=S.multiLaw_test_bound coreTestIndex
  have hB:∀ᶠi in (L.filter:Filter ℕ),(∫d,f d ∂S.multiLaw i)≤C*D := by
    filter_upwards [hD.filter_mono L.refines] with i hi
    have h:=integral_mono (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (((continuous_arrayTest _).const_mul C).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun d => (hb d).trans (hcap d)) (μ:=S.multiLaw i)
    rw [integral_const_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hi hC)
  obtain ⟨Q⟩:=exists_compact_weight_limit L.filter S.multiLaw f hf h0 (C*D) hB
  exact S.weight_tendsto_integral L f hf h0 hb Q (S.weight_affine_null L hα f hf h0 hb Q)
lemma capG_limit_balance {α:ℝ} (hα:0≤α) :
    Tendsto (fun i => ∫d,capG α d ∂S.multiLaw i) (L.filter:Filter ℕ)
      (𝓝 (∫d:NonAffineArray,capG α d.val ∂L.multi)) := by
  let f:DistanceArray→ℝ:=fun d=>max (capG α d) 0
  let g:DistanceArray→ℝ:=fun d=>max (-capG α d) 0
  have hf:Continuous f := (continuous_capG α).max continuous_const
  have hg:Continuous g := (continuous_capG α).neg.max continuous_const
  have hfb:∀d,f d≤|capG α d| := fun d=>max_le (le_abs_self _) (abs_nonneg _)
  have hgb:∀d,g d≤|capG α d| := fun d=>max_le (neg_le_abs _) (abs_nonneg _)
  have hft:=S.cap_dominated_tendsto L hα f hf (fun d=>le_max_right _ _) hfb
  have hgt:=S.cap_dominated_tendsto L hα g hg (fun d=>le_max_right _ _) hgb
  have he:∀d,capG α d=f d-g d := by
    intro d; dsimp [f,g]
    by_cases hd:0≤capG α d
    · rw [max_eq_left hd,max_eq_right (neg_nonpos.mpr hd),sub_zero]
    · rw [max_eq_right (le_of_not_ge hd),max_eq_left (neg_nonneg.mpr (le_of_not_ge hd))]; ring
  have hif:=S.cap_dominated_integrable L (α:=α) f hf (fun d => by rw [abs_of_nonneg (show 0≤f d from le_max_right _ _)]; exact hfb d)
  have hig:=S.cap_dominated_integrable L (α:=α) g hg (fun d => by rw [abs_of_nonneg (show 0≤g d from le_max_right _ _)]; exact hgb d)
  simp_rw [he]
  rw [integral_sub hif hig]
  have hsi (i:ℕ):(∫d,f d-g d ∂S.multiLaw i)=(∫d,f d ∂S.multiLaw i)-(∫d,g d ∂S.multiLaw i) :=
    integral_sub (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  simp_rw [hsi]
  exact hft.sub hgt
end CriticalScaleSequence
end StandardMapEntropy

end OAI
