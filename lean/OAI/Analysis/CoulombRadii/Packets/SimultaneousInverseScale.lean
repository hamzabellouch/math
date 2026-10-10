import Mathlib
import OAI.Analysis.CoulombRadii.Packets.NormalizedBandModulus

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace NeutralAtom

lemma exists_simultaneous_inverse_scale {c L D A B ξ ε : ℝ}
    (hc : 0 < c) (hξ : 0 < ξ) (hε : 0 < ε) :
    ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1/16 ∧ ∀ {r : ℝ},0 < r → r < s₀ →
      c*(1+packetExponent)*r^packetExponent ≤ 1/4 ∧
      c*r^packetExponent ≤ 1/10000 ∧
      (8*L/100000)*r ≤ 1 ∧ D*((8*L/100000)*r)^7 ≤ 1 ∧
      Real.sqrt 3*r^(101/100:ℝ) ≤ r/12 ∧
      c*(r/3)*(r/3)^packetExponent ≤ r ∧
      A*r ≤ 1 ∧ A*r*(r/(c*(r/3)*(r/3)^packetExponent))^3 ≤ ξ/8 ∧
      B*(r*(r/(c*(r/3)*(r/3)^packetExponent))^4) ≤ ε := by
  have hw : 0 < packetExponent := by norm_num [packetExponent]
  have h1 := (tendsto_positive_rpow_zero hw).const_mul (c*(1+packetExponent))
  have h2 := (tendsto_positive_rpow_zero hw).const_mul c
  have ht : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h3 := ht.const_mul (8*L/100000)
  have h4 := ((ht.const_mul (8*L/100000)).pow 7).const_mul D
  have h5 := (tendsto_positive_rpow_zero (by norm_num : (0:ℝ) < 1/100)).const_mul (Real.sqrt 3)
  have h6 := (tendsto_positive_rpow_zero hw).const_mul (c/(3^packetExponent))
  have h7 := ht.const_mul A
  have h8 := (mesh_width_power_tendsto hc 3 (by norm_num [packetExponent])).const_mul A
  have h9 := (mesh_width_power_tendsto hc 4 (by norm_num [packetExponent])).const_mul B
  simp only [mul_zero,zero_pow (by decide : 7≠0)] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0,
      c*(1+packetExponent)*r^packetExponent < 1/4 ∧
      c*r^packetExponent < 1/10000 ∧
      (8*L/100000)*r < 1 ∧ D*((8*L/100000)*r)^7 < 1 ∧
      Real.sqrt 3*r^(1/100:ℝ) < 1/12 ∧
      (c/(3^packetExponent))*r^packetExponent < 3 ∧
      A*r < 1 ∧ A*(r*(r/(c*(r/3)*(r/3)^packetExponent))^3) < ξ/8 ∧
      B*(r*(r/(c*(r/3)*(r/3)^packetExponent))^4) < ε := by
    filter_upwards [h1.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
      h2.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/10000)),
      h3.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
      h4.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
      h5.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/12)),
      h6.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 3)),
      h7.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
      h8.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ξ/8)),
      h9.eventually (gt_mem_nhds hε)] with r hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9
    exact ⟨hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9⟩
  obtain ⟨s,hs,Hs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨min s (1/16),lt_min hs (by norm_num),min_le_right _ _,?_⟩
  intro r hr hrs
  obtain ⟨H1,H2,H3,H4,H5,H6,H7,H8,H9⟩ := Hs ⟨hr,hrs.trans_le (min_le_left _ _)⟩
  refine ⟨H1.le,H2.le,H3.le,H4.le,?_,?_,H7.le,?_,H9.le⟩
  · have he : (101/100:ℝ)=1+1/100 := by norm_num
    rw [he,Real.rpow_add hr,Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left H5.le hr.le]
  · have ht : c*(r/3)^packetExponent < 3 := by
      rw [Real.div_rpow hr.le (by norm_num : (0:ℝ) ≤ 3)]
      convert H6 using 1
      ring
    nlinarith [mul_le_mul_of_nonneg_left ht.le (by positivity : 0 ≤ r/3)]
  · simpa only [mul_assoc] using H8.le
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma mesh_exception_probability_scale {r L C N M : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hM : 0 ≤ M) (hMbound : M ≤ (12*L+1)^3/r^3) :
    r^40+C*r^249+2*M*N*r^42 ≤ (1+C+2*(12*L+1)^3*N)*r^25 := by
  have h40 : r^40 ≤ r^25 := pow_le_pow_of_le_one hr.le hr1 (by omega)
  have h249 : r^249 ≤ r^25 := pow_le_pow_of_le_one hr.le hr1 (by omega)
  have h39 : r^39 ≤ r^25 := pow_le_pow_of_le_one hr.le hr1 (by omega)
  have H : 2*M*N*r^42 ≤ 2*(12*L+1)^3*N*r^39 := by
    calc
      _ ≤ 2*((12*L+1)^3/r^3)*N*r^42 := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        apply mul_le_mul_of_nonneg_right ?_ hN
        exact mul_le_mul le_rfl hMbound hM (by norm_num)
      _ = _ := by field_simp
  calc
    _ ≤ r^25+C*r^25+2*(12*L+1)^3*N*r^25 :=
      add_le_add (add_le_add h40 (mul_le_mul_of_nonneg_left h249 hC))
        (H.trans (mul_le_mul_of_nonneg_left h39 (by positivity)))
    _ = _ := by ring
end NeutralAtom
end

end

end OAI
