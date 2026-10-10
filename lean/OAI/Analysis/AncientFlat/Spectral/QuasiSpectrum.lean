import OAI.Analysis.AncientFlat.Spectral.QuasiFinite
import OAI.Analysis.AncientFlat.Spectral.QuasiPowers
import OAI.Analysis.AncientFlat.Spectral.CompactFredholm

namespace OAI
noncomputable section
open Set Filter Topology Module.End
namespace FlatSpectral
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
lemma resolvent_of_power_bound (R : X →L[ℂ] X) (a C : ℝ)
    (ha : 0≤a) (hb : ∀ n : ℕ, ‖R^n‖≤C*a^n)
    (z : ℂ) (hz : a<‖z‖) : z∈resolventSet ℂ R := by
  by_contra hs
  obtain ⟨n,hn,hsmall⟩ := exists_power_small R a C ‖z‖ ha (lt_of_le_of_lt ha hz) hz hb
  have hsp := spectrum.norm_le_norm_mul_of_mem (spectrum.pow_mem_pow R n hs)
  have h1 : ‖(1 : X →L[ℂ] X)‖≤1 := ContinuousLinearMap.norm_id_le
  have hb' : ‖z‖^n≤‖R^n‖ := by
    calc
      _ = ‖z^n‖ := (norm_pow z n).symm
      _ ≤ ‖R^n‖*‖(1 : X →L[ℂ] X)‖ := hsp
      _ ≤ ‖R^n‖*1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := mul_one _
  have := norm_nonneg (R^n)
  linarith

lemma finite_spectrum_outside (T R : X →L[ℂ] X) (hK : IsCompactOperator (T-R))
    (a C : ℝ) (ha : 0≤a) (hb : ∀ n : ℕ, ‖R^n‖≤C*a^n)
    (r : ℝ) (hr : a<r) : {z : ℂ | r≤‖z‖ ∧ z∈spectrum ℂ T}.Finite := by
  have hr0 : 0<r := lt_of_le_of_lt ha hr
  obtain ⟨n,hn,hsmall⟩ := exists_power_small R a C r ha hr0 hr hb
  have hf := finite_eigenvalues_of_small_remainder (T^n) (R^n) (compact_difference_pow T R hK n)
    (r^n) hsmall
  have hp := finite_preimage_pow n hn _ hf
  apply hp.subset
  intro z hz
  refine ⟨?_,?_⟩
  · rw [norm_pow]
    exact pow_le_pow_left₀ hr0.le hz.1 n
  · have he := hasEigenvalue_of_mem_spectrum_compact_difference T R hK z
      (resolvent_of_power_bound R a C ha hb z (lt_of_lt_of_le hr hz.1)) hz.2
    simpa only [ContinuousLinearMap.toLinearMap_pow] using he.pow n

lemma countable_spectrum_outside (T R : X →L[ℂ] X) (hK : IsCompactOperator (T-R))
    (a C : ℝ) (ha : 0≤a) (hb : ∀ n : ℕ, ‖R^n‖≤C*a^n) :
    {z : ℂ | a<‖z‖ ∧ z∈spectrum ℂ T}.Countable := by
  have hf (n : ℕ) := (finite_spectrum_outside T R hK a C ha hb (a+1/((n:ℝ)+1))
    (by
      have : 0<1/((n:ℝ)+1) := by positivity
      linarith)).countable
  apply (countable_iUnion hf).mono
  intro z hz
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hz.1)
  exact mem_iUnion.mpr ⟨n,by exact ⟨by linarith,hz.2⟩⟩

theorem exists_circle_of_compact_difference_power_bound (T R : X →L[ℂ] X)
    (hK : IsCompactOperator (T-R)) (a C : ℝ) (ha : 0≤a) (ha1 : a<1)
    (hb : ∀ n : ℕ, ‖R^n‖≤C*a^n) :
    ∃ q : ℝ, a<q ∧ q<1 ∧ ∀ z : ℂ, ‖z‖=q → z∈resolventSet ℂ T := by
  have hc := (countable_spectrum_outside T R hK a C ha hb).image (fun z : ℂ => ‖z‖)
  obtain ⟨q,hqi,hqn⟩ := (hc.dense_compl ℝ).inter_open_nonempty (Ioo a 1) isOpen_Ioo (nonempty_Ioo.mpr ha1)
  refine ⟨q,hqi.1,hqi.2,fun z hz => ?_⟩
  by_contra hzs
  apply hqn
  exact ⟨z,⟨by rw [hz]; exact hqi.1,hzs⟩,hz⟩
end FlatSpectral

end

end OAI
