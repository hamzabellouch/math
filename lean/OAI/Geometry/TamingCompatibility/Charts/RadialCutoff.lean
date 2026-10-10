import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialLower

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma cutoff_joint_smooth (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (h0 : (0:E) ∉ tsupport χ) (f : ℝ → E → ℝ)
    (hf : ∀ p : ℝ × E, p.2 ≠ 0 → ContDiffAt ℝ ∞ (fun q : ℝ × E => f q.1 q.2) p) :
    ContDiff ℝ ∞ (fun p : ℝ × E => χ p.2 * f p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 = 0
  · have hz : χ =ᶠ[𝓝 p.2] 0 := by
      rw [hp]
      exact notMem_tsupport_iff_eventuallyEq.mp h0
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × E => (0:ℝ)) p).congr_of_eventuallyEq
    filter_upwards [hz.comp_tendsto continuous_snd.continuousAt] with q hq
    change χ q.2 = 0 at hq
    rw [hq,zero_mul]
  · exact (hχ.comp contDiff_snd).contDiffAt.mul (hf p hp)

lemma cutoff_log_joint_smooth (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (h0 : (0:E) ∉ tsupport χ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => χ p.2 * logPotential p.1 p.2) := by
  apply cutoff_joint_smooth χ hχ h0
  intro p hp
  apply log_joint_smooth_at
  have hz : 0 < ‖p.2‖ := norm_pos_iff.mpr hp
  nlinarith [sq_nonneg p.1]

lemma cutoff_sqrt_joint_smooth (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (h0 : (0:E) ∉ tsupport χ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => χ p.2 * sqrtPotential p.1 p.2) := by
  apply cutoff_joint_smooth χ hχ h0
  intro p hp
  apply sqrt_joint_smooth_at
  have hz : 0 < ‖p.2‖ := norm_pos_iff.mpr hp
  nlinarith [sq_nonneg p.1]

lemma norm_iteratedFDeriv_slice_le (f : ℝ × E → ℝ) (hf : ContDiff ℝ ∞ f)
    (s : ℝ) (z : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => f (s,x)) z‖ ≤ ‖iteratedFDeriv ℝ n f (s,z)‖ := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  have he : (fun x : E => f (s,x)) = (fun q : ℝ × E => f ((s,0)+q)) ∘ L := by
    funext x
    simp [L]
  have hshift : ContDiff ℝ ∞ (fun q : ℝ × E => f ((s,0)+q)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [he,L.iteratedFDeriv_comp_right hshift z
    (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  have hnorm := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n (fun q : ℝ × E => f ((s,0)+q)) (L z)) (fun _ : Fin n => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hnorm
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ ℝ E
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun q : ℝ × E => f ((s,0)+q)) (L z)‖ * ‖L‖^n := hnorm
    _ ≤ ‖iteratedFDeriv ℝ n (fun q : ℝ × E => f ((s,0)+q)) (L z)‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg L) hL) (norm_nonneg _)
    _ = _ := by rw [iteratedFDeriv_comp_add_left]; simp [L]

lemma smooth_slice_derivatives_bounded (f : ℝ × E → ℝ) (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ n (fun x => f (s,x)) z‖ ≤ C := by
  have hc := hf.continuous_iteratedFDeriv (m := n) (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s hs z hz
  exact (norm_iteratedFDeriv_slice_le f hf s z n).trans ((hC (s,z) ⟨hs,hz⟩).trans (le_max_left _ _))

lemma cutoff_slice_derivatives_bounded (χ : E → ℝ) (hχc : HasCompactSupport χ)
    (f : ℝ → E → ℝ)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => χ p.2*f p.1 p.2)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ z : E,
      ‖iteratedFDeriv ℝ n (fun x => χ x*f s x) z‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := smooth_slice_derivatives_bounded
    (fun p : ℝ × E => χ p.2*f p.1 p.2) hf hχc n
  refine ⟨C,hC,?_⟩
  intro s hs z
  by_cases hz : z ∈ tsupport χ
  · exact hbound s hs z hz
  · have hz' : z ∉ tsupport (iteratedFDeriv ℝ n (fun x => χ x*f s x)) := by
      intro h
      exact hz (tsupport_mul_subset_left ((tsupport_iteratedFDeriv_subset n) h))
    rw [image_eq_zero_of_notMem_tsupport hz',norm_zero]
    exact hC

lemma cutoff_log_derivatives_bounded (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (h0 : (0:E) ∉ tsupport χ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ z : E,
      ‖iteratedFDeriv ℝ n (fun x => χ x*logPotential s x) z‖ ≤ C :=
  cutoff_slice_derivatives_bounded χ hχc logPotential (cutoff_log_joint_smooth χ hχ h0) n

lemma cutoff_sqrt_derivatives_bounded (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (h0 : (0:E) ∉ tsupport χ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ z : E,
      ‖iteratedFDeriv ℝ n (fun x => χ x*sqrtPotential s x) z‖ ≤ C :=
  cutoff_slice_derivatives_bounded χ hχc sqrtPotential (cutoff_sqrt_joint_smooth χ hχ h0) n
end TamingCompatibility.RadialPotential

end

end OAI
