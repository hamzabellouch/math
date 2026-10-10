import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter
open scoped ContDiff Topology
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cutoff_parameter_smooth (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (h0 : (0:E) ∉ tsupport χ) (f : P → E → ℝ)
    (hf : ∀ p : P × E, p.2 ≠ 0 → ContDiffAt ℝ ∞ (fun q : P × E => f q.1 q.2) p) :
    ContDiff ℝ ∞ (fun p : P × E => χ p.2 * f p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 = 0
  · have hz : χ =ᶠ[𝓝 p.2] 0 := by
      rw [hp]
      exact notMem_tsupport_iff_eventuallyEq.mp h0
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : P × E => (0:ℝ)) p).congr_of_eventuallyEq
    filter_upwards [hz.comp_tendsto continuous_snd.continuousAt] with q hq
    change χ q.2 = 0 at hq
    rw [hq,zero_mul]
  · exact (hχ.comp contDiff_snd).contDiffAt.mul (hf p hp)

lemma norm_iteratedFDeriv_parameter_slice_le (f : P × E → ℝ) (hf : ContDiff ℝ ∞ f)
    (a : P) (z : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => f (a,x)) z‖ ≤ ‖iteratedFDeriv ℝ n f (a,z)‖ := by
  let L := ContinuousLinearMap.inr ℝ P E
  have he : (fun x : E => f (a,x)) = (fun q : P × E => f ((a,0)+q)) ∘ L := by
    funext x
    simp [L]
  have hshift : ContDiff ℝ ∞ (fun q : P × E => f ((a,0)+q)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [he,L.iteratedFDeriv_comp_right hshift z
    (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  have hnorm := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n (fun q : P × E => f ((a,0)+q)) (L z)) (fun _ : Fin n => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hnorm
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ P E
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun q : P × E => f ((a,0)+q)) (L z)‖ * ‖L‖^n := hnorm
    _ ≤ ‖iteratedFDeriv ℝ n (fun q : P × E => f ((a,0)+q)) (L z)‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg L) hL) (norm_nonneg _)
    _ = _ := by rw [iteratedFDeriv_comp_add_left]; simp [L]

lemma parameter_slice_derivatives_bounded (f : P × E → ℝ) (hf : ContDiff ℝ ∞ f)
    {K : Set P} (hK : IsCompact K) {S : Set E} (hS : IsCompact S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ z ∈ S,
      ‖iteratedFDeriv ℝ n (fun x => f (a,x)) z‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hK.prod hS).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := n) (WithTop.coe_le_coe.mpr le_top)).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro a ha z hz
  exact (norm_iteratedFDeriv_parameter_slice_le f hf a z n).trans
    ((hC (a,z) ⟨ha,hz⟩).trans (le_max_left _ _))

lemma compact_parameter_family_derivatives_bounded (f : P → E → ℝ)
    (hf : ContDiff ℝ ∞ (fun p : P × E => f p.1 p.2))
    {K : Set P} (hK : IsCompact K) {S : Set E} (hS : IsCompact S)
    (hsupp : ∀ a ∈ K, tsupport (f a) ⊆ S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (f a) z‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := parameter_slice_derivatives_bounded
    (fun p : P × E => f p.1 p.2) hf hK hS n
  refine ⟨C,hC,?_⟩
  intro a ha z
  by_cases hz : z ∈ S
  · exact hbound a ha z hz
  · have hz' : z ∉ tsupport (iteratedFDeriv ℝ n (f a)) := by
      intro h
      exact hz (hsupp a ha ((tsupport_iteratedFDeriv_subset n) h))
    rw [image_eq_zero_of_notMem_tsupport hz',norm_zero]
    exact hC

lemma compact_parameter_cutoff_derivatives_bounded (χ : E → ℝ)
    (hχc : HasCompactSupport χ) (f : P → E → ℝ)
    (hf : ContDiff ℝ ∞ (fun p : P × E => χ p.2 * f p.1 p.2))
    {K : Set P} (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (fun x => χ x * f a x) z‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := parameter_slice_derivatives_bounded
    (fun p : P × E => χ p.2 * f p.1 p.2) hf hK hχc n
  refine ⟨C,hC,?_⟩
  intro a ha z
  by_cases hz : z ∈ tsupport χ
  · exact hbound a ha z hz
  · have hz' : z ∉ tsupport (iteratedFDeriv ℝ n (fun x => χ x * f a x)) := by
      intro h
      exact hz (tsupport_mul_subset_left ((tsupport_iteratedFDeriv_subset n) h))
    rw [image_eq_zero_of_notMem_tsupport hz',norm_zero]
    exact hC
end TamingCompatibility.RadialPotential

end

end OAI
