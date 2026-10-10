import OAI.Analysis.KadisonKastler.RemoteScalingConjugations
import OAI.Analysis.KadisonKastler.StateScalingConjugation

namespace OAI

/-! # Coisometries with a prescribed asymptotic modular ratio

The finite-site constructions give genuine coisometries. Their modular
ratios converge to an arbitrary number in the open unit interval, and
their conjugations converge strongly to the identity.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

include S in
theorem exists_remote_scaling_conjugations (d : ModularConjugationData M Ω)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ (s : ℕ → ℝ) (v : ℕ → Algebra M),
      Tendsto s atTop (𝓝 r) ∧
      (∀ n, 0 < s n ∧ s n < 1 ∧ v n*star (v n)=1 ∧ StateScales M Ω (s n) (v n).val) ∧
      (∀ (a : Algebra M) (η : H),
        Tendsto (fun n => (v n*a*star (v n)).val η) atTop (𝓝 (a.val η))) := by
  choose s w hpos hlt hclose hco hscale using
    (fun n : ℕ => S.exists_scaling_coisometry_near hr hr1
      (show 0 < (1 : ℝ)/(n+1) by positivity))
  have ht : Tendsto s atTop (𝓝 r) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (hclose n).trans_le ((one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hn 1)).trans hk.le)
  refine ⟨s,(fun n => S.remoteCopy n (w n)),ht,?_,?_⟩
  · intro n
    refine ⟨hpos n,hlt n,?_,S.remoteCopy_scales n (w n) (hscale n)⟩
    rw [← map_star,← map_mul,hco,map_one]
  · intro a η
    have hc : 0 < r/2 := by positivity
    have hc1 : r/2 ≤ 1 := by linarith
    have hcr : ∀ᶠ n in atTop, r/2 ≤ s n :=
      (ht.eventually (eventually_gt_nhds (show r/2 < r by linarith))).mono
        (fun _ h => h.le)
    exact S.remoteCopy_conjugation_tendsto d s w hco hscale hc hc1 hcr a η

end PointedMatrixSites

/-- A converging state ratio gives the corresponding approximate modular
vector equation for every uniformly contractive coisometry sequence. -/
theorem scaling_vector_limit (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (s : ℕ → ℝ) (v : ℕ → Algebra M) {r : ℝ}
    (hs : Tendsto s atTop (𝓝 r)) (hpos : ∀ n, 0 < s n)
    (hv : ∀ n, v n*star (v n)=1)
    (hscale : ∀ n, StateScales M Ω (s n) (v n).val) :
    Tendsto (fun n => (v n).val Ω - (Real.sqrt r : ℂ) •
      tomitaPolarConjugation J Ω hsep hcyc (star (v n).val Ω)) atTop (𝓝 0) := by
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hc : Tendsto (fun n => ‖(Real.sqrt (s n) : ℂ)-(Real.sqrt r : ℂ)‖ * ‖Ω‖)
      atTop (𝓝 0) := by
    have ht := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_sqrt.continuousAt.tendsto.comp hs)).sub_const (Real.sqrt r : ℂ)
    have ht' := ht.norm.mul_const ‖Ω‖
    simpa only [sub_self,norm_zero,zero_mul,Function.comp_def] using ht'
  have hbound (n : ℕ) : ‖(v n).val Ω-(Real.sqrt r : ℂ) • C (star (v n).val Ω)‖ ≤
      ‖(Real.sqrt (s n) : ℂ)-(Real.sqrt r : ℂ)‖ * ‖Ω‖ := by
    have he := (hscale n).polarConjugation_adjoint J hsep hcyc (v n) (hpos n)
    rw [← he,← sub_smul,norm_smul,C.norm_map]
    have hn : ‖star (v n).val‖ ≤ 1 := by
      rw [norm_star]
      exact coisometry_norm_le (v n) (hv n)
    exact mul_le_mul_of_nonneg_left
      (((star (v n).val).le_opNorm Ω).trans
        (mul_le_of_le_one_left (norm_nonneg Ω) hn)) (norm_nonneg _)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hc

end

end KadisonKastler

end OAI
