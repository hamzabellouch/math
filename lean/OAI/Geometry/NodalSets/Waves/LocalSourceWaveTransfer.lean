import OAI.Geometry.NodalSets.Coefficients.CoefficientLocality
import OAI.Geometry.NodalSets.Waves.EuclideanSourceWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem local_source_wave_transfer
    (g G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w W S A : Coord → ℝ)
    (y : T → Coord) (hy : Continuous y) {E : Set Coord} (hE : IsOpen E) (hyE : ∀ t, y t ∈ E)
    (he : ∀ x ∈ E, (G =ᶠ[𝓝 x] g) ∧ (W =ᶠ[𝓝 x] w) ∧ A x = S x)
    (u : ℕ → T → Coord → ℂ) (k0 K : ℕ) (c Cw Cr R : ℝ)
    (hCw : 0 < Cw) (hCr : 0 < Cr)
    (hest : ∀ᶠ n : ℕ in atTop, ∀ t,
      ContDiff ℝ ∞ (u n t) ∧ HasCompactSupport (u n t) ∧
      tsupport (u n t) ⊆ {z | sourceEuclideanNorm (z-y t) ≤ R*(n:ℝ)^(-1/3:ℝ)} ∧
      ∀ z : Coord,
        (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (u n t) z‖ ≤
          Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*A z-c*(n:ℝ)*(sourceEuclideanNorm (z-y t))^2)) ∧
        DerivativeBound k0 (fun z ↦ sourceWeightedOperator G W (u n t) z +
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*u n t z) z
            (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*A z))) :
    ∀ᶠ n : ℕ in atTop, ∀ t,
      ContDiff ℝ ∞ (u n t) ∧ HasCompactSupport (u n t) ∧ tsupport (u n t) ⊆ E ∧
      tsupport (u n t) ⊆ {z | sourceEuclideanNorm (z-y t) ≤ R*(n:ℝ)^(-1/3:ℝ)} ∧
      ∀ z : Coord,
        (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (u n t) z‖ ≤
          Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c*(n:ℝ)*(sourceEuclideanNorm (z-y t))^2)) ∧
        DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w (u n t) z +
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*u n t z) z
            (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z)) := by
  obtain ⟨r,hr,hball⟩ := compact_family_common_radius isCompact_univ
    (fun z : T × Coord ↦ y z.1+z.2) ((hy.comp continuous_fst).add continuous_snd)
    hE (fun t _ ↦ by simpa using hyE t)
  have hsmall : ∀ᶠ n : ℕ in atTop, R*(n:ℝ)^(-1/3:ℝ) < r := by
    apply eventually_nat_frequency (P := fun N : ℝ ↦ R*N^(-1/3:ℝ) < r)
    have ht : Tendsto (fun N : ℝ ↦ R*N^(-1/3:ℝ)) atTop (𝓝 0) := by
      simpa only [neg_div,mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul R
    exact ht.eventually (gt_mem_nhds hr)
  filter_upwards [hest,hsmall] with n hn hnr
  intro t
  obtain ⟨hsm,hcomp,hsup,hb⟩ := hn t
  have hsE : tsupport (u n t) ⊆ E := by
    intro z hz
    have hd := (norm_le_sourceEuclideanNorm (z-y t)).trans (hsup hz)
    have hh := hball t (mem_univ t) (z-y t) (hd.trans_lt hnr)
    simpa only [add_sub_cancel] using hh
  refine ⟨hsm,hcomp,hsE,hsup,?_⟩
  intro z
  by_cases hz : z ∈ E
  · have hsame := he z hz
    refine ⟨?_,?_⟩
    · simpa only [hsame.2.2] using (hb z).1
    · intro k hk
      rw [← sourceResidual_coefficients_derivative_eq hsame.1 hsame.2.1]
      simpa only [hsame.2.2] using (hb z).2 k hk
  · have hnot : z ∉ tsupport (u n t) := fun hh ↦ hz (hsE hh)
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hnot
    constructor
    · intro k
      rw [(hzero.iteratedFDeriv ℝ k.val).self_of_nhds]
      simp only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
      positivity
    · intro k hk
      rw [source_residual_derivative_zero g w (u n t) _ z hnot k,norm_zero]
      positivity

end
end Yau.Geometry

end OAI
