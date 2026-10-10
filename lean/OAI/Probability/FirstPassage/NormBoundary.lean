import OAI.Probability.FirstPassage.MainTheorem

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

theorem norm_ball_frontier (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    frontier {v | μ v ≤ 1}={v | μ v=1} := by
  apply Subset.antisymm (frontier_le_subset_eq (timeConstantNorm_continuous μ hμ) continuous_const)
  intro v hv
  change μ v=1 at hv
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (show μ v ≤ 1 by exact hv.le),?_⟩
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝[>] (1 : ℝ)) (𝓝 v) := by
    have hh : ContinuousAt (fun t : ℝ => t • v) 1 := continuous_id.smul continuous_const |>.continuousAt
    simpa only [one_smul] using hh.mono_left (show 𝓝[>] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 1<t at ht
  change ¬μ (t • v) ≤ 1
  rw [hμ.homogeneous,hv,abs_of_pos (show 0<t by linarith)]
  linarith

lemma ball_support_contact_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (v : Plane) (g : Plane →L[ℝ] ℝ) (hg : g ≠ 0)
    (hs : ∀ z, μ z ≤ 1 → g z ≤ g v) : 0 < g v := by
  obtain ⟨u,hu⟩ : ∃ u : Plane, g u ≠ 0 := by
    by_contra hh
    apply hg
    ext u
    simpa using not_exists.mp hh u
  let w := g u • u
  have hwg : 0 < g w := by
    dsimp [w]
    rw [map_smul,smul_eq_mul]
    exact mul_self_pos.mpr hu
  have hw : w ≠ 0 := by intro hz; rw [hz,map_zero] at hwg; exact lt_irrefl _ hwg
  have hμw : 0 < μ w := lt_of_le_of_ne (hμ.nonneg w) (fun h => hw ((hμ.zero_iff w).mp h.symm))
  have hunit : μ ((μ w)⁻¹ • w)=1 := by
    rw [hμ.homogeneous,abs_of_pos (inv_pos.mpr hμw),inv_mul_cancel₀ hμw.ne']
  have hh := hs ((μ w)⁻¹ • w) hunit.le
  rw [map_smul,smul_eq_mul] at hh
  exact (mul_pos (inv_pos.mpr hμw) hwg).trans_le hh

lemma ball_support_normalized (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (v : Plane) (_hv : μ v=1) (g : Plane →L[ℝ] ℝ) (hg : g ≠ 0)
    (hs : ∀ z, μ z ≤ 1 → g z ≤ g v) :
    ((g v)⁻¹ • g) v=1 ∧ ∀ z, ((g v)⁻¹ • g) z ≤ μ z := by
  have hc := ball_support_contact_pos μ hμ v g hg hs
  constructor
  · simp [inv_mul_cancel₀ hc.ne']
  · intro z
    by_cases hz : z=0
    · subst z
      simp [(hμ.zero_iff 0).mpr rfl]
    · have hμz : 0 < μ z := lt_of_le_of_ne (hμ.nonneg z) (fun h => hz ((hμ.zero_iff z).mp h.symm))
      have hn : μ ((μ z)⁻¹ • z)=1 := by
        rw [hμ.homogeneous,abs_of_pos (inv_pos.mpr hμz),inv_mul_cancel₀ hμz.ne']
      have hh := hs ((μ z)⁻¹ • z) hn.le
      simp only [map_smul,smul_eq_mul] at hh
      have hmul := mul_le_mul_of_nonneg_left hh hμz.le
      rw [← mul_assoc,mul_inv_cancel₀ hμz.ne',one_mul] at hmul
      change (g v)⁻¹*g z ≤ μ z
      exact (inv_mul_le_iff₀ hc).mpr (by nlinarith)

theorem norm_supporting_line_unique (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hd : DifferentiableAwayFromOrigin μ) (v : Plane) (hv : v ∈ frontier {z | μ z ≤ 1}) :
    ∃! L : Set Plane, ∃ g : Plane →L[ℝ] ℝ, g ≠ 0 ∧
      (∀ z, μ z ≤ 1 → g z ≤ g v) ∧ L={z | g z=g v} := by
  have hv1 : μ v=1 := by rw [norm_ball_frontier μ hμ] at hv; exact hv
  obtain ⟨ℓ,hℓ,hunique⟩ := unique_supports_of_differentiable μ hμ hd v hv1
  have hℓne : ℓ ≠ 0 := by intro he; simp [he] at hℓ
  refine ⟨{z | ℓ z=1},⟨ℓ,hℓne,fun z hz => (hℓ.2 z).trans (by rw [hℓ.1]; exact hz),by rw [hℓ.1]⟩,?_⟩
  rintro L ⟨g,hg,hs,rfl⟩
  have hc := ball_support_contact_pos μ hμ v g hg hs
  have he := hunique ((g v)⁻¹ • g) (ball_support_normalized μ hμ v hv1 g hg hs)
  ext z
  rw [← he]
  change g z=g v ↔ (g v)⁻¹*g z=1
  constructor
  · intro hz
    rw [hz,inv_mul_cancel₀ hc.ne']
  · intro hz
    have hh := congrArg (fun x : ℝ => g v*x) hz
    simpa only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul,mul_one] using hh

end PlanarFPP

end OAI
