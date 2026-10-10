import OAI.Analysis.DiamondDistortion.RecursiveModels

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Midpoint
open Filter
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Uniform pure-tail vanishing at the unit sphere, the qualitative mass-removal
    input. No power law or quantitative modulus is inserted into this hypothesis. -/
def Heads.TailVanishing (A : Heads ι X) : Prop :=
  ∀ ε : ℝ,0 < ε → ∃ δ : ℝ,0 < δ ∧
    ∀ (H : ι) (p y : X),A.projection H p=p → A.projection H y=0 →
      ‖p+y‖ ≤ 1 → ‖p-y‖ ≤ 1 → 1-δ ≤ ‖p‖ → ‖y‖ < ε

lemma Heads.vanishing_gap (A : Heads ι X) (hinput : A.TailVanishing) {ε : ℝ}
    (hε : 0 < ε) : ∃ ρ : ℝ,0 ≤ ρ ∧ ρ < 1 ∧
    ∀ x : X,(∀ η : ℝ,0 < η → ∃ (H : ι) (p y : X),
      A.projection H p=p ∧ A.projection H y=0 ∧
      ‖x‖-η ≤ ‖p‖ ∧ ε-η ≤ ‖y‖ ∧ ‖p+y‖ ≤ 1+2*η ∧ ‖p-y‖ ≤ 1+2*η) → ‖x‖ ≤ ρ := by
  obtain ⟨δ,hδ,hvan⟩ := hinput (ε/4) (by positivity)
  let d := min δ 1
  have hd : 0 < d := lt_min hδ (by norm_num)
  have hd1 : d ≤ 1 := min_le_right _ _
  have hdδ : d ≤ δ := min_le_left _ _
  refine ⟨1-d/4,by linarith,by linarith,?_⟩
  intro x hx
  by_contra hc
  have hc' : 1-d/4 < ‖x‖ := lt_of_not_ge hc
  let η := min (d/16) (min (ε/4) (1/4:ℝ))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hηd : η ≤ d/16 := min_le_left _ _
  have hηε : η ≤ ε/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨H,p,y,hP,hY,hpx,hyε,hp,hm⟩ := hx η hη
  let r := 1+2*η
  have hr : 0 < r := by dsimp [r]; positivity
  have hnorm (v : X) : ‖r⁻¹ • v‖=‖v‖/r := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    ring
  have hp1 : ‖r⁻¹ • p+r⁻¹ • y‖ ≤ 1 := by
    rw [← smul_add,hnorm]
    exact (div_le_one hr).mpr hp
  have hm1 : ‖r⁻¹ • p-r⁻¹ • y‖ ≤ 1 := by
    rw [← smul_sub,hnorm]
    exact (div_le_one hr).mpr hm
  have hcenter : 1-δ ≤ ‖r⁻¹ • p‖ := by
    rw [hnorm]
    apply (le_div_iff₀ hr).mpr
    have hmul := mul_nonneg hd.le hη.le
    have hmon := mul_le_mul_of_nonneg_right (show 1-δ ≤ 1-d by linarith) hr.le
    dsimp [r] at hmon ⊢
    nlinarith
  have htail : ε/4 ≤ ‖r⁻¹ • y‖ := by
    rw [hnorm]
    apply (le_div_iff₀ hr).mpr
    dsimp [r]
    nlinarith
  have hsmall := hvan H (r⁻¹ • p) (r⁻¹ • y)
    (by rw [map_smul,hP]) (by rw [map_smul,hY,smul_zero]) hp1 hm1 hcenter
  exact (not_lt_of_ge htail) hsmall

/-- Pure-tail vanishing transfers uniformly to separated lenses at arbitrary
    centers. This retains the qualitative route independently of a square input. -/
theorem Heads.vanishing_lens (A : Heads ι X) (hinput : A.TailVanishing) {ε : ℝ}
    (hε : 0 < ε) : ∃ ρ : ℝ,0 ≤ ρ ∧ ρ < 1 ∧ Diamond.UnitLensBound X ε ρ := by
  obtain ⟨ρ,hρ,hρ1,hgap⟩ := A.vanishing_gap hinput (show 0 < ε/2 by positivity)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro x z hp hm hs
  exact hgap x (fun η hη => A.pure_pair z hη hp hm hs)

/-- The separately stated weak-null uniformity: the same rho works for every
    center and sequence with the specified positive lower norm bound. -/
theorem Heads.vanishing_weak (A : Heads ι X) (hinput : A.TailVanishing) {ε : ℝ}
    (hε : 0 < ε) : ∃ ρ : ℝ,0 ≤ ρ ∧ ρ < 1 ∧
    ∀ (x : X) (z : ℕ → X),WeaklyNull z → (∀ i,ε ≤ ‖z i‖) →
      (∀ i,‖x+z i‖ ≤ 1) → (∀ i,‖x-z i‖ ≤ 1) → ‖x‖ ≤ ρ := by
  obtain ⟨ρ,hρ,hρ1,hgap⟩ := A.vanishing_gap hinput hε
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro x z hz hl hp hm
  exact hgap x (fun η hη => A.weak_pure z hz hη hl hp hm)

/-- Bottom-up mass removal, qualitative diamond obstruction. -/
theorem Heads.vanishing_obstruction (A : Heads ι X) (hinput : A.TailVanishing) :
    ¬ Diamond.UniformEmbeddings X := by
  rintro ⟨D,h⟩
  obtain ⟨f0,s0,hf0⟩ := h 0
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) hf0.1
  have hα : 0 < D⁻¹ := inv_pos.mpr hD
  have hα1 : D⁻¹ ≤ 1 := (inv_le_one₀ hD).mpr hf0.1
  obtain ⟨ρ,hρ,hρ1,hlens⟩ := A.vanishing_lens hinput (show 0 < 2*D⁻¹ by positivity)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1
  have he : ∀ᶠ k : ℕ in atTop,ρ^k < D⁻¹ := ht.eventually (gt_mem_nhds hα)
  obtain ⟨k,hk⟩ := he.exists
  obtain ⟨f,s,hf⟩ := h k
  have hn := Diamond.upper_one_normalization f hf
  have hb := Diamond.backward hα hα1 hρ hρ1 hlens k (fun v => (D*s)⁻¹ • f v)
    (fun u v => (hn u v).1) (fun u v => (hn u v).2)
  exact (not_lt_of_ge hb) hk
end Midpoint

open scoped ENNReal

end DiamondDistortion

end

end OAI
