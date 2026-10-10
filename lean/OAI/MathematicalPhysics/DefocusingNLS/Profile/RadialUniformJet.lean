import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformAnnulus

namespace OAI

/-! A uniform bound for the full outgoing value/velocity jet. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialFreeSlowJet_bounded (q m : ℂ) (hq : -1 < q.re) (L : ℝ) :
    ∃ B : ℝ, ∀ t : ℝ, L ≤ t → ‖radialFreeSlowJet q m t‖ ≤ B := by
  have hc : Continuous (radialFreeSlowJet q m) :=
    (show Differentiable ℝ (radialFreeSlowJet q m) from
      fun t => (radialFreeSlowJet_hasDerivAt q m hq t).differentiableAt).continuous
  have he := (radialFreeSlowJet_tendsto q m hq).norm.eventually
    (gt_mem_nhds (show ‖(m,(0 : ℂ))‖ < ‖(m,(0 : ℂ))‖+1 by linarith))
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hc.norm.continuousOn
  refine ⟨max B (‖(m,(0 : ℂ))‖+1),fun t ht => ?_⟩
  by_cases h : t ≤ T
  · exact (hB ⟨t,⟨ht,h⟩,rfl⟩).trans (le_max_left _ _)
  · exact (hT t (le_of_lt (lt_of_not_ge h))).le.trans (le_max_right _ _)

theorem radialShooting_uniform_jet_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      ∀ t : ℝ, Real.log innerBoundaryRadius ≤ t →
        ‖radialExteriorCanonical (radialShootingNu n z) n (radialShootingM z)
          (Real.log innerBoundaryRadius) t‖ ≤ B := by
  classical
  by_contra h
  have hf (k N : ℕ) : ∃ n, N ≤ n ∧ ∃ z : ProfileMatchingBall, ∃ t : ℝ,
      Real.log innerBoundaryRadius ≤ t ∧
      (k : ℝ)+1 < ‖radialExteriorCanonical (radialShootingNu n z) n
        (radialShootingM z) (Real.log innerBoundaryRadius) t‖ := by
    by_contra hh
    apply h
    refine ⟨(k : ℝ)+1,by positivity,eventually_atTop.mpr ⟨N,?_⟩⟩
    intro n hn z t ht
    exact le_of_not_gt (fun hb => hh ⟨n,hn,z,t,ht,hb⟩)
  choose f hf z t ht hbad using hf
  let a : ℕ → ℕ := Nat.rec 0 (fun i b => f i b+1)
  let s : ℕ → ℕ := fun i => f i (a i)
  have hs : StrictMono s := strictMono_nat_of_lt_succ (fun i => by
    have hh := hf (i+1) (a (i+1))
    change f i (a i) < f (i+1) (a (i+1))
    have ha : a (i+1)=f i (a i)+1 := rfl
    exact (show f i (a i) < a (i+1) by rw [ha]; omega).trans_le hh)
  obtain ⟨z₀,σ,hσ,hz⟩ := CompactSpace.tendsto_subseq (fun i => z i (a i))
  have hν := radialShootingNu_subsequence_tendsto (s ∘ σ) (hs.comp hσ)
    (fun i => z (σ i) (a (σ i))) z₀ hz
  have hm := continuous_radialShootingM.continuousAt.tendsto.comp hz
  obtain ⟨δ,ρ,hδ,hδm,hsmall,hρ,hupper,hlower⟩ := radialShooting_free_annulus z₀
  have hconv := (radialExteriorCanonical_H_limit_subsequence (s ∘ σ) (hs.comp hσ)
    (fun i => radialShootingNu (s (σ i)) (z (σ i) (a (σ i))))
    (fun i => radialShootingM (z (σ i) (a (σ i))))
    (radialShootingQ z₀) (radialShootingM z₀) (by simp [radialShootingQ])
    hν hm δ ρ (Real.log innerBoundaryRadius) hδ hδm hsmall hρ hupper hlower).2
  obtain ⟨B,hB⟩ := radialFreeSlowJet_bounded (radialShootingQ z₀)
    (radialShootingM z₀) (by simp [radialShootingQ]) (Real.log innerBoundaryRadius)
  have hlarge := ((tendsto_natCast_atTop_atTop : Tendsto (fun i : ℕ => (i : ℝ))
    atTop atTop).comp hσ.tendsto_atTop).eventually (eventually_gt_atTop B)
  have hu := (Metric.tendstoUniformlyOn_iff.mp hconv) 1 (by norm_num)
  obtain ⟨i,hi,hiu⟩ := (hlarge.and hu).exists
  let ti := t (σ i) (a (σ i))
  let F := radialExteriorCanonical (radialShootingNu (s (σ i)) (z (σ i) (a (σ i))))
    (s (σ i)) (radialShootingM (z (σ i) (a (σ i)))) (Real.log innerBoundaryRadius) ti
  let F₀ := radialFreeSlowJet (radialShootingQ z₀) (radialShootingM z₀) ti
  have hti : Real.log innerBoundaryRadius ≤ ti := ht (σ i) (a (σ i))
  have hdist : ‖F-F₀‖ < 1 := by
    have hh : dist F₀ F < 1 := hiu ti hti
    simpa only [dist_eq_norm,norm_sub_rev] using hh
  have hn : ‖F‖ ≤ ‖F-F₀‖+‖F₀‖ := by
    calc
      ‖F‖ = ‖(F-F₀)+F₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖F-F₀‖+‖F₀‖ := norm_add_le _ _
  have hb : ‖F₀‖ ≤ B := hB ti hti
  have hbad' : (σ i : ℝ)+1 < ‖F‖ := hbad (σ i) (a (σ i))
  change B < (σ i : ℝ) at hi
  linarith

end DefocusingNLS

end OAI
