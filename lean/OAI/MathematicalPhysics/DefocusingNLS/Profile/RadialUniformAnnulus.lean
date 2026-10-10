import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMovingDeformation

namespace OAI

/-! Fixed upper and lower annulus bounds for the full compact outgoing family. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialShooting_uniform_annulus :
    ∃ κ ρ : ℝ, 0 < κ ∧ ρ < 1 ∧ ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      ∀ t : ℝ, Real.log innerBoundaryRadius ≤ t →
        κ ≤ ‖(radialExteriorCanonical (radialShootingNu n z) n (radialShootingM z)
          (Real.log innerBoundaryRadius) t).1‖ ∧
        ‖(radialExteriorCanonical (radialShootingNu n z) n (radialShootingM z)
          (Real.log innerBoundaryRadius) t).1‖ ≤ ρ := by
  classical
  by_contra h
  let ε : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hf (k N : ℕ) : ∃ n, N ≤ n ∧ ∃ z : ProfileMatchingBall, ∃ t : ℝ,
      Real.log innerBoundaryRadius ≤ t ∧
      ¬ (ε k ≤ ‖(radialExteriorCanonical (radialShootingNu n z) n (radialShootingM z)
          (Real.log innerBoundaryRadius) t).1‖ ∧
        ‖(radialExteriorCanonical (radialShootingNu n z) n (radialShootingM z)
          (Real.log innerBoundaryRadius) t).1‖ ≤ 1-ε k) := by
    by_contra hh
    apply h
    refine ⟨ε k,1-ε k,hε k,by linarith [hε k],eventually_atTop.mpr ⟨N,?_⟩⟩
    intro n hn z t ht
    by_contra hb
    exact hh ⟨n,hn,z,t,ht,hb⟩
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
  have hεlim : Tendsto (fun i => ε (σ i)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hσ.tendsto_atTop
  have he1 := hεlim.eventually (gt_mem_nhds (show (0 : ℝ)<δ/2 by positivity))
  have he2 := hεlim.eventually (gt_mem_nhds (show (0 : ℝ)<1-ρ by linarith))
  have hu := (Metric.tendstoUniformlyOn_iff.mp hconv) (δ/2) (by positivity)
  obtain ⟨i,hi1,hi2,hiu⟩ := (he1.and (he2.and hu)).exists
  let ti := t (σ i) (a (σ i))
  let F := radialExteriorCanonical (radialShootingNu (s (σ i)) (z (σ i) (a (σ i))))
    (s (σ i)) (radialShootingM (z (σ i) (a (σ i)))) (Real.log innerBoundaryRadius) ti
  let F₀ := radialFreeSlowJet (radialShootingQ z₀) (radialShootingM z₀) ti
  have hti : Real.log innerBoundaryRadius ≤ ti := ht (σ i) (a (σ i))
  have hdist : dist F₀ F < δ/2 := hiu ti hti
  have hnorm : |‖F₀.1‖-‖F.1‖| ≤ dist F₀ F := by
    calc
      _ ≤ ‖F₀.1-F.1‖ := abs_norm_sub_norm_le _ _
      _ ≤ ‖F₀-F‖ := norm_fst_le (F₀-F)
      _ = dist F₀ F := (dist_eq_norm _ _).symm
  have hu0 := hupper ti hti
  have hl0 := hlower ti hti
  have hn := abs_le.mp hnorm
  apply hbad (σ i) (a (σ i))
  change ε (σ i) ≤ ‖F.1‖ ∧ ‖F.1‖ ≤ 1-ε (σ i)
  change ‖F₀.1‖+2*δ ≤ ρ at hu0
  change δ < ‖F₀.1‖ at hl0
  constructor <;> linarith [hn.1,hn.2]

end DefocusingNLS

end OAI
