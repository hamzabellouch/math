import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMovingDeformation

namespace OAI

/-! A single large-radius deformation bound for every sufficiently large matched power. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchedVelocity (n : ℕ) (z : ProfileMatchingBall) : ℝ → ℝ :=
  radialVelocity (6-2*radialShootingA n) (fun t => ‖radialMatchedProfile n z t‖)

def HasPositiveMatchedDeformation (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : Prop :=
  (1/4 : ℝ) ≤ radialMatchedVelocity n z r/r ∧
    (1/4 : ℝ) ≤ deriv (radialMatchedVelocity n z) r

theorem radialMatched_uniform_tail_deformation :
    ∃ R N : ℕ, ∀ n, N ≤ n → ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ r : ℝ, (R : ℝ) ≤ r →
        HasPositiveMatchedDeformation n z r := by
  classical
  by_contra h
  have hf (R N : ℕ) : ∃ n, N ≤ n ∧ ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialMatchingMap n z=0 ∧ ∃ r : ℝ, (R : ℝ) ≤ r ∧
        ¬ HasPositiveMatchedDeformation n z r := by
    by_contra hh
    apply h
    refine ⟨R,N,?_⟩
    intro n hn z hX hz r hr
    by_contra hb
    exact hh ⟨n,hn,z,hX,hz,r,hr,hb⟩
  choose f hf z hX hm r hr hbad using hf
  let a : ℕ → ℕ := Nat.rec 0 (fun i b => f i b+1)
  let s : ℕ → ℕ := fun i => f i (a i)
  have hs : StrictMono s := strictMono_nat_of_lt_succ (fun i => by
    have hh := hf (i+1) (a (i+1))
    change f i (a i) < f (i+1) (a (i+1))
    have ha : a (i+1)=f i (a i)+1 := rfl
    exact (show f i (a i) < a (i+1) by rw [ha]; omega).trans_le hh)
  obtain ⟨z₀,σ,hσ,hz⟩ := CompactSpace.tendsto_subseq (fun i => z i (a i))
  have hrinf : Tendsto (fun i => r i (a i)) atTop atTop := by
    apply tendsto_atTop_mono (fun i => hr i (a i))
    exact tendsto_natCast_atTop_atTop
  have hd := radialMatched_moving_deformation (s ∘ σ) (hs.comp hσ)
    (fun i => z (σ i) (a (σ i))) z₀ hz (fun i => r (σ i) (a (σ i)))
    (hrinf.comp hσ.tendsto_atTop) (fun i => hX (σ i) (a (σ i)))
    (fun i => hm (σ i) (a (σ i)))
  have h1 := hd.1.eventually (lt_mem_nhds (show (1/4 : ℝ)<1/2 by norm_num))
  have h2 := hd.2.eventually (lt_mem_nhds (show (1/4 : ℝ)<1/2 by norm_num))
  obtain ⟨i,hi1,hi2⟩ := (h1.and h2).exists
  apply hbad (σ i) (a (σ i))
  exact ⟨hi1.le,hi2.le⟩

end DefocusingNLS

end OAI
