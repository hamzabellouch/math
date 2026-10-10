import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactFreeDeformation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformTailDeformation

namespace OAI

/-! Uniform positive deformation on the entire exterior, including bounded radii. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_uniform_exterior_deformation :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ r : ℝ, innerBoundaryRadius < r →
        c ≤ radialMatchedVelocity n z r/r ∧ c ≤ deriv (radialMatchedVelocity n z) r := by
  classical
  obtain ⟨R,N,hTail⟩ := radialMatched_uniform_tail_deformation
  let ε := fun k : ℕ => 1/((k : ℝ)+5)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεb (k : ℕ) : ε k ≤ (1/4 : ℝ) := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ)+5)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  by_contra h
  have hf (k M : ℕ) : ∃ n, M ≤ n ∧ N ≤ n ∧ ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialMatchingMap n z=0 ∧ ∃ r : ℝ, innerBoundaryRadius < r ∧ r ≤ (R : ℝ) ∧
        ¬ (ε k ≤ radialMatchedVelocity n z r/r ∧ ε k ≤ deriv (radialMatchedVelocity n z) r) := by
    by_contra hh
    apply h
    refine ⟨ε k,hε k,eventually_atTop.mpr ⟨max M N,?_⟩⟩
    intro n hn z hX hz r hr
    have hnM : M ≤ n := (le_max_left M N).trans hn
    have hnN : N ≤ n := (le_max_right M N).trans hn
    by_contra hb
    have hrR : r ≤ (R : ℝ) := by
      by_contra hhR
      have ht := hTail n hnN z hX hz r (le_of_not_ge hhR)
      exact hb ⟨(hεb k).trans ht.1,(hεb k).trans ht.2⟩
    exact hh ⟨n,hnM,hnN,z,hX,hz,r,hr,hrR,hb⟩
  choose f hf hN z hX hm r hr hrR hbad using hf
  let a : ℕ → ℕ := Nat.rec 0 (fun i b => f i b+1)
  let s : ℕ → ℕ := fun i => f i (a i)
  have hs : StrictMono s := strictMono_nat_of_lt_succ (fun i => by
    have hh := hf (i+1) (a (i+1))
    change f i (a i) < f (i+1) (a (i+1))
    have ha : a (i+1)=f i (a i)+1 := rfl
    exact (show f i (a i) < a (i+1) by rw [ha]; omega).trans_le hh)
  let x : ℕ → ProfileMatchingBall × Icc innerBoundaryRadius (R : ℝ) := fun i =>
    (z i (a i),⟨r i (a i),⟨(hr i (a i)).le,hrR i (a i)⟩⟩)
  obtain ⟨x₀,σ,hσ,hx⟩ := CompactSpace.tendsto_subseq x
  have hzlim : Tendsto (fun i => z (σ i) (a (σ i))) atTop (nhds x₀.1) := hx.fst_nhds
  have hrlim : Tendsto (fun i => r (σ i) (a (σ i))) atTop (nhds (x₀.2 : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hx.snd_nhds
  have hd := radialMatched_converging_free_deformation (s ∘ σ) (hs.comp hσ)
    (fun i => z (σ i) (a (σ i))) x₀.1 hzlim
    (fun i => r (σ i) (a (σ i))) x₀.2 hrlim x₀.2.property.1
    (fun i => hr (σ i) (a (σ i))) (fun i => hX (σ i) (a (σ i)))
    (fun i => hm (σ i) (a (σ i)))
  have hfree := radialFreeVelocity_deformation (profileMatchingParameter x₀.1)
    x₀.2 x₀.2.property.1
  have hrpos : 0 < (x₀.2 : ℝ) :=
    lt_of_lt_of_le (by linarith [innerBoundaryRadius_bounds.1]) x₀.2.property.1
  have hpos1 := div_pos hfree.1 hrpos
  have hpos2 : 0 < deriv (radialFreeVelocity
      (radialShootingB (profileMatchingParameter x₀.1))) x₀.2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ)<27/1000) hfree.2.2
  have heps : Tendsto (fun i => ε (σ i)) atTop (nhds 0) := by
    have hh : Tendsto (fun k : ℕ => (k : ℝ)+5) atTop atTop :=
      tendsto_atTop_add_const_right atTop (5 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [ε,one_div,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hh).comp hσ.tendsto_atTop
  have hp1 := ((hd.1.sub heps).eventually (lt_mem_nhds (by simpa using hpos1)))
  have hp2 := ((hd.2.sub heps).eventually (lt_mem_nhds (by simpa using hpos2)))
  obtain ⟨i,hi1,hi2⟩ := (hp1.and hp2).exists
  change 0 < radialMatchedVelocity (f (σ i) (a (σ i))) (z (σ i) (a (σ i)))
    (r (σ i) (a (σ i)))/r (σ i) (a (σ i))-ε (σ i) at hi1
  change 0 < deriv (radialMatchedVelocity (f (σ i) (a (σ i))) (z (σ i) (a (σ i))))
    (r (σ i) (a (σ i)))-ε (σ i) at hi2
  apply hbad (σ i) (a (σ i))
  constructor <;> linarith

end DefocusingNLS

end OAI
