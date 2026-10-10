import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowGibbsGap

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem backwards_no_annulus (f : ℕ → ℝ) {l u : ℕ} (_hlu : l≤u) (a d : ℝ)
    (hend : |f u|<a)
    (hstep : ∀ k,l≤k → k<u → |f (k+1)-f k|≤d)
    (havoid : ∀ k,l≤k → k≤u → ¬(a≤|f k| ∧ |f k|≤a+d)) :
    ∀ k,l≤k → k≤u → |f k|<a := by
  intro k hlk hku
  induction hku using Nat.decreasingInduction with
  | self => exact hend
  | @of_succ k hku ih =>
    have hs := hstep k hlk hku
    have hh := ih (by omega)
    by_contra h
    apply havoid k hlk hku.le
    refine ⟨le_of_not_gt h,?_⟩
    have ht : |f k|≤|f (k+1)|+|f (k+1)-f k| := by
      have H := abs_add_le (f (k+1)) (-(f (k+1)-f k))
      rw [show f (k+1)+-(f (k+1)-f k)=f k by ring,abs_neg] at H
      exact H
    linarith only [ht,hs,hh]

theorem narrow_first_violation {n : ℕ} (μ : ProbabilityMeasure ℝ)
    (v y w : Config n) (t₀ ρ E d rᵢ rⱼ : ℝ)
    (_ht : 0<t₀) (_hρ : 0<ρ) (hri : rᵢ∈Icc t₀ (2*t₀))
    (hspacing : 3*ρ≤rⱼ-rᵢ) (hwidth : ρ^8<t₀/2)
    (hsmall : E+ρ^20+d/2<ρ^8) (hsep : E+ρ^20+3*d/2≤2*ρ)
    (hd : d/2≤ρ^20)
    (hmass : (μ : Measure ℝ).real (Icc (rᵢ-2*ρ^8) (rᵢ+2*ρ^8))≤ρ^4)
    (href : |overlap v w-rᵢ|≤E) (hq : rⱼ-d≤overlap w y)
    (hlo : 2*ρ^20≤|overlap v y-overlap v w|)
    (hhi : |overlap v y-overlap v w|≤2*ρ^20+d) :
    (![v,y,w] : ReplicaConfig n 3)∈narrowLockingSet n μ t₀ ρ := by
  classical
  let r := (overlap v y+overlap v w)/2
  let δ := (overlap v y-overlap v w)/2
  have hδl : ρ^20≤|δ| := by dsimp [δ]; rw [abs_div]; rw [abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith only [hlo]
  have hδh : |δ|≤ρ^20+d/2 := by dsimp [δ]; rw [abs_div]; rw [abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith only [hhi]
  have hrr : |r-rᵢ|≤E+ρ^20+d/2 := by
    have HH := abs_add_le (overlap v w-rᵢ) δ
    have he : r-rᵢ=(overlap v w-rᵢ)+δ := by dsimp [r,δ]; ring
    rw [he]
    linarith only [HH,href,hδh]
  have hrr' : |r-rᵢ|<ρ^8 := hrr.trans_lt hsmall
  have hr : r∈Ioo (t₀/2) (3*t₀) := by
    obtain ⟨h₁,h₂⟩ := abs_lt.mp hrr'
    constructor <;> linarith only [h₁,h₂,hri.1,hri.2,hwidth]
  have hsub : Icc (r-ρ^8) (r+ρ^8) ⊆ Icc (rᵢ-2*ρ^8) (rᵢ+2*ρ^8) := by
    intro z hz
    obtain ⟨h₁,h₂⟩ := abs_lt.mp hrr'
    constructor <;> linarith only [h₁,h₂,hz.1,hz.2]
  have hq' : r+ρ≤overlap y w := by
    rw [overlap_comm y w]
    have hh := (abs_le.mp hrr).2
    linarith only [hq,hspacing,hsep,hh]
  have hm : (μ : Measure ℝ).real (Icc (r-ρ^8) (r+ρ^8))≤ρ^4 :=
    (measureReal_mono hsub).trans hmass
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  change r∈Ioo (t₀/2) (3*t₀) ∧ _≤ρ^4 ∧ r+ρ≤overlap y w ∧ ρ^20≤|δ| ∧ |δ|≤2*ρ^20
  exact ⟨hr,hm,hq',hδl,by linarith only [hδh,hd]⟩

theorem narrow_backwards_transfer {n : ℕ} (μ : ProbabilityMeasure ℝ)
    (v w : Config n) (x : ℕ → Config n) (t₀ ρ E d rᵢ rⱼ : ℝ) {l u : ℕ}
    (hlu : l≤u) (ht : 0<t₀) (hρ : 0<ρ) (hri : rᵢ∈Icc t₀ (2*t₀))
    (hspacing : 3*ρ≤rⱼ-rᵢ) (hwidth : ρ^8<t₀/2)
    (hsmall : E+ρ^20+d/2<ρ^8) (hsep : E+ρ^20+3*d/2≤2*ρ) (hd : d/2≤ρ^20)
    (hmass : (μ : Measure ℝ).real (Icc (rᵢ-2*ρ^8) (rᵢ+2*ρ^8))≤ρ^4)
    (href : |overlap v w-rᵢ|≤E)
    (hend : |overlap v (x u)-overlap v w|<2*ρ^20)
    (hjump : ∀ k,l≤k → k<u → |overlap v (x (k+1))-overlap v (x k)|≤d)
    (hsearch : ∀ k,l≤k → k≤u → rⱼ-d≤overlap w (x k))
    (havoid : ∀ k,l≤k → k≤u →
      (![v,x k,w] : ReplicaConfig n 3)∉narrowLockingSet n μ t₀ ρ) :
    ∀ k,l≤k → k≤u → |overlap v (x k)-overlap v w|<2*ρ^20 := by
  apply backwards_no_annulus (fun k => overlap v (x k)-overlap v w) hlu (2*ρ^20) d hend
  · intro k hk hku
    simpa only [sub_sub_sub_cancel_right] using hjump k hk hku
  · intro k hk hku ⟨hlo,hhi⟩
    exact havoid k hk hku (narrow_first_violation μ v (x k) w t₀ ρ E d rᵢ rⱼ
      ht hρ hri hspacing hwidth hsmall hsep hd hmass href (hsearch k hk hku) hlo hhi)

end SK.Analytic

end
end

end OAI
