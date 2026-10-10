import Mathlib
import OAI.Combinatorics.UniformKServer.PilotSlope
import OAI.Combinatorics.UniformKServer.PilotExtension
import OAI.Combinatorics.UniformKServer.PilotStability

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

def positiveDrift [DecidableEq X] (r σ R : ℝ) (μ ν g : X → ℝ) (x : X) : ℝ :=
  max (value r σ R (fun y => μ y-ν y+if y=x then 1 else 0) g - value r σ R μ g) 0

def exceptional (r σ : ℝ) (ν : X → ℝ) (x : X) : ℝ :=
  ∑ y, if r ≤ 8*dist x y/σ then 514*r*ν y else 0

theorem exceptional_nonneg (r σ : ℝ) (hr : 0 ≤ r) (ν : X → ℝ)
    (hν : ∀ y, 0 ≤ ν y) (x : X) : 0 ≤ exceptional r σ ν x := by
  apply Finset.sum_nonneg
  intro y _
  have hy := hν y
  split_ifs <;> positivity

theorem good_drift [DecidableEq X] (r σ R γ δ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ ν g : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y)
    (hν1 : ∑ y, ν y = 1) (hg : ∀ y, g y ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ y z, |g y-g z| ≤ L*(dist y z/r)) (x : X)
    (hM : 0 < ballMass r γ μ x) (hgood : shellRatio r γ R μ x ≤ δ) :
    positiveDrift r σ R μ ν g x ≤
      localSlopeConstant σ L*(shellRatio r γ R μ x+momentRatio r γ μ x)*
        (∑ y, ν y*dist x y)+exceptional r σ ν x := by
  have hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x := by
    have hx := (div_le_iff₀ hM).mp hgood
    linarith
  have hh := shellRatio_nonneg r γ R hr.le (by linarith) μ hμ x
  have ht := momentRatio_nonneg r γ hr μ hμ x
  have hC : 0 ≤ localSlopeConstant σ L := by unfold localSlopeConstant; positivity
  obtain ⟨z,hz,hmin,_⟩ := minimum_exists r σ R μ g
  have hpoint (y : X) :
      max (integrand r σ R g z x-integrand r σ R g z y) 0 ≤
        localSlopeConstant σ L*(shellRatio r γ R μ x+momentRatio r γ μ x)*(dist x y/r)+
          if r ≤ 8*dist x y/σ then 514 else 0 := by
    by_cases he : r ≤ 8*dist x y/σ
    · rw [ite_eq_left he]
      have hd : 0 ≤ localSlopeConstant σ L*(shellRatio r γ R μ x+momentRatio r γ μ x)*(dist x y/r) := by positivity
      apply max_le _ (by linarith)
      linarith [(integrand_bounds r σ R hr hσ hσ1 hR g z hg hz x).2,
        (integrand_bounds r σ R hr hσ hσ1 hR g z hg hz y).1]
    · rw [ite_eq_right he,add_zero]
      apply local_slope r σ R γ δ L hr hσ hσ1 hR hL hγ hγσ hγL hδ hδbound
        μ g z hμ hg hgLip x y hM hconc hz hmin
      apply (div_lt_iff₀ hr).mpr
      have hx := (div_lt_iff₀ hσ).mp (lt_of_not_ge he)
      nlinarith
  calc
    _ ≤ r*∑ y, ν y*max (integrand r σ R g z x-integrand r σ R g z y) 0 :=
      drift_nonneg_bound r σ R hr μ ν g z hν hν1 x hz hmin
    _ ≤ r*∑ y, ν y*(localSlopeConstant σ L*(shellRatio r γ R μ x+momentRatio r γ μ x)*(dist x y/r)+
          if r ≤ 8*dist x y/σ then 514 else 0) := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpoint y) (hν y)
    _ = _ := by
      unfold exceptional
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs
      · field_simp
      · field_simp
        ring

theorem mixed_drift [DecidableEq X] (r σ R γ δ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ ν g : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y)
    (hν1 : ∑ y, ν y = 1) (hg : ∀ y, g y ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ y z, |g y-g z| ≤ L*(dist y z/r)) (x : X)
    (hM : 0 < ballMass r γ μ x) :
    positiveDrift r σ R μ ν g x ≤
      ((L+1026/σ)/δ*min 1 (shellRatio r γ R μ x)+
        localSlopeConstant σ L*(min 1 (shellRatio r γ R μ x)+momentRatio r γ μ x))*
        (∑ y, ν y*dist x y)+exceptional r σ ν x := by
  let h := shellRatio r γ R μ x
  let t := momentRatio r γ μ x
  have hh : 0 ≤ h := shellRatio_nonneg r γ R hr.le (by linarith) μ hμ x
  have ht : 0 ≤ t := momentRatio_nonneg r γ hr μ hμ x
  have he : 0 ≤ ∑ y, ν y*dist x y := Finset.sum_nonneg fun y _ => mul_nonneg (hν y) dist_nonneg
  have hC : 0 ≤ localSlopeConstant σ L := by unfold localSlopeConstant; positivity
  have hΛ : 0 ≤ L+1026/σ := by positivity
  have hm : 0 ≤ min 1 h := le_min (by norm_num) hh
  have hex := exceptional_nonneg r σ hr.le ν hν x
  change positiveDrift r σ R μ ν g x ≤
    ((L+1026/σ)/δ*min 1 h+localSlopeConstant σ L*(min 1 h+t))*(∑ y,ν y*dist x y)+exceptional r σ ν x
  by_cases hg' : h ≤ δ
  · have hmin : min 1 h = h := min_eq_right (by linarith)
    rw [hmin]
    have hbound := good_drift r σ R γ δ L hr hσ hσ1 hR hL hγ hγσ hγL hδ hδbound
      μ ν g hμ hν hν1 hg hgLip x hM hg'
    have hnonneg : 0 ≤ ((L+1026/σ)/δ*h)*(∑ y, ν y*dist x y) := by positivity
    dsimp [h,t] at hnonneg ⊢
    nlinarith only [hbound,hnonneg]
  · have hδmin : δ ≤ min 1 h := le_min (by linarith) (le_of_not_ge hg')
    have hΛbound : L+1026/σ ≤ (L+1026/σ)/δ*min 1 h := by
      calc
        _ = (L+1026/σ)/δ*δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hδmin (by positivity)
    have hbound := drift_lipschitz r σ R L hr hσ hσ1 hR hL μ ν g hν hν1 x hg hgLip
    have hmul := mul_le_mul_of_nonneg_right hΛbound he
    have hnonneg : 0 ≤ (localSlopeConstant σ L*(min 1 h+t))*(∑ y,ν y*dist x y) := by positivity
    change positiveDrift r σ R μ ν g x ≤ _ at hbound
    nlinarith only [hbound,hmul,hnonneg,hex]

theorem exceptional_sum (r τ σ : ℝ) (N : ℕ) (hr : 0 < r) (hτ : 2 ≤ τ)
    (hσ : 0 < σ) (ν : X → ℝ) (hν : ∀ y, 0 ≤ ν y) (x : X) :
    (∑ j ∈ Finset.range N, exceptional (r*τ^j) σ ν x) ≤
      (8224/σ)*(∑ y, ν y*dist x y) := by
  classical
  unfold exceptional
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  let s := (Finset.range N).filter (fun j => r*τ^j ≤ 8*dist x y/σ)
  have hs := radius_subsum_le r τ (8*dist x y/σ) hr.le hτ (by positivity) s
    (fun j hj => (Finset.mem_filter.mp hj).2)
  calc
    _ = 514*ν y*(∑ j ∈ s, r*τ^j) := by
      rw [Finset.mul_sum]
      simp only [s,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    _ ≤ 514*ν y*(2*(8*dist x y/σ)) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num) (hν y))
    _ = _ := by ring

end
end UniformKServer.PilotCompact


end OAI
