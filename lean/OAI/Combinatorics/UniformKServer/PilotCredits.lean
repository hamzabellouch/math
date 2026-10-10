import Mathlib
import OAI.Combinatorics.UniformKServer.PilotPersistence

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

def coarseConstant (σ γ δ L : ℝ) (p : ℕ) (k : ℝ) : ℝ :=
  (L+1026/σ)/δ*((p:ℝ)/Real.log 2*Real.log (2*k)) +
    localSlopeConstant σ L*((p:ℝ)/Real.log 2*Real.log (2*k) +
      2*γ*(1+Real.log (2*k))) + 8224/σ

theorem coarseConstant_nonneg (σ γ δ L : ℝ) (p : ℕ) (k : ℝ)
    (hσ : 0 < σ) (hγ : 0 < γ) (hδ : 0 < δ) (hL : 0 ≤ L) (hk : 1/2 ≤ k) :
    0 ≤ coarseConstant σ γ δ L p k := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlk : 0 ≤ Real.log (2*k) := Real.log_nonneg (by linarith)
  unfold coarseConstant localSlopeConstant
  positivity

theorem coarse_drift [DecidableEq X] (r τ σ R γ δ L : ℝ) (N p : ℕ) (k : ℝ)
    (hr : 0 < r) (hτ : 2 ≤ τ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112) (hk : 1/2 ≤ k)
    (hp : 100*R ≤ γ*(2:ℝ)^p)
    (μ ν : X → ℝ) (g : ℕ → X → ℝ) (x : X)
    (hμ : ∀ y, 0 ≤ μ y) (hμk : ∑ y, μ y = k)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1)
    (hg : ∀ j y, g j y ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ j y z, |g j y-g j z| ≤ L*(dist y z/(r*τ^j)))
    (hM : 1/2 ≤ ballMass r γ μ x) :
    (∑ j ∈ Finset.range N, positiveDrift (r*τ^j) σ R μ ν (g j) x) ≤
      coarseConstant σ γ δ L p k*(∑ y, ν y*dist x y) := by
  have hτ0 : 0 < τ := by linarith
  have he : 0 ≤ ∑ y, ν y*dist x y := Finset.sum_nonneg fun y _ => mul_nonneg (hν y) dist_nonneg
  have hA : 0 ≤ (L+1026/σ)/δ := by positivity
  have hC : 0 ≤ localSlopeConstant σ L := by unfold localSlopeConstant; positivity
  have hH := shell_scale_sum r τ γ R N p k hr hτ hγ (by linarith) hp hk μ hμ hμk x hM
  have hT := moment_scale_sum r τ γ N k hr hτ hγ hk μ hμ hμk x hM
  have hE := exceptional_sum r τ σ N hr hτ hσ ν hν x
  have hpoint (j : ℕ) : positiveDrift (r*τ^j) σ R μ ν (g j) x ≤
      ((L+1026/σ)/δ*min 1 (shellRatio (r*τ^j) γ R μ x)+
        localSlopeConstant σ L*(min 1 (shellRatio (r*τ^j) γ R μ x)+momentRatio (r*τ^j) γ μ x))*
        (∑ y, ν y*dist x y)+exceptional (r*τ^j) σ ν x := by
    apply mixed_drift _ σ R γ δ L (by positivity) hσ hσ1 hR hL hγ hγσ hγL hδ hδbound
      μ ν (g j) hμ hν hν1 (hg j) (hgLip j) x
    have hm := ballMass_extent_mono r (r*τ^j) γ γ (mul_le_mul_of_nonneg_left
      (by simpa [PilotScales.radius] using PilotScales.radius_mono r τ hr.le (by linarith) (Nat.zero_le j)) hγ.le) μ hμ x
    linarith
  calc
    _ ≤ ∑ j ∈ Finset.range N,
      (((L+1026/σ)/δ*min 1 (shellRatio (r*τ^j) γ R μ x)+
        localSlopeConstant σ L*(min 1 (shellRatio (r*τ^j) γ R μ x)+momentRatio (r*τ^j) γ μ x))*
        (∑ y, ν y*dist x y)+exceptional (r*τ^j) σ ν x) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = ((L+1026/σ)/δ*(∑ j ∈ Finset.range N, min 1 (shellRatio (r*τ^j) γ R μ x))+
        localSlopeConstant σ L*((∑ j ∈ Finset.range N, min 1 (shellRatio (r*τ^j) γ R μ x))+
          ∑ j ∈ Finset.range N, momentRatio (r*τ^j) γ μ x))*(∑ y,ν y*dist x y)+
        ∑ j ∈ Finset.range N, exceptional (r*τ^j) σ ν x := by
      rw [Finset.sum_add_distrib,←Finset.sum_mul,Finset.sum_add_distrib,
        ←Finset.mul_sum,←Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ ((L+1026/σ)/δ*((p:ℝ)/Real.log 2*Real.log (2*k)) +
        localSlopeConstant σ L*((p:ℝ)/Real.log 2*Real.log (2*k)+2*γ*(1+Real.log (2*k))))*
        (∑ y,ν y*dist x y)+(8224/σ)*(∑ y,ν y*dist x y) := by
      exact add_le_add (mul_le_mul_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_left hH hA)
          (mul_le_mul_of_nonneg_left (add_le_add hH hT) hC)) he) hE
    _ = _ := by unfold coarseConstant; ring

/-- The constant in companion Lemma pilot-drift. -/
def driftConstant (σ γ δ L : ℝ) (p : ℕ) : ℝ :=
  2056/γ + 8224/σ + 2*(L+1026/σ)*p/(δ*Real.log 2) +
    2*localSlopeConstant σ L*((p:ℝ)/Real.log 2+2*γ)

theorem driftConstant_log (σ γ δ L : ℝ) (p : ℕ) (k : ℝ)
    (hσ : 0 < σ) (hγ : 0 < γ) (hδ : 0 < δ) (hL : 0 ≤ L) (hk : 2 ≤ k) :
    2056/γ + coarseConstant σ γ δ L p k ≤ driftConstant σ γ δ L p*(1+Real.log (k+1)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk1 : 0 < k+1 := by linarith
  have hlk : 0 ≤ Real.log (k+1) := Real.log_nonneg (by linarith)
  have hl : Real.log (2*k) ≤ 2*Real.log (k+1) := by
    have hh := Real.log_le_log (by linarith : 0 < 2*k)
      (show 2*k ≤ (k+1)*(k+1) by nlinarith [sq_nonneg k])
    rw [Real.log_mul hk1.ne' hk1.ne'] at hh
    linarith
  have hl' : Real.log (2*k) ≤ 2*(1+Real.log (k+1)) := by linarith
  have h1l : 1+Real.log (2*k) ≤ 2*(1+Real.log (k+1)) := by linarith
  have hH := mul_le_mul_of_nonneg_left hl' (show 0 ≤ (p:ℝ)/Real.log 2 by positivity)
  have hT := mul_le_mul_of_nonneg_left h1l (show 0 ≤ 2*γ by positivity)
  have hbase := mul_le_mul_of_nonneg_left (show 1 ≤ 1+Real.log (k+1) by linarith)
    (show 0 ≤ 2056/γ+8224/σ by positivity)
  have hA : 0 ≤ (L+1026/σ)/δ := by positivity
  have hC : 0 ≤ localSlopeConstant σ L := by unfold localSlopeConstant; positivity
  calc
    _ = (2056/γ+8224/σ) + (L+1026/σ)/δ*((p:ℝ)/Real.log 2*Real.log (2*k)) +
        localSlopeConstant σ L*((p:ℝ)/Real.log 2*Real.log (2*k)+2*γ*(1+Real.log (2*k))) := by
      unfold coarseConstant; ring
    _ ≤ (2056/γ+8224/σ)*(1+Real.log (k+1)) +
        (L+1026/σ)/δ*((p:ℝ)/Real.log 2*(2*(1+Real.log (k+1)))) +
        localSlopeConstant σ L*((p:ℝ)/Real.log 2*(2*(1+Real.log (k+1)))+
          2*γ*(2*(1+Real.log (k+1)))) := by
      exact add_le_add (add_le_add (by simpa using hbase) (mul_le_mul_of_nonneg_left hH hA))
        (mul_le_mul_of_nonneg_left (add_le_add hH hT) hC)
    _ = _ := by unfold driftConstant; field_simp

theorem scale_cut (r τ γ e : ℝ) (N : ℕ) (hγ : 0 < γ) :
    ∃ m ≤ N, (∀ j < m, r*τ^j ≤ 2*e/γ) ∧ (m = N ∨ 2*e ≤ γ*(r*τ^m)) := by
  let P := fun j => j ≤ N ∧ (j=N ∨ 2*e ≤ γ*(r*τ^j))
  have hex : ∃ j, P j := ⟨N,le_rfl,Or.inl rfl⟩
  refine ⟨Nat.find hex,(Nat.find_spec hex).1,?_,(Nat.find_spec hex).2⟩
  intro j hj
  have hjN : j ≤ N := (le_of_lt hj).trans (Nat.find_spec hex).1
  have hnot : ¬ 2*e ≤ γ*(r*τ^j) := by
    intro h
    have hh := Nat.find_min' hex (show P j from ⟨hjN,Or.inr h⟩)
    omega
  apply (le_div_iff₀ hγ).mpr
  nlinarith only [lt_of_not_ge hnot]

theorem small_drift [DecidableEq X] (r τ σ R γ e : ℝ) (N : ℕ)
    (hr : 0 < r) (hτ : 2 ≤ τ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hγ : 0 < γ) (he : 0 ≤ e)
    (μ ν : X → ℝ) (g : ℕ → X → ℝ) (x : X)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1)
    (hg : ∀ j y, g j y ∈ Set.Icc (0:ℝ) 1)
    (hsmall : ∀ j < N, r*τ^j ≤ 2*e/γ) :
    (∑ j ∈ Finset.range N, positiveDrift (r*τ^j) σ R μ ν (g j) x) ≤ (2056/γ)*e := by
  have hτ0 : 0 < τ := by linarith
  calc
    _ ≤ ∑ j ∈ Finset.range N, 514*(r*τ^j) := by
      apply Finset.sum_le_sum
      intro j _
      exact drift_bounded _ σ R (by positivity) hσ hσ1 hR μ ν (g j) hν hν1 x (hg j)
    _ = 514*(∑ j ∈ Finset.range N, r*τ^j) := (Finset.mul_sum ..).symm
    _ ≤ 514*(2*(2*e/γ)) := mul_le_mul_of_nonneg_left
      (radius_subsum_le r τ _ hr.le hτ (by positivity) _
        (fun j hj => hsmall j (Finset.mem_range.mp hj))) (by norm_num)
    _ = _ := by ring

end
end UniformKServer.PilotCompact



end OAI
