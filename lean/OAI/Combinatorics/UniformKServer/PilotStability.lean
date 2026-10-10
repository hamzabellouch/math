import Mathlib
import OAI.Combinatorics.UniformKServer.PilotRelocation
import OAI.Combinatorics.UniformKServer.PilotScales

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

def shellRatio (r γ R : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  (ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x

def momentRatio (r γ : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  innerMoment r γ μ x/ballMass r γ μ x

theorem ballMass_extent_mono (r s a b : ℝ) (hab : a*r ≤ b*s)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) :
    ballMass r a μ x ≤ ballMass s b μ x :=
  PilotScales.mass_mono μ (dist x) hμ hab

theorem ballMass_total (r a : ℝ) (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) :
    ballMass r a μ x ≤ ∑ y, μ y := by
  apply Finset.sum_le_sum
  intro y _
  split_ifs <;> first | rfl | exact hμ y

theorem shellRatio_nonneg (r γ R : ℝ) (hr : 0 ≤ r) (hγR : γ ≤ 100*R)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) :
    0 ≤ shellRatio r γ R μ x := by
  apply div_nonneg
  · exact sub_nonneg.mpr (ballMass_mono r γ (100*R) hr hγR μ hμ x)
  · exact PilotScales.mass_nonneg μ (dist x) hμ _

theorem momentRatio_nonneg (r γ : ℝ) (hr : 0 < r)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) :
    0 ≤ momentRatio r γ μ x :=
  div_nonneg (innerMoment_bounds r γ hr μ hμ x).1
    (PilotScales.mass_nonneg μ (dist x) hμ _)

theorem innerMoment_mass (r γ : ℝ) (μ : X → ℝ) (x : X) :
    innerMoment r γ μ x = PilotScales.moment μ (dist x) (γ*r)/r := by
  rw [PilotScales.moment, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp [mul_div_assoc]

theorem shell_scale_sum (r τ γ R : ℝ) (N p : ℕ) (k : ℝ)
    (hr : 0 < r) (hτ : 2 ≤ τ) (hγ : 0 < γ) (hγR : γ ≤ 100*R)
    (hp : 100*R ≤ γ*(2:ℝ)^p) (hk : 1/2 ≤ k)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμk : ∑ y, μ y = k) (x : X)
    (hM : 1/2 ≤ ballMass r γ μ x) :
    (∑ j ∈ Finset.range N, min 1 (shellRatio (r*τ^j) γ R μ x)) ≤
      (p:ℝ)/Real.log 2*Real.log (2*k) := by
  let A := fun j => ballMass (r*τ^(N-1-j)) γ μ x
  let B := fun j => ballMass (r*τ^(N-1-j)) (100*R) μ x
  have hrad : Monotone (fun j => r*τ^j) := PilotScales.radius_mono r τ hr.le (by linarith)
  have ha (j : ℕ) : 1/2 ≤ A j := by
    apply hM.trans
    apply ballMass_extent_mono _ _ _ _ _ μ hμ x
    exact mul_le_mul_of_nonneg_left (by simpa using hrad (Nat.zero_le (N-1-j))) hγ.le
  have hs : ∀ j < N, B j ≤ if j < p then k else A (j-p) := by
    intro j hj
    by_cases hjp : j < p
    · rw [ite_eq_left hjp]
      exact (ballMass_total _ _ μ hμ x).trans_eq hμk
    · rw [ite_eq_right hjp]
      apply ballMass_extent_mono _ _ _ _ _ μ hμ x
      have hid : N-1-(j-p) = (N-1-j)+p := by omega
      have hpow : (2:ℝ)^p ≤ τ^p := pow_le_pow_left₀ (by norm_num) hτ p
      have hshift : 100*R ≤ γ*τ^p := hp.trans (mul_le_mul_of_nonneg_left hpow hγ.le)
      change 100*R*(r*τ^(N-1-j)) ≤ γ*(r*τ^(N-1-(j-p)))
      rw [hid,pow_add]
      calc
        _ ≤ (γ*τ^p)*(r*τ^(N-1-j)) := mul_le_mul_of_nonneg_right hshift (by positivity)
        _ = _ := by ring
  have hb : ∀ j < N, A j ≤ B j := by
    intro j _
    exact ballMass_mono _ γ (100*R) (by positivity) hγR μ hμ x
  have hh := PilotScales.shell_sum A B N p (1/2) k (by norm_num) hk
    (fun j _ => ha j) hb hs
  have he : k/(1/2) = 2*k := by ring
  rw [he] at hh
  change (∑ j ∈ Finset.range N, (fun i => min 1 (shellRatio (r*τ^i) γ R μ x)) (N-1-j)) ≤ _ at hh
  rw [Finset.sum_range_reflect (fun i => min 1 (shellRatio (r*τ^i) γ R μ x)) N] at hh
  exact hh

theorem moment_scale_sum (r τ γ : ℝ) (N : ℕ) (k : ℝ)
    (hr : 0 < r) (hτ : 2 ≤ τ) (hγ : 0 < γ) (hk : 1/2 ≤ k)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμk : ∑ y, μ y = k) (x : X)
    (hM : 1/2 ≤ ballMass r γ μ x) :
    (∑ j ∈ Finset.range N, momentRatio (r*τ^j) γ μ x) ≤
      2*γ*(1+Real.log (2*k)) := by
  have hpos : 0 < ballMass r γ μ x := by linarith
  have hlog : 0 ≤ Real.log (2*k) := Real.log_nonneg (by linarith)
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · have h := PilotScales.pilot_moment_sum μ (dist x) hμ (fun _ => dist_nonneg)
      r τ γ hr hτ hγ N (Nat.pos_of_ne_zero hN) hpos
    have he : (∑ j ∈ Finset.range N, momentRatio (r*τ^j) γ μ x) =
        ∑ j ∈ Finset.range N, PilotScales.moment μ (dist x) (γ*PilotScales.radius r τ j) /
          (PilotScales.radius r τ j * PilotScales.mass μ (dist x) (γ*PilotScales.radius r τ j)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [momentRatio,innerMoment_mass,div_div,ballMass,PilotScales.mass,PilotScales.radius]
      rfl
    rw [he]
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add_right
    apply Real.log_le_log
    · exact div_pos ((show ballMass r γ μ x ≤ ballMass (r*τ^(N-1)) γ μ x from
        ballMass_extent_mono _ _ _ _ (mul_le_mul_of_nonneg_left
          (by simpa [PilotScales.radius] using PilotScales.radius_mono r τ hr.le (by linarith) (Nat.zero_le (N-1))) hγ.le) μ hμ x).trans_lt' hpos) hpos
    · apply (div_le_iff₀ hpos).mpr
      change ballMass (r*τ^(N-1)) γ μ x ≤ 2*k*ballMass r γ μ x
      have ht := (ballMass_total (r*τ^(N-1)) γ μ hμ x).trans_eq hμk
      nlinarith [mul_le_mul_of_nonneg_left hM (show 0 ≤ k by linarith)]

end
end UniformKServer.PilotCompact


end OAI
