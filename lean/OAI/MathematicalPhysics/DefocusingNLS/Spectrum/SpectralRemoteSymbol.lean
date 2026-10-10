import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogJetBound

namespace OAI

/-! Uniform logarithmic symbols on escaping half-lines. Constants are shared
by the parameter sequence, while each fixed derivative order can discard a
finite initial segment. This is the quantifier order needed at the remote
endpoint. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

structure HasUniformLogJetBound {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (L : ℕ → ℝ) (sigma : ℝ) (f : ℕ → ℝ → A) : Prop where
  smooth : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) (Ioi (L n))
  bound : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
    ∀ t ∈ Ioi (L n), ‖iteratedDeriv k (f n) t‖ ≤ C*Real.exp (sigma*t)

namespace HasUniformLogJetBound
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {L : ℕ → ℝ} {sigma tau : ℝ} {f g : ℕ → ℝ → A}

theorem mono (hf : HasUniformLogJetBound L sigma f) (hL : Tendsto L atTop atTop)
    (hst : sigma ≤ tau) : HasUniformLogJetBound L tau f := by
  refine ⟨hf.smooth,?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := hf.bound k
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,hL.eventually (eventually_ge_atTop (0 : ℝ))] with n hn hLn
  intro t ht
  exact (hn t ht).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hst (hLn.trans ht.le))) hC)

theorem eventually_small (hf : HasUniformLogJetBound L sigma f)
    (hL : Tendsto L atTop atTop) (hsigma : sigma < 0) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖f n t‖ < eps := by
  obtain ⟨C,hC,hb⟩ := hf.bound 0
  have he : Tendsto (fun n => C*Real.exp (sigma*L n)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hsigma).2 hL)
    simpa only [mul_zero,Function.comp_def] using hh.const_mul C
  filter_upwards [hb,he.eventually (gt_mem_nhds heps)] with n hn hsmall
  intro t ht
  have ht' : ‖f n t‖ ≤ C*Real.exp (sigma*L n) := by
    simpa only [iteratedDeriv_zero] using (hn t ht).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left ht.le hsigma.le)) hC)
  exact ht'.trans_lt hsmall

theorem deriv (hf : HasUniformLogJetBound L sigma f) :
    HasUniformLogJetBound L sigma (fun n => deriv (f n)) := by
  refine ⟨hf.smooth.mono (fun _ hn => hn.deriv_of_isOpen isOpen_Ioi (by simp)),?_⟩
  intro k
  simpa only [← iteratedDeriv_succ'] using hf.bound (k+1)

theorem add (hf : HasUniformLogJetBound L sigma f) (hg : HasUniformLogJetBound L sigma g) :
    HasUniformLogJetBound L sigma (fun n t => f n t+g n t) := by
  refine ⟨?_,?_⟩
  · filter_upwards [hf.smooth,hg.smooth] with n hfn hgn
    exact hfn.add hgn
  · intro k
    obtain ⟨C,hC,hb⟩ := hf.bound k
    obtain ⟨D,hD,hd⟩ := hg.bound k
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    filter_upwards [hb,hd,hf.smooth,hg.smooth] with n hn hn' hfn hgn
    intro t ht
    have hft := (hfn t ht).contDiffAt (Ioi_mem_nhds ht)
    have hgt := (hgn t ht).contDiffAt (Ioi_mem_nhds ht)
    rw [iteratedDeriv_fun_add (hft.of_le (by simp)) (hgt.of_le (by simp))]
    exact (norm_add_le _ _).trans ((add_le_add (hn t ht) (hn' t ht)).trans_eq (by ring))

theorem neg (hf : HasUniformLogJetBound L sigma f) :
    HasUniformLogJetBound L sigma (fun n t => -f n t) := by
  refine ⟨hf.smooth.mono (fun _ hn => hn.neg),?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := hf.bound k
  exact ⟨C,hC,by simpa only [iteratedDeriv_fun_neg,norm_neg] using hb⟩

theorem sub (hf : HasUniformLogJetBound L sigma f) (hg : HasUniformLogJetBound L sigma g) :
    HasUniformLogJetBound L sigma (fun n t => f n t-g n t) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end HasUniformLogJetBound
end DefocusingNLS

end OAI
