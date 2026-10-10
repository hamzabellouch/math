import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogJetBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogJetOperations

namespace OAI

/-! The qualitative incoming decay used to remove the endpoint at infinity.
Solving the incoming equation for its large, invertible leading term gains
two powers at every step, including every fixed logarithmic derivative. -/

open Set Filter Topology
namespace DefocusingNLS

theorem HasLogJetBound.eventually_congr {σ : ℝ} {f g : ℝ → ℂ}
    (hf : HasLogJetBound σ f) (hfg : f =ᶠ[atTop] g) : HasLogJetBound σ g := by
  obtain ⟨L,hL⟩ := hf.smooth
  obtain ⟨S,hS⟩ := eventually_atTop.mp hfg
  have heq : EqOn f g (Ioi S) := fun t ht => hS t ht.le
  refine ⟨⟨max L S,?_⟩,?_⟩
  · exact (hL.mono (Ioi_subset_Ioi (le_max_left _ _))).congr
      (fun t ht => (hS t ((le_max_right L S).trans ht.le)).symm)
  · intro k
    obtain ⟨C,hC,hbound⟩ := hf.bound k
    refine ⟨C,hC,?_⟩
    filter_upwards [hbound,eventually_gt_atTop S] with t ht htS
    rw [← heq.iteratedDeriv_of_isOpen isOpen_Ioi k htS]
    exact ht

theorem spectralRemote_incoming_gain (sigma tau : ℝ) (htau : tau ≤ sigma)
    (a b f y : ℝ → ℂ)
    (ha : HasLogJetBound 0 a) (hb : HasLogJetBound 0 b)
    (hf : HasLogJetBound tau f) (hy : HasLogJetBound sigma y)
    (hsolve : ∀ᶠ t in atTop, y t = (Real.exp (-2*t) : ℂ)*a t*(deriv y t-b t*y t-f t)) :
    HasLogJetBound (sigma-2) y := by
  have hby : HasLogJetBound sigma (fun t => b t*y t) := by
    simpa only [zero_add] using hb.mul hy
  have hterm := (hy.deriv.sub hby).sub (hf.mono htau)
  have hat : HasLogJetBound sigma (fun t => a t*(deriv y t-b t*y t-f t)) := by
    simpa only [zero_add] using ha.mul hterm
  have hexp : HasLogJetBound (-2) (fun t : ℝ => (Real.exp (-2*t) : ℂ)) := by
    simpa only [Complex.real_smul,mul_one] using HasLogJetBound.exponential (-2) (1 : ℂ)
  have hres : HasLogJetBound (sigma-2)
      (fun t => (Real.exp (-2*t) : ℂ)*a t*(deriv y t-b t*y t-f t)) := by
    have he : (-2 : ℝ)+sigma = sigma-2 := by ring
    simpa only [he,mul_assoc] using hexp.mul hat
  exact hres.eventually_congr (hsolve.mono (fun _ ht => ht.symm))

theorem spectralRemote_incoming_iterate (sigma tau : ℝ) (N : ℕ)
    (a b f y : ℝ → ℂ)
    (ha : HasLogJetBound 0 a) (hb : HasLogJetBound 0 b)
    (hf : HasLogJetBound tau f) (hy : HasLogJetBound sigma y)
    (hsolve : ∀ᶠ t in atTop, y t = (Real.exp (-2*t) : ℂ)*a t*(deriv y t-b t*y t-f t))
    (htau : tau ≤ sigma-2*(N : ℝ)) :
    HasLogJetBound (sigma-2*(N : ℝ)) y := by
  induction N with
  | zero => simpa only [Nat.cast_zero,mul_zero,sub_zero] using hy
  | succ N ih =>
    have htau' : tau ≤ sigma-2*(N : ℝ) := by
      push_cast at htau
      linarith
    have hs := spectralRemote_incoming_gain (sigma-2*(N : ℝ)) tau htau' a b f y
      ha hb hf (ih htau') hsolve
    have he : sigma-2*((N+1 : ℕ) : ℝ) = (sigma-2*(N : ℝ))-2 := by push_cast; ring
    rwa [he]

theorem HasLogJetBound.tendsto_zero {sigma : ℝ} {y : ℝ → ℂ}
    (hy : HasLogJetBound sigma y) (hsigma : sigma < 0) : Tendsto y atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := hy.bound 0
  have hexp : Tendsto (fun t : ℝ => Real.exp (sigma*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hsigma).2 tendsto_id)
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using hexp.const_mul C)
  simpa only [iteratedDeriv_zero] using hbound

end DefocusingNLS

end OAI
