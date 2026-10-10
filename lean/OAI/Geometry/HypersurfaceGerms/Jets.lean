import Mathlib

namespace OAI

/-! Derivative-order calculus and vanishing jets. -/

namespace AmbientMultiplicity.Jets
noncomputable section
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Vanishing (n : ℕ) (f : E → ℂ) : Prop :=
  AnalyticAt ℂ f 0 ∧ ∀ k < n, iteratedFDeriv ℂ k f 0 = 0

lemma analytic_neighborhood {f g : E → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    ∃ s : Set E, IsOpen s ∧ (0 : E) ∈ s ∧ AnalyticOnNhd ℂ f s ∧ AnalyticOnNhd ℂ g s := by
  obtain ⟨s, hs, hopen, hzero⟩ := mem_nhds_iff.mp
    (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  exact ⟨s, hopen, hzero, fun x hx => (hs hx).1, fun x hx => (hs hx).2⟩

namespace Vanishing
variable {n m : ℕ} {f g : E → ℂ}
lemma analytic (h : Vanishing n f) : AnalyticAt ℂ f 0 := h.1
lemma zero (hf : AnalyticAt ℂ f 0) : Vanishing 0 f := ⟨hf, by omega⟩
lemma mono (h : Vanishing n f) (hm : m ≤ n) : Vanishing m f :=
  ⟨h.1, fun k hk => h.2 k (lt_of_lt_of_le hk hm)⟩
lemma one (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) : Vanishing 1 f := by
  refine ⟨hf, ?_⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  ext v
  simpa only [iteratedFDeriv_zero_apply, zero_apply] using h0
lemma eq_zero (h : Vanishing n f) (hn : 0 < n) : f 0 = 0 := by
  have he := congrArg (fun p => p (0 : Fin 0 → E)) (h.2 0 hn)
  simpa only [iteratedFDeriv_zero_apply, zero_apply] using he
lemma congr (h : Vanishing n f) (he : f =ᶠ[𝓝 0] g) : Vanishing n g := by
  refine ⟨h.1.congr he, ?_⟩
  intro k hk
  rw [← (he.iteratedFDeriv ℂ k).eq_of_nhds, h.2 k hk]
lemma add (hf : Vanishing n f) (hg : Vanishing n g) :
    Vanishing n (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro k hk
  change iteratedFDeriv ℂ k (f+g) 0 = 0
  rw [iteratedFDeriv_add_apply hf.1.contDiffAt hg.1.contDiffAt, hf.2 k hk, hg.2 k hk, add_zero]
lemma sub (hf : Vanishing n f) (hg : Vanishing n g) :
    Vanishing n (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  intro k hk
  change iteratedFDeriv ℂ k (f-g) 0 = 0
  rw [iteratedFDeriv_sub_apply hf.1.contDiffAt hg.1.contDiffAt, hf.2 k hk, hg.2 k hk, sub_zero]

lemma mul (hf : Vanishing n f) (hg : Vanishing m g) :
    Vanishing (n+m) (fun x => f x*g x) := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  intro k hk
  obtain ⟨s, hs, hz, haf, hag⟩ := analytic_neighborhood hf.1 hg.1
  have hfs : ContDiffOn ℂ (k : WithTop ℕ∞) f s := haf.contDiffOn hs.uniqueDiffOn
  have hgs : ContDiffOn ℂ (k : WithTop ℕ∞) g s := hag.contDiffOn hs.uniqueDiffOn
  have hle := norm_iteratedFDerivWithin_mul_le hfs hgs hs.uniqueDiffOn hz (le_refl (k : WithTop ℕ∞))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (f := fun y => f y*g y) hs.uniqueDiffOn
    (by convert! (hf.1.mul hg.1).contDiffAt using 1) hz] at hle
  have hsum : (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
      ‖iteratedFDerivWithin ℂ i f s 0‖ * ‖iteratedFDerivWithin ℂ (k-i) g s 0‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn hf.1.contDiffAt hz,
      iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn hg.1.contDiffAt hz]
    by_cases hin : i < n
    · simp [hf.2 i hin]
    · have hig : k-i < m := by have := Finset.mem_range.mp hi; omega
      simp [hg.2 (k-i) hig]
  rw [hsum] at hle
  exact norm_le_zero_iff.mp hle

lemma const_mul (hf : Vanishing n f) (c : ℂ) : Vanishing n (fun x => c*f x) := by
  simpa only [zero_add] using (zero (f := fun _ : E => c) analyticAt_const).mul hf
lemma mul_const (hf : Vanishing n f) (c : ℂ) : Vanishing n (fun x => f x*c) := by
  simpa only [add_zero] using hf.mul (zero (f := fun _ : E => c) analyticAt_const)
lemma pow (hf : Vanishing n f) (k : ℕ) : Vanishing (n*k) (fun x => (f x)^k) := by
  induction k with
  | zero => simpa using zero (f := fun _ : E => (1 : ℂ)) analyticAt_const
  | succ k ih =>
    simpa only [pow_succ, Nat.mul_succ, Nat.add_comm] using ih.mul hf

end Vanishing

 

lemma iteratedFDeriv_comp_linear {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → ℂ} (hf : AnalyticAt ℂ f 0) (L : F →L[ℂ] E) (k : ℕ) :
    iteratedFDeriv ℂ k (f ∘ L) 0 =
      (iteratedFDeriv ℂ k f 0).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨s, hs, hz, haf, _⟩ := analytic_neighborhood hf hf
  have ht := hs.preimage L.continuous
  have hz' : L (0 : F) ∈ s := by simpa using hz
  have h := L.iteratedFDerivWithin_comp_right
    (haf.contDiffOn hs.uniqueDiffOn : ContDiffOn ℂ (k : WithTop ℕ∞) f s) hs.uniqueDiffOn ht.uniqueDiffOn hz' (le_refl (k : WithTop ℕ∞))
  have hac : AnalyticAt ℂ (f ∘ L) 0 := by
    have ha : AnalyticAt ℂ f (L 0) := by simpa using hf
    exact ha.comp (L.analyticAt 0)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv ht.uniqueDiffOn hac.contDiffAt hz',
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (by simpa using hf.contDiffAt) hz'] at h
  simpa using h

lemma derivative_eq_of_remainder {f g : E → ℂ} {n k : ℕ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hr : Vanishing n (fun x => f x-g x)) (hk : k < n) :
    iteratedFDeriv ℂ k f 0 = iteratedFDeriv ℂ k g 0 := by
  have h := hr.2 k hk
  change iteratedFDeriv ℂ k (f-g) 0 = 0 at h
  rw [iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt] at h
  exact sub_eq_zero.mp h

lemma nonzero_derivative_of_line {f : E → ℂ} (hf : AnalyticAt ℂ f 0)
    (L : ℂ →L[ℂ] E) (n : ℕ) {c : ℂ} (hc : c ≠ 0)
    (he : ∀ t : ℂ, f (L t) = c*t^n) :
    iteratedFDeriv ℂ n f 0 ≠ 0 := by
  intro hz
  have hd := iteratedFDeriv_comp_linear hf L n
  rw [hz] at hd
  have hd0 : iteratedDeriv n (f ∘ L) 0 = 0 := by
    rw [iteratedDeriv_eq_iteratedFDeriv, hd]
    simp
  have heq : f ∘ L = fun t : ℂ => c*t^n := funext he
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_pow] at hd0
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp [Nat.descFactorial_self, hc, hn] at hd0

lemma Vanishing.gradient_zero {f : E → ℂ} {n : ℕ}
    (hf : Vanishing n f) (hn : 1 < n) : fderiv ℂ f 0 = 0 := by
  ext v
  have h := congrArg (fun M => M (fun _ : Fin 1 => v)) (hf.2 1 hn)
  simpa only [iteratedFDeriv_one_apply, zero_apply] using h

 
lemma order_of_remainder {f g : E → ℂ} {n : ℕ} (hf : AnalyticAt ℂ f 0)
    (hg : Vanishing n g) (hr : Vanishing (n+1) (fun x => f x-g x))
    (hgn : iteratedFDeriv ℂ n g 0 ≠ 0) :
    Vanishing n f ∧ iteratedFDeriv ℂ n f 0 ≠ 0 := by
  constructor
  · refine ⟨hf, fun k hk => ?_⟩
    rw [derivative_eq_of_remainder hf hg.1 hr (by omega), hg.2 k hk]
  · rw [derivative_eq_of_remainder hf hg.1 hr (by omega)]
    exact hgn

end
end AmbientMultiplicity.Jets

end OAI
