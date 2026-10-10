import OAI.MeasureTheory.Falconer.Angular.AngularIntegrationByParts
import OAI.MeasureTheory.Falconer.Angular.AngularTransportBounds
import OAI.MeasureTheory.Falconer.Angular.SmoothInverseSine

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

 theorem angularTransportIterate_integral {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hqs : ∀ x ∈ tsupport f, (Real.sin x:ℂ)*q x = 1) (Λ : ℝ) (n : ℕ) :
    (∫ x : ℝ, cosineOscillator Λ x * angularTransportIterate q n f x) =
      (Complex.I*(Λ:ℂ))^n * ∫ x : ℝ, cosineOscillator Λ x * f x := by
  induction n with
  | zero => simp [angularTransportIterate]
  | succ n ih =>
    have hi := angularTransportIterate_contDiff hq hf n
    have hc' : HasCompactSupport (angularTransportIterate q n f) :=
      hc.mono' (fun x hx => angularTransportIterate_support q f n (subset_closure hx))
    have hh := angular_integration_by_parts hq hi hc'
      (fun x hx => hqs x (angularTransportIterate_support q f n hx)) Λ
    change (∫ x : ℝ, cosineOscillator Λ x * angularTransport q (angularTransportIterate q n f) x) = _
    rw [hh,ih,pow_succ]
    ring

 theorem angular_nonstationary_uniform {η a b : ℝ} (hη : 0 < η) (hab : a ≤ b) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    tsupport f ⊆ Icc a b → (∀ x ∈ tsupport f, η ≤ |Real.sin x|) →
    ∀ {C D Λ : ℝ}, 0 ≤ C → 1 ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ x * f x‖ ≤ A*C*D^n/Λ^n := by
  let q : ℝ → ℂ := fun x => (smoothInverseSine η hη x : ℂ)
  have hq : ContDiff ℝ ∞ q := Complex.ofRealCLM.contDiff.comp (smoothInverseSine_contDiff η hη)
  obtain ⟨A,hA,hbound⟩ := angularTransportIterate_uniform_bound hq (K := Icc a b) isCompact_Icc n
  refine ⟨A*(b-a),mul_nonneg hA (sub_nonneg.mpr hab),?_⟩
  intro f hf hs haway C D Λ hC hD hΛ hb
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  have hqs : ∀ x ∈ tsupport f, (Real.sin x:ℂ)*q x = 1 := by
    intro x hx
    change (Real.sin x:ℂ)*(smoothInverseSine η hη x:ℂ) = 1
    exact_mod_cast smoothInverseSine_eq hη (haway x hx)
  have hit := angularTransportIterate_contDiff hq hf n
  have hist : tsupport (angularTransportIterate q n f) ⊆ Icc a b :=
    (angularTransportIterate_support q f n).trans hs
  have hib : ∀ x, ‖angularTransportIterate q n f x‖ ≤ A*C*D^n := by
    intro x
    by_cases hx : x ∈ Icc a b
    · exact hbound hf hC hD hb x hx
    · rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hist hh)),norm_zero]
      positivity
  obtain ⟨φ,hφ⟩ := compact_smooth_to_schwartz hist hit
  have hsφ : tsupport (φ : ℝ → ℂ) ⊆ Icc a b := by simpa [hφ] using hist
  have hbφ : ∀ x, ‖iteratedDeriv 0 (φ : ℝ → ℂ) x‖ ≤ A*C*D^n := by simpa [hφ] using hib
  have hL := compact_derivative_integral_bound φ hab hsφ 0 hbφ
  simp only [iteratedDeriv_zero] at hL
  have hφ' : ∀ x, φ x = angularTransportIterate q n f x := congrFun hφ
  simp only [hφ'] at hL
  have hi : ‖∫ x : ℝ, cosineOscillator Λ x * angularTransportIterate q n f x‖ ≤
      (A*C*D^n)*(b-a) := by
    apply (norm_integral_le_integral_norm _).trans
    simpa only [norm_mul,cosineOscillator_norm,one_mul] using hL
  rw [angularTransportIterate_integral hq hf hc hqs Λ n,norm_mul,norm_pow,norm_mul,
    Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hΛ] at hi
  apply (le_div_iff₀ (pow_pos hΛ n)).mpr
  calc
    _ = Λ^n * ‖∫ x : ℝ, cosineOscillator Λ x * f x‖ := by ring
    _ ≤ (A*C*D^n)*(b-a) := hi
    _ = _ := by ring

end PlanarFalconer

end OAI
