import OAI.Geometry.PolarProducts.PeriodicFourier

namespace OAI

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 theorem critical_H1_bounds (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B D : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hd : ∀ j, |d j| ≤ D)
    (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) :
    (∫ t in (0:ℝ)..1, ‖loop k a (t : Time)‖^2) ≤ (B/(2*γ))^2 ∧
    (∫ t in (0:ℝ)..1, ‖loop k (velocityCoeff k a) (t : Time)‖^2) ≤
      (B+2*D*(B/(2*γ)))^2 := by
  have hn := critical_norm_bound k hk hH d hγ hB hgap hrem a ha
  have hv := norm_project_grad k hk hH d hB hD hd hrem a
  rw [← norm_velocityCoeff_critical k hH a ha] at hv
  have hd' : 0 ≤ 2*D := mul_nonneg (by norm_num) hD
  have hvel : ‖velocityCoeff k a‖ ≤ B+2*D*(B/(2*γ)) :=
    hv.trans (by linarith [mul_le_mul_of_nonneg_left hn hd'])
  rw [intervalIntegral_eq_average (fun t : Time => ‖loop k a t‖^2),
    intervalIntegral_eq_average (fun t : Time => ‖loop k (velocityCoeff k a) t‖^2),
    integral_loop_norm_sq k hk, integral_loop_norm_sq k hk]
  exact ⟨pow_le_pow_left₀ (norm_nonneg _) hn 2, pow_le_pow_left₀ (norm_nonneg _) hvel 2⟩

 theorem critical_modulus (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B D : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hd : ∀ j, |d j| ≤ D)
    (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) (t s : L2Paths.Segment) :
    dist (loop k a (t.val : Time)) (loop k a (s.val : Time))^2 ≤
      (B+2*D*(B/(2*γ)))^2*dist t s := by
  have hb := (critical_H1_bounds k hk hH d hγ hB hD hd hgap hrem a ha).2
  have h := L2Paths.norm_sub_sq_le_global
    (fun t : ℝ => loop k a (t : Time)) (fun t : ℝ => loop k (velocityCoeff k a) (t : Time))
    ((loop k (velocityCoeff k a)).continuous.comp continuous_quot_mk)
    (hasDerivAt_loop k a) hb s.property t.property
  simpa only [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, Real.norm_eq_abs] using h

 theorem critical_loop_bound (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B D : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hd : ∀ j, |d j| ≤ D)
    (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) (t : L2Paths.Segment) :
    ‖loop k a (t.val : Time)‖ ≤ B/(2*γ)+(B+2*D*(B/(2*γ))) := by
  have hb := critical_H1_bounds k hk hH d hγ hB hD hd hgap hrem a ha
  apply L2Paths.norm_bound
    (fun t : ℝ => loop k a (t : Time)) (fun t : ℝ => loop k (velocityCoeff k a) (t : Time))
    ((loop k (velocityCoeff k a)).continuous.comp continuous_quot_mk)
    (hasDerivAt_loop k a) (by positivity) (by positivity) hb.1 hb.2 t.property

 theorem critical_subsequence {α : ℕ → Type} [∀ n, Fintype (α n)]
    (k : (n : ℕ) → α n → ℤ) (hk : ∀ n, Function.Injective (k n))
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B D : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hd : ∀ j, |d j| ≤ D)
    (hgap : ∀ n i j, γ ≤ |Real.pi*(k n i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B)
    (a : (n : ℕ) → Coeff (α n) κ) (ha : ∀ n, gradient (action (k n) H) (a n) = 0) :
    ∃ x : C(Time,Vector κ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => loop (k (φ n)) (a (φ n))) atTop (𝓝 x) := by
  exact L2Paths.exists_periodic_subsequence (fun n => loop (k n) (a n))
    (fun n t s => critical_modulus (k n) (hk n) hH d hγ hB hD hd (hgap n) hrem (a n) (ha n) t s)
    (fun n t => critical_loop_bound (k n) (hk n) hH d hγ hB hD hd (hgap n) hrem (a n) (ha n) t)

 def coordPath (j : κ) : C(Time,Vector κ) →L[ℂ] C(Time,ℂ) :=
   ContinuousLinearMap.compLeftContinuous ℂ Time (PiLp.proj 2 (fun _ : κ => ℂ) j)

@[simp] theorem coordPath_apply (j : κ) (x : C(Time,Vector κ)) (t : Time) : coordPath j x t = x t j := rfl

 def gradPath {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) : C(Time,Vector κ) → C(Time,Vector κ) :=
   SmoothPaths.superpose (contDiff_gradient_function hH).continuous

 theorem contDiff_gradPath {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (gradPath hH) :=
   SmoothPaths.contDiff_superpose (contDiff_gradient_function hH)

 theorem critical_coefficient (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) (i : ι) (j : κ) :
    PeriodicFourier.coefficient (k i) (coordPath j (gradPath hH (loop k a))) =
      (2*(Real.pi : ℂ)*(k i : ℂ))*PeriodicFourier.coefficient (k i) (coordPath j (loop k a)) := by
  have he : (2 : ℝ) • diag (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a = project k (gradLoop k hH a) := by
    simpa only [gradient_action k hH, sub_eq_zero] using ha
  change project k (gradLoop k hH a) (i,j) = (2*(Real.pi : ℂ)*(k i : ℂ))*project k (loop k a) (i,j)
  rw [project_loop k hk, ← he]
  simp only [PiLp.smul_apply, diag_apply, RCLike.real_smul_eq_coe_mul, map_mul, map_intCast, map_ofNat]
  change (2:ℂ)*((Real.pi : ℂ)*(k i : ℂ)*a (i,j)) = (2*(Real.pi : ℂ)*(k i : ℂ))*a (i,j)
  ring

 theorem limit_coefficient {α : ℕ → Type} [∀ n, Fintype (α n)]
    (k : (n : ℕ) → α n → ℤ) (hk : ∀ n, Function.Injective (k n))
    (hex : ∀ m : ℤ, ∀ᶠ n in atTop, m ∈ Set.range (k n))
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : (n : ℕ) → Coeff (α n) κ) (ha : ∀ n, gradient (action (k n) H) (a n) = 0)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x : C(Time,Vector κ))
    (ht : Tendsto (fun n => loop (k (φ n)) (a (φ n))) atTop (𝓝 x)) (m : ℤ) (j : κ) :
    PeriodicFourier.coefficient m (coordPath j (gradPath hH x)) =
      (2*(Real.pi : ℂ)*(m : ℂ))*PeriodicFourier.coefficient m (coordPath j x) := by
  have hg := (contDiff_gradPath hH).continuous.continuousAt.tendsto.comp ht
  have hc := (PeriodicFourier.coefficient m).continuous.comp (coordPath j).continuous
  have hleft := hc.continuousAt.tendsto.comp hg
  have hright := (tendsto_const_nhds (x := (2*(Real.pi : ℂ)*(m : ℂ)))).mul
    (hc.continuousAt.tendsto.comp ht)
  apply tendsto_nhds_unique_of_eventuallyEq hleft hright
  filter_upwards [hφ.tendsto_atTop.eventually (hex m)] with n hn
  rcases hn with ⟨i,rfl⟩
  exact critical_coefficient (k (φ n)) (hk (φ n)) hH (a (φ n)) (ha (φ n)) i j

 theorem hasDerivAt_of_critical_coefficients {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (x : C(Time,Vector κ))
    (h : ∀ m j, PeriodicFourier.coefficient m (coordPath j (gradPath hH x)) =
      (2*(Real.pi : ℂ)*(m : ℂ))*PeriodicFourier.coefficient m (coordPath j x)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x (s : Time)) (Complex.I • gradient H (x (t : Time))) t := by
  have hj (j : κ) : HasDerivAt (fun s : ℝ => x (s : Time) j)
      (Complex.I • gradient H (x (t : Time)) j) t := by
    have hc (m : ℤ) : PeriodicFourier.coefficient m (Complex.I • coordPath j (gradPath hH x)) =
        (2*(Real.pi : ℂ)*Complex.I*(m : ℂ))*PeriodicFourier.coefficient m (coordPath j x) := by
      rw [map_smul, h]
      simp only [smul_eq_mul]
      ring
    exact PeriodicFourier.hasDerivAt_of_coefficients (coordPath j x)
      (Complex.I • coordPath j (gradPath hH x)) hc t
  have hp := hasDerivAt_pi.mpr hj
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.hasFDerivAt.comp_hasDerivAt t hp

 theorem positive_action_limit {α : ℕ → Type} [∀ n, Fintype (α n)]
    (k : (n : ℕ) → α n → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : (n : ℕ) → Coeff (α n) κ) (ha : ∀ n, gradient (action (k n) H) (a n) = 0)
    {L : ℝ} (hL : ∀ n, L ≤ action (k n) H (a n))
    (φ : ℕ → ℕ) (x : C(Time,Vector κ))
    (ht : Tendsto (fun n => loop (k (φ n)) (a (φ n))) atTop (𝓝 x)) :
    L ≤ meanAction hH x := by
  apply ge_of_tendsto' ((contDiff_meanAction hH).continuous.continuousAt.tendsto.comp ht)
  intro n
  change L ≤ meanAction hH (loop (k (φ n)) (a (φ n)))
  rw [← critical_action_eq _ hH _ (ha (φ n))]
  exact hL (φ n)

end
end FourierPolynomial

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
open DiagonalQuadratic FourierPolynomial

 def negativeMode (N : ℕ) (i : Fin (N+1)) : ℤ := -(i.val : ℤ)
 def positiveMode (N : ℕ) (i : Fin (N+1)) : ℕ := i.val+1
 def frequency (N : ℕ) : Fin (N+1) ⊕ Fin (N+1) → ℤ :=
   Sum.elim (negativeMode N) (fun i => (positiveMode N i : ℤ))

 theorem negativeMode_nonpos (N : ℕ) (i : Fin (N+1)) : negativeMode N i ≤ 0 := by
  simp [negativeMode]

 theorem positiveMode_pos (N : ℕ) (i : Fin (N+1)) : 0 < positiveMode N i := Nat.succ_pos _

 theorem positiveMode_injective (N : ℕ) : Function.Injective (positiveMode N) := by
  intro i j hij
  apply Fin.ext
  simpa [positiveMode] using hij

 theorem frequency_injective (N : ℕ) : Function.Injective (frequency N) := by
  intro i j hij
  cases i <;> cases j
  · simp only [frequency, Sum.elim_inl, negativeMode, neg_inj, Nat.cast_inj] at hij
    exact congrArg Sum.inl (Fin.ext hij)
  · simp only [frequency, Sum.elim_inl, Sum.elim_inr, negativeMode, positiveMode, Nat.cast_add, Nat.cast_one] at hij
    omega
  · simp only [frequency, Sum.elim_inl, Sum.elim_inr, negativeMode, positiveMode, Nat.cast_add, Nat.cast_one] at hij
    omega
  · simp only [frequency, Sum.elim_inr, Nat.cast_inj] at hij
    exact congrArg Sum.inr (positiveMode_injective N hij)

 theorem frequency_exhausts (m : ℤ) : ∀ᶠ N in atTop, m ∈ Set.range (frequency N) := by
  cases m with
  | ofNat m =>
    cases m with
    | zero =>
      filter_upwards [] with N
      exact ⟨Sum.inl ⟨0,Nat.succ_pos N⟩, by simp [frequency,negativeMode]⟩
    | succ m =>
      filter_upwards [eventually_ge_atTop m] with N hN
      exact ⟨Sum.inr ⟨m,by omega⟩, by simp [frequency,positiveMode]⟩
  | negSucc m =>
    filter_upwards [eventually_ge_atTop (m+1)] with N hN
    exact ⟨Sum.inl ⟨m+1,by omega⟩, by simp [frequency,negativeMode,Int.negSucc_eq]⟩

 variable {κ : Type} [Fintype κ] [DecidableEq κ]

 theorem exists_positive_periodic
    (j₀ : κ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hH0 : ∀ z, 0 ≤ H z)
    (d₀ d : κ → ℝ) {C M η γ B D : ℝ}
    (hM : 0 ≤ M) (hη : 0 < η) (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hup : ∀ z, H z ≤ M*‖z‖^4)
    (hd : ∀ j, η ≤ d₀ j) (hd0 : Real.pi+η ≤ d₀ j₀)
    (hlo : ∀ z, energy d₀ z-C ≤ H z) (hdD : ∀ j, |d j| ≤ D)
    (hgap : ∀ m : ℤ, ∀ j, γ ≤ |Real.pi*(m : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) :
    ∃ x : C(Time,Vector κ), 0 < meanAction hH x ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => x (s : Time))
        (Complex.I • gradient H (x (t : Time))) t := by
  have he (N : ℕ) := finite_critical (negativeMode N) (negativeMode_nonpos N)
    (positiveMode N) (positiveMode_injective N) (positiveMode_pos N) (frequency_injective N)
    (⟨0,Nat.succ_pos N⟩ : Fin (N+1)) rfl j₀ hH hH0 d₀ d hM hη hγ hB hup hd hd0 hlo
    (fun i j => hgap (frequency N i) j) hrem
  choose a ha hupper hz using he
  obtain ⟨x,φ,hφ,ht⟩ := critical_subsequence frequency frequency_injective hH d hγ hB hD hdD
    (fun n i j => hgap (frequency n i) j) hrem a hz
  refine ⟨x,lt_of_lt_of_le (linkLevel_pos hM) (positive_action_limit frequency hH a hz ha φ x ht),?_⟩
  exact hasDerivAt_of_critical_coefficients hH x
    (limit_coefficient frequency frequency_injective frequency_exhausts hH a hz φ hφ x ht)

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
