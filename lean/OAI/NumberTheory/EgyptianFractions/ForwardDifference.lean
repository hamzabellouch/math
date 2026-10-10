import OAI.NumberTheory.EgyptianFractions.ReciprocalDerivatives

namespace OAI
noncomputable section
open Set
open scoped ContDiff Topology

namespace Problem337

/-- Iterated forward differences, with the shifts in list order. -/
def forwardDifference : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | h :: hs, f => fun x => forwardDifference hs f (x + h) - forwardDifference hs f x

theorem forwardDifference_contDiffOn (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) :
    ContDiffOn ℝ ∞ (forwardDifference hs f) (Ioi 0) := by
  induction hs with
  | nil => exact hf
  | cons h hs ih =>
      have hh : 0 ≤ h := hhs h (by simp)
      have ih' := ih (fun d hd => hhs d (by simp [hd]))
      change ContDiffOn ℝ ∞ (fun x => forwardDifference hs f (x + h) - forwardDifference hs f x) (Ioi 0)
      apply ContDiffOn.sub _ ih'
      apply ih'.comp (contDiffOn_id.add contDiffOn_const)
      intro x hx
      change 0 < x + h
      change 0 < x at hx
      linarith

theorem deriv_forwardDifference (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    deriv (forwardDifference hs f) x = forwardDifference hs (deriv f) x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      have hh : 0 ≤ h := hhs h (by simp)
      have htail : ∀ d ∈ hs, 0 ≤ d := fun d hd => hhs d (by simp [hd])
      have hcont := forwardDifference_contDiffOn hs htail hf
      have hx' : 0 < x + h := by linarith
      have hdiff : DifferentiableAt ℝ (forwardDifference hs f) x :=
        (hcont.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)
      have hdiff' : DifferentiableAt ℝ (fun y => forwardDifference hs f (y + h)) x := by
        exact ((hcont.contDiffAt (isOpen_Ioi.mem_nhds hx')).differentiableAt (by simp)).comp x
          (differentiableAt_id.add_const h)
      change deriv (fun y => forwardDifference hs f (y + h) - forwardDifference hs f y) x = _
      rw [deriv_fun_sub hdiff' hdiff, deriv_comp_add_const]
      change deriv (forwardDifference hs f) (x + h) - deriv (forwardDifference hs f) x = _
      rw [ih htail, ih htail]
      rfl
      all_goals assumption

/-- Repeated mean value theorem for positive shifts. The witness remains in the
interval swept out by all shifts. -/
theorem forwardDifference_eq_derivative (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    ∃ ξ : ℝ, x ≤ ξ ∧ ξ ≤ x + hs.sum ∧
      forwardDifference hs f x = hs.prod * iteratedDeriv hs.length f ξ := by
  induction hs generalizing f x with
  | nil => exact ⟨x, le_rfl, by simp, by simp [forwardDifference]⟩
  | cons h hs ih =>
      have hh : 0 < h := hhs h (by simp)
      have htail : ∀ d ∈ hs, 0 < d := fun d hd => hhs d (by simp [hd])
      have hnonneg : ∀ d ∈ hs, 0 ≤ d := fun d hd => (htail d hd).le
      have hcont := forwardDifference_contDiffOn hs hnonneg hf
      have hcc : Icc x (x + h) ⊆ Ioi 0 := by intro y hy; exact hx.trans_le hy.1
      have hco : Ioo x (x + h) ⊆ Ioi 0 := Ioo_subset_Icc_self.trans hcc
      obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope (forwardDifference hs f)
        (by linarith : x < x + h) (hcont.continuousOn.mono hcc)
        ((hcont.differentiableOn (by simp)).mono hco)
      have hc0 : 0 < c := hx.trans hc.1
      rw [deriv_forwardDifference hs hnonneg hf hc0] at hderiv
      have hden : x + h - x = h := by ring
      rw [hden] at hderiv
      have hmul : forwardDifference (h :: hs) f x = h * forwardDifference hs (deriv f) c := by
        have heq := (eq_div_iff hh.ne').1 hderiv
        dsimp [forwardDifference]
        nlinarith
      have hf' : ContDiffOn ℝ ∞ (deriv f) (Ioi 0) :=
        hf.deriv_of_isOpen isOpen_Ioi (by simp)
      obtain ⟨ξ, hcξ, hξ, heq⟩ := ih htail hf' hc0
      refine ⟨ξ, hc.1.le.trans hcξ, ?_, ?_⟩
      · simp only [List.sum_cons]
        linarith [hc.2]
      · rw [hmul, heq]
        simp only [List.prod_cons, List.length_cons, iteratedDeriv_succ']
        ring

theorem iteratedDeriv_forwardDifference (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (forwardDifference hs f) x = forwardDifference hs (iteratedDeriv k f) x := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      have heq : deriv (forwardDifference hs f) =ᶠ[𝓝 x] forwardDifference hs (deriv f) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact deriv_forwardDifference hs hhs hf hy
      rw [iteratedDeriv_succ', heq.iteratedDeriv_eq k]
      rw [ih (hf.deriv_of_isOpen isOpen_Ioi (by simp))]
      rw [iteratedDeriv_succ']

private theorem smooth_iteratedDeriv_Ioi (k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) : ContDiffOn ℝ ∞ (iteratedDeriv k f) (Ioi 0) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

private theorem iteratedDeriv_order_add (r k : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv r (iteratedDeriv k f) = iteratedDeriv (r + k) f := by
  induction r with
  | zero => simp
  | succ r ih => simp only [iteratedDeriv_succ, ih, Nat.succ_add]

/-- The derivative of an iterated difference is a scaled higher derivative at an
intermediate point. This avoids a multi-dimensional integral in the phase estimate. -/
theorem iteratedDeriv_forwardDifference_eq (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    ∃ ξ : ℝ, x ≤ ξ ∧ ξ ≤ x + hs.sum ∧
      iteratedDeriv k (forwardDifference hs f) x =
        hs.prod * iteratedDeriv (hs.length + k) f ξ := by
  rw [iteratedDeriv_forwardDifference k hs (fun h hh => (hhs h hh).le) hf hx]
  obtain ⟨ξ, hxξ, hξ, heq⟩ := forwardDifference_eq_derivative hs hhs
    (smooth_iteratedDeriv_Ioi k hf) hx
  refine ⟨ξ, hxξ, hξ, ?_⟩
  simpa only [iteratedDeriv_order_add] using heq

/-- Uniform bounds for the derivatives of a differenced reciprocal phase on its
untruncated support. In particular `k=2` is the input to a second-derivative test. -/
theorem reciprocal_forwardDifference_derivative_bounds (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (Z : ℝ) {U x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxend : x + hs.sum ≤ 2 * U) :
    hs.prod * ((hs.length + k).factorial : ℝ) * |Z| /
        (2 * U) ^ (hs.length + k + 1) ≤
      |iteratedDeriv k (forwardDifference hs (fun y => Z / y)) x| ∧
    |iteratedDeriv k (forwardDifference hs (fun y => Z / y)) x| ≤
      hs.prod * ((hs.length + k).factorial : ℝ) * |Z| /
        U ^ (hs.length + k + 1) := by
  have hf : ContDiffOn ℝ ∞ (fun y : ℝ => Z / y) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun y hy => ne_of_gt hy)
  obtain ⟨ξ, hxξ, hξ, heq⟩ := iteratedDeriv_forwardDifference_eq k hs hhs hf (hU.trans_le hx)
  have hp : 0 ≤ hs.prod := List.prod_nonneg (fun h hh => (hhs h hh).le)
  rw [heq, abs_mul, abs_of_nonneg hp]
  obtain ⟨hl, hu⟩ := reciprocal_phase_derivative_bounds (hs.length + k) Z hU
    (hx.trans hxξ) (hξ.trans hxend)
  constructor
  · simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hl hp
  · simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hu hp

/-- Endpoint-flexible version, allowing the upper endpoint to extend beyond
an exponential sum's support by the one or two derivative-test samples. -/
theorem reciprocal_forwardDifference_derivative_bounds_interval (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (Z : ℝ) {U V x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxend : x + hs.sum ≤ V) :
    hs.prod * ((hs.length + k).factorial : ℝ) * |Z| /
        V ^ (hs.length + k + 1) ≤
      |iteratedDeriv k (forwardDifference hs (fun y => Z / y)) x| ∧
    |iteratedDeriv k (forwardDifference hs (fun y => Z / y)) x| ≤
      hs.prod * ((hs.length + k).factorial : ℝ) * |Z| /
        U ^ (hs.length + k + 1) := by
  have hf : ContDiffOn ℝ ∞ (fun y : ℝ => Z / y) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun y hy => ne_of_gt hy)
  obtain ⟨ξ, hxξ, hξ, heq⟩ := iteratedDeriv_forwardDifference_eq k hs hhs hf (hU.trans_le hx)
  have hp : 0 ≤ hs.prod := List.prod_nonneg (fun h hh => (hhs h hh).le)
  rw [heq, abs_mul, abs_of_nonneg hp]
  obtain ⟨hl, hu⟩ := reciprocal_phase_derivative_bounds_interval (hs.length + k) Z hU
    (hx.trans hxξ) (hξ.trans hxend)
  constructor
  · simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hl hp
  · simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hu hp

end Problem337

end

end OAI
