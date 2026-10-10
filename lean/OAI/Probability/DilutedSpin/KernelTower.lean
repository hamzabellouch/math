import OAI.Probability.DilutedSpin.FiniteLaw

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- A finite path space. All probability kernels in the bounded auxiliary
perturbation construction are finite, conditional on the physical root. -/
def FinitePath (Ω : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => Ω × FinitePath Ω n

instance finitePathFintype (Ω : Type) [Fintype Ω] : (n : ℕ) → Fintype (FinitePath Ω n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    letI := finitePathFintype Ω n
    exact inferInstanceAs (Fintype (Ω × FinitePath Ω n))

/-- Finite kernels depending on the full preceding path, before tilting. -/
def KernelTower (Ω : Type) [Fintype Ω] : ℕ → Type
  | 0 => Unit
  | n + 1 => FiniteLaw Ω × (Ω → KernelTower Ω n)

namespace KernelTower

variable {Ω : Type} [Fintype Ω]

noncomputable def unitLaw : FiniteLaw Unit where
  weight _ := 1
  nonneg _ := by norm_num
  total := by simp

noncomputable def law : (n : ℕ) → KernelTower Ω n → FiniteLaw (FinitePath Ω n)
  | 0, _ => unitLaw
  | n+1, T => T.1.bind (fun x => law n (T.2 x))

noncomputable def backwardLog : (n : ℕ) → KernelTower Ω n →
    (Fin n → ℝ) → (FinitePath Ω n → ℝ) → ℝ
  | 0, _, _, f => f ()
  | n+1, T, m, f => T.1.logMean (m 0)
      (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

noncomputable def tilt : (n : ℕ) → KernelTower Ω n →
    (Fin n → ℝ) → (FinitePath Ω n → ℝ) → KernelTower Ω n
  | 0, _, _, _ => ()
  | n+1, T, m, f =>
    (T.1.tilt (m 0) (fun x => backwardLog n (T.2 x)
        (fun j => m j.succ) (fun y => f (x,y))),
      fun x => tilt n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

@[simp] theorem expect_unitLaw (f : Unit → ℝ) : unitLaw.expect f = f () := by
  simp [FiniteLaw.expect, unitLaw]

@[simp] theorem law_zero_expect (T : KernelTower Ω 0) (f : FinitePath Ω 0 → ℝ) :
    (law 0 T).expect f = f () := expect_unitLaw f

@[simp] theorem law_succ_expect (n : ℕ) (T : KernelTower Ω (n+1))
    (f : FinitePath Ω (n+1) → ℝ) :
    (law (n+1) T).expect f = T.1.expect (fun x => (law n (T.2 x)).expect (fun y => f (x,y))) :=
  T.1.expect_bind (fun x => law n (T.2 x)) f

/-- First variation through the entire finite hierarchy, with all exponents
and all original path-dependent priors retained. -/
theorem hasDerivAt_backwardLog (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (hm : ∀ i, m i ≠ 0)
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => backwardLog n T m (f t))
      ((law n (tilt n T m (f u))).expect f') u := by
  induction n with
  | zero =>
    rw [law_zero_expect (Ω := Ω)]
    exact hf ()
  | succ n ih =>
    have hs := fun x => ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
      (fun y => hf (x,y))
    rw [law_succ_expect (Ω := Ω) n]
    simpa only [backwardLog, tilt] using
      T.1.hasDerivAt_logMean (hm 0) hs

 
theorem insertion (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (f a : FinitePath Ω n → ℝ) :
    backwardLog n T m (fun x => f x + a x) - backwardLog n T m f =
      backwardLog n (tilt n T m f) m a := by
  induction n with
  | zero => simp only [backwardLog]; ring
  | succ n ih =>
    let F := fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y))
    let A := fun x => backwardLog n
      (tilt n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
      (fun j => m j.succ) (fun y => a (x,y))
    have hc : (fun x => backwardLog n (T.2 x) (fun j => m j.succ)
        (fun y => f (x,y) + a (x,y))) = (fun x => F x + A x) := by
      funext x
      have hi := ih (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) (fun y => a (x,y))
      change _ - F x = A x at hi
      linarith
    change T.1.logMean (m 0) _ - T.1.logMean (m 0) F =
      (T.1.tilt (m 0) F).logMean (m 0) A
    rw [hc]
    exact T.1.logMean_insertion F A


 
noncomputable def varianceEnergy : (n : ℕ) → KernelTower Ω n →
    (Fin n → ℝ) → (FinitePath Ω n → ℝ) → ℝ
  | 0, _, _, _ => 0
  | n+1, T, m, f =>
      m 0 * T.1.covariance
        (fun x => (law n (T.2 x)).expect (fun y => f (x,y)))
        (fun x => (law n (T.2 x)).expect (fun y => f (x,y))) +
      T.1.expect (fun x => varianceEnergy n (T.2 x) (fun j => m j.succ)
        (fun y => f (x,y)))

/-- The lower energy estimate in pert:second-derivative; the smallest exponent
controls the full terminal path variance, not merely the root variance. -/
theorem varianceEnergy_lower (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) {c : ℝ} (hm : ∀ i, c ≤ m i) (f : FinitePath Ω n → ℝ) :
    c * (law n T).covariance f f ≤ varianceEnergy n T m f := by
  induction n with
  | zero => simp [FiniteLaw.covariance, law_zero_expect, varianceEnergy]
  | succ n ih =>
    let g := fun x => (law n (T.2 x)).expect (fun y => f (x,y))
    have hfirst : c * T.1.covariance g g ≤ m 0 * T.1.covariance g g :=
      mul_le_mul_of_nonneg_right (hm 0) (T.1.covariance_self_nonneg g)
    have hrest := T.1.expect_mono (fun x => ih (T.2 x) (fun j => m j.succ)
      (fun j => hm j.succ) (fun y => f (x,y)))
    have hv := T.1.variance_bind (fun x => law n (T.2 x)) f
    change (law (n+1) T).covariance f f = _ at hv
    rw [hv]
    simp only [varianceEnergy]
    dsimp only [g] at hfirst
    rw [FiniteLaw.expect_mul_left] at hrest
    nlinarith

/-- The exact martingale-energy telescoping identity. -/
theorem varianceEnergy_const (n : ℕ) (T : KernelTower Ω n) (c : ℝ)
    (f : FinitePath Ω n → ℝ) :
    varianceEnergy n T (fun _ => c) f = c * (law n T).covariance f f := by
  induction n with
  | zero => simp [FiniteLaw.covariance, law_zero_expect, varianceEnergy]
  | succ n ih =>
    have hv := T.1.variance_bind (fun x => law n (T.2 x)) f
    change (law (n+1) T).covariance f f = _ at hv
    rw [hv]
    simp only [varianceEnergy, ih, FiniteLaw.expect_mul_left]
    ring

/-- Second variation through a tower. Terminal derivatives plus the positive
weighted martingale energy from every depth. No concentration is assumed. -/
theorem hasDerivAt_path_score (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (hm : ∀ i, m i ≠ 0)
    {f f' : ℝ → FinitePath Ω n → ℝ} {f'' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' u x) u)
    (hf' : ∀ x, HasDerivAt (fun t => f' t x) (f'' x) u) :
    HasDerivAt (fun t => (law n (tilt n T m (f t))).expect (f' t))
      ((law n (tilt n T m (f u))).expect f'' +
        varianceEnergy n (tilt n T m (f u)) m (f' u)) u := by
  induction n with
  | zero =>
    simp_rw [law_zero_expect (Ω := Ω)]
    simpa only [varianceEnergy, add_zero] using hf' ()
  | succ n ih =>
    have hfirst := fun x => hasDerivAt_backwardLog n (T.2 x)
      (fun j => m j.succ) (fun j => hm j.succ) (fun y => hf (x,y))
    have hsecond := fun x => ih (T.2 x) (fun j => m j.succ)
      (fun j => hm j.succ) (fun y => hf (x,y)) (fun y => hf' (x,y))
    have hd := T.1.hasDerivAt_tilt_expect hfirst hsecond (m := m 0)
    simp_rw [law_succ_expect (Ω := Ω) n]
    simpa only [tilt, backwardLog, varianceEnergy, FiniteLaw.expect_add, add_assoc, add_comm, add_left_comm] using hd

/-- Root-measurable homogeneous shifts pass through the whole backward recursion. -/
theorem backwardLog_add (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (f : FinitePath Ω n → ℝ) (c : ℝ) :
    backwardLog n T m (fun x => f x + c) = backwardLog n T m f + c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ)
        (fun y => f (x,y) + c)) =
        (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) + c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ) (fun y => f (x,y))
    rw [heq, FiniteLaw.logMean_add _ (hm 0)]

theorem backwardLog_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (c : ℝ) : backwardLog n T m (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun _ => c)) =
        (fun _ => c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
    rw [heq, FiniteLaw.logMean_const _ (hm 0)]

/-- The uniform insertion bound, with full arbitrary depth-dependent priors. -/
theorem backwardLog_stability (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f g : FinitePath Ω n → ℝ} {c : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ c) :
    |backwardLog n T m f - backwardLog n T m g| ≤ c := by
  induction n with
  | zero => exact hfg ()
  | succ n ih =>
    apply T.1.logMean_stability (hm 0)
    intro x
    exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ) (fun y => hfg (x,y))

/-- Pointwise bounds survive every backward step, uniformly in depth. -/
theorem backwardLog_bound (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f : FinitePath Ω n → ℝ} {c : ℝ}
    (hf : ∀ x, |f x| ≤ c) : |backwardLog n T m f| ≤ c := by
  have h := backwardLog_stability n T m hm (g := fun _ => 0)
    (fun x => by simpa only [sub_zero] using hf x)
  rwa [backwardLog_const n T m (fun i => ne_of_gt (hm i)), sub_zero] at h

/-- Updated kernels after an insertion agree with the successive tilting of
all the old tilted kernels. This is tree:updated-kernel at every depth. -/
theorem tilt_insertion (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (f a : FinitePath Ω n → ℝ) :
    tilt n (tilt n T m f) m a = tilt n T m (fun x => f x + a x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change (T.1.tilt (m 0) _).tilt (m 0) _ = T.1.tilt (m 0) _
      rw [FiniteLaw.tilt_insertion]
      congr 1
      funext x
      have h := insertion n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) (fun y => a (x,y))
      change _ + backwardLog n (tilt n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
        (fun j => m j.succ) (fun y => a (x,y)) = _
      linarith
    · funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) (fun y => a (x,y))

theorem continuousOn_backwardLog (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {S : Set ℝ} {f : ℝ → FinitePath Ω n → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S) :
    ContinuousOn (fun t => backwardLog n T m (f t)) S := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
    exact T.1.continuousOn_logMean (fun x => ih (T.2 x) (fun j => m j.succ)
      (fun y => hf (x,y))) (m 0)

theorem continuousOn_path_expect (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {S : Set ℝ} {f g : ℝ → FinitePath Ω n → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S)
    (hg : ∀ x, ContinuousOn (fun t => g t x) S) :
    ContinuousOn (fun t => (law n (tilt n T m (f t))).expect (g t)) S := by
  induction n with
  | zero => simpa only [law_zero_expect] using hg ()
  | succ n ih =>
    simp_rw [law_succ_expect (Ω := Ω) n]
    exact T.1.continuousOn_tilt_expect
      (fun x => continuousOn_backwardLog n (T.2 x) (fun j => m j.succ) (fun y => hf (x,y)))
      (fun x => ih (T.2 x) (fun j => m j.succ) (fun y => hf (x,y)) (fun y => hg (x,y))) (m 0)

theorem continuousOn_varianceEnergy_tilt (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {S : Set ℝ} {f g : ℝ → FinitePath Ω n → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S)
    (hg : ∀ x, ContinuousOn (fun t => g t x) S) :
    ContinuousOn (fun t => varianceEnergy n (tilt n T m (f t)) m (g t)) S := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
    have hF := fun x => continuousOn_backwardLog n (T.2 x) (fun j => m j.succ)
      (fun y => hf (x,y))
    have hG := fun x => continuousOn_path_expect n (T.2 x) (fun j => m j.succ)
      (fun y => hf (x,y)) (fun y => hg (x,y))
    exact (continuousOn_const.mul (T.1.continuousOn_tilt_covariance hF hG (m 0))).add
      (T.1.continuousOn_tilt_expect hF (fun x => ih (T.2 x) (fun j => m j.succ)
        (fun y => hf (x,y)) (fun y => hg (x,y))) (m 0))

 
theorem second_variation_lower (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {c C : ℝ} (hm : ∀ i, c ≤ m i) (f g h : FinitePath Ω n → ℝ)
    (hh : ∀ x, -C ≤ h x) :
    c * (law n (tilt n T m f)).covariance g g - C ≤
      (law n (tilt n T m f)).expect h + varianceEnergy n (tilt n T m f) m g := by
  have hv := varianceEnergy_lower n (tilt n T m f) m hm g
  have he := (law n (tilt n T m f)).expect_mono hh
  rw [FiniteLaw.expect_const] at he
  linarith

 
theorem thermal_variance_integral (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {a b c B C : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : ∀ i, c ≤ m i)
    {f g h : ℝ → FinitePath Ω n → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, ∀ x, HasDerivAt (fun t => f t x) (g u x) u)
    (hg : ∀ u ∈ Set.Icc a b, ∀ x, HasDerivAt (fun t => g t x) (h u x) u)
    (hh : ∀ x, ContinuousOn (fun u => h u x) (Set.Icc a b))
    (hbound : ∀ u ∈ Set.Icc a b, ∀ x, |g u x| ≤ B)
    (hcurv : ∀ u ∈ Set.Icc a b, ∀ x, -C ≤ h u x) :
    (∫ u in a..b, (law n (tilt n T m (f u))).covariance (g u) (g u)) ≤
      (2*B + C*(b-a))/c := by
  let D := fun u => (law n (tilt n T m (f u))).expect (g u)
  let V := fun u => (law n (tilt n T m (f u))).covariance (g u) (g u)
  let E := fun u => (law n (tilt n T m (f u))).expect (h u) +
    varianceEnergy n (tilt n T m (f u)) m (g u)
  have hm' : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hc.trans_le (hm i))
  have hfc : ∀ x, ContinuousOn (fun u => f u x) (Set.Icc a b) :=
    fun x u hu => (hf u hu x).continuousAt.continuousWithinAt
  have hgc : ∀ x, ContinuousOn (fun u => g u x) (Set.Icc a b) :=
    fun x u hu => (hg u hu x).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Set.Icc a b) := continuousOn_path_expect n T m hfc hgc
  have hVc : ContinuousOn V (Set.Icc a b) := by
    unfold V FiniteLaw.covariance
    exact (continuousOn_path_expect n T m hfc (fun x => (hgc x).mul (hgc x))).sub (hDc.mul hDc)
  have hEc : ContinuousOn E (Set.Icc a b) :=
    (continuousOn_path_expect n T m hfc hh).add (continuousOn_varianceEnergy_tilt n T m hfc hgc)
  have hVi : IntervalIntegrable V MeasureTheory.volume a b :=
    hVc.intervalIntegrable_of_Icc hab
  have hEi : IntervalIntegrable E MeasureTheory.volume a b :=
    hEc.intervalIntegrable_of_Icc hab
  have hd : ∀ u ∈ Set.uIcc a b, HasDerivAt D (E u) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact hasDerivAt_path_score n T m hm' (hf u hu) (hg u hu)
  have hEq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hEi
  have hmono := intervalIntegral.integral_mono_on hab
    ((hVi.const_mul c).sub intervalIntegrable_const) hEi
    (fun u hu => second_variation_lower n T m hm (f u) (g u) (h u) (hcurv u hu))
  rw [intervalIntegral.integral_sub (hVi.const_mul c) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, hEq] at hmono
  have hDa : |D a| ≤ B := (law n (tilt n T m (f a))).abs_expect_le (hbound a ⟨le_rfl,hab⟩)
  have hDb : |D b| ≤ B := (law n (tilt n T m (f b))).abs_expect_le (hbound b ⟨hab,le_rfl⟩)
  apply (le_div_iff₀ hc).mpr
  change (∫ u in a..b, V u) * c ≤ _
  simp only [smul_eq_mul] at hmono
  linarith [(abs_le.mp hDa).1, (abs_le.mp hDb).2]

end KernelTower
end DilutedSpinGlass

end

end OAI
