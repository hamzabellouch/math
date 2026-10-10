import OAI.Probability.DilutedSpin.PoissonVariance

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

/-- Actual log weight after a finite family of perturbations of one type.
The base includes the physical Hamiltonian and every other fixed type. -/
noncomputable def perturbLog {L n : ℕ} (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) (y : FinitePath Ω L) : ℝ :=
  base y + ∑ q, Real.log (1+t*D q y+u*E q y)

noncomputable def perturbScore {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (t u : ℝ) (y : FinitePath Ω L) : ℝ :=
  ∑ q, E q y / (1+t*D q y+u*E q y)

noncomputable def perturbCurvature {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (t u : ℝ) (y : FinitePath Ω L) : ℝ :=
  -∑ q, (E q y / (1+t*D q y+u*E q y))^2

omit [Fintype Ω] in
theorem perturb_factor_lower {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (q : Fin n) (y : FinitePath Ω L) :
    (1:ℝ)/2 ≤ 1+t*D q y+u*E q y := by
  have ht' := mul_le_mul_of_nonneg_left (hD q y) (abs_nonneg t)
  have hu' := mul_le_mul_of_nonneg_left (hE q y) (abs_nonneg u)
  rw [← abs_mul, mul_one] at ht' hu'
  linarith [(abs_le.mp (ht'.trans ht)).1, (abs_le.mp (hu'.trans hu)).1]

omit [Fintype Ω] in
theorem hasDerivAt_perturbLog {L n : ℕ} (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) (y : FinitePath Ω L)
    (hp : ∀ q, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (fun v => perturbLog base D E t v y) (perturbScore D E t u y) u := by
  have hh (q : Fin n) := (((hasDerivAt_id u).mul_const (E q y)).const_add
    (1+t*D q y)).log (ne_of_gt (hp q))
  simpa only [perturbLog, perturbScore, id_eq, one_mul] using
    (HasDerivAt.fun_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) => hh q)).const_add (base y)

omit [Fintype Ω] in
theorem hasDerivAt_perturbScore {L n : ℕ}
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) (y : FinitePath Ω L)
    (hp : ∀ q, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (fun v => perturbScore D E t v y) (perturbCurvature D E t u y) u := by
  have hh (q : Fin n) := (hasDerivAt_const u (E q y)).div
    (((hasDerivAt_id u).mul_const (E q y)).const_add (1+t*D q y)) (ne_of_gt (hp q))
  have hsum := HasDerivAt.fun_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) => hh q)
  change HasDerivAt (fun v => perturbScore D E t v y) _ u at hsum
  apply hsum.congr_deriv
  simp only [id_eq, one_mul, perturbCurvature, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  simp only [div_pow]
  ring

omit [Fintype Ω] in
theorem perturb_fraction_bound {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (q : Fin n) (y : FinitePath Ω L) :
    |E q y / (1+t*D q y+u*E q y)| ≤ 2 := by
  have hb := perturb_factor_lower D E hD hE ht hu q y
  have hp : 0 < 1+t*D q y+u*E q y := by linarith
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
  linarith [hE q y]

omit [Fintype Ω] in
theorem perturbScore_bound {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (y : FinitePath Ω L) :
    |perturbScore D E t u y| ≤ 2*n := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ q, |E q y / (1+t*D q y+u*E q y)|) ≤ ∑ _q : Fin n, (2:ℝ) :=
      Finset.sum_le_sum (fun q _ => perturb_fraction_bound D E hD hE ht hu q y)
    _ = _ := by simp [mul_comm]

omit [Fintype Ω] in
theorem perturbCurvature_bounds {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (y : FinitePath Ω L) :
    -4*n ≤ perturbCurvature D E t u y ∧ perturbCurvature D E t u y ≤ 0 := by
  have hsq (q : Fin n) : (E q y / (1+t*D q y+u*E q y))^2 ≤ 4 := by
    have hh := abs_le.mp (perturb_fraction_bound D E hD hE ht hu q y)
    nlinarith
  have hh := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) => hsq q)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  constructor
  · dsimp [perturbCurvature]
    linarith
  · exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

 
theorem perturb_thermal_variance {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t a b c : ℝ} (ht : |t| ≤ 1/4) (hab : a ≤ b) (hc : 0 < c)
    (hm : ∀ i, c ≤ m i) (hI : Set.Icc a b ⊆ Set.Icc (-(1:ℝ)/4) (1/4)) :
    (∫ u in a..b, (law L (tilt L T m (perturbLog base D E t u))).covariance
      (perturbScore D E t u) (perturbScore D E t u)) ≤
      (4*n + 4*n*(b-a))/c := by
  have huv (u : ℝ) (hu : u ∈ Set.Icc a b) : |u| ≤ 1/4 := abs_le.mpr ⟨by linarith [(hI hu).1], (hI hu).2⟩
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) (q : Fin n) (y : FinitePath Ω L) :
      0 < 1+t*D q y+u*E q y := by
    linarith [perturb_factor_lower D E hD hE ht (huv u hu) q y]
  have hh (y : FinitePath Ω L) :
      ContinuousOn (fun u => perturbCurvature D E t u y) (Set.Icc a b) := by
    apply ContinuousOn.neg
    apply continuousOn_finsetSum
    intro q _
    apply ContinuousOn.pow
    apply continuousOn_const.div
    · fun_prop
    · intro u hu
      exact ne_of_gt (hp u hu q y)
  have H := thermal_variance_integral L T m hab hc hm
    (fun u hu y => hasDerivAt_perturbLog base D E t u y (fun q => hp u hu q y))
    (fun u hu y => hasDerivAt_perturbScore D E t u y (fun q => hp u hu q y)) hh
    (fun u hu y => perturbScore_bound D E hD hE ht (huv u hu) y)
    (C := 4*n) (fun u hu y => by
      simpa only [neg_mul] using (perturbCurvature_bounds D E hD hE ht (huv u hu) y).1)
  convert H using 2
  ring

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

/-- The manuscript's random convex correction, still before any root
expectation is taken. -/
noncomputable def correctedPerturbLog {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) : ℝ :=
  backwardLog L T m (perturbLog base D E t u) + 2*n*u^2

noncomputable def correctedPerturbScore {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) : ℝ :=
  (law L (tilt L T m (perturbLog base D E t u))).expect (perturbScore D E t u) + 4*n*u

theorem hasDerivAt_correctedPerturbLog {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (hm : ∀ i, m i ≠ 0) (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ)
    (hp : ∀ q y, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (correctedPerturbLog T m base D E t)
      (correctedPerturbScore T m base D E t u) u := by
  have h1 := hasDerivAt_backwardLog L T m hm
    (fun y => hasDerivAt_perturbLog base D E t u y (fun q => hp q y))
  have h2 : HasDerivAt (fun v : ℝ => 2*(n:ℝ)*v^2) (4*n*u) u := by
    exact (((hasDerivAt_id u).pow 2).const_mul (2*(n:ℝ))).congr_deriv (by
      norm_num
      ring)
  have h3 := h1.add h2
  change HasDerivAt (fun v => backwardLog L T m (perturbLog base D E t v) + 2*n*v^2)
    ((law L (tilt L T m (perturbLog base D E t u))).expect (perturbScore D E t u) + 4*n*u) u
  exact h3

theorem hasDerivAt_correctedPerturbScore {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (hm : ∀ i, m i ≠ 0) (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ)
    (hp : ∀ q y, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (correctedPerturbScore T m base D E t)
      ((law L (tilt L T m (perturbLog base D E t u))).expect (perturbCurvature D E t u) +
        varianceEnergy L (tilt L T m (perturbLog base D E t u)) m (perturbScore D E t u) + 4*n) u := by
  have h1 := hasDerivAt_path_score L T m hm
    (fun y => hasDerivAt_perturbLog base D E t u y (fun q => hp q y))
    (fun y => hasDerivAt_perturbScore D E t u y (fun q => hp q y))
  have h2 : HasDerivAt (fun v : ℝ => 4*(n:ℝ)*v) (4*n) u := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul (4*(n:ℝ))
  change HasDerivAt (fun v =>
    (law L (tilt L T m (perturbLog base D E t v))).expect (perturbScore D E t v) + 4*n*v) _ u
  exact h1.add h2

 
theorem correctedPerturbLog_convex {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (hm : ∀ i, 0 < m i) (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t : ℝ} (ht : |t| ≤ 1/4) :
    ConvexOn ℝ (Set.Icc (-(1:ℝ)/4) (1/4)) (correctedPerturbLog T m base D E t) := by
  let J := Set.Icc (-(1:ℝ)/4) (1/4)
  have hu (u : ℝ) (h : u ∈ J) : |u| ≤ 1/4 := abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have hp (u : ℝ) (h : u ∈ J) (q : Fin n) (y : FinitePath Ω L) :
      0 < 1+t*D q y+u*E q y := by
    linarith [perturb_factor_lower D E hD hE ht (hu u h) q y]
  have h1 (u : ℝ) (h : u ∈ J) := hasDerivAt_correctedPerturbLog T m
    (fun i => ne_of_gt (hm i)) base D E t u (hp u h)
  have h2 (u : ℝ) (h : u ∈ J) := hasDerivAt_correctedPerturbScore T m
    (fun i => ne_of_gt (hm i)) base D E t u (hp u h)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun u h => (h1 u h).continuousAt.continuousWithinAt)
    (fun u h => (h1 u (interior_subset h)).hasDerivWithinAt)
    (fun u h => (h2 u (interior_subset h)).hasDerivWithinAt)
  intro u h
  have hb := (law L (tilt L T m (perturbLog base D E t u))).expect_mono
    (fun y => (perturbCurvature_bounds D E hD hE ht (hu u (interior_subset h)) y).1)
  rw [FiniteLaw.expect_const] at hb
  have hv := varianceEnergy_lower L (tilt L T m (perturbLog base D E t u)) m
    (c := 0) (fun i => (hm i).le) (perturbScore D E t u)
  simp only [zero_mul] at hv
  linarith

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.FiniteLaw
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_tilt_expect (P : FiniteLaw Ω) (m : ℝ) {f g : X → Ω → ℝ}
    (hf : ∀ a, Measurable (fun x => f x a))
    (hg : ∀ a, Measurable (fun x => g x a)) :
    Measurable (fun x => (P.tilt m (f x)).expect (g x)) := by
  simp_rw [tilt_expect]
  exact (P.measurable_expect (fun a => ((hf a).const_mul m).exp.mul (hg a))).div
    (P.measurable_expect (fun a => ((hf a).const_mul m).exp))

/-- Conditional absolute score fluctuations are controlled by their exact
conditional variance; all randomness is still in the tilted path law. -/
theorem mean_absolute_deviation_sq (P : FiniteLaw Ω) (f : Ω → ℝ) :
    (P.expect (fun x => |f x-P.expect f|))^2 ≤ P.covariance f f := by
  have h := P.sq_expect_le_expect_sq (fun x => |f x-P.expect f|)
  simp only [sq_abs] at h
  rw [P.expect_sq_sub_expect] at h
  simpa only [covariance,pow_two] using h

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_path_expect (L : ℕ) (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f g : X → FinitePath Ω L → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y))
    (hg : ∀ y, Measurable (fun x => g x y)) :
    Measurable (fun x => (law L (tilt L T m (f x))).expect (g x)) := by
  induction L with
  | zero => simpa only [law_zero_expect] using hg ()
  | succ L ih =>
    simp_rw [law_succ_expect (Ω := Ω) L]
    exact T.1.measurable_tilt_expect (m 0)
      (fun a => measurable_backwardLog L (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)))
      (fun a => ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)) (fun b => hg (a,b)))

omit [Fintype Ω] [MeasurableSpace X] in
theorem continuousOn_perturbLog {L n : ℕ} (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) {t : ℝ} {S : Set ℝ}
    (hp : ∀ u ∈ S, ∀ q y, 0 < 1+t*D q y+u*E q y) (y : FinitePath Ω L) :
    ContinuousOn (fun u => perturbLog base D E t u y) S := by
  apply ContinuousOn.const_add
  apply continuousOn_finsetSum
  intro q _
  apply ContinuousOn.log
  · fun_prop
  · intro u hu
    exact ne_of_gt (hp u hu q y)

omit [Fintype Ω] [MeasurableSpace X] in
theorem continuousOn_perturbScore {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    {t : ℝ} {S : Set ℝ} (hp : ∀ u ∈ S, ∀ q y, 0 < 1+t*D q y+u*E q y)
    (y : FinitePath Ω L) :
    ContinuousOn (fun u => perturbScore D E t u y) S := by
  apply continuousOn_finsetSum
  intro q _
  apply continuousOn_const.div
  · fun_prop
  · intro u hu
    exact ne_of_gt (hp u hu q y)

/-- The L1 thermal defect for the literal score of all selected marks. -/
noncomputable def thermalDefect {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) : ℝ :=
  let P := law L (tilt L T m (perturbLog base D E t u))
  P.expect (fun y => |perturbScore D E t u y-P.expect (perturbScore D E t u)|)

omit [MeasurableSpace X] in
theorem thermalDefect_nonneg {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) :
    0 ≤ thermalDefect T m base D E t u :=
  FiniteLaw.expect_nonneg _ (fun _ => abs_nonneg _)

omit [MeasurableSpace X] in
theorem continuousOn_thermalDefect {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ) {t : ℝ} {S : Set ℝ}
    (hp : ∀ u ∈ S, ∀ q y, 0 < 1+t*D q y+u*E q y) :
    ContinuousOn (thermalDefect T m base D E t) S := by
  apply continuousOn_path_expect
  · exact continuousOn_perturbLog base D E hp
  · intro y
    exact ((continuousOn_perturbScore D E hp y).sub
      (continuousOn_path_expect L T m (continuousOn_perturbLog base D E hp)
        (continuousOn_perturbScore D E hp))).abs

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

omit [Fintype Ω] in
theorem measurable_perturbLog {L n : ℕ}
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u)
    (y : FinitePath Ω L) :
    Measurable (fun x => perturbLog (base x) (D x) (E x) (t x) (u x) y) := by
  apply (hbase y).add
  apply Finset.measurable_sum
  intro q _
  exact ((measurable_const.add (ht.mul (hD q y))).add (hu.mul (hE q y))).log

omit [Fintype Ω] in
theorem measurable_perturbScore {L n : ℕ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u)
    (y : FinitePath Ω L) :
    Measurable (fun x => perturbScore (D x) (E x) (t x) (u x) y) := by
  apply Finset.measurable_sum
  intro q _
  exact (hE q y).div ((measurable_const.add (ht.mul (hD q y))).add (hu.mul (hE q y)))

theorem measurable_thermalDefect {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u) :
    Measurable (fun x => thermalDefect T m (base x) (D x) (E x) (t x) (u x)) := by
  apply measurable_path_expect
  · exact measurable_perturbLog hbase hD hE ht hu
  · intro y
    exact ((measurable_perturbScore hD hE ht hu y).sub
      (measurable_path_expect L T m (measurable_perturbLog hbase hD hE ht hu)
        (measurable_perturbScore hD hE ht hu))).abs

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass
open MeasureTheory intervalIntegral

theorem sq_intervalIntegral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∫ u in a..b, f u)^2 ≤ (b-a)*(∫ u in a..b, (f u)^2) := by
  let l := b-a
  let z := ∫ u in a..b, f u
  have hl : 0 < l := sub_pos.mpr hab
  have hi : IntervalIntegrable f volume a b :=
    hf.intervalIntegrable_of_Icc (le_of_lt hab)
  have hi2 : IntervalIntegrable (fun u => (f u)^2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc (le_of_lt hab)
  have hprint (u : ℝ) : (f u-z/l)^2 = (f u)^2-2*(z/l)*f u+(z/l)^2 := by ring
  have h := integral_nonneg (μ := volume) (le_of_lt hab)
    (f := fun u => (f u-z/l)^2) (fun u _ => sq_nonneg _)
  simp_rw [hprint] at h
  rw [integral_add (hi2.sub (hi.const_mul (2*(z/l)))) intervalIntegrable_const,
    integral_sub hi2 (hi.const_mul (2*(z/l))),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,smul_eq_mul] at h
  change 0 ≤ (∫ u in a..b, (f u)^2)-2*(z/l)*z+l*(z/l)^2 at h
  have heq : (∫ u in a..b, (f u)^2)-2*(z/l)*z+l*(z/l)^2 =
      (∫ u in a..b, (f u)^2)-z^2/l := by
    field_simp [ne_of_gt hl]
    ring
  rw [heq] at h
  have hh : z^2/l ≤ ∫ u in a..b, (f u)^2 := by linarith
  have hh' := (div_le_iff₀ hl).mp hh
  change z^2 ≤ l*(∫ u in a..b, (f u)^2)
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass.KernelTower
open MeasureTheory intervalIntegral
variable {Ω : Type} [Fintype Ω]

 
theorem perturb_thermal_absolute {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t a b c : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hc : 0 < c)
    (hm : ∀ i, c ≤ m i) (hI : Set.Icc a b ⊆ Set.Icc (-(1:ℝ)/4) (1/4)) :
    (∫ u in a..b, thermalDefect T m base D E t u)^2 ≤
      (b-a)*(4*n+4*n*(b-a))/c := by
  have huv (u : ℝ) (hu : u ∈ Set.Icc a b) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI hu).1],(hI hu).2⟩
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) (q : Fin n) (y : FinitePath Ω L) :
      0 < 1+t*D q y+u*E q y := by
    linarith [perturb_factor_lower D E hD hE ht (huv u hu) q y]
  have hf := continuousOn_perturbLog base D E hp
  have hg := continuousOn_perturbScore D E hp
  have hd := continuousOn_thermalDefect T m base D E hp
  have hcov : ContinuousOn
      (fun u => (law L (tilt L T m (perturbLog base D E t u))).covariance
        (perturbScore D E t u) (perturbScore D E t u)) (Set.Icc a b) := by
    unfold FiniteLaw.covariance
    exact (continuousOn_path_expect L T m hf (fun y => (hg y).mul (hg y))).sub
      ((continuousOn_path_expect L T m hf hg).mul (continuousOn_path_expect L T m hf hg))
  have hb := integral_mono_on (μ := volume) (le_of_lt hab)
    ((hd.pow 2).intervalIntegrable_of_Icc (le_of_lt hab))
    (hcov.intervalIntegrable_of_Icc (le_of_lt hab))
    (fun u _ => (law L (tilt L T m (perturbLog base D E t u))).mean_absolute_deviation_sq
      (perturbScore D E t u))
  have h1 := sq_intervalIntegral_le hab hd
  have h2 := perturb_thermal_variance T m base D E hD hE ht (le_of_lt hab) hc hm hI
  have h3 := mul_le_mul_of_nonneg_left (hb.trans h2) (by linarith : 0 ≤ b-a)
  dsimp only [thermalDefect] at h1 ⊢
  calc
    _ ≤ _ := h1
    _ ≤ _ := by simpa only [mul_div_assoc,Pi.pow_apply,thermalDefect] using h3

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

 
theorem poisson_family_average_sq {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)
    (F : ∀ n, X n → ℝ) (hF : ∀ n, Measurable (F n)) {K : ℝ}
    (hK : ∀ n x, (F n x)^2 ≤ K*(n : ℝ)) :
    (∫ n : ℕ, ∫ x, F n x ∂ν n ∂poissonMeasure r)^2 ≤ K*(r : ℝ) := by
  let G (n : ℕ) := ∫ x, F n x ∂ν n
  have hLp (n : ℕ) : MemLp (F n) 2 (ν n) :=
    bounded_memLp (hF n) (fun x => Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hK n x)) 2
  have hg (n : ℕ) : (G n)^2 ≤ K*(n : ℝ) := by
    have hv := variance_nonneg (F n) (ν n)
    rw [variance_eq_sub (hLp n)] at hv
    have hsq := integral_mono (hLp n).integrable_sq (integrable_const (K*(n : ℝ))) (hK n)
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hsq
    change 0 ≤ (∫ x, (F n x)^2 ∂ν n)-(G n)^2 at hv
    linarith
  have hi : Integrable (fun n => (G n)^2) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 0) (B := K)
    intro n
    simpa only [abs_sq,zero_add] using hg n
  have hGLp : MemLp G 2 (poissonMeasure r) :=
    (memLp_two_iff_integrable_sq StronglyMeasurable.of_discrete.aestronglyMeasurable).mpr hi
  have hv := variance_nonneg G (poissonMeasure r)
  rw [variance_eq_sub hGLp] at hv
  have hh := integral_mono hi ((poisson_integrable_count r).const_mul K) hg
  rw [integral_const_mul,poisson_mean] at hh
  change (∫ n, G n ∂poissonMeasure r)^2 ≤ K*(r : ℝ)
  simp only [Pi.pow_apply] at hv
  linarith

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The actual thermal estimate after both independent root averaging and
Poisson averaging, allowing the whole mark alphabet/tower to depend on the
count. -/
theorem poisson_thermal_absolute
    {X Ω : ℕ → Type} [∀ n, MeasurableSpace (X n)] [∀ n, Fintype (Ω n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)
    (L : ℕ) (T : ∀ n, KernelTower (Ω n) L) (m : Fin L → ℝ)
    (base : ∀ n, X n → FinitePath (Ω n) L → ℝ)
    (D E : ∀ n, X n → Fin n → FinitePath (Ω n) L → ℝ)
    (hb : ∀ n y, Measurable (fun x => base n x y))
    (hD : ∀ n q y, Measurable (fun x => D n x q y))
    (hE : ∀ n q y, Measurable (fun x => E n x q y))
    (hDb : ∀ n x q y, |D n x q y| ≤ 1)
    (hEb : ∀ n x q y, |E n x q y| ≤ 1)
    {t a b c : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hc : 0 < c)
    (hm : ∀ i, c ≤ m i) (hI : Set.Icc a b ⊆ Set.Icc (-(1:ℝ)/4) (1/4)) :
    (∫ n : ℕ, ∫ x, (∫ u in a..b,
      KernelTower.thermalDefect (T n) m (base n x) (D n x) (E n x) t u)
      ∂ν n ∂poissonMeasure r)^2 ≤ (b-a)*(4+4*(b-a))/c * (r : ℝ) := by
  apply poisson_family_average_sq
  · intro n
    have hj : Measurable (fun z : X n × ℝ =>
        KernelTower.thermalDefect (T n) m (base n z.1) (D n z.1) (E n z.1) t z.2) :=
      KernelTower.measurable_thermalDefect (T n) m
        (fun y => (hb n y).comp measurable_fst)
        (fun q y => (hD n q y).comp measurable_fst)
        (fun q y => (hE n q y).comp measurable_fst) measurable_const measurable_snd
    simp_rw [intervalIntegral.integral_of_le hab.le]
    exact (hj.stronglyMeasurable.integral_prod_right').measurable
  · intro n x
    have hh := KernelTower.perturb_thermal_absolute (T n) m (base n x) (D n x) (E n x)
      (hDb n x) (hEb n x) ht hab hc hm hI
    convert hh using 1; ring

end DilutedSpinGlass

end

end OAI
