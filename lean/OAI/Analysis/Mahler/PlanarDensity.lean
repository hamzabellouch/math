import OAI.Analysis.Mahler.ActualVerticalPrimitive
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The vertical primitive density, written with squared norms
so smoothness at the zero is explicit for integral m. -/
noncomputable def planarDensity (m : ℕ) (u : ℂ) : ℝ :=
  (4*(m : ℝ)/Real.pi)*Complex.normSq (MahlerConformal.inverseF u)^(m-1)*
    Complex.normSq (deriv MahlerConformal.inverseF u)

lemma contDiffAt_normSq_comp {f : ℂ → ℂ} {u : ℂ}
    (hf : ContDiffAt ℝ ∞ f u) : ContDiffAt ℝ ∞ (fun z => Complex.normSq (f z)) u := by
  have hre := Complex.reCLM.contDiff.contDiffAt.comp u hf
  have him := Complex.imCLM.contDiff.contDiffAt.comp u hf
  convert (hre.mul hre).add (him.mul him) using 1 ; rfl

/-- Smoothness of the actual vertical density, including at the origin. -/
theorem contDiffAt_planarDensity (m : ℕ) {u : ℂ} (hu : u ∈ MahlerConformal.Omega) :
    ContDiffAt ℝ ∞ (planarDensity m) u := by
  have hA := MahlerConformal.differentiableOn_inverseF.analyticAt
    (MahlerConformal.isOpen_Omega.mem_nhds hu)
  have hh : ContDiffAt ℝ ∞ MahlerConformal.inverseF u := hA.contDiffAt.restrict_scalars ℝ
  have hhd : ContDiffAt ℝ ∞ (deriv MahlerConformal.inverseF) u := hA.deriv.contDiffAt.restrict_scalars ℝ
  exact (contDiffAt_const.mul ((contDiffAt_normSq_comp hh).pow (m-1))).mul
    (contDiffAt_normSq_comp hhd)

lemma planarDensity_nonneg (m : ℕ) (u : ℂ) : 0 ≤ planarDensity m u := by
  have hh := Complex.normSq_nonneg (MahlerConformal.inverseF u)
  have hd := Complex.normSq_nonneg (deriv MahlerConformal.inverseF u)
  unfold planarDensity
  positivity

lemma planarDensity_pos {m : ℕ} (hm : 0 < m) {u : ℂ}
    (hu : u ∈ MahlerConformal.Omega) (hu0 : u ≠ 0) : 0 < planarDensity m u := by
  have hh : 0 < Complex.normSq (MahlerConformal.inverseF u) :=
    Complex.normSq_pos.mpr (fun h => hu0 ((MahlerConformal.inverseF_eq_zero_iff hu).mp h))
  have hhd : 0 < Complex.normSq (deriv MahlerConformal.inverseF u) :=
    Complex.normSq_pos.mpr (MahlerConformal.inverseF_deriv_ne_zero hu)
  unfold planarDensity
  positivity

/-- The original vertical integral, before its equality with the radial integral. -/
noncomputable def planarPrimitive (m : ℕ) (q t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)

lemma continuousAt_planarDensity_vertical (m : ℕ) {q t : ℝ}
    (hu : (q : ℂ)+(t : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    ContinuousAt (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) t := by
  have hl : ContinuousAt (fun s : ℝ => (q : ℂ)+(s : ℂ)*Complex.I) t := by fun_prop
  have hd := (contDiffAt_planarDensity m hu).continuousAt
  have hc := hd.comp (f := fun s : ℝ => (q : ℂ)+(s : ℂ)*Complex.I) hl
  exact hc

/-- The fundamental theorem yields the vertical derivative whenever
the segment from zero lies in Omega.
Segment containment is an explicit geometric premise. -/
theorem hasDerivAt_planarPrimitive (m : ℕ) {q t : ℝ}
    (hseg : ∀ s ∈ uIcc (0 : ℝ) t, (q : ℂ)+(s : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    HasDerivAt (planarPrimitive m q) (planarDensity m ((q : ℂ)+(t : ℂ)*Complex.I)) t := by
  have hi : IntervalIntegrable (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    exact (continuousAt_planarDensity_vertical m (hseg s hs)).continuousWithinAt
  have hopen : IsOpen {s : ℝ | (q : ℂ)+(s : ℂ)*Complex.I ∈ MahlerConformal.Omega} :=
    MahlerConformal.isOpen_Omega.preimage
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hmeas := ContinuousAt.stronglyMeasurableAtFilter (μ := volume) hopen
    (fun s hs => continuousAt_planarDensity_vertical m hs) t (hseg t (right_mem_uIcc))
  exact intervalIntegral.integral_hasDerivAt_right hi hmeas
    (continuousAt_planarDensity_vertical m (hseg t (right_mem_uIcc)))

/-- The polynomial expression equals the norm-power density. -/
theorem planarDensity_eq (m : ℕ) (hm : 1 ≤ m) (u : ℂ) :
    planarDensity m u = (4*(m : ℝ)/Real.pi)*
      ‖MahlerConformal.inverseF u‖^(2*(m : ℝ)-2 : ℝ)*
      ‖deriv MahlerConformal.inverseF u‖^2 := by
  have he : ((2*(m-1) : ℕ) : ℝ) = 2*(m : ℝ)-2 := by
    rw [Nat.cast_mul, Nat.cast_sub hm]
    norm_num
    ; ring
  have hp : ‖MahlerConformal.inverseF u‖^(2*(m-1) : ℕ) =
      ‖MahlerConformal.inverseF u‖^(2*(m : ℝ)-2 : ℝ) := by
    rw [← Real.rpow_natCast, he]
  unfold planarDensity
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ← pow_mul, hp]

/-- Both the radial inverse-coordinate primitive and the original vertical
integral have the same density on each upper fiber. -/
theorem hasDerivAt_actual_primitive_density {q r₀ r : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    HasDerivAt (fun t => radialPrimitive q r₀ (m : ℝ) (verticalRadius q t))
      (planarDensity m ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I)) (fiberHeight q r) := by
  rw [planarDensity_eq m (by omega)]
  exact actual_vertical_primitive_derivative (by exact_mod_cast hm) hr₀ hq hr

lemma planarPrimitive_zero (m : ℕ) (q : ℝ) : planarPrimitive m q 0 = 0 := by
  simp [planarPrimitive]

lemma planarPrimitive_nonneg (m : ℕ) (q : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ planarPrimitive m q t :=
  intervalIntegral.integral_nonneg_of_forall ht (fun _s => planarDensity_nonneg m _)

/-- Positivity away from the single zero is sufficient for strict increase on
an entire vertical interval, including intervals crossing the origin. -/
theorem strictMonoOn_planarPrimitive {m : ℕ} (hm : 0 < m) {q l u : ℝ}
    (hl : l < 0) (hu : 0 < u)
    (hOmega : ∀ t ∈ Ioo l u, (q : ℂ)+(t : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    StrictMonoOn (planarPrimitive m q) (Ioo l u) := by
  have hcont : ∀ a b : ℝ, a ∈ Ioo l u → b ∈ Ioo l u →
      ContinuousOn (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) (uIcc a b) := by
    intro a b ha hb s hs
    have hmem : s ∈ Ioo l u := by
      rcases le_total a b with hab | hba
      · rw [uIcc_of_le hab] at hs
        exact ⟨ha.1.trans_le hs.1,hs.2.trans_lt hb.2⟩
      · rw [uIcc_of_ge hba] at hs
        exact ⟨hb.1.trans_le hs.1,hs.2.trans_lt ha.2⟩
    exact (continuousAt_planarDensity_vertical m (hOmega s hmem)).continuousWithinAt
  intro a ha b hb hab
  have h0 : (0 : ℝ) ∈ Ioo l u := ⟨hl,hu⟩
  have hia := (hcont 0 a h0 ha).intervalIntegrable (μ := volume)
  have hiab := (hcont a b ha hb).intervalIntegrable (μ := volume)
  have heq := intervalIntegral.integral_add_adjacent_intervals hia hiab
  have hpos : 0 < ∫ s in a..b, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I) := by
    apply intervalIntegral.integral_pos hab
    · simpa only [uIcc_of_le hab.le] using hcont a b ha hb
    · intro s _
      exact planarDensity_nonneg m _
    · by_cases ha0 : a = 0
      · refine ⟨b,⟨hab.le,le_rfl⟩,planarDensity_pos hm (hOmega b hb) ?_⟩
        intro hz
        have him := congrArg Complex.im hz
        simp at him
        linarith
      · refine ⟨a,⟨le_rfl,hab.le⟩,planarDensity_pos hm (hOmega a ha) ?_⟩
        intro hz
        have him := congrArg Complex.im hz
        simp at him
        exact ha0 him
  change (∫ s in (0 : ℝ)..a, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) <
    ∫ s in (0 : ℝ)..b, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)
  linarith

end SymmetricMahler

end OAI
