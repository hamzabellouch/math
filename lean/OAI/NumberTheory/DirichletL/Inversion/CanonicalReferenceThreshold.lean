import OAI.NumberTheory.DirichletL.Foundation

namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap ContDiff

namespace SevenEighths.InverseMoment

theorem exists_canonical_reference_cutoff (lo hi : ℝ) :
    ∃ Vlog : SchwartzMap ℝ ℂ, ∃ Alog : ℝ, 0 < Alog ∧
      Alog = CanonicalCubeSeparation.columnWindowRadius lo hi + 1 ∧
      HasCompactSupport Vlog ∧
      tsupport Vlog ⊆ Set.Icc (-Alog) Alog ∧
      (∀ x, Vlog x ≠ 0 → |x| ≤ Alog) ∧
      (∀ x, |x| ≤ CanonicalCubeSeparation.columnWindowRadius lo hi → Vlog x = 1) ∧
      Vlog 0 = 1 := by
  obtain ⟨v, hvc, hvs, hvone, hvbox, hvzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff
      (CanonicalCubeSeparation.columnWindowRadius lo hi)
      (CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi)
  let Vlog : SchwartzMap ℝ ℂ := hvc.toSchwartzMap hvs
  refine ⟨Vlog, CanonicalCubeSeparation.columnWindowRadius lo hi + 1,
    by linarith [CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi],
    rfl, hvc, hvbox, ?_, hvone, hvzero⟩
  intro x hx
  exact abs_le.mpr (hvbox (subset_tsupport v hx))

theorem eventually_canonical_reference_gates (hi Alog window eta : ℝ)
    (heta : 0 < eta) :
    ∃ Z0 : ℝ, 1 < Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
      1 ≤ eta * Real.log Z ∧ hi ≤ Z ^ eta ∧
      Real.exp Alog ≤ Z ^ eta ∧ Real.exp window ≤ Z ^ eta := by
  let R : ℝ := 2 + |hi| + |Alog| + |window|
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg hi, abs_nonneg Alog, abs_nonneg window]
  refine ⟨2 + Real.exp (R / eta), by linarith [Real.exp_pos (R / eta)], ?_⟩
  intro Z hZ
  have hZtwo : 2 ≤ Z := by linarith [Real.exp_pos (R / eta)]
  have hZpos : 0 < Z := by linarith
  have hZexp : Real.exp (R / eta) ≤ Z := by linarith
  have hlog := Real.log_le_log (Real.exp_pos (R / eta)) hZexp
  rw [Real.log_exp] at hlog
  have hRlog : R ≤ Real.log Z * eta := (div_le_iff₀ heta).mp hlog
  have hpow : Real.exp R ≤ Z ^ eta := by
    rw [Real.rpow_def_of_pos hZpos]
    exact Real.exp_le_exp.mpr hRlog
  have hexp : Real.exp 1 ≤ Z ^ eta :=
    (Real.exp_le_exp.mpr hR).trans hpow
  refine ⟨hZtwo, (by linarith [Real.add_one_le_exp (1 : ℝ)] : 2 ≤ Real.exp 1).trans
    hexp, hexp, by nlinarith, ?_, ?_, ?_⟩
  · have hhi : hi ≤ R := by
      dsimp [R]
      linarith [le_abs_self hi, abs_nonneg Alog, abs_nonneg window]
    exact hhi.trans ((by linarith [Real.add_one_le_exp R] : R ≤ Real.exp R).trans hpow)
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    dsimp [R]
    linarith [le_abs_self Alog, abs_nonneg hi, abs_nonneg window]
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    dsimp [R]
    linarith [le_abs_self window, abs_nonneg hi, abs_nonneg Alog]

theorem canonical_reference_pool_coverage (hi B Z N L D : ℝ)
    (hB : 0 ≤ B) (hhi : hi ≤ B) (hZ : 1 ≤ Z) (hNL : N ≤ L)
    (hD : B * Z ^ L ≤ D) : hi * Z ^ N ≤ D := by
  calc
    hi * Z ^ N ≤ B * Z ^ N :=
      mul_le_mul_of_nonneg_right hhi (Real.rpow_nonneg (by linarith) _)
    _ ≤ B * Z ^ L :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hNL) hB
    _ ≤ D := hD

theorem exists_canonical_reference_family_gates {ι : Type*} (s : Finset ι)
    (hi Alog window : ι → ℝ) (eta : ℝ) (heta : 0 < eta) :
    ∃ B : ℝ, 0 < B ∧ ∃ Z0 : ℝ, 1 < Z0 ∧
      (∀ i ∈ s, hi i ≤ B ∧ Real.exp (Alog i) ≤ B ∧ Real.exp (window i) ≤ B) ∧
      ∀ Z : ℝ, Z0 ≤ Z →
        2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
        1 ≤ eta * Real.log Z ∧ B ≤ Z ^ eta ∧
        (∀ i ∈ s, hi i ≤ Z ^ eta ∧ Real.exp (Alog i) ≤ Z ^ eta ∧
          Real.exp (window i) ≤ Z ^ eta) ∧
        (∀ i ∈ s, ∀ N L D : ℝ, N ≤ L → B * Z ^ L ≤ D → hi i * Z ^ N ≤ D) := by
  let mass : ι → ℝ := fun i => |hi i| + Real.exp (Alog i) + Real.exp (window i)
  have hm : ∀ i, 0 ≤ mass i := by intro i; dsimp [mass]; positivity
  let B : ℝ := 1 + ∑ i ∈ s, mass i
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound : ∀ i ∈ s, hi i ≤ B ∧ Real.exp (Alog i) ≤ B ∧
      Real.exp (window i) ≤ B := by
    intro i hiS
    have hsum : mass i ≤ ∑ j ∈ s, mass j := Finset.single_le_sum (fun j _ => hm j) hiS
    dsimp [mass, B] at *
    constructor
    · linarith [le_abs_self (hi i), Real.exp_pos (Alog i), Real.exp_pos (window i)]
    constructor
    · linarith [abs_nonneg (hi i), Real.exp_pos (window i)]
    · linarith [abs_nonneg (hi i), Real.exp_pos (Alog i)]
  obtain ⟨Z0, hZ0, hgate⟩ := eventually_canonical_reference_gates B 0 0 eta heta
  refine ⟨B, hB, Z0, hZ0, hbound, ?_⟩
  intro Z hZ
  obtain ⟨hZtwo, htwo, hexp, hlog, hBpow, _, _⟩ := hgate Z hZ
  refine ⟨hZtwo, htwo, hexp, hlog, hBpow, ?_, ?_⟩
  · intro i hiS
    obtain ⟨hhi, hA, hw⟩ := hbound i hiS
    exact ⟨hhi.trans hBpow, hA.trans hBpow, hw.trans hBpow⟩
  · intro i hiS N L D hNL hD
    exact canonical_reference_pool_coverage (hi i) B Z N L D hB.le
      (hbound i hiS).1 (by linarith) hNL hD

end SevenEighths.InverseMoment

end

end OAI
