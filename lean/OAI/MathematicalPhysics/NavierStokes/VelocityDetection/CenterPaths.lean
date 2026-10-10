import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TranslationGates

namespace OAI

noncomputable section
namespace VelocityDetection.CenterPaths
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open SmoothProfiles

def ramp (r : ℝ) : ℝ := step (2 * r - 1 / 2)

@[fun_prop] theorem contDiff_ramp : ContDiff ℝ ∞ ramp := by
  unfold ramp
  fun_prop

theorem ramp_nonneg (r : ℝ) : 0 ≤ ramp r := Real.smoothTransition.nonneg _

theorem ramp_le_one (r : ℝ) : ramp r ≤ 1 := Real.smoothTransition.le_one _

theorem ramp_zero {r : ℝ} (hr : r ≤ 1 / 4) : ramp r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem ramp_one {r : ℝ} (hr : 3 / 4 ≤ r) : ramp r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

def theta (a T : ℝ) (j : ℕ) (t : ℝ) : ℝ := ramp (3 * (t - a) / T - j)

def privateRow (S : ℝ) (k : ℕ) : ℝ := -((k : ℝ) + 2) * S

def center (a T S S' σ : ℝ) (k l : ℕ) (t : ℝ) : Coord 2 :=
  ![(1 - theta a T 1 t) * S * k + theta a T 1 t * S' * l,
    -(1 - theta a T 0 t) * S +
      (theta a T 0 t - theta a T 2 t) * privateRow S k + theta a T 2 t * σ * S']

@[fun_prop] theorem contDiff_theta (a T : ℝ) (j : ℕ) : ContDiff ℝ ∞ (theta a T j) := by
  unfold theta
  fun_prop

@[fun_prop] theorem contDiff_center (a T S S' σ : ℝ) (k l : ℕ) :
    ContDiff ℝ ∞ (center a T S S' σ k l) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [center] <;> fun_prop

theorem center_first_slot {a T S S' σ t : ℝ} (k l : ℕ)
    (ht : 3 * (t - a) / T ≤ 1) :
    center a T S S' σ k l t 0 = S * k := by
  have h1 : theta a T 1 t = 0 := ramp_zero (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
  simp [center, h1]

theorem center_second_slot {a T S S' σ t : ℝ} (k l : ℕ)
    (ht : 1 ≤ 3 * (t - a) / T) (ht' : 3 * (t - a) / T ≤ 2) :
    center a T S S' σ k l t 1 = privateRow S k := by
  have h0 : theta a T 0 t = 1 := ramp_one (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
  have h2 : theta a T 2 t = 0 := ramp_zero (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
  simp [center, h0, h2]

theorem center_third_slot {a T S S' σ t : ℝ} (k l : ℕ)
    (ht : 2 ≤ 3 * (t - a) / T) :
    center a T S S' σ k l t 0 = S' * l := by
  have h1 : theta a T 1 t = 1 := ramp_one (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
  simp [center, h1]

theorem nat_gap {k l : ℕ} (hkl : k ≠ l) : (1 : ℝ) ≤ |(k : ℝ) - l| := by
  rcases lt_or_gt_of_ne hkl with h | h
  · have h' : (k : ℝ) + 1 ≤ l := by exact_mod_cast Nat.succ_le_of_lt h
    exact le_abs.mpr (Or.inr (by linarith))
  · have h' : (l : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt h
    exact le_abs.mpr (Or.inl (by linarith))

theorem scaled_nat_gap {S : ℝ} (hS : 0 ≤ S) {k l : ℕ} (hkl : k ≠ l) :
    S ≤ |S * k - S * l| := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hS]
  simpa using mul_le_mul_of_nonneg_left (nat_gap hkl) hS

theorem separated {S S' : ℝ} (hS : 0 ≤ S) (hSS : S ≤ S')
    (a T σ τ t : ℝ) {k l k' l' : ℕ} (hkl : k ≠ l) (hkl' : k' ≠ l') :
    ∃ i : Fin 2, S ≤ |center a T S S' σ k k' t i - center a T S S' τ l l' t i| := by
  by_cases h1 : 3 * (t - a) / T ≤ 1
  · refine ⟨0, ?_⟩
    rw [center_first_slot k k' h1, center_first_slot l l' h1]
    exact scaled_nat_gap hS hkl
  · by_cases h2 : 3 * (t - a) / T ≤ 2
    · refine ⟨1, ?_⟩
      rw [center_second_slot k k' (by linarith) h2,
        center_second_slot l l' (by linarith) h2]
      have hrow : privateRow S k - privateRow S l = -(S * k - S * l) := by
        dsimp [privateRow]
        ring
      rw [hrow, abs_neg]
      exact scaled_nat_gap hS hkl
    · refine ⟨0, ?_⟩
      rw [center_third_slot k k' (by linarith), center_third_slot l l' (by linarith)]
      exact hSS.trans (scaled_nat_gap (hS.trans hSS) hkl')

theorem negative_height {S S' : ℝ} (hS : 0 ≤ S) (hSS : S ≤ S')
    (a T t : ℝ) (k l : ℕ) : center a T S S' (-1) k l t 1 ≤ -S := by
  have hrow : privateRow S k ≤ -S := by
    dsimp [privateRow]
    nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hθ (j : ℕ) : 0 ≤ theta a T j t ∧ theta a T j t ≤ 1 :=
    ⟨ramp_nonneg _, ramp_le_one _⟩
  by_cases h1 : 3 * (t - a) / T ≤ 1
  · have h2 : theta a T 2 t = 0 := ramp_zero (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
    simp [center, h2]
    have := mul_le_mul_of_nonneg_left hrow (hθ 0).1
    nlinarith
  · by_cases h2 : 3 * (t - a) / T ≤ 2
    · rw [center_second_slot k l (by linarith) h2]
      exact hrow
    · have h0 : theta a T 0 t = 1 := ramp_one (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
      simp [center, h0]
      have hw : 0 ≤ 1 - theta a T 2 t := by linarith [(hθ 2).2]
      have hp := mul_le_mul_of_nonneg_left hrow hw
      have hq := mul_le_mul_of_nonneg_left hSS (hθ 2).1
      nlinarith

theorem center_source_collar {a T S S' σ t : ℝ} (k l : ℕ)
    (ht : 3 * (t - a) / T ≤ 1 / 4) :
    center a T S S' σ k l t = ![S * k, -S] := by
  have h0 : theta a T 0 t = 0 := ramp_zero (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
  have h1 : theta a T 1 t = 0 := ramp_zero (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
  have h2 : theta a T 2 t = 0 := ramp_zero (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
  simp [center, h0, h1, h2]

theorem center_target_collar {a T S S' σ t : ℝ} (k l : ℕ)
    (ht : 11 / 4 ≤ 3 * (t - a) / T) :
    center a T S S' σ k l t = ![S' * l, σ * S'] := by
  have h0 : theta a T 0 t = 1 := ramp_one (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
  have h1 : theta a T 1 t = 1 := ramp_one (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
  have h2 : theta a T 2 t = 1 := ramp_one (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)
  simp [center, h0, h1, h2]

theorem center_start (a T S S' σ : ℝ) (k l : ℕ) :
    center a T S S' σ k l a = ![S * k, -S] :=
  center_source_collar k l (by simp)

theorem center_end {T : ℝ} (hT : 0 < T) (a S S' σ : ℝ) (k l : ℕ) :
    center a T S S' σ k l (a + T) = ![S' * l, σ * S'] := by
  apply center_target_collar
  have hT0 : T ≠ 0 := ne_of_gt hT
  field_simp
  linarith

@[fun_prop] theorem contDiff_velocity (a T S S' σ : ℝ) (k l : ℕ) :
    ContDiff ℝ ∞ (deriv (center a T S S' σ k l)) :=
  (contDiff_infty_iff_deriv.mp (contDiff_center a T S S' σ k l)).2

theorem velocity_source_collar {a T S S' σ t : ℝ} (k l : ℕ)
    (ht : 3 * (t - a) / T < 1 / 4) : deriv (center a T S S' σ k l) t = 0 := by
  have hev : ∀ᶠ s in 𝓝 t, 3 * (s - a) / T < 1 / 4 :=
    (isOpen_lt (f := fun s : ℝ => 3 * (s - a) / T) (by fun_prop) continuous_const).mem_nhds ht
  have heq : center a T S S' σ k l =ᶠ[𝓝 t] fun _ => ![S * k, -S] :=
    hev.mono (fun s hs => center_source_collar k l hs.le)
  rw [heq.deriv_eq]
  simp

theorem velocity_target_collar {a T S S' σ t : ℝ} (k l : ℕ)
    (ht : 11 / 4 < 3 * (t - a) / T) : deriv (center a T S S' σ k l) t = 0 := by
  have hev : ∀ᶠ s in 𝓝 t, 11 / 4 < 3 * (s - a) / T :=
    (isOpen_lt continuous_const (g := fun s : ℝ => 3 * (s - a) / T) (by fun_prop)).mem_nhds ht
  have heq : center a T S S' σ k l =ᶠ[𝓝 t] fun _ => ![S' * l, σ * S'] :=
    hev.mono (fun s hs => center_target_collar k l hs.le)
  rw [heq.deriv_eq]
  simp

def gate (R a T S S' σ : ℝ) (k l : ℕ) (t : ℝ) (X : Coord 2) : Coord 2 :=
  TranslationGates.field R (center a T S S' σ k l t)
    (deriv (center a T S S' σ k l) t) X

@[fun_prop] theorem contDiff_gate (R a T S S' σ : ℝ) (k l : ℕ) :
    ContDiff ℝ ∞ (uncurry (gate R a T S S' σ k l)) :=
  TranslationGates.contDiff_movingField R (contDiff_center a T S S' σ k l)
    (contDiff_velocity a T S S' σ k l)

theorem gate_divergence (R a T S S' σ : ℝ) (k l : ℕ) (t : ℝ) (X : Coord 2) :
    divergence (gate R a T S S' σ k l) t X = 0 := by
  simpa only [divergence, spatialD, gate] using
    TranslationGates.divergence_field R (center a T S S' σ k l t)
      (deriv (center a T S S' σ k l) t) X

theorem gate_zero_before {T : ℝ} (hT : 0 < T) (R a S S' σ : ℝ) (k l : ℕ)
    {t : ℝ} (ht : t ≤ a) (X : Coord 2) : gate R a T S S' σ k l t X = 0 := by
  unfold gate
  rw [velocity_source_collar k l, TranslationGates.field_zero_velocity]
  have hq : 3 * (t - a) / T ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hT.le
  linarith

theorem gate_zero_after {T : ℝ} (hT : 0 < T) (R a S S' σ : ℝ) (k l : ℕ)
    {t : ℝ} (ht : a + T ≤ t) (X : Coord 2) : gate R a T S S' σ k l t X = 0 := by
  unfold gate
  rw [velocity_target_collar k l, TranslationGates.field_zero_velocity]
  have hq : 3 ≤ 3 * (t - a) / T := (le_div_iff₀ hT).mpr (by linarith)
  linarith

theorem compactSupport_gate {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (a S S' σ : ℝ) (k l : ℕ) :
    HasCompactSupport (uncurry (gate R a T S S' σ k l)) := by
  let c := center a T S S' σ k l
  let F : ℝ × Coord 2 → ℝ × Coord 2 := fun q => (q.1, c q.1 + q.2)
  have hc : Continuous c := (contDiff_center a T S S' σ k l).continuous
  have hF : Continuous F := continuous_fst.prodMk ((hc.comp continuous_fst).add continuous_snd)
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc.prod (isCompact_Icc : IsCompact (Icc (fun _ : Fin 2 => -3 * R)
      (fun _ : Fin 2 => 3 * R)))).image hF)
  intro q hq
  have ht : q.1 ∈ Icc a (a + T) := by
    constructor
    · exact (lt_of_not_ge (fun h => hq (gate_zero_before hT R a S S' σ k l h q.2))).le
    · exact (lt_of_not_ge (fun h => hq (gate_zero_after hT R a S S' σ k l h q.2))).le
  have hi (i : Fin 2) : |q.2 i - c q.1 i| < 3 * R := by
    apply lt_of_not_ge
    intro h
    exact hq (TranslationGates.field_zero_outside hR _ _ _ ⟨i, h⟩)
  refine ⟨(q.1, q.2 - c q.1), ⟨ht, ?_⟩, ?_⟩
  · exact ⟨fun i => by dsimp; linarith [(abs_lt.mp (hi i)).1],
      fun i => by dsimp; linarith [(abs_lt.mp (hi i)).2]⟩
  · dsimp [F]
    congr 1
    abel

theorem gate_derivatives_bounded {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (a S S' σ : ℝ) (k l m : ℕ) :
    ∃ C : ℝ, ∀ q, ‖iteratedFDeriv ℝ m (uncurry (gate R a T S S' σ k l)) q‖ ≤ C := by
  apply ((compactSupport_gate hR hT a S S' σ k l).iteratedFDeriv m).exists_bound_of_continuous
  exact ((contDiff_infty.mp (contDiff_gate R a T S S' σ k l)) m).continuous_iteratedFDeriv le_rfl

end VelocityDetection.CenterPaths
end

end OAI
