import OAI.Analysis.FourierLLogL.Fourier.Interval
/-! # Delayed Haar shifts on real intervals -/

open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL.Period
noncomputable section

def box (a s : ℝ) := Ico a (a+s)

def haarH : ℝ → ℝ :=
  (Ico (0:ℝ) (1/2)).indicator (fun _ => 1) -
    (Ico (1/2:ℝ) 1).indicator (fun _ => 1)

def haarG (x : ℝ) := haarH (2*x) - haarH (2*x-1)

lemma measurableH : Measurable haarH :=
  (measurable_const.indicator measurableSet_Ico).sub (measurable_const.indicator measurableSet_Ico)

lemma measurableG : Measurable haarG :=
  (measurableH.comp (measurable_const.mul measurable_id)).sub
    (measurableH.comp ((measurable_const.mul measurable_id).sub measurable_const))

lemma H_of_left {x : ℝ} (hx : x ∈ Ico (0:ℝ) (1/2)) : haarH x = 1 := by
  have : x ∉ Ico (1/2:ℝ) 1 := fun h => (not_lt_of_ge h.1) hx.2
  rw [haarH, Pi.sub_apply, indicator_of_mem hx, indicator_of_notMem this, sub_zero]

lemma H_of_right {x : ℝ} (hx : x ∈ Ico (1/2:ℝ) 1) : haarH x = -1 := by
  have : x ∉ Ico (0:ℝ) (1/2) := fun h => (not_lt_of_ge hx.1) h.2
  rw [haarH, Pi.sub_apply, indicator_of_notMem this, indicator_of_mem hx, zero_sub]

lemma H_outside {x : ℝ} (hx : x ∉ unitInt) : haarH x = 0 := by
  have h1 : x ∉ Ico (0:ℝ) (1/2) := fun h => hx ⟨h.1,h.2.trans (by norm_num)⟩
  have h2 : x ∉ Ico (1/2:ℝ) 1 := fun h => hx ⟨le_trans (by norm_num : (0:ℝ)≤1/2) h.1,h.2⟩
  rw [haarH, Pi.sub_apply, indicator_of_notMem h1, indicator_of_notMem h2, sub_zero]

lemma H_bound (x : ℝ) : |haarH x| ≤ 1 := by
  by_cases hx : x ∈ unitInt
  · rcases lt_or_ge x (1/2) with h|h
    · rw [H_of_left ⟨hx.1,h⟩]; simp
    · rw [H_of_right ⟨h,hx.2⟩]; simp
  · simp [H_outside hx]

lemma G_outside {x : ℝ} (hx : x ∉ unitInt) : haarG x = 0 := by
  have h1 : 2*x ∉ unitInt := by
    rintro ⟨h1,h2⟩
    exact hx ⟨by linarith, by linarith⟩
  have h2 : 2*x - 1 ∉ unitInt := by
    rintro ⟨h1,h2⟩
    exact hx ⟨by linarith, by linarith⟩
  simp [haarG,H_outside h1,H_outside h2]

lemma G_bound (x : ℝ) : |haarG x| ≤ 1 := by
  by_cases hx : 2*x ∈ unitInt
  · have hx' : 2*x-1 ∉ unitInt := by
      intro h
      linarith [hx.2,h.1]
    simpa [haarG,H_outside hx'] using H_bound (2*x)
  · simpa [haarG,H_outside hx] using H_bound (2*x-1)

def side (n : ℕ) : ℝ := ((1:ℝ) / 2)^n

lemma side_pos (n : ℕ) : 0 < side n := by unfold side; positivity

lemma side_le (n : ℕ) : side n ≤ 1 := by unfold side; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma pow_mul_side (n : ℕ) : (2:ℝ)^n * side n = 1 := by rw [side, ← mul_pow]; norm_num

lemma side_succ (n : ℕ) : side (n+1) = side n / 2 := by simp [side, pow_succ, div_eq_mul_inv]

def lft (a s : ℝ) (n k : ℕ) : ℝ := a + k*(s * side n)

lemma cell_in_top (a : ℝ) {s : ℝ} {n k : ℕ} (hs : 0 < s) (hk : k < 2^n) :
    box (lft a s n k) (s * side n) ⊆ box a s := by
  intro x hx
  rcases hx with ⟨h1,h2⟩
  constructor
  · refine le_trans ?_ h1
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (mul_pos hs (side_pos _)).le)
  · refine lt_of_lt_of_le h2 ?_
    calc
      lft a s n k + s * side n = a + ((k+1:ℕ) : ℝ) * (s*side n) := by
        push_cast; unfold lft; ring
      _ ≤ a + ((2:ℝ)^n) * (s*side n) :=
        add_le_add_right (mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Nat.succ_le_of_lt hk)) (mul_pos hs (side_pos _)).le) _
      _ = a + s := by rw [mul_left_comm, pow_mul_side, mul_one]

lemma norm_mem_box {a s x : ℝ} (hs : 0 < s) :
    (x-a)/s ∈ unitInt ↔ x ∈ box a s := by
  unfold unitInt box
  simp only [mem_Ico, le_div_iff₀ hs, div_lt_iff₀ hs, one_mul, zero_mul]
  constructor
  · intro ⟨h1,h2⟩; constructor <;> linarith
  · intro ⟨h1,h2⟩; constructor <;> linarith

def coeffH (F : ℝ → ℂ) (a r : ℝ) :=
  ∫ v, haarH v • F (a+r*v) ∂μ₁

def jump (F : ℝ → ℂ) (a r x : ℝ) :=
  haarG ((x-a)/r) • coeffH F a r

def haarLayer (F : ℝ → ℂ) (a s : ℝ) (n : ℕ) (x : ℝ) :=
    ∑ k ∈ Finset.range (2^n), jump F (lft a s n k) (s*side n) x

def shift (F : ℝ → ℂ) (a s : ℝ) (J : ℕ) (x : ℝ) :=
    ∑ n ∈ Finset.range J, haarLayer F a s n x

def modρ (ρ : ℝ → ℝ) (u : ℝ) (x : ℝ) : ℂ := (ρ x:ℂ)* phase u x

def maxShift (ρ : ℝ → ℝ) (a s : ℝ) (J : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℤ, ENNReal.ofReal ‖shift (modρ ρ n) a s J x‖

def density (ρ : ℝ → ℝ) (a s : ℝ) := ∫ y, ρ (a+s*y) ∂μ₁

def usable (ρ : ℝ → ℝ) (a s : ℝ) (J : ℕ) (B : ℝ) (x : ℝ) : Prop :=
  ∀ n, n < J → ∀ k, k < 2^n → x ∈ box (lft a s n k) (s*side n) →
    density ρ (lft a s n k) (s*side n) ≤ B

/-- A cut dyadic statement on one top. Used only at levels B polynomial in log d. -/
def UnitTreeBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j : ℕ in atTop, ∀ (ρ : ℝ → ℝ),
    Measurable ρ → (∀ x, 0 ≤ ρ x) → (∫ x, ρ x ∂μ₁) ≤ 2 →
    (∀ x, ρ x ≤ Real.exp ((2 : ℝ)^j)) →
    ∀ (J : ℕ) (G : Set ℝ), MeasurableSet G → G ⊆ unitInt →
    (∀ x ∈ G, usable ρ 0 1 J (((j:ℝ)+1)^3) x) →
    (∫⁻ x in G, maxShift ρ 0 1 J x) ≤ ENNReal.ofReal (C * (2:ℝ)^j)

lemma jump_outside {a r x : ℝ} (hr : 0 < r) (hx : x ∉ box a r) (F) :
    jump F a r x = 0 := by simp only [jump, G_outside (mt (norm_mem_box hr).mp hx), zero_smul]

lemma shift_outside {a s x : ℝ} (hs : 0 < s) (hx : x ∉ box a s) (F J) :
    shift F a s J x = 0 := by
  refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun k hk => ?_
  exact jump_outside (mul_pos hs (side_pos _)) (fun H => hx (cell_in_top a hs
    (Finset.mem_range.mp hk) H)) _

lemma measurable_mod {ρ : ℝ → ℝ} (hρ : Measurable ρ) (u : ℝ) : Measurable (modρ ρ u) :=
  (Complex.continuous_ofReal.measurable.comp hρ).mul (phase_cont u).measurable

section meas
variable {X : Type*} [MeasurableSpace X] {A R O : X → ℝ}
    {F : ℝ → ℂ}

lemma measurable_jump_comp (hF : Measurable F) (ha : Measurable A) (hr : Measurable R)
    (ho : Measurable O) : Measurable fun x => jump F (A x) (R x) (O x) := by
  refine (measurableG.comp ((ho.sub ha).div hr)).smul ?_
  apply StronglyMeasurable.measurable
  unfold coeffH
  refine StronglyMeasurable.integral_prod_right (Measurable.stronglyMeasurable ?_)
  exact (measurableH.comp measurable_snd).smul (hF.comp
    ((ha.comp measurable_fst).add ((hr.comp measurable_fst).mul measurable_snd)))

lemma measurable_shift_comp (hF : Measurable F) (ha : Measurable A) (hr : Measurable R)
    (ho : Measurable O) (J : ℕ) : Measurable fun x => shift F (A x) (R x) J (O x) :=
  Finset.measurable_sum _ (fun _ _ => Finset.measurable_sum _ (fun _ _ =>
    measurable_jump_comp hF (ha.add (measurable_const.mul (hr.mul measurable_const)))
      (hr.mul measurable_const) ho))

lemma measurable_maxShift_comp {ρ : ℝ → ℝ} (hρ : Measurable ρ) (ha : Measurable A) (hr : Measurable R)
    (ho : Measurable O) (J) : Measurable fun x => maxShift ρ (A x) (R x) J (O x) :=
  Measurable.iSup (fun _ => (measurable_shift_comp (measurable_mod hρ _) ha hr ho J).norm.ennreal_ofReal)

end meas

lemma bounded_jump {F : ℝ → ℂ} (hf : Measurable F) (B : ℝ) (hb : ∀ x, ‖F x‖ ≤ B)
    (a r x : ℝ) : ‖jump F a r x‖ ≤ B := by
  have h (v : ℝ) : ‖haarH v • F (a+r*v)‖ ≤ B := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (H_bound _)).trans (hb _)
  have hm : Measurable (fun v => haarH v • F (a+r*v)) :=
    measurableH.smul (hf.comp (measurable_const.add (measurable_const.mul measurable_id)))
  rw [jump, norm_smul, Real.norm_eq_abs]
  refine (mul_le_of_le_one_left (norm_nonneg _) (G_bound _)).trans
    ((norm_integral_le_integral_norm _).trans ?_)
  apply le_trans (b:= ∫ _, B ∂μ₁)
  · exact integral_mono (Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ h)).norm
      (integrable_const _) h
  · simp

lemma bounded_haarLayer {F : ℝ → ℂ} (hf : Measurable F) (B : ℝ) (hb : ∀ x, ‖F x‖ ≤ B)
    (a s : ℝ) (n : ℕ) (x : ℝ) : ‖haarLayer F a s n x‖ ≤ (2:ℝ)^n * B := by
  apply (norm_sum_le _ _).trans
  apply le_trans (b := ∑ _ ∈ Finset.range ((2:ℕ)^n), B)
  · exact Finset.sum_le_sum fun k _ => bounded_jump hf B hb _ _ _
  simp

lemma bounded_shift {F : ℝ → ℂ} (hf : Measurable F) (B : ℝ) (hb : ∀ x, ‖F x‖ ≤ B)
    (a s : ℝ) (J : ℕ) (x : ℝ) : ‖shift F a s J x‖ ≤ ∑ n ∈ Finset.range J, (2:ℝ)^n * B :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => bounded_haarLayer hf B hb _ _ _ _)

end
end FourierLLogL.Period

end OAI
