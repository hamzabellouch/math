import OAI.Combinatorics.TreeEdit.EditMetric

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteFourier

open scoped ComplexConjugate
open RCLike

variable {A : Type*} [Fintype A] [AddCommGroup A]

noncomputable def coefficient (f : A → ℂ) (χ : AddChar A ℂ) : ℂ :=
  (AddChar.complexBasis A).repr f χ

lemma expansion (f : A → ℂ) (x : A) :
    ∑ χ : AddChar A ℂ, coefficient f χ * χ x = f x := by
  simpa [coefficient, AddChar.complexBasis_apply, Pi.smul_apply, smul_eq_mul]
    using congr_fun ((AddChar.complexBasis A).sum_repr f) x

omit [AddCommGroup A] in
lemma weighted_sum_right {ι : Type*} (s : Finset ι) (f : A → ℂ) (g : ι → A → ℂ) :
    ⟪f, ∑ i ∈ s, g i⟫ₙ_[ℂ] = ∑ i ∈ s, ⟪f, g i⟫ₙ_[ℂ] := by
  simp only [wInner, Finset.sum_apply, inner_sum, Finset.smul_sum]
  exact Finset.sum_comm

omit [AddCommGroup A] in
lemma weighted_sum_left {ι : Type*} (s : Finset ι) (f : ι → A → ℂ) (g : A → ℂ) :
    ⟪∑ i ∈ s, f i, g⟫ₙ_[ℂ] = ∑ i ∈ s, ⟪f i, g⟫ₙ_[ℂ] := by
  simp only [wInner, Finset.sum_apply, sum_inner, Finset.smul_sum]
  exact Finset.sum_comm

lemma coefficient_inner (f : A → ℂ) (χ : AddChar A ℂ) :
    coefficient f χ = ⟪(χ : A → ℂ), f⟫ₙ_[ℂ] := by
  classical
  conv_rhs => rw [← (AddChar.complexBasis A).sum_repr f]
  simp only [weighted_sum_right, AddChar.complexBasis_apply,
    wInner_smul_right, smul_eq_mul, AddChar.wInner_cWeight_eq_boole]
  simp [coefficient]

lemma parseval_complex (f : A → ℂ) :
    ⟪f, f⟫ₙ_[ℂ] = ∑ χ : AddChar A ℂ,
      conj (coefficient f χ) * coefficient f χ := by
  conv_lhs => lhs; rw [← (AddChar.complexBasis A).sum_repr f]
  simp only [weighted_sum_left, AddChar.complexBasis_apply, wInner_smul_left,
    smul_eq_mul, ← coefficient_inner, starRingEnd_apply, coefficient]

lemma coefficient_translate (f : A → ℂ) (z : A) (χ : AddChar A ℂ) :
    coefficient (fun x => f (x + z) - f x) χ = coefficient f χ * (χ z - 1) := by
  classical
  have hexp : (fun x => f (x + z) - f x) =
      ∑ ψ : AddChar A ℂ, (coefficient f ψ * (ψ z - 1)) • (ψ : A → ℂ) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← expansion f (x + z), ← expansion f x, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [AddChar.map_add_eq_mul]
    ring
  rw [hexp, coefficient_inner, weighted_sum_right]
  simp only [wInner_smul_right, smul_eq_mul, AddChar.wInner_cWeight_eq_boole]
  simp

lemma parseval (f : A → ℂ) :
    (Fintype.card A : ℝ)⁻¹ * ∑ x, ‖f x‖ ^ 2 =
      ∑ χ : AddChar A ℂ, ‖coefficient f χ‖ ^ 2 := by
  have h := congr_arg Complex.re (parseval_complex f)
  have hn (z : ℂ) : (conj z * z).re = ‖z‖ ^ 2 := by
    simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  simpa only [wInner, cWeight, Function.const_apply, map_sum, Complex.re_sum,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id,
    id_eq, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re, ← Finset.mul_sum, hn] using h

lemma displacement_parseval (f : A → ℂ) (z : A) :
    (Fintype.card A : ℝ)⁻¹ * ∑ x, ‖f (x + z) - f x‖ ^ 2 =
      ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * ‖coefficient f χ‖ ^ 2 := by
  rw [parseval]
  apply Finset.sum_congr rfl
  intro χ _
  rw [coefficient_translate, norm_mul, mul_pow, norm_sub_rev]
  ring

noncomputable def multiplier (χ : AddChar A ℂ) (z : A) : ℝ := ‖1 - χ z‖ ^ 2

omit [Fintype A] in
@[simp] lemma multiplier_zero (z : A) : multiplier (0 : AddChar A ℂ) z = 0 := by
  simp [multiplier]

omit [Fintype A] in
lemma multiplier_nonneg (χ : AddChar A ℂ) (z : A) : 0 ≤ multiplier χ z := sq_nonneg _

noncomputable def average (f : A → ℝ) : ℝ := (Fintype.card A : ℝ)⁻¹ * ∑ x, f x

def HasSpectrum (V : A → ℝ) : Prop :=
  ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧ H 0 = 0 ∧
    ∀ z, V z = ∑ χ, multiplier χ z * H χ

lemma spectrum_zero : HasSpectrum (fun _ : A => 0) := by
  exact ⟨fun _ => 0, by simp, rfl, by simp⟩

lemma HasSpectrum.add {V W : A → ℝ} (hV : HasSpectrum V) (hW : HasSpectrum W) :
    HasSpectrum (fun z => V z + W z) := by
  obtain ⟨H, hH, hH0, heH⟩ := hV
  obtain ⟨K, hK, hK0, heK⟩ := hW
  refine ⟨fun χ => H χ + K χ, fun χ => add_nonneg (hH χ) (hK χ), by simp [hH0, hK0], ?_⟩
  intro z
  simp [heH, heK, mul_add, Finset.sum_add_distrib]

lemma HasSpectrum.mul {V : A → ℝ} (hV : HasSpectrum V) {c : ℝ} (hc : 0 ≤ c) :
    HasSpectrum (fun z => c * V z) := by
  obtain ⟨H, hH, hH0, heH⟩ := hV
  refine ⟨fun χ => c * H χ, fun χ => mul_nonneg hc (hH χ), by simp [hH0], ?_⟩
  intro z
  simp only [heH, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  ring

lemma cut_spectrum (U : A → Bool) :
    HasSpectrum (fun z => average (fun x => |(if U (x + z) then 1 else 0 : ℝ) -
      (if U x then 1 else 0)|)) := by
  classical
  let f : A → ℂ := fun x => if U x then 1 else 0
  refine ⟨fun χ => if χ = 0 then 0 else ‖coefficient f χ‖ ^ 2, ?_, by simp, ?_⟩
  · intro χ; dsimp; split_ifs <;> positivity
  · intro z
    have hd (x : A) : |(if U (x + z) then 1 else 0 : ℝ) - (if U x then 1 else 0)| =
        ‖f (x + z) - f x‖ ^ 2 := by
      dsimp [f]
      cases U (x + z) <;> cases U x <;> norm_num
    simp only [average, hd]
    rw [displacement_parseval]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases h : χ = 0
    · subst χ; simp [multiplier]
    · simp [h, multiplier]

lemma scalar_spectrum_aux (s : Finset ℝ) :
    ∀ g : A → ℝ, (∀ x, g x ∈ s) →
      HasSpectrum (fun z => average (fun x => |g (x + z) - g x|)) := by
  classical
  induction s using Finset.induction_on_min with
  | empty =>
      intro g hg
      simpa using hg 0
  | insert a s hmin ih =>
      intro g hg
      by_cases hs : s.Nonempty
      · let b := s.min' hs
        have hb : b ∈ s := s.min'_mem hs
        have hab : a < b := hmin b hb
        let g' : A → ℝ := fun x => if g x = a then b else g x
        let U : A → Bool := fun x => decide (g x ≠ a)
        have hg' (x : A) : g' x ∈ s := by
          dsimp [g']
          split_ifs with h
          · exact hb
          · exact (Finset.mem_insert.mp (hg x)).resolve_left h
        have hlow (x : A) (hx : g x ≠ a) : b ≤ g x :=
          s.min'_le _ ((Finset.mem_insert.mp (hg x)).resolve_left hx)
        have hid (x y : A) : |g x - g y| = |g' x - g' y| +
            (b - a) * |(if U x then 1 else 0 : ℝ) - (if U y then 1 else 0)| := by
          by_cases hx : g x = a <;> by_cases hy : g y = a
          · simp [g', U, hx, hy]
          · have hby := hlow y hy
            simp only [g', U, hx, hy, ↓reduceIte, ne_eq, decide_eq_true_eq,
              not_true_eq_false, not_false_eq_true,
              zero_sub, abs_neg, abs_one, mul_one]
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            ring
          · have hbx := hlow x hx
            simp only [g', U, hy, hx, ↓reduceIte, ne_eq, decide_eq_true_eq,
              not_true_eq_false, not_false_eq_true, sub_zero, abs_one, mul_one]
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
            ring
          · simp [g', U, hx, hy]
        have hspec := (ih g' hg').add ((cut_spectrum U).mul (sub_nonneg.mpr hab.le))
        convert hspec using 1
        funext z
        simp only [average, hid, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        have hc (x : A) : g x = a := by simpa [he] using hg x
        simpa [hc, average] using (spectrum_zero (A := A))

lemma scalar_spectrum (g : A → ℝ) :
    HasSpectrum (fun z => average (fun x => |g (x + z) - g x|)) := by
  classical
  apply scalar_spectrum_aux (Finset.univ.image g)
  intro x
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

lemma multiplier_eq (χ : AddChar A ℂ) (z : A) :
    multiplier χ z = 2 - 2 * (χ z).re := by
  rw [multiplier, Complex.sq_norm, Complex.normSq_sub]
  norm_num [Complex.normSq_eq_norm_sq, χ.norm_apply]

lemma average_const (c : ℝ) : average (fun _ : A => c) = c := by
  have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [average, hn]

lemma average_nonneg {f : A → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ average f := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => hf x)

lemma average_le_const {f : A → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) : average f ≤ c := by
  rw [← average_const (A := A) c]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hf x) (by positivity)

lemma average_multiplier (χ : AddChar A ℂ) :
    average (multiplier χ) = if χ = 0 then 0 else 2 := by
  classical
  by_cases hχ : χ = 0
  · subst χ; simp [average]
  · have hs : ∑ z, (χ z).re = 0 := by
      simpa [Complex.re_sum, hχ] using congr_arg Complex.re (χ.sum_eq_ite)
    have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [average, multiplier_eq, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, hχ, hn]

lemma spectrum_total {V : A → ℝ} {H : AddChar A ℂ → ℝ}
    (hH0 : H 0 = 0) (he : ∀ z, V z = ∑ χ, multiplier χ z * H χ) :
    average V = 2 * ∑ χ, H χ := by
  classical
  calc
    average V = ∑ χ, average (multiplier χ) * H χ := by
      simp only [average, he, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 2 * ∑ χ, H χ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [average_multiplier]
      split_ifs with h
      · subst χ; simp [hH0]
      · rfl

lemma scalar_spectrum_bounded (g : A → ℝ) :
    ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧ H 0 = 0 ∧
      (∀ χ, H χ ≤ ∑ x, |g x|) ∧
      ∀ z, average (fun x => |g (x + z) - g x|) = ∑ χ, multiplier χ z * H χ := by
  obtain ⟨H, hH, hH0, he⟩ := scalar_spectrum g
  refine ⟨H, hH, hH0, ?_, he⟩
  have hle : average (fun z => average (fun x => |g (x + z) - g x|)) ≤ 2 * ∑ x, |g x| := by
    apply average_le_const
    intro z
    apply average_le_const
    intro x
    have h1 : |g (x + z)| ≤ ∑ y, |g y| :=
      Finset.single_le_sum (fun y _ => abs_nonneg (g y)) (Finset.mem_univ _)
    have h2 : |g x| ≤ ∑ y, |g y| :=
      Finset.single_le_sum (fun y _ => abs_nonneg (g y)) (Finset.mem_univ _)
    have htri := abs_sub (g (x + z)) (g x)
    linarith
  rw [spectrum_total hH0 he] at hle
  intro χ
  have hsingle : H χ ≤ ∑ ψ, H ψ :=
    Finset.single_le_sum (fun ψ _ => hH ψ) (Finset.mem_univ _)
  linarith

omit [Fintype A] [AddCommGroup A] in
lemma l1_distance_series (v w : RealL1) :
    dist v w = ∑' j : ℕ, |v j - w j| := by
  rw [dist_eq_norm, lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)]
  simp [Real.norm_eq_abs]

omit [Fintype A] [AddCommGroup A] in
lemma l1_coordinate_summable (v : RealL1) : Summable (fun j : ℕ => |v j|) := by
  simpa [Real.norm_eq_abs] using (lp.memℓp v).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)

omit [Fintype A] [AddCommGroup A] in
lemma l1_distance_summable (v w : RealL1) : Summable (fun j : ℕ => |v j - w j|) := by
  simpa [lp.coeFn_sub] using l1_coordinate_summable (v - w)

theorem l1_displacement_spectrum (F : A → RealL1) :
    HasSpectrum (fun z => average (fun x => dist (F (x + z)) (F x))) := by
  classical
  choose H hH hH0 hHb he using fun j : ℕ => scalar_spectrum_bounded (fun x => F x j)
  have hs : Summable (fun j : ℕ => ∑ x, |F x j|) :=
    summable_sum fun x _ => l1_coordinate_summable (F x)
  have hHs (χ : AddChar A ℂ) : Summable (fun j : ℕ => H j χ) :=
    Summable.of_nonneg_of_le (fun j => hH j χ) (fun j => hHb j χ) hs
  refine ⟨fun χ => ∑' j, H j χ, fun χ => tsum_nonneg (fun j => hH j χ), by simp [hH0], ?_⟩
  intro z
  have hd (x : A) : Summable (fun j : ℕ => |F (x + z) j - F x j|) :=
    l1_distance_summable _ _
  calc
    average (fun x => dist (F (x + z)) (F x)) =
        ∑' j : ℕ, average (fun x => |F (x + z) j - F x j|) := by
      simp only [average, l1_distance_series]
      rw [Summable.tsum_mul_left _ (summable_sum fun x _ => hd x),
        Summable.tsum_finsetSum (fun x _ => hd x)]
    _ = ∑' j : ℕ, ∑ χ, multiplier χ z * H j χ := by simp only [he]
    _ = ∑ χ, multiplier χ z * ∑' j : ℕ, H j χ := by
      rw [Summable.tsum_finsetSum (fun χ _ => (hHs χ).mul_left _)]
      simp only [Summable.tsum_mul_left _ (hHs _)]

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

noncomputable def energy (H : AddChar A ℂ → ℝ) (z : A) : ℝ :=
  ∑ χ, multiplier χ z * H χ

lemma multiplier_le_four (χ : AddChar A ℂ) (z : A) : multiplier χ z ≤ 4 := by
  have hn : ‖1 - χ z‖ ≤ 2 := by
    have hh := norm_sub_le (1 : ℂ) (χ z)
    rw [norm_one, χ.norm_apply] at hh
    norm_num at hh
    exact hh
  dsimp [multiplier]
  nlinarith [norm_nonneg (1 - χ z)]

lemma energy_nonneg {H : AddChar A ℂ → ℝ} (hH : ∀ χ, 0 ≤ H χ) (z : A) :
    0 ≤ energy H z := Finset.sum_nonneg fun χ _ => mul_nonneg (multiplier_nonneg χ z) (hH χ)

noncomputable def pushSpectrum (H : AddChar A ℂ → ℝ) (f : B →+ A) (η : AddChar B ℂ) : ℝ :=
  ∑ χ, if χ.compAddMonoidHom f = η then H χ else 0

omit [Fintype B] in
lemma pushSpectrum_nonneg {H : AddChar A ℂ → ℝ} (hH : ∀ χ, 0 ≤ H χ) (f : B →+ A) :
    ∀ η, 0 ≤ pushSpectrum H f η := by
  classical
  intro η
  exact Finset.sum_nonneg fun χ _ => by split_ifs; exact hH χ; rfl

lemma pushSpectrum_sum (H : AddChar A ℂ → ℝ) (f : B →+ A) (g : AddChar B ℂ → ℝ) :
    ∑ η, g η * pushSpectrum H f η = ∑ χ, g (χ.compAddMonoidHom f) * H χ := by
  classical
  simp only [pushSpectrum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_eq_single (χ.compAddMonoidHom f)]
  · simp
  · intro η _ hη; simp [Ne.symm hη]
  · simp

lemma energy_push (H : AddChar A ℂ → ℝ) (f : B →+ A) (z : B) :
    energy (pushSpectrum H f) z = energy H (f z) := by
  rw [energy, pushSpectrum_sum]
  rfl

lemma average_energy (H : AddChar A ℂ → ℝ) :
    average (energy H) = 2 * ∑ χ, if χ = 0 then 0 else H χ := by
  classical
  calc
    _ = ∑ χ, average (multiplier χ) * H χ := by
      simp only [average, energy, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      simp only [average_multiplier, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      split_ifs <;> ring

lemma sum_multiplier_period (χ : AddChar A ℂ) (v : A) (n : ℕ)
    (hne : χ v ≠ 1) (hper : (χ v) ^ n = 1) :
    ∑ s ∈ Finset.range n, multiplier χ ((s + 1) • v) = 2 * n := by
  have hs : ∑ s ∈ Finset.range n, (χ v) ^ s = 0 := by
    have hh := geom_sum_mul (χ v) n
    rw [hper, sub_self] at hh
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hne)
  have hs' : ∑ s ∈ Finset.range n, χ ((s + 1) • v) = 0 := by
    simp only [AddChar.map_nsmul_eq_pow, pow_succ, ← Finset.sum_mul, hs, zero_mul]
  have hr : ∑ s ∈ Finset.range n, (χ ((s + 1) • v)).re = 0 := by
    simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re hs'
  simp only [multiplier_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.mul_sum, hr, mul_zero, sub_zero]
  ring

lemma period_detect (χ : AddChar A ℂ) (v : A) {n J : ℕ}
    (hn : 0 < n) (hJ : 2 * n ≤ J) (hne : χ v ≠ 1) (hper : (χ v) ^ n = 1) :
    (J : ℝ) ≤ ∑ s ∈ Finset.range J, multiplier χ ((s + 1) • v) := by
  let N := n * (J / n)
  have hN : N ≤ J := Nat.mul_div_le J n
  have hcount : J ≤ 2 * N := by
    have hm := Nat.mod_lt J hn
    have he := Nat.mod_add_div J n
    dsimp [N]
    omega
  have hperN : (χ v) ^ N = 1 := by simp [N, pow_mul, hper]
  calc
    (J : ℝ) ≤ 2 * N := by exact_mod_cast hcount
    _ = ∑ s ∈ Finset.range N, multiplier χ ((s + 1) • v) :=
      (sum_multiplier_period χ v N hne hperN).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
      (fun s _ _ => multiplier_nonneg χ ((s + 1) • v))

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

noncomputable def active (χ : AddChar A ℂ) (v : A) : ℝ := if χ v = 1 then 0 else 1

noncomputable def activeMass (H : AddChar A ℂ → ℝ) (v : A) : ℝ :=
  ∑ χ, active χ v * H χ

omit [Fintype A] in
lemma active_nonneg (χ : AddChar A ℂ) (v : A) : 0 ≤ active χ v := by
  unfold active; split_ifs <;> norm_num

lemma activeMass_nonneg {H : AddChar A ℂ → ℝ} (hH : ∀ χ, 0 ≤ H χ) (v : A) :
    0 ≤ activeMass H v := Finset.sum_nonneg fun χ _ => mul_nonneg (active_nonneg χ v) (hH χ)

lemma activeMass_push (H : AddChar A ℂ → ℝ) (f : B →+ A) (v : B) :
    activeMass (pushSpectrum H f) v = ∑ χ, active χ (f v) * H χ := by
  rw [activeMass, pushSpectrum_sum]
  rfl

lemma energy_le_mass {H : AddChar A ℂ → ℝ} (hH : ∀ χ, 0 ≤ H χ) (v : A) :
    energy H v ≤ 4 * activeMass H v := by
  classical
  rw [energy, activeMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro χ _
  by_cases hv : χ v = 1
  · simp [multiplier, active, hv]
  · have hh := mul_le_mul_of_nonneg_right (multiplier_le_four χ v) (hH χ)
    simpa [active, hv] using hh

lemma twice_activeMass_le_average {H : AddChar A ℂ → ℝ} (hH : ∀ χ, 0 ≤ H χ) (v : A) :
    2 * activeMass H v ≤ average (energy H) := by
  classical
  rw [average_energy, activeMass]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro χ _
  by_cases hχ : χ = 0
  · subst χ; simp [active]
  · by_cases hv : χ v = 1
    · simpa [active, hv, hχ] using hH χ
    · simp [active, hv, hχ]

end FiniteFourier

namespace FiniteFourier

variable {A : Type*} [Fintype A] [AddCommGroup A]

lemma average_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

lemma average_le {f : A → ℝ} {C : ℝ} (h : ∀ x, f x ≤ C) : average f ≤ C :=
  (average_mono h).trans_eq (average_const C)

end FiniteFourier

end TreeEdit

end OAI
