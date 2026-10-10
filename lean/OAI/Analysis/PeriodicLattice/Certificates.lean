import OAI.Analysis.PeriodicLattice.Arithmetic

namespace OAI

/-! Quantitative certificates for planar derivatives and products. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingCertificates {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace Quantitative
open RapidCalculus Profiles TorusCalculus RecursiveArithmetic
open scoped ContDiff

structure BiCertificate (F : Input → ℝ → ℝ → ℝ) where
  budget : Input × ℕ × ℕ → ℕ
  recursive : Primrec budget
  smooth : ∀ d, ContDiff ℝ ∞ (Function.uncurry (F d))
  estimate : ∀ d, d.WellFormed → ∀ w n J, w.length ≤ n → ∀ t, 0 ≤ t → ∀ y,
    (1+t)^J * ‖wordD w (F d) t y‖ ≤ (budget (d,n,J) : ℝ)

theorem word_mul_estimate {F G : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (hG : ContDiff ℝ ∞ (Function.uncurry G))
    (w : List Bool) (t y a C D : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hf : ∀ v : List Bool, v.length ≤ w.length → a * ‖wordD v F t y‖ ≤ C)
    (hg : ∀ v : List Bool, v.length ≤ w.length → ‖wordD v G t y‖ ≤ D) :
    a * ‖wordD w (F*G) t y‖ ≤ 2^w.length * C * D := by
  induction w using List.reverseRecOn generalizing F G with
  | nil =>
    simpa only [wordD_nil, Pi.mul_apply, norm_mul, List.length_nil, pow_zero, one_mul,
      ← mul_assoc] using mul_le_mul (hf [] le_rfl) (hg [] le_rfl) (norm_nonneg _) hC
  | append_singleton w i ih =>
    have hfi v (hv : v.length ≤ w.length) : a * ‖wordD v (biD i F) t y‖ ≤ C := by
      simpa only [wordD_append, wordD_cons, wordD_nil] using
        hf (v++[i]) (by simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hv 1)
    have hgi v (hv : v.length ≤ w.length) : ‖wordD v (biD i G) t y‖ ≤ D := by
      simpa only [wordD_append, wordD_cons, wordD_nil] using
        hg (v++[i]) (by simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hv 1)
    have hf' v (hv : v.length ≤ w.length) := hf v (hv.trans (by simp))
    have hg' v (hv : v.length ≤ w.length) := hg v (hv.trans (by simp))
    have H1 := ih (partial_contDiff hF i) hG hfi hg'
    have H2 := ih hF (partial_contDiff hG i) hf' hgi
    rw [wordD_append, wordD_cons, wordD_nil, biD_mul hF hG,
      wordD_add (F := biD i F * G) (G := F * biD i G) ((partial_contDiff hF i).mul hG) (hF.mul (partial_contDiff hG i))]
    calc
      _ ≤ a * (‖wordD w (biD i F * G) t y‖ + ‖wordD w (F * biD i G) t y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) ha
      _ ≤ 2^w.length*C*D + 2^w.length*C*D := by rw [mul_add]; exact add_le_add H1 H2
      _ = _ := by simp only [List.length_append, List.length_singleton, pow_succ]; ring

namespace BiCertificate

noncomputable def diff {F : Input → ℝ → ℝ → ℝ} (h : BiCertificate F) (i : Bool) :
    BiCertificate (fun d => biD i (F d)) where
  budget p := h.budget (p.1, p.2.1+1, p.2.2)
  recursive := h.recursive.comp (by fun_prop)
  smooth d := partial_contDiff (h.smooth d) i
  estimate d hd w n J hn t ht y := by
    simpa only [wordD_append, wordD_cons, wordD_nil] using
      h.estimate d hd (w++[i]) (n+1) J (by simpa using Nat.add_le_add_right hn 1) t ht y

noncomputable def add {F G : Input → ℝ → ℝ → ℝ} (h : BiCertificate F) (k : BiCertificate G) :
    BiCertificate (fun d => F d + G d) where
  budget p := h.budget p + k.budget p
  recursive := Primrec.nat_add.comp h.recursive k.recursive
  smooth d := (h.smooth d).add (k.smooth d)
  estimate d hd w n J hn t ht y := by
    rw [wordD_add (h.smooth d) (k.smooth d)]
    calc
      _ ≤ (1+t)^J * (‖wordD w (F d) t y‖ + ‖wordD w (G d) t y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ _ := by rw [mul_add, Nat.cast_add]; exact add_le_add (h.estimate d hd w n J hn t ht y) (k.estimate d hd w n J hn t ht y)

noncomputable def scale {F : Input → ℝ → ℝ → ℝ} (h : BiCertificate F) (c : ℝ) (N : ℕ)
    (hc : ‖c‖ ≤ N) : BiCertificate (fun d => c • F d) where
  budget p := N * h.budget p
  recursive := Primrec.nat_mul.comp (Primrec.const N) h.recursive
  smooth d := (contDiff_const (c := c)).mul (h.smooth d)
  estimate d hd w n J hn t ht y := by
    rw [wordD_scale c (h.smooth d), Pi.smul_apply, Pi.smul_apply, norm_smul, mul_left_comm]
    simpa only [Nat.cast_mul] using mul_le_mul hc (h.estimate d hd w n J hn t ht y)
      (by positivity) (Nat.cast_nonneg N)

noncomputable def mul {F G : Input → ℝ → ℝ → ℝ} (h : BiCertificate F) (k : BiCertificate G) :
    BiCertificate (fun d => F d * G d) where
  budget p := 2^p.2.1 * h.budget p * k.budget (p.1,p.2.1,0)
  recursive := by
    have hp : Primrec (fun p : Input × ℕ × ℕ => k.budget (p.1,p.2.1,0)) := k.recursive.comp (by fun_prop)
    exact Primrec.nat_mul.comp (Primrec.nat_mul.comp (by fun_prop) h.recursive) hp
  smooth d := (h.smooth d).mul (k.smooth d)
  estimate d hd w n J hn t ht y := by
    have hh := word_mul_estimate (h.smooth d) (k.smooth d) w t y ((1+t)^J)
      (h.budget (d,n,J)) (k.budget (d,n,0)) (by positivity) (by positivity) (by positivity)
      (fun v hv => h.estimate d hd v n J (hv.trans hn) t ht y)
      (fun v hv => by simpa using k.estimate d hd v n 0 (hv.trans hn) t ht y)
    refine hh.trans ?_
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    gcongr
    norm_num

noncomputable def mean {F : Input → ℝ → ℝ → ℝ} (h : BiCertificate F) :
    BiCertificate (fun d => PeriodicInverse.mean (F d)) where
  budget := h.budget
  recursive := h.recursive
  smooth d := PeriodicInverse.mean_contDiff (h.smooth d)
  estimate d hd w n J hn t ht y := by
    rw [PeriodicInverse.mean_wordD (h.smooth d)]
    split_ifs
    · simp
    · have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (f := fun s => (1 + t) ^ J * wordD w (F d) t s) (C := (h.budget (d,n,J) : ℝ)) (fun s _ => by
          rw [norm_mul, Real.norm_eq_abs ((1+t)^J), abs_of_nonneg (by positivity)]
          exact h.estimate d hd w n J hn t ht s)
      simpa only [intervalIntegral.integral_const_mul, norm_mul, Real.norm_eq_abs ((1+t)^J),
        abs_of_nonneg (show 0 ≤ (1+t)^J by positivity), sub_zero, abs_one, mul_one, PeriodicInverse.mean] using hi

noncomputable def first {F : Input → ℝ → ℝ → ℝ} (h : BiCertificate F) (lam : ℝ) :
    BiCertificate (fun d => PeriodicInverse.first lam (F d)) := by
  let N : ℕ := ⌈‖(1 - Real.exp lam)⁻¹‖ * Real.exp |lam|⌉₊
  have hN : ‖(1 - Real.exp lam)⁻¹‖ * Real.exp |lam| ≤ N := Nat.le_ceil _
  refine ⟨(fun p => N * h.budget p), Primrec.nat_mul.comp (Primrec.const N) h.recursive,
    (fun d => PeriodicInverse.first_contDiff lam (h.smooth d)), ?_⟩
  intro d hd w n J hn t ht y
  rw [PeriodicInverse.first_wordD lam (h.smooth d)]
  calc
    _ ≤ ‖(1 - Real.exp lam)⁻¹‖ * Real.exp |lam| * h.budget (d,n,J) :=
      PeriodicInverse.first_weighted_bound lam t (by positivity) (h.estimate d hd w n J hn t ht) y
    _ ≤ _ := by rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_right hN (by positivity)

end BiCertificate
end Quantitative
namespace Quantitative
open RapidCalculus Profiles TorusCalculus RecursiveArithmetic
open scoped ContDiff

def planarBudget (p : Input × ℕ × ℕ) : ℕ :=
  ∑ r ∈ Finset.range (p.2.1+1), ∑ k ∈ Finset.range (p.2.1+1),
    Planar.planarBound (CompilerPlanar.radix p.1) p.1.word.length
      (CompilerPlanar.loadingCode p.1) k p.2.2 (ProfileJets.pulseBound r) (ProfileJets.bumpBound k)

@[fun_prop] theorem planarBudget_recursive : Primrec planarBudget := by
  have hg : Primrec (fun p : ((Input × ℕ × ℕ) × ℕ) × ℕ =>
      Planar.planarBound (CompilerPlanar.radix p.1.1.1) p.1.1.1.word.length
        (CompilerPlanar.loadingCode p.1.1.1) p.2 p.1.1.2.2
        (ProfileJets.pulseBound p.1.2) (ProfileJets.bumpBound p.2)) := by fun_prop
  have hh := sumRange (f := fun p : (Input × ℕ × ℕ) × ℕ => p.1.2.1+1) (by fun_prop) hg.to₂
  exact sumRange (by fun_prop) hh.to₂

theorem planarBudget_bound (d : Input) (hd : d.WellFormed) (w : List Bool)
    (n J : ℕ) (hn : w.length ≤ n) (t : ℝ) (ht : 0 ≤ t) (y : ℝ) :
    (1+t)^J * ‖wordD w (FluidLift.v d) t y‖ ≤ (planarBudget (d,n,J) : ℝ) := by
  let F : ℕ → ℤ → ℝ := fun n j => CompilerPlanar.nextTable d n j
  let H : ℕ → ℤ → ℝ := fun n j => if CompilerPlanar.haltTable d n j then 1 else 0
  have hF (n : ℕ) (j : ℤ) : |F n j| ≤ (Scales.capacity (CompilerPlanar.radix d) d.word.length (n + 1) : ℝ) := by
    simpa only [F, Nat.abs_cast] using
      (Nat.cast_le.mpr (CompilerPlanar.nextTable_bound d hd n j).le :
        (CompilerPlanar.nextTable d n j : ℝ) ≤ _)
  have hH (n : ℕ) (j : ℤ) : |H n j| ≤ 1 := by dsimp [H]; split_ifs <;> norm_num
  let V := Planar.coefficients (CompilerPlanar.radix d) d.word.length (CompilerPlanar.loadingCode d) F H
  have hV (k : ℕ) : ContDiff ℝ ∞ (V k) := by
    cases k with
    | zero => exact contDiff_const
    | succ k => exact Planar.slot_contDiff _ _ _ _ _
  change (1+t)^J * ‖wordD w (schedule V) t y‖ ≤ _
  rw [wordD_schedule V hV w ⌊t⌋₊ (Nat.floor_le ht) (Nat.lt_floor_add_one t).le]
  apply (Planar.field_weighted_derivative_bound (CompilerPlanar.radix_ge_two d) d.word.length
    (CompilerPlanar.loadingCode d) (w.count true) (w.count false) J
    (ProfileJets.pulseBound (w.count true)) (ProfileJets.bumpBound (w.count false)) F H hF hH
    (ProfileJets.pulseBound_spec _) (ProfileJets.bumpBound_spec _) ht y).trans
  apply Nat.cast_le.mpr
  let h (r k : ℕ) := Planar.planarBound (CompilerPlanar.radix d) d.word.length
    (CompilerPlanar.loadingCode d) k J (ProfileJets.pulseBound r) (ProfileJets.bumpBound k)
  have hk : w.count false ∈ Finset.range (n+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le ((List.count_le_length ..).trans hn))
  have hr : w.count true ∈ Finset.range (n+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le ((List.count_le_length ..).trans hn))
  exact (Finset.single_le_sum (f := h (w.count true)) (fun k _ => Nat.zero_le _) hk).trans
    (Finset.single_le_sum (f := fun r => ∑ k ∈ Finset.range (n+1), h r k)
      (fun r _ => Nat.zero_le _) hr)

noncomputable def aCertificate : BiCertificate FluidLift.a where
  budget := planarBudget
  recursive := planarBudget_recursive
  smooth := FluidLift.a_contDiff
  estimate d hd w n J hn t ht y := by
    have he : wordD w (FluidLift.v d) = fun t y =>
        (wordD w (FluidLift.a d) t y, wordD w (FluidLift.b d) t y) :=
      wordD_pair _ _ (FluidLift.a_contDiff d) (FluidLift.b_contDiff d) w
    have hh := planarBudget_bound d hd w n J hn t ht y
    rw [he] at hh
    exact (mul_le_mul_of_nonneg_left (norm_fst_le _) (by positivity)).trans hh

noncomputable def bCertificate : BiCertificate FluidLift.b where
  budget := planarBudget
  recursive := planarBudget_recursive
  smooth := FluidLift.b_contDiff
  estimate d hd w n J hn t ht y := by
    have he : wordD w (FluidLift.v d) = fun t y =>
        (wordD w (FluidLift.a d) t y, wordD w (FluidLift.b d) t y) :=
      wordD_pair _ _ (FluidLift.a_contDiff d) (FluidLift.b_contDiff d) w
    have hh := planarBudget_bound d hd w n J hn t ht y
    rw [he] at hh
    exact (mul_le_mul_of_nonneg_left (norm_snd_le _) (by positivity)).trans hh

structure ProfileCertificate (f : ℝ → ℝ) where
  budget : ℕ → ℕ
  recursive : Primrec budget
  smooth : ContDiff ℝ ∞ f
  estimate : ∀ k n, k ≤ n → ∀ z, ‖iteratedDeriv k f z‖ ≤ (budget n : ℝ)

namespace ProfileCertificate
noncomputable def one : ProfileCertificate (fun _ => 1) where
  budget _ := 1
  recursive := Primrec.const _
  smooth := contDiff_const
  estimate k n _ z := by rw [iteratedDeriv_const]; split_ifs <;> norm_num

noncomputable def neg {f : ℝ → ℝ} (hf : ProfileCertificate f) : ProfileCertificate (-f) where
  budget := hf.budget
  recursive := hf.recursive
  smooth := hf.smooth.neg
  estimate k n hk z := by simpa only [iteratedDeriv_neg, Pi.neg_apply, norm_neg] using hf.estimate k n hk z
end ProfileCertificate

theorem vertical_derivative_bound (k : ℕ) (z : ℝ) :
    ‖iteratedDeriv k FluidLift.eta z‖ ≤ (64:ℝ)^k ∧
    ‖iteratedDeriv k FluidLift.slope z‖ ≤ (64:ℝ)^k := by
  induction k with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero]
    constructor
    · rw [FluidLift.eta, norm_div]
      apply (div_le_one (norm_pos_iff.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero) : 0 < ‖2*Real.pi‖)).mpr
      calc
        ‖Real.sin (2 * Real.pi * (z - 1/2))‖ ≤ (1:ℝ) := by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one _
        _ ≤ ‖2*Real.pi‖ := by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith [Real.two_le_pi]
    · simpa only [FluidLift.slope, Real.norm_eq_abs] using Real.abs_cos_le_one _
  | succ k ih =>
    constructor
    · rw [iteratedDeriv_succ', FluidLift.eta_deriv]
      exact ih.2.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k))
    · rw [iteratedDeriv_succ', FluidLift.slope_deriv, iteratedDeriv_const_mul_field, norm_mul]
      have hc : ‖-(2*Real.pi)^2‖ ≤ (64:ℝ) := by
        rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [Real.pi_lt_four, Real.pi_pos]
      calc
        _ ≤ 64 * 64^k := mul_le_mul hc ih.1 (norm_nonneg _) (by norm_num)
        _ = _ := by ring

noncomputable def etaCertificate : ProfileCertificate FluidLift.eta where
  budget n := 64^n
  recursive := by fun_prop
  smooth := FluidLift.eta_contDiff
  estimate k n hk z := (vertical_derivative_bound k z).1.trans (by
    simp only [Nat.cast_pow, Nat.cast_ofNat]; exact pow_le_pow_right₀ (by norm_num) hk)

noncomputable def slopeCertificate : ProfileCertificate FluidLift.slope where
  budget n := 64^n
  recursive := by fun_prop
  smooth := FluidLift.slope_contDiff
  estimate k n hk z := (vertical_derivative_bound k z).2.trans (by
    simp only [Nat.cast_pow, Nat.cast_ofNat]; exact pow_le_pow_right₀ (by norm_num) hk)

namespace BiCertificate
noncomputable def neg {F : Input → ℝ → ℝ → ℝ} (h : BiCertificate F) :
    BiCertificate (fun d => -F d) := by
  simpa only [neg_one_smul] using h.scale (-1) 1 (by norm_num)
noncomputable def sub {F G : Input → ℝ → ℝ → ℝ} (h : BiCertificate F) (k : BiCertificate G) :
    BiCertificate (fun d => F d - G d) := by simpa only [sub_eq_add_neg] using h.add k.neg
end BiCertificate

noncomputable def pressureSourceCertificate : BiCertificate FluidLift.pressureSource :=
  ((bCertificate.diff false).mul (bCertificate.diff false)).sub
    (bCertificate.mul ((bCertificate.diff false).diff false))

noncomputable def pressureBaseCertificate : BiCertificate FluidLift.pressureBase :=
  ((bCertificate.mul bCertificate).sub (bCertificate.mul bCertificate).mean).scale (1/2) 1 (by norm_num)

noncomputable def pressureModeCertificate : BiCertificate FluidLift.pressureMode :=
  (pressureSourceCertificate.first (4*Real.pi)).first (-(4*Real.pi))

theorem trig_iterated_bound (k : ℕ) (z : ℝ) :
    ‖iteratedDeriv k Real.sin z‖ ≤ 1 ∧ ‖iteratedDeriv k Real.cos z‖ ≤ 1 := by
  induction k with
  | zero => exact ⟨Real.abs_sin_le_one _, Real.abs_cos_le_one _⟩
  | succ k ih => simpa only [Real.iteratedDeriv_add_one_sin, Real.iteratedDeriv_add_one_cos,
      Pi.neg_apply, norm_neg] using And.intro ih.2 ih.1

noncomputable def doubleSlopeCertificate : ProfileCertificate FluidLift.doubleSlope where
  budget n := 16^n
  recursive := by fun_prop
  smooth := FluidLift.doubleSlope_contDiff
  estimate k n hk z := by
    have he : FluidLift.doubleSlope = fun x => Real.cos (4*Real.pi*(x-1/2)) := by
      funext x
      rw [show 4*Real.pi*(x-1/2) = 2*(2*Real.pi*(x-1/2)) by ring, Real.cos_two_mul]
      rfl
    rw [he, iteratedDeriv_comp_sub_const (f := fun u => Real.cos (4*Real.pi*u)),
      iteratedDeriv_comp_const_mul (Real.contDiff_cos) (4*Real.pi), norm_mul, norm_pow]
    have hc : ‖4*Real.pi‖ ≤ (16:ℝ) := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith [Real.pi_lt_four]
    calc
      _ ≤ 16^k * 1 := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hc _) (trig_iterated_bound k _).2
        (norm_nonneg _) (by positivity)
      _ ≤ (16^n:ℕ) := by simp only [mul_one, Nat.cast_pow, Nat.cast_ofNat]; exact pow_le_pow_right₀ (by norm_num) hk

end Quantitative

end
end PeriodicLattice

end OAI
