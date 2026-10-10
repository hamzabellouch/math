import OAI.Analysis.Littlewood.Rounding

namespace OAI

universe uE uX

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma integral_circle_fourier (n : ℤ) :
    (∫ x : UnitAddCircle, fourier n x) = if n=0 then 1 else 0 := by
  have hh := congrFun (fourierCoeff_fourier (T := (1:ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using! hh

def cosine (x : UnitAddCircle) : ℝ := (fourier 1 x).re

@[fun_prop] lemma cosine_continuous : Continuous cosine := Complex.continuous_re.comp (fourier 1).continuous

lemma cosine_abs_le (x : UnitAddCircle) : |cosine x| ≤ 1 := by
  simpa only [cosine, fourier_apply, Circle.norm_coe] using Complex.abs_re_le_norm (fourier 1 x)

lemma cosine_cast (x : UnitAddCircle) :
    (cosine x : ℂ) = (fourier 1 x + fourier (-1) x)/2 := by
  rw [fourier_neg]
  apply Complex.ext <;> simp [cosine]

lemma integral_cosine : (∫ x : UnitAddCircle, cosine x) = 0 := by
  have hi : Integrable (fun x : UnitAddCircle ↦ fourier 1 x) := (fourier 1).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x : UnitAddCircle, (fourier 1 x).re) = 0
  have hr : (∫ x : UnitAddCircle, (fourier 1 x).re) = (∫ x : UnitAddCircle, fourier 1 x).re := by
    simpa using! integral_re hi
  rw [hr, integral_circle_fourier]
  norm_num

lemma integral_cosine_sq : (∫ x : UnitAddCircle, cosine x ^ 2) = 1/2 := by
  have hp (x : UnitAddCircle) : ((cosine x ^ 2 : ℝ) : ℂ) =
      (fourier 2 x + 2 + fourier (-2) x)/4 := by
    rw [Complex.ofReal_pow, cosine_cast, div_pow, add_sq]
    have h1 : fourier (1:ℤ) x * fourier 1 x = fourier 2 x := by
      rw [← fourier_add]; norm_num
    have h2 : fourier (-1:ℤ) x * fourier (-1) x = fourier (-2) x := by
      rw [← fourier_add]; norm_num
    have h3 : fourier (1:ℤ) x * fourier (-1) x = 1 := by rw [← fourier_add]; norm_num
    rw [pow_two, pow_two, h1, h2]
    calc
      _ = (fourier 2 x + 2*(fourier 1 x*fourier (-1) x) + fourier (-2) x)/4 := by ring
      _ = _ := by rw [h3]; ring
  have hh : ((∫ x : UnitAddCircle, cosine x ^ 2 : ℝ) : ℂ) = (1/2:ℂ) := by
    have hr : (∫ x : UnitAddCircle, ((cosine x ^ 2 : ℝ) : ℂ)) =
        ((∫ x : UnitAddCircle, cosine x^2 : ℝ) : ℂ) := by
      simpa using! (integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure UnitAddCircle)) (f := fun x : UnitAddCircle ↦ cosine x^(2:ℕ)))
    rw [← hr]
    simp_rw [hp]
    rw [integral_div, integral_add, integral_add, integral_circle_fourier,
      integral_circle_fourier, integral_const]
    · norm_num
    all_goals apply Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  have hr := congrArg Complex.re hh
  simpa using hr

lemma integral_pi_cons {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (n+1) → UnitAddCircle) → E) (hf : Integrable f) :
    (∫ x, f x) = ∫ u : UnitAddCircle, ∫ y : Fin n → UnitAddCircle, f (Fin.cons u y) := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ UnitAddCircle) 0).symm
  have hi := he.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr hf
  rw [← he.integral_comp' f]
  change (∫ z, f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ UnitAddCircle) 0).symm z) ∂(volume.prod volume)) = _
  have hp := integral_prod _ hi
  dsimp only [Function.comp_def] at hp
  rw [hp]
  congr 1
  ext u
  congr 1
  ext y
  congr 1
  ext i
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    ]

def binary : (n : ℕ) → (Fin n → UnitAddCircle) → ℝ
  | 0, _ => 0
  | n+1, x => binary n (Fin.tail x) + (1-binary n (Fin.tail x)^2)/2*cosine (x 0)

@[fun_prop] lemma binary_continuous (n : ℕ) : Continuous (binary n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have ht : Continuous (fun x : Fin (n+1) → UnitAddCircle ↦ Fin.tail x) := by fun_prop
      exact (ih.comp ht).add (((continuous_const.sub ((ih.comp ht).pow 2)).div_const 2).mul
        (cosine_continuous.comp (continuous_apply 0)))

lemma binary_abs_le (n : ℕ) (x : Fin n → UnitAddCircle) : |binary n x| ≤ 1 := by
  induction n with
  | zero => simp [binary]
  | succ n ih =>
      have hz := ih (Fin.tail x)
      have hc := cosine_abs_le (x 0)
      have hsq : binary n (Fin.tail x)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hz
      have hcoeff : 0 ≤ (1-binary n (Fin.tail x)^2)/2 := by linarith
      have hstep : (1-binary n (Fin.tail x)^2)/2 ≤ 1-|binary n (Fin.tail x)| := by
        nlinarith [sq_abs (binary n (Fin.tail x)), sq_nonneg (1-|binary n (Fin.tail x)|)]
      calc
        |binary (n+1) x| ≤ |binary n (Fin.tail x)| + |(1-binary n (Fin.tail x)^2)/2*cosine (x 0)| := abs_add_le _ _
        _ = |binary n (Fin.tail x)| + (1-binary n (Fin.tail x)^2)/2*|cosine (x 0)| := by rw [abs_mul, abs_of_nonneg hcoeff]
        _ ≤ |binary n (Fin.tail x)| + (1-binary n (Fin.tail x)^2)/2 := by nlinarith
        _ ≤ 1 := by linarith

lemma binary_cons (n : ℕ) (u : UnitAddCircle) (y : Fin n → UnitAddCircle) :
    binary (n+1) (Fin.cons u y) = binary n y+(1-binary n y^2)/2*cosine u := by
  simp [binary]

def energy (n : ℕ) : ℝ := ∫ x : Fin n → UnitAddCircle, binary n x^2

lemma energy_bounds (n : ℕ) : 0 ≤ energy n ∧ energy n ≤ 1 := by
  refine ⟨integral_nonneg (fun x ↦ sq_nonneg _), ?_⟩
  calc
    energy n ≤ ∫ _ : Fin n → UnitAddCircle, (1:ℝ) := by
      apply integral_mono (((binary_continuous n).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)
      intro x
      exact (sq_le_one_iff_abs_le_one _).mpr (binary_abs_le n x)
    _ = 1 := by simp

lemma integrable_cont {X : Type uX} {E : Type uE} [TopologicalSpace X] [MeasurableSpace X]
    [CompactSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {f : X → E} (h : Continuous f) :
    Integrable f μ := h.integrable_of_hasCompactSupport (.of_compactSpace _)

lemma integral_pi_cons_rev {n : ℕ} {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (Fin (n+1) → UnitAddCircle) → E) (hf : Continuous f) :
    (∫ x, f x) = ∫ y : Fin n → UnitAddCircle, ∫ u : UnitAddCircle, f (Fin.cons u y) := by
  rw [integral_pi_cons f (integrable_cont hf)]
  apply integral_integral_swap
  apply integrable_cont
  exact hf.comp (by fun_prop)

lemma integral_cosine_linear (a b : ℝ) :
    (∫ u : UnitAddCircle, a+b*cosine u) = a := by
  rw [integral_add (integrable_const _) ((integrable_cont cosine_continuous).const_mul _),
    integral_const_mul, integral_cosine]
  simp

lemma integral_cosine_square (a b : ℝ) :
    (∫ u : UnitAddCircle, (a+b*cosine u)^2) = a^2+b^2/2 := by
  have h (u : UnitAddCircle) : (a+b*cosine u)^2 = a^2+2*a*b*cosine u+b^2*cosine u^2 := by ring
  simp_rw [h]
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_cosine, integral_cosine_sq]
  · simp; ring
  all_goals apply integrable_cont; fun_prop

lemma binary_mean_zero (n : ℕ) : (∫ x : Fin n → UnitAddCircle, binary n x) = 0 := by
  induction n with
  | zero => simp [binary]
  | succ n ih =>
    rw [integral_pi_cons_rev _ (binary_continuous _)]
    simp_rw [binary_cons, integral_cosine_linear]
    exact ih

lemma energy_succ (n : ℕ) : energy (n+1) = energy n +
    (1/8)*∫ y : Fin n → UnitAddCircle, (1-binary n y^2)^2 := by
  unfold energy
  rw [integral_pi_cons_rev (fun x : Fin (n+1) → UnitAddCircle ↦ binary (n+1) x^2) (by fun_prop)]
  simp_rw [binary_cons, integral_cosine_square]
  have h (y : Fin n → UnitAddCircle) : binary n y^2+((1-binary n y^2)/2)^2/2 =
      binary n y^2+(1/8)*(1-binary n y^2)^2 := by ring
  simp_rw [h]
  rw [integral_add (integrable_cont (by fun_prop)) (integrable_cont (by fun_prop)), integral_const_mul]

lemma energy_increment (n : ℕ) : energy n+(1-energy n)^2/8 ≤ energy (n+1) := by
  have h0 : (0:ℝ) ≤ ∫ y : Fin n → UnitAddCircle, (energy n-binary n y^2)^2 :=
    integral_nonneg (fun y ↦ sq_nonneg (energy n-binary n y^2))
  have hpoint (y : Fin n → UnitAddCircle) : (energy n-binary n y^2)^2 =
      (1-binary n y^2)^2 + 2*(1-energy n)*binary n y^2 + (energy n^2-1) := by ring
  simp_rw [hpoint] at h0
  rw [integral_add, integral_add, integral_const_mul, integral_const] at h0
  · simp only [probReal_univ, smul_eq_mul, one_mul] at h0
    change 0 ≤ (∫ y : Fin n → UnitAddCircle, (1-binary n y^2)^2) +
      2*(1-energy n)*energy n+(energy n^2-1) at h0
    rw [energy_succ]
    nlinarith
  all_goals apply integrable_cont; fun_prop

lemma energy_monotone : Monotone energy := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_trans (by nlinarith [sq_nonneg (1-energy n)]) (energy_increment n)

lemma exists_binary_energy {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : ℕ, 2 ≤ d ∧ 1-δ ≤ energy d := by
  by_contra hc
  have hall : ∀ n : ℕ, energy n < 1-δ := by
    intro n
    have hm : energy (max 2 n) < 1-δ := by
      by_contra h
      exact hc ⟨max 2 n, le_max_left _ _, le_of_not_gt h⟩
    exact lt_of_le_of_lt (energy_monotone (le_max_right _ _)) hm
  have hgrowth : ∀ n : ℕ, (n:ℝ)*(δ^2/8) ≤ energy n := by
    intro n
    induction n with
    | zero => simpa using (energy_bounds 0).1
    | succ n ih =>
      have hi := energy_increment n
      have hb := hall n
      rw [Nat.cast_succ]
      nlinarith [sq_nonneg (1-energy n-δ)]
  obtain ⟨n,hn⟩ := exists_nat_gt (8/δ^2)
  have hpos : 0 < δ^2 := sq_pos_of_pos hδ
  have hnum : 1 < (n:ℝ)*(δ^2/8) := by
    have hh := (div_lt_iff₀ hpos).mp hn
    nlinarith
  linarith [hgrowth n, (energy_bounds n).2]

open UnitAddTorus

def primitive : (n : ℕ) → (Fin n → ℤ) → Prop
  | 0, _ => False
  | n+1, s => s 0 = 1 ∨ s 0 = -1 ∨ (s 0 = 0 ∧ primitive n (Fin.tail s))

def spectrumSpan {n : ℕ} (P : (Fin n → ℤ) → Prop) :
    Submodule ℂ ((Fin n → UnitAddCircle) → ℂ) :=
  Submodule.span ℂ ((fun s ↦ (mFourier s : (Fin n → UnitAddCircle) → ℂ)) '' {s | P s})

lemma spectrumSpan_mono {n : ℕ} {P Q : (Fin n → ℤ) → Prop} (h : ∀ s, P s → Q s) :
    spectrumSpan P ≤ spectrumSpan Q := by
  apply Submodule.span_mono
  rintro _ ⟨s,hs,rfl⟩
  exact ⟨s,h s hs,rfl⟩

lemma character_mem {n : ℕ} {P : (Fin n → ℤ) → Prop} {s : Fin n → ℤ} (h : P s) :
    (mFourier s : (Fin n → UnitAddCircle) → ℂ) ∈ spectrumSpan P :=
  Submodule.subset_span ⟨s,h,rfl⟩

lemma character_cons {n : ℕ} (k : ℤ) (s : Fin n → ℤ) (x : Fin (n+1) → UnitAddCircle) :
    mFourier (Fin.cons k s) x = fourier k (x 0)*mFourier s (Fin.tail x) := by
  simp [mFourier, Fin.prod_univ_succ, Fin.tail]

lemma spectrumSpan_lift {n : ℕ} {P : (Fin n → ℤ) → Prop}
    {Q : (Fin (n+1) → ℤ) → Prop} (k : ℤ)
    (h : ∀ s, P s → Q (Fin.cons k s)) {f : (Fin n → UnitAddCircle) → ℂ}
    (hf : f ∈ spectrumSpan P) :
    (fun x : Fin (n+1) → UnitAddCircle ↦ fourier k (x 0)*f (Fin.tail x)) ∈ spectrumSpan Q := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,hs,rfl⟩ := hf
    simpa only [← character_cons] using character_mem (h s hs)
  | zero =>
    simp only [Pi.zero_apply, mul_zero]
    exact (spectrumSpan Q).zero_mem
  | add f g hf hg ihf ihg =>
    convert (spectrumSpan Q).add_mem ihf ihg using 1
    ext x
    simp [mul_add]
  | smul a f hf ih =>
    convert (spectrumSpan Q).smul_mem a ih using 1
    ext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

lemma allSpectrum_mul {n : ℕ} {f g : (Fin n → UnitAddCircle) → ℂ}
    (hf : f ∈ spectrumSpan (fun _ ↦ True)) (hg : g ∈ spectrumSpan (fun _ ↦ True)) :
    f*g ∈ spectrumSpan (fun _ ↦ True) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,_,rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨t,_,rfl⟩ := hg
      convert character_mem (P := fun _ ↦ True) (s := s+t) trivial using 1
      ext x
      exact (mFourier_add).symm
    | zero => simp
    | add g h hg hh ihg ihh => simpa [mul_add] using (spectrumSpan (n := n) (fun _ ↦ True)).add_mem ihg ihh
    | smul a g hg ih => simpa [mul_smul_comm] using (spectrumSpan (n := n) (fun _ ↦ True)).smul_mem a ih
  | zero => simp
  | add f h hf hh ihf ihh => simpa [add_mul] using (spectrumSpan (n := n) (fun _ ↦ True)).add_mem ihf ihh
  | smul a f hf ih => simpa [smul_mul_assoc] using (spectrumSpan (n := n) (fun _ ↦ True)).smul_mem a ih

lemma allSpectrum_one (n : ℕ) : (1 : (Fin n → UnitAddCircle) → ℂ) ∈ spectrumSpan (fun _ ↦ True) := by
  simpa only [mFourier_zero, ContinuousMap.coe_one] using
    character_mem (P := fun _ ↦ True) (s := (0 : Fin n → ℤ)) trivial

lemma binary_spectrum (n : ℕ) :
    (fun x : Fin n → UnitAddCircle ↦ (binary n x : ℂ)) ∈ spectrumSpan (primitive n) := by
  induction n with
  | zero =>
    simp only [binary, Complex.ofReal_zero]
    exact (spectrumSpan (primitive 0)).zero_mem
  | succ n ih =>
    have ho := spectrumSpan_lift (Q := primitive (n+1)) 0
      (fun s hs ↦ by simp [primitive, hs]) ih
    have ha := spectrumSpan_mono (Q := fun _ ↦ True) (fun _ _ ↦ trivial) ih
    have hn := (spectrumSpan (n := n) (fun _ ↦ True)).sub_mem (allSpectrum_one n) (allSpectrum_mul ha ha)
    have hp := spectrumSpan_lift (Q := primitive (n+1)) 1 (fun s hs ↦ by simp [primitive]) hn
    have hm := spectrumSpan_lift (Q := primitive (n+1)) (-1) (fun s hs ↦ by simp [primitive]) hn
    convert (spectrumSpan (primitive (n+1))).add_mem ho
      ((spectrumSpan (primitive (n+1))).smul_mem (1/4:ℂ)
        ((spectrumSpan (primitive (n+1))).add_mem hp hm)) using 1
    ext x
    simp only [binary, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_ofNat,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.one_apply, Pi.smul_apply, fourier_zero,
      one_mul, smul_eq_mul, cosine_cast]
    ring

lemma primitive_ne_zero {n : ℕ} {s : Fin n → ℤ} (h : primitive n s) : s ≠ 0 := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    intro hs
    subst hs
    simp only [primitive, Pi.zero_apply, zero_ne_one, false_or] at h
    rcases h with h | ⟨_,h⟩
    · norm_num at h
    · exact ih h rfl

lemma primitive_neg {n : ℕ} {s : Fin n → ℤ} (h : primitive n s) : primitive n (-s) := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    rcases h with h | h | ⟨h,hs⟩
    · exact Or.inr (Or.inl (by simp [h]))
    · exact Or.inl (by simp [h])
    · exact Or.inr (Or.inr ⟨by simp [h], by change primitive n (-Fin.tail s); exact ih hs⟩)

lemma primitive_parallel_scalar {n : ℕ} {s t : Fin n → ℤ}
    (hs : primitive n s) (ht : primitive n t) {c : ℝ}
    (he : ∀ i, (s i : ℝ) = c*(t i : ℝ)) : c=1 ∨ c = -1 := by
  have hc : c ≠ 0 := by
    intro hc
    apply primitive_ne_zero hs
    ext i
    exact_mod_cast (by simpa [hc] using he i : (s i : ℝ) = 0)
  induction n with
  | zero => exact hs.elim
  | succ n ih =>
    by_cases ht0 : t 0 = 0
    · have hs0 : s 0 = 0 := by exact_mod_cast (by simpa [ht0] using he 0 : (s 0 : ℝ) = 0)
      have hs' : primitive n (Fin.tail s) := by simpa [primitive, hs0] using hs
      have ht' : primitive n (Fin.tail t) := by simpa [primitive, ht0] using ht
      exact ih hs' ht' (fun i ↦ he i.succ)
    · have hs0 : s 0 ≠ 0 := by
        intro hs0
        have hz := he 0
        rw [hs0, Int.cast_zero] at hz
        have htR : (t 0 : ℝ) ≠ 0 := by exact_mod_cast ht0
        exact (mul_ne_zero hc htR) hz.symm
      have htsign : t 0 = 1 ∨ t 0 = -1 := by
        rcases ht with h | h | ⟨h,_⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact (ht0 h).elim
      have hssign : s 0 = 1 ∨ s 0 = -1 := by
        rcases hs with h | h | ⟨h,_⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact (hs0 h).elim
      rcases htsign with h | h <;> rcases hssign with h' | h'
      all_goals have hz := he 0; norm_num [h,h'] at hz; first | left; linarith | right; linarith

lemma exists_binary_coefficients (n : ℕ) :
    ∃ c : (Fin n → ℤ) →₀ ℂ, (∀ s ∈ c.support, primitive n s) ∧
      ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x := by
  classical
  obtain ⟨c,hc,he⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp (binary_spectrum n)
  refine ⟨c, ?_, ?_⟩
  · exact fun s hs ↦ ((Finsupp.mem_supported ℂ c).mp hc) hs
  · intro x
    have hh := congrFun he x
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, smul_eq_mul] using hh.symm

lemma integral_character {n : ℕ} (s : Fin n → ℤ) :
    (∫ x : Fin n → UnitAddCircle, mFourier s x) = if s=0 then 1 else 0 := by
  classical
  simp only [mFourier, ContinuousMap.coe_mk, integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_circle_fourier]
  by_cases hs : s=0
  · simp [hs]
  · rw [ite_eq_right hs]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hs
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa using hi

lemma coeff_finite_sum {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (s : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ ∑ t ∈ c.support, c t*mFourier t x) s = c s := by
  classical
  unfold mFourierCoeff
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · have he (t : Fin n → ℤ) :
        (fun x : Fin n → UnitAddCircle ↦ mFourier (-s) x*(c t*mFourier t x)) =
        (fun x ↦ c t*mFourier (t-s) x) := by
      ext x
      rw [sub_eq_add_neg, mFourier_add]
      ring
    simp_rw [he, integral_const_mul, integral_character]
    have hz (t : Fin n → ℤ) : t-s=0 ↔ t=s := sub_eq_zero
    simp_rw [hz, mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_eq' _ _ _ |>.trans (by split_ifs with h <;> simp_all)
  · intro t ht
    apply integrable_cont
    fun_prop

lemma coeff_real_neg {n : ℕ} (f : (Fin n → UnitAddCircle) → ℝ) (s : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ (f x : ℂ)) (-s) = conj (mFourierCoeff (fun x ↦ (f x : ℂ)) s) := by
  unfold mFourierCoeff
  trans ∫ x : Fin n → UnitAddCircle, conj (mFourier (-s) x*(f x : ℂ))
  · apply integral_congr_ae
    filter_upwards [] with x
    simp [mFourier_neg]
  · simpa only [smul_eq_mul] using! integral_conj

lemma parseval_continuous {n : ℕ} (f : C((Fin n → UnitAddCircle), ℂ)) :
    HasSum (fun s ↦ ‖mFourierCoeff f s‖^2) (∫ x, ‖f x‖^2) := by
  have hh := hasSum_sq_mFourierCoeff (f.toLp 2 volume ℂ)
  simp only [mFourierCoeff_toLp] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) volume] with x hx
  rw [hx]

lemma binary_coefficients_energy {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) :
    (∑ s ∈ c.support, ‖c s‖^2) = energy n := by
  classical
  let f : C((Fin n → UnitAddCircle),ℂ) := ⟨fun x ↦ (binary n x : ℂ), by fun_prop⟩
  have hf : ∀ s, mFourierCoeff f s = c s := by
    intro s
    convert coeff_finite_sum c s using 1
    exact congrArg (fun g ↦ mFourierCoeff g s) (funext he)
  have hh := parseval_continuous f
  simp_rw [hf] at hh
  have he' : (∫ x, ‖f x‖^2) = energy n := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [f, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [he'] at hh
  have hs : HasSum (fun s ↦ ‖c s‖^2) (∑ s ∈ c.support, ‖c s‖^2) :=
    hasSum_sum_of_ne_finset_zero (fun s hs ↦ by simp [Finsupp.notMem_support_iff.mp hs])
  exact hs.unique hh

def positive : (n : ℕ) → (Fin n → ℤ) → Prop
  | 0, _ => False
  | n+1, s => s 0=1 ∨ (s 0=0 ∧ positive n (Fin.tail s))

lemma positive_primitive {n : ℕ} {s : Fin n → ℤ} (h : positive n s) :
    primitive n s := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    rcases h with h | ⟨h,ht⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h,ih ht⟩)

lemma positive_not_neg {n : ℕ} {s : Fin n → ℤ} (h : positive n s) :
    ¬ positive n (-s) := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    intro hn
    rcases h with h | ⟨h,ht⟩ <;> rcases hn with hn | ⟨hn,hnt⟩
    · simp [h] at hn
    · simp [h] at hn
    · simp [h] at hn
    · exact ih ht hnt

lemma primitive_positive_or_neg {n : ℕ} {s : Fin n → ℤ} (h : primitive n s) :
    positive n s ∨ positive n (-s) := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    rcases h with h | h | ⟨h,ht⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (by simp [h]))
    · rcases ih ht with hp | hp
      · exact Or.inl (Or.inr ⟨h,hp⟩)
      · exact Or.inr (Or.inr ⟨by simp [h],hp⟩)

lemma positive_parallel_eq {n : ℕ} {s t : Fin n → ℤ}
    (hs : positive n s) (ht : positive n t) {c : ℝ}
    (he : ∀ i, (s i : ℝ) = c*(t i : ℝ)) : s=t ∧ c=1 := by
  rcases primitive_parallel_scalar (positive_primitive hs) (positive_primitive ht) he with hc | hc
  · refine ⟨?_,hc⟩
    ext i
    exact_mod_cast (by simpa [hc] using he i : (s i : ℝ)=(t i : ℝ))
  · have hh : s = -t := by
      ext i
      exact_mod_cast (by simpa [hc] using he i : (s i : ℝ) = -(t i : ℝ))
    exact (positive_not_neg ht (hh ▸ hs)).elim

lemma binary_coefficients_conj {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) (s : Fin n → ℤ) :
    c (-s) = conj (c s) := by
  have hf (t : Fin n → ℤ) : mFourierCoeff (fun x ↦ (binary n x : ℂ)) t = c t := by
    convert coeff_finite_sum c t using 1
    exact congrArg (fun g ↦ mFourierCoeff g t) (funext he)
  simpa only [hf] using coeff_real_neg (binary n) s

lemma binary_support_neg {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) (s : Fin n → ℤ) :
    -s ∈ c.support ↔ s ∈ c.support := by
  simp only [Finsupp.mem_support_iff, binary_coefficients_conj c he, map_ne_zero]

lemma coefficient_support_pairs {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (hp : ∀ s ∈ c.support, primitive n s)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) :
    ∃ S : Finset (Fin n → ℤ), (∀ s ∈ S, positive n s) ∧
      ∀ s, s ∈ c.support ↔ s ∈ S ∨ -s ∈ S := by
  classical
  refine ⟨c.support.filter (positive n),?_,?_⟩
  · exact fun s hs ↦ (Finset.mem_filter.mp hs).2
  · intro s
    simp only [Finset.mem_filter, binary_support_neg c he, ← and_or_left]
    exact ⟨fun hs ↦ ⟨hs,primitive_positive_or_neg (hp s hs)⟩,fun h ↦ h.1⟩

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

end OAI
