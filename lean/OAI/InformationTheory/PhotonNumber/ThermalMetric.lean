import OAI.InformationTheory.PhotonNumber.Gibbs
import OAI.Analysis.DiagonalForms

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace ThermalMetric

section
open EntropyPhotonNumber DiagonalForms.System

def h (r : ℝ) : ℝ := Real.log (r+1)-Real.log r

theorem h_pos {r : ℝ} (hr : 0<r) : 0<h r :=
  sub_pos.mpr (Real.strictMonoOn_log hr (show 0<r+1 by linarith) (by linarith))

def frequency (r p q : ℝ) : ℝ := (Real.log p-Real.log q)/h r

def weight (r v : ℝ) : ℝ := fourWeightTarget (1/h r) (h r*v/2) (-h r/2)

theorem logMean_reference {r : ℝ} (_hr : 0<r) : logMean r (r+1)=1/h r := by
  rw [logMean, ite_eq_right (by linarith : r≠r+1)]
  unfold h
  congr 1
  ring

theorem weight_pos {r : ℝ} (hr : 0<r) (v : ℝ) : 0<weight r v :=
  fourWeightTarget_pos (div_pos (by norm_num) (h_pos hr)) _ _

theorem tilted_logMean {r p q : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q) :
    logMean p q*weight r (frequency r p q)=logMean (r*p) ((r+1)*q) := by
  rw [weight, frequency, mul_div_cancel₀ _ (h_pos hr).ne', ← logMean_reference hr]
  have he : -h r/2=(Real.log r-Real.log (r+1))/2 := by unfold h; ring
  rw [he]
  simpa only [mul_comm r p, mul_comm (r+1) q] using (logMean_product hp hq hr (by positivity)).symm

theorem weight_frequency_bounds {r p q : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q) :
    r≤weight r (frequency r p q) ∧ weight r (frequency r p q)≤r+1 := by
  have h₁ := logMean_mono (mul_pos hr hp) (mul_pos hr hq) le_rfl
    (mul_le_mul_of_nonneg_right (by linarith : r≤r+1) hq.le)
  have h₂ := logMean_mono (mul_pos hr hp) (mul_pos (by positivity : 0<r+1) hq)
    (mul_le_mul_of_nonneg_right (by linarith : r≤r+1) hp.le) le_rfl
  rw [logMean_scale hp hq hr, ← tilted_logMean hr hp hq] at h₁
  rw [logMean_scale hp hq (by positivity : 0<r+1), ← tilted_logMean hr hp hq] at h₂
  have hl := logMean_pos hp hq
  constructor <;> nlinarith

end

section
open DiagonalForms.System

theorem logMean_mul_log_sub {p q : ℝ} (hp : 0<p) (hq : 0<q) :
    logMean p q*(Real.log q-Real.log p)=q-p := by
  by_cases he : p=q
  · subst q; simp
  · rw [logMean, ite_eq_right he]
    apply div_mul_cancel₀
    intro h
    apply he
    exact Real.log_injOn_pos hp hq (sub_eq_zero.mp h).symm

def defectCoefficient (r p q : ℝ) : ℝ := (r+1)*q-r*p

def metricCoefficient (r p q : ℝ) : ℝ :=
  h r*logMean p q*weight r (frequency r p q)

theorem metricCoefficient_pos {r p q : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q) :
    0 < metricCoefficient r p q :=
  mul_pos (mul_pos (h_pos hr) (logMean_pos hp hq)) (weight_pos hr _)

theorem defect_multiplier {r p q : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q) :
    defectCoefficient r p q = (1-frequency r p q)*metricCoefficient r p q := by
  have ht := tilted_logMean hr hp hq
  have hl := logMean_mul_log_sub (mul_pos hr hp) (mul_pos (by positivity : 0<r+1) hq)
  rw [Real.log_mul (by positivity : r+1≠0) hq.ne', Real.log_mul hr.ne' hp.ne'] at hl
  rw [← ht] at hl
  unfold defectCoefficient metricCoefficient frequency h at *
  have hh : Real.log (r+1)-Real.log r≠0 := (h_pos hr).ne'
  field_simp
  linear_combination -hl

theorem defect_dual_square {r p q : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q) :
    (defectCoefficient r p q)^2/metricCoefficient r p q =
      (1-frequency r p q)*defectCoefficient r p q := by
  rw [defect_multiplier hr hp hq]
  field_simp [(metricCoefficient_pos hr hp hq).ne']

end

section
open EntropyPhotonNumber
variable {J : Type*}

def weightedVector (a : J → ℝ) (z : J → ℂ)
    (hz : Summable (fun j => a j*‖z j‖^2)) (ha : ∀ j, 0 ≤ a j) :
    lp (fun _ : J => ℂ) 2 := by
  refine ⟨fun j => (Real.sqrt (a j):ℂ)*z j, ?_⟩
  apply memℓp_gen
  convert! hz using 1
  funext j
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (ha j)]

@[simp] theorem weightedVector_apply (a : J → ℝ) (z : J → ℂ)
    (hz : Summable (fun j => a j*‖z j‖^2)) (ha : ∀ j, 0 ≤ a j) (j : J) :
    weightedVector a z hz ha j=(Real.sqrt (a j):ℂ)*z j := rfl

theorem weightedVector_norm_sq (a : J → ℝ) (z : J → ℂ)
    (hz : Summable (fun j => a j*‖z j‖^2)) (ha : ∀ j, 0 ≤ a j) :
    ‖weightedVector a z hz ha‖^2=∑' j, a j*‖z j‖^2 := by
  have hh := lp.hasSum_norm (p := 2) (by norm_num : 0 < (2:ENNReal).toReal) (weightedVector a z hz ha)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, weightedVector_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (ha _)] using hh.tsum_eq.symm

theorem defectVector_entry_norm (r p q : ℝ) (hr : 0<r) (hp : 0<p) (hq : 0<q) (d : ℂ) :
    ‖((defectCoefficient r p q / Real.sqrt (metricCoefficient r p q):ℝ):ℂ)*d‖^2 =
      (1-frequency r p q)*defectCoefficient r p q*‖d‖^2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (metricCoefficient_pos hr hp hq).le, defect_dual_square hr hp hq]

def defectVector (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ)
    (hd : Summable (fun a : J × J =>
      (1-frequency r (p a.1) (p a.2))*defectCoefficient r (p a.1) (p a.2)*‖d a‖^2)) :
    lp (fun _ : J × J => ℂ) 2 := by
  refine ⟨fun a => ((defectCoefficient r (p a.1) (p a.2) /
    Real.sqrt (metricCoefficient r (p a.1) (p a.2)):ℝ):ℂ)*d a, ?_⟩
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    defectVector_entry_norm r _ _ hr (hp _) (hp _)] using hd

@[simp] theorem defectVector_apply (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) (a : J × J) :
    defectVector r hr p hp d hd a=((defectCoefficient r (p a.1) (p a.2) /
      Real.sqrt (metricCoefficient r (p a.1) (p a.2)):ℝ):ℂ)*d a := rfl

theorem defectVector_norm_sq (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) :
    ‖defectVector r hr p hp d hd‖^2=∑' a : J × J,
      (1-frequency r (p a.1) (p a.2))*defectCoefficient r (p a.1) (p a.2)*‖d a‖^2 := by
  have hh := lp.hasSum_norm (p := 2) (by norm_num : 0 < (2:ENNReal).toReal) (defectVector r hr p hp d hd)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, defectVector_apply,
    defectVector_entry_norm r _ _ hr (hp _) (hp _)] using hh.tsum_eq.symm

theorem defectVector_pairing (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) (z : J × J → ℂ)
    (hz : Summable (fun a : J × J => metricCoefficient r (p a.1) (p a.2)*‖z a‖^2)) :
    HasSum (fun a : J × J => (defectCoefficient r (p a.1) (p a.2):ℂ)*conj (d a)*z a)
      (inner ℂ (defectVector r hr p hp d hd)
        (weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) z hz
          (fun a => (metricCoefficient_pos hr (hp a.1) (hp a.2)).le))) := by
  have hh := lp.hasSum_inner (𝕜 := ℂ) (defectVector r hr p hp d hd)
    (weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) z hz
      (fun a => (metricCoefficient_pos hr (hp a.1) (hp a.2)).le))
  convert! hh using 1
  ext a
  simp only [defectVector_apply, weightedVector_apply, RCLike.inner_apply,
    map_mul, Complex.ofReal_div, map_div₀, Complex.conj_ofReal]
  have hn : (Real.sqrt (metricCoefficient r (p a.1) (p a.2)):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (metricCoefficient_pos hr (hp a.1) (hp a.2))).ne'
  field_simp

end

section
variable {J : Type*}

def defectFunctional (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ)
    (hd : Summable (fun a : J × J =>
      (1-frequency r (p a.1) (p a.2))*defectCoefficient r (p a.1) (p a.2)*‖d a‖^2)) :
    lp (fun _ : J × J => ℂ) 2 →L[ℂ] ℂ :=
  innerSL ℂ (defectVector r hr p hp d hd)

theorem defectFunctional_norm_sq (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) :
    ‖defectFunctional r hr p hp d hd‖^2=∑' a : J × J,
      (1-frequency r (p a.1) (p a.2))*defectCoefficient r (p a.1) (p a.2)*‖d a‖^2 := by
  rw [defectFunctional, innerSL_apply_norm, defectVector_norm_sq]

theorem defectFunctional_restrict_norm (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) (P : Submodule ℂ (lp (fun _ : J × J => ℂ) 2))
    (hv : defectVector r hr p hp d hd ∈ P) :
    ‖(defectFunctional r hr p hp d hd).comp P.subtypeL‖=
      ‖defectFunctional r hr p hp d hd‖ := by
  have he : (defectFunctional r hr p hp d hd).comp P.subtypeL =
      innerSL ℂ (⟨defectVector r hr p hp d hd,hv⟩ : P) := by
    ext z
    rfl
  rw [he, innerSL_apply_norm, defectFunctional, innerSL_apply_norm]
  rfl
end

open scoped ComplexConjugate
variable {J : Type*}

@[simp] theorem metricCoefficient_self {r p : ℝ} (hr : 0<r) (hp : 0<p) :
    metricCoefficient r p p=p := by
  have hh := defect_multiplier hr hp hp
  simp only [frequency, sub_self, zero_div, sub_zero, one_mul, defectCoefficient] at hh
  nlinarith

theorem hasSum_diagonal [DecidableEq J] {f : J → ℂ} {s : ℂ} (hf : HasSum f s) :
    HasSum (fun a : J × J => if a.1=a.2 then f a.1 else 0) s := by
  have hi : Function.Injective (fun j : J => (j,j)) := fun _ _ he => (Prod.mk.inj he).1
  apply (hi.hasSum_iff (fun a ha => ?_)).mp
  · simpa only [Function.comp_def, ↓reduceIte] using hf
  · have hn : a.1≠a.2 := by
      intro he
      apply ha
      exact ⟨a.1, Prod.ext rfl he⟩
    simp only [hn, ↓reduceIte]

theorem summable_diagonal [DecidableEq J] {f : J → ℝ} (hf : Summable f) :
    Summable (fun a : J × J => if a.1=a.2 then f a.1 else 0) := by
  have hi : Function.Injective (fun j : J => (j,j)) := fun _ _ he => (Prod.mk.inj he).1
  apply (hi.summable_iff (fun a ha => ?_)).mp
  · simpa only [Function.comp_def, ↓reduceIte] using hf
  · have hn : a.1≠a.2 := by
      intro he
      exact ha ⟨a.1, Prod.ext rfl he⟩
    simp only [hn, ↓reduceIte]

def identityEntry (a : J × J) : ℂ := by
  classical
  exact if a.1=a.2 then 1 else 0

theorem identityEntry_summable (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) :
    Summable (fun a : J × J => metricCoefficient r (p a.1) (p a.2)*‖identityEntry a‖^2) := by
  classical
  convert! summable_diagonal hs using 1
  ext a
  by_cases he : a.1=a.2
  · simp only [identityEntry, he, ↓reduceIte, norm_one, one_pow, mul_one,
      metricCoefficient_self hr (hp _)]
  · simp only [identityEntry, he, ↓reduceIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero]

def identityVector (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j) (hs : Summable p) :
    lp (fun _ : J × J => ℂ) 2 :=
  weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) identityEntry
    (identityEntry_summable r hr p hp hs) (fun _a => (metricCoefficient_pos hr (hp _) (hp _)).le)

def centeredSpace (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j) (hs : Summable p) :
    Submodule ℂ (lp (fun _ : J × J => ℂ) 2) :=
  (innerSL ℂ (identityVector r hr p hp hs)).ker

theorem defectVector_mem_centeredSpace (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (d : J × J → ℂ) (hd)
    (hc : HasSum (fun j => (p j:ℂ)*d (j,j)) 0) :
    defectVector r hr p hp d hd ∈ centeredSpace r hr p hp hs := by
  classical
  have ht := hasSum_diagonal (Complex.hasSum_conj'.mpr hc)
  have hz : HasSum (fun a : J × J => (defectCoefficient r (p a.1) (p a.2):ℂ)*
      conj (d a)*identityEntry a) 0 := by
    convert! ht using 1
    · ext a
      by_cases he : a.1=a.2
      · obtain ⟨l,q⟩ := a
        dsimp only [Prod.fst, Prod.snd] at he ⊢
        subst q
        simp only [identityEntry, ↓reduceIte, mul_one, map_mul, Complex.conj_ofReal]
        congr 1
        unfold defectCoefficient
        push_cast
        ring
      · simp only [identityEntry, he, ↓reduceIte, mul_zero]
    · simp
  have hh := defectVector_pairing r hr p hp d hd identityEntry (identityEntry_summable r hr p hp hs)
  have he : inner ℂ (defectVector r hr p hp d hd) (identityVector r hr p hp hs)=0 := hh.unique hz
  change inner ℂ (identityVector r hr p hp hs) (defectVector r hr p hp d hd)=0
  rw [← inner_conj_symm, he, map_zero]

theorem centered_defect_norm_sq (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (d : J × J → ℂ) (hd)
    (hc : HasSum (fun j => (p j:ℂ)*d (j,j)) 0) :
    ‖(defectFunctional r hr p hp d hd).comp (centeredSpace r hr p hp hs).subtypeL‖^2=
      ∑' a : J × J, (1-frequency r (p a.1) (p a.2))*defectCoefficient r (p a.1) (p a.2)*‖d a‖^2 := by
  rw [defectFunctional_restrict_norm r hr p hp d hd _
    (defectVector_mem_centeredSpace r hr p hp hs d hd hc), defectFunctional_norm_sq]

theorem defect_series_summable (t : ℝ) (p : J → ℝ) (c : J → ℝ)
    (hc : ∀ j, c j = -Real.log (p j)) (d : J × J → ℂ)
    (h₁ : Summable (fun a : J × J => p a.2*‖d a‖^2))
    (h₂ : Summable (fun a : J × J => p a.1*‖d a‖^2))
    (h₃ : Summable (fun a : J × J => c a.1*p a.2*‖d a‖^2))
    (h₄ : Summable (fun a : J × J => c a.2*p a.2*‖d a‖^2))
    (h₅ : Summable (fun a : J × J => c a.1*p a.1*‖d a‖^2))
    (h₆ : Summable (fun a : J × J => c a.2*p a.1*‖d a‖^2)) :
    Summable (fun a : J × J => (1-frequency t (p a.1) (p a.2))*
      defectCoefficient t (p a.1) (p a.2)*‖d a‖^2) := by
  convert! ((h₁.mul_left (t+1)).sub (h₂.mul_left t)).add
    ((((h₃.sub h₄).mul_left (t+1)).sub ((h₅.sub h₆).mul_left t)).div_const (h t)) using 1
  ext a
  simp only [hc, frequency, defectCoefficient]
  ring

theorem coefficient_series_summable (t : ℝ) (p : J → ℝ) (d : J × J → ℂ)
    (h₁ : Summable (fun a : J × J => p a.2*‖d a‖^2))
    (h₂ : Summable (fun a : J × J => p a.1*‖d a‖^2)) :
    Summable (fun a : J × J => defectCoefficient t (p a.1) (p a.2)*‖d a‖^2) := by
  convert! (h₁.mul_left (t+1)).sub (h₂.mul_left t) using 1
  ext a
  simp only [defectCoefficient]
  ring

theorem production_series_subtraction (t : ℝ) (p : J → ℝ) (c : J → ℝ)
    (hc : ∀ j, c j = -Real.log (p j)) (d : J × J → ℂ)
    (hd : Summable (fun a : J × J => (1-frequency t (p a.1) (p a.2))*
      defectCoefficient t (p a.1) (p a.2)*‖d a‖^2))
    (hk : Summable (fun a : J × J => defectCoefficient t (p a.1) (p a.2)*‖d a‖^2)) :
    (∑' a : J × J, (c a.1-c a.2)*defectCoefficient t (p a.1) (p a.2)*‖d a‖^2)/h t =
      (∑' a : J × J, (1-frequency t (p a.1) (p a.2))*
        defectCoefficient t (p a.1) (p a.2)*‖d a‖^2)-
      (∑' a : J × J, defectCoefficient t (p a.1) (p a.2)*‖d a‖^2) := by
  rw [← tsum_div_const, ← hd.tsum_sub hk]
  apply tsum_congr
  intro a
  simp only [hc, frequency]
  ring

theorem diagonal_mean_summable (p : J → ℝ) (hp : ∀ j, 0≤p j) (hs : Summable p)
    (d : J × J → ℂ) (hd : Summable (fun a : J × J => p a.2*‖d a‖^2)) :
    Summable (fun j => (p j:ℂ)*d (j,j)) := by
  have hi : Function.Injective (fun j : J => (j,j)) := fun _ _ he => (Prod.mk.inj he).1
  have hh := hd.comp_injective hi
  apply Summable.of_norm_bounded (hh.add hs)
  intro j
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
  have hn : ‖d (j,j)‖≤‖d (j,j)‖^2+1 := by nlinarith [sq_nonneg (‖d (j,j)‖-1)]
  simpa only [mul_add, mul_one, Function.comp_apply] using mul_le_mul_of_nonneg_left hn (hp j)

def diagonalMean (p : J → ℝ) (d : J × J → ℂ) : ℂ := ∑' j, (p j:ℂ)*d (j,j)

theorem diagonal_centering (p : J → ℝ) (hs : HasSum p 1)
    (d : J × J → ℂ) (hd : Summable (fun j => (p j:ℂ)*d (j,j))) :
    HasSum (fun j => (p j:ℂ)*(d (j,j)-diagonalMean p d)) 0 := by
  have hh := hd.hasSum.sub ((Complex.hasSum_ofReal.mpr hs).mul_right (diagonalMean p d))
  simpa only [diagonalMean, Complex.ofReal_one, one_mul, sub_self, mul_sub] using hh

end ThermalMetric

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

def centeredEntry (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (x : J → Fock n)
    (j : Fin n) (μ : ℂ) (l r : J) : ℂ := by
  classical
  exact loweringEntry b p x j l r - if l=r then μ else 0

theorem nonlog_summable (b : HilbertBasis J ℂ (Fock n))
    (x : J → Fock n) (hx : Summable (fun r => ‖x r‖^2)) (j : Fin n) (u : Bool) :
    Summable (fun a : J × J => ‖spectralGain b x j u a.1 a.2‖^2) := by
  have hs := CrossEnsemble.applied_summable hx (unweightedGain j u ∘L inverseWeight 2)
  have hh := CrossEnsemble.square_coordinates_summable b hs
  simpa only [spectralGain, ContinuousLinearMap.comp_apply, Prod.swap] using hh.prod_symm

theorem centered_weight_summable [DecidableEq J] (f : J × J → ℝ) (hf : ∀ a, 0 ≤ f a)
    (d : J × J → ℂ) (hd : Summable (fun a => f a*‖d a‖^2))
    (hdiag : Summable (fun j => f (j,j))) (μ : ℂ) :
    Summable (fun a : J × J => f a*‖d a-(if a.1=a.2 then μ else 0)‖^2) := by
  classical
  have ht : Summable (fun a : J × J => if a.1=a.2 then f a*‖μ‖^2 else 0) := by
    apply (summable_prod_of_nonneg (by intro a; dsimp only; split_ifs; exact mul_nonneg (hf a) (sq_nonneg _); exact le_rfl)).mpr
    refine ⟨?_, ?_⟩
    · intro l
      have hh := (hasSum_ite_eq' l (f (l,l)*‖μ‖^2)).summable
      convert! hh using 1
      ext q
      by_cases h : l=q
      · subst q; rfl
      · simp only [h, ↓reduceIte]
    · simpa only [tsum_ite_eq'] using hdiag.mul_right (‖μ‖^2)
  apply Summable.of_nonneg_of_le (fun a => mul_nonneg (hf a) (sq_nonneg _)) _
    ((hd.mul_left 2).add (ht.mul_left 2))
  intro a
  by_cases he : a.1=a.2
  · simp only [he, ↓reduceIte]
    have hn := norm_sub_le (d a) μ
    have hsq : ‖d a-μ‖^2 ≤ 2*‖d a‖^2+2*‖μ‖^2 := by
      nlinarith [sq_nonneg (‖d a‖-‖μ‖), norm_nonneg (d a-μ), norm_nonneg (d a), norm_nonneg μ]
    nlinarith [mul_le_mul_of_nonneg_left hsq (hf a)]
  · simp only [he, ↓reduceIte, sub_zero, mul_zero, add_zero]
    nlinarith [mul_nonneg (hf a) (sq_nonneg ‖d a‖)]

theorem entropy_weight_summable (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (S : Fock n →L[ℂ] Fock n) (c : J → ℝ)
    (he : ∀ r, S (inverseWeight 1 (x r)) = (c r : ℂ) • inverseWeight 5 (x r)) :
    Summable (fun r => c r*p r) := by
  have hs := CrossEnsemble.applied_summable hx (inverseWeight 1)
  have ht := (CrossEnsemble.pairing_summable hs hs S).hasSum.mapL Complex.reCLM
  convert! ht.summable using 1
  ext r
  simp only [Complex.reCLM_apply, he, inner_smul_right]
  have hw : inner ℂ (inverseWeight 1 (x r)) (inverseWeight 5 (x r))=
      inner ℂ (inverseWeight 3 (x r)) (inverseWeight 3 (x r)) := by
    have h5 : inverseWeight 5 (x r)=inverseWeight 2 (inverseWeight 3 (x r)) := by
      exact congrArg (fun T : Fock n →L[ℂ] Fock n => T (x r)) (inverseWeight_add 2 3)
    rw [h5]
    calc
      _ = inner ℂ (inverseWeight 2 (inverseWeight 1 (x r))) (inverseWeight 3 (x r)) :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint 2)
          (inverseWeight 1 (x r)) (inverseWeight 3 (x r))).symm
      _ = _ := by
        congr 1
        change (inverseWeight 2 ∘L inverseWeight 1) (x r)=_
        rw [← inverseWeight_add]
  rw [hw, hi, inner_self_eq_norm_sq_to_K, norm_smul, b.orthonormal.norm_eq_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  norm_cast
  rw [Real.sq_sqrt (hp r).le]
  simp

theorem centered_six_sums (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (hs : Summable p) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (S : Fock n →L[ℂ] Fock n) (hS : S.IsSymmetric) (c : J → ℝ)
    (hc : ∀ l, 0 ≤ c l)
    (hf : ∀ y, HasSum (fun l => c l*‖inner ℂ (b l) (inverseWeight 2 y)‖^2)
      (inner ℂ y (S y)).re)
    (he : ∀ r, S (inverseWeight 1 (x r)) = (c r : ℂ) • inverseWeight 5 (x r))
    (j : Fin n) (μ : ℂ) :
    Summable (fun a : J × J => p a.2*‖centeredEntry b p x j μ a.1 a.2‖^2) ∧
    Summable (fun a : J × J => p a.1*‖centeredEntry b p x j μ a.1 a.2‖^2) ∧
    Summable (fun a : J × J => c a.1*p a.2*‖centeredEntry b p x j μ a.1 a.2‖^2) ∧
    Summable (fun a : J × J => c a.2*p a.2*‖centeredEntry b p x j μ a.1 a.2‖^2) ∧
    Summable (fun a : J × J => c a.1*p a.1*‖centeredEntry b p x j μ a.1 a.2‖^2) ∧
    Summable (fun a : J × J => c a.2*p a.1*‖centeredEntry b p x j μ a.1 a.2‖^2) := by
  classical
  have hec := entropy_weight_summable b p hp x hx hi S c he
  have hd := nonlog_summable b x hx j false
  have hu := (nonlog_summable b x hx j true).prod_symm
  have hcd := crossed_log_summable b x hx S c hc hf j false
  have hud := uncrossed_log_summable b x hx S hS c hc he j false
  have hcu := (crossed_log_summable b x hx S c hc hf j true).prod_symm
  have huu := (uncrossed_log_summable b x hx S hS c hc he j true).prod_symm
  simp only [spectralGain_lowering_sq b p hp, spectralGain_raising_sq b p hp x hi,
    Prod.swap, ← mul_assoc] at hd hu hcd hud hcu huu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact centered_weight_summable (fun a => p a.2) (fun a => (hp a.2).le)
      (fun a => loweringEntry b p x j a.1 a.2) hd hs μ
  · exact centered_weight_summable (fun a => p a.1) (fun a => (hp a.1).le)
      (fun a => loweringEntry b p x j a.1 a.2) hu hs μ
  · exact centered_weight_summable (fun a => c a.1*p a.2) (fun a => mul_nonneg (hc _) (hp _).le)
      (fun a => loweringEntry b p x j a.1 a.2) hcd hec μ
  · exact centered_weight_summable (fun a => c a.2*p a.2) (fun a => mul_nonneg (hc _) (hp _).le)
      (fun a => loweringEntry b p x j a.1 a.2) hud hec μ
  · exact centered_weight_summable (fun a => c a.1*p a.1) (fun a => mul_nonneg (hc _) (hp _).le)
      (fun a => loweringEntry b p x j a.1 a.2) huu hec μ
  · exact centered_weight_summable (fun a => c a.2*p a.1) (fun a => mul_nonneg (hc _) (hp _).le)
      (fun a => loweringEntry b p x j a.1 a.2) hcu hec μ

end WeightedGenerator

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ} {J : Type*}

theorem centered_canonical_norm (j : Fin n) (x : Fock n) (μ : ℂ) :
    ‖raising j x-conj μ • inverseWeight 1 x‖^2 =
      ‖lowering j x-μ • inverseWeight 1 x‖^2+‖inverseWeight 1 x‖^2 := by
  have ha := ladder_adjoint_pairing j x x
  have hc : (inner ℂ (raising j x) (conj μ • inverseWeight 1 x)).re =
      (inner ℂ (lowering j x) (μ • inverseWeight 1 x)).re := by
    rw [inner_smul_right, inner_smul_right, ha]
    have he := inner_conj_symm (𝕜 := ℂ) (inverseWeight 1 x) (raising j x)
    calc
      _ = (conj (μ*inner ℂ (inverseWeight 1 x) (raising j x))).re := by
        rw [map_mul, ← he]
        simp
      _ = _ := Complex.conj_re _
  change RCLike.re (inner ℂ (raising j x) (conj μ • inverseWeight 1 x)) =
    RCLike.re (inner ℂ (lowering j x) (μ • inverseWeight 1 x)) at hc
  rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), hc, norm_smul, norm_smul, Complex.norm_conj,
    canonical_norm_identity]
  ring

def centeredLadder (j : Fin n) (μ : ℂ) (up : Bool) : Fock n →L[ℂ] Fock n :=
  (if up then raising j-conj μ • inverseWeight 1 else lowering j-μ • inverseWeight 1) ∘L inverseWeight 2

theorem centeredLadder_summable (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2)) (j : Fin n) (μ : ℂ) (up : Bool) :
    Summable (fun r => ‖centeredLadder j μ up (x r)‖^2) :=
  CrossEnsemble.applied_summable hx _

theorem centeredLadder_ccr (x : Fock n) (j : Fin n) (μ : ℂ) :
    ‖centeredLadder j μ true x‖^2=‖centeredLadder j μ false x‖^2+‖inverseWeight 3 x‖^2 := by
  have hw : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  simpa only [centeredLadder, Bool.false_eq_true, ↓reduceIte,
    ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, hw] using centered_canonical_norm j (inverseWeight 2 x) μ

theorem centeredLadder_ensemble_gap (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hn : HasSum (fun r => ‖inverseWeight 3 (x r)‖^2) 1) (μ : Fin n → ℂ) :
    (∑ j, ∑' r, ‖centeredLadder j (μ j) true (x r)‖^2) =
      (∑ j, ∑' r, ‖centeredLadder j (μ j) false (x r)‖^2)+(n:ℝ) := by
  have hj (j : Fin n) : (∑' r, ‖centeredLadder j (μ j) true (x r)‖^2) =
      (∑' r, ‖centeredLadder j (μ j) false (x r)‖^2)+1 := by
    simp only [centeredLadder_ccr]
    exact ((centeredLadder_summable x hx j (μ j) false).hasSum.add hn).tsum_eq
  simp only [hj, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

theorem centered_lowering_coordinate (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) (l r : J) :
    inner ℂ (b l) (centeredLadder j μ false (x r))=
      (Real.sqrt (p r):ℂ)*centeredEntry b p x j μ l r := by
  classical
  have hw : inverseWeight 1 (inverseWeight 2 (x r))=(Real.sqrt (p r):ℂ) • b r := by
    change (inverseWeight 1 ∘L inverseWeight 2) (x r)=_
    rw [← inverseWeight_add]; exact hi r
  have hb : inner ℂ (b l) (b r)=if l=r then 1 else 0 := orthonormal_iff_ite.mp b.orthonormal l r
  have hd := spectralGain_lowering b p hp x j l r
  change inner ℂ (b l) (lowering j (inverseWeight 2 (x r)))=_ at hd
  simp only [centeredLadder, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply, inner_sub_right, inner_smul_right, hw, hd, hb, centeredEntry]
  split_ifs <;> ring

theorem centered_raising_coordinate (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) (l r : J) :
    inner ℂ (b r) (centeredLadder j μ true (x l))=
      (Real.sqrt (p l):ℂ)*conj (centeredEntry b p x j μ l r) := by
  classical
  have hw : inverseWeight 1 (inverseWeight 2 (x l))=(Real.sqrt (p l):ℂ) • b l := by
    change (inverseWeight 1 ∘L inverseWeight 2) (x l)=_
    rw [← inverseWeight_add]; exact hi l
  have hb : inner ℂ (b r) (b l)=if r=l then 1 else 0 := orthonormal_iff_ite.mp b.orthonormal r l
  have hd := spectralGain_raising b p hp x hi j l r
  change inner ℂ (b r) (raising j (inverseWeight 2 (x l)))=_ at hd
  simp only [centeredLadder, ↓reduceIte, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply, inner_sub_right, inner_smul_right, hw, hd, hb, centeredEntry]
  by_cases hh : l=r
  · subst r
    simp only [↓reduceIte, map_sub, mul_one]
    ring
  · simp only [hh, Ne.symm hh, ↓reduceIte, sub_zero, mul_zero]

theorem centered_down_sq (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) (l r : J) :
    ‖inner ℂ (b l) (centeredLadder j μ false (x r))‖^2=
      p r*‖centeredEntry b p x j μ l r‖^2 := by
  rw [centered_lowering_coordinate b p hp x hi, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp r).le]

theorem centered_up_sq (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) (l r : J) :
    ‖inner ℂ (b r) (centeredLadder j μ true (x l))‖^2=
      p l*‖centeredEntry b p x j μ l r‖^2 := by
  rw [centered_raising_coordinate b p hp x hi, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp l).le, Complex.norm_conj]

theorem centered_down_sum (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) :
    (∑' a : J × J, p a.2*‖centeredEntry b p x j μ a.1 a.2‖^2)=
      ∑' r, ‖centeredLadder j μ false (x r)‖^2 := by
  have hs := (CrossEnsemble.square_coordinates_summable b (centeredLadder_summable x hx j μ false)).prod_symm
  simp only [Prod.swap] at hs
  simp only [← centered_down_sq b p hp x hi]
  rw [hs.tsum_prod]
  calc
    _ = ∑' (r : J) (l : J), ‖inner ℂ (b l) (centeredLadder j μ false (x r))‖^2 :=
      (Summable.tsum_comm (f := fun l r : J => ‖inner ℂ (b l) (centeredLadder j μ false (x r))‖^2) hs).symm
    _ = _ := by simp only [(TraceEnsemble.basis_hasSum_norm_sq b _).tsum_eq]

theorem centered_up_sum (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) :
    (∑' a : J × J, p a.1*‖centeredEntry b p x j μ a.1 a.2‖^2)=
      ∑' l, ‖centeredLadder j μ true (x l)‖^2 := by
  have hs := CrossEnsemble.square_coordinates_summable b (centeredLadder_summable x hx j μ true)
  simp only [← centered_up_sq b p hp x hi]
  rw [hs.tsum_prod]
  simp only [(TraceEnsemble.basis_hasSum_norm_sq b _).tsum_eq]

theorem centered_K_sum (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (hn : HasSum (fun r => ‖inverseWeight 3 (x r)‖^2) 1) (μ : Fin n → ℂ) (t : ℝ) :
    (∑ j, ∑' a : J × J, ((t+1)*p a.2-t*p a.1)*‖centeredEntry b p x j (μ j) a.1 a.2‖^2)=
      (∑ j, ∑' r, ‖centeredLadder j (μ j) false (x r)‖^2)-(n:ℝ)*t := by
  have hj (j : Fin n) :
      (∑' a : J × J, ((t+1)*p a.2-t*p a.1)*‖centeredEntry b p x j (μ j) a.1 a.2‖^2)=
      (t+1)*(∑' r, ‖centeredLadder j (μ j) false (x r)‖^2)-
      t*(∑' r, ‖centeredLadder j (μ j) true (x r)‖^2) := by
    have hd := (CrossEnsemble.square_coordinates_summable b (centeredLadder_summable x hx j (μ j) false)).prod_symm
    have hu := CrossEnsemble.square_coordinates_summable b (centeredLadder_summable x hx j (μ j) true)
    simp only [Prod.swap, centered_down_sq b p hp x hi] at hd
    simp only [centered_up_sq b p hp x hi] at hu
    simp only [sub_mul, mul_assoc]
    rw [(hd.mul_left (t+1)).tsum_sub (hu.mul_left t), tsum_mul_left, tsum_mul_left,
      centered_down_sum b p hp x hx hi, centered_up_sum b p hp x hx hi]
  simp only [hj, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [centeredLadder_ensemble_gap x hx hn μ]
  ring
end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

def annihilationMatrix (j : Fin n) (a : G.J × G.J) : ℂ :=
  loweringEntry G.basis G.probability G.spectralColumns j a.1 a.2

def annihilationMean (j : Fin n) : ℂ := diagonalMean G.probability (G.annihilationMatrix j)

def centeredMatrix (j : Fin n) (a : G.J × G.J) : ℂ :=
  centeredEntry G.basis G.probability G.spectralColumns j (G.annihilationMean j) a.1 a.2

theorem annihilation_mean_summable (j : Fin n) :
    Summable (fun r => (G.probability r:ℂ)*G.annihilationMatrix j (r,r)) := by
  apply diagonal_mean_summable G.probability (fun r => (G.probability_pos r).le)
    G.probability_sum.summable
  have hh := nonlog_summable G.basis G.spectralColumns G.spectralColumns_summable j false
  simpa only [spectralGain_lowering_sq G.basis G.probability G.probability_pos,
    annihilationMatrix] using hh

theorem centeredMatrix_mean_zero (j : Fin n) :
    HasSum (fun r => (G.probability r:ℂ)*G.centeredMatrix j (r,r)) 0 := by
  classical
  simpa only [centeredMatrix, centeredEntry, ↓reduceIte, annihilationMean, annihilationMatrix]
    using diagonal_centering G.probability G.probability_sum
      (G.annihilationMatrix j) (G.annihilation_mean_summable j)

theorem centeredMatrix_six_sums (hk : 0<k) (j : Fin n) :
    Summable (fun a : G.J × G.J => G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.probability a.1*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.1*G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.2*G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.1*G.probability a.1*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.2*G.probability a.1*‖G.centeredMatrix j a‖^2) :=
  centered_six_sums G.basis G.probability G.probability_pos G.probability_sum.summable
    G.spectralColumns G.spectralColumns_summable G.spectralColumns_inverse
    G.logSandwich (G.logSandwich_symmetric hk) G.logCoefficient G.logCoefficient_nonneg
    (G.logSandwich_parseval hk)
    (fun r => G.logSandwich_preimage hk r _ (G.spectralColumns_inverse r)) j (G.annihilationMean j)

theorem centeredMatrix_defect_summable (hk : 0<k) (t : ℝ) (j : Fin n) :
    Summable (fun a : G.J × G.J =>
      (1-frequency t (G.probability a.1) (G.probability a.2))*
      defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2) := by
  rcases G.centeredMatrix_six_sums hk j with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  exact defect_series_summable t G.probability G.logCoefficient (fun _ => rfl)
    (G.centeredMatrix j) h₁ h₂ h₃ h₄ h₅ h₆

def defect (hk : 0<k) (t : ℝ) (ht : 0<t) (j : Fin n) :
    centeredSpace t ht G.probability G.probability_pos G.probability_sum.summable →L[ℂ] ℂ :=
  (defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable hk t j)).comp
    (centeredSpace t ht G.probability G.probability_pos G.probability_sum.summable).subtypeL

theorem defect_norm_sq (hk : 0<k) (t : ℝ) (ht : 0<t) (j : Fin n) :
    ‖G.defect hk t ht j‖^2=∑' a : G.J × G.J,
      (1-frequency t (G.probability a.1) (G.probability a.2))*
      defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2 :=
  centered_defect_norm_sq t ht G.probability G.probability_pos G.probability_sum.summable
    (G.centeredMatrix j) (G.centeredMatrix_defect_summable hk t j) (G.centeredMatrix_mean_zero j)

def centeredEnergy : ℝ := ∑ j, ∑' r,
  ‖centeredLadder j (G.annihilationMean j) false (G.spectralColumns r)‖^2

theorem thermalGenerator_centered_logarithmic_trace (hk : 0<k) (hm : FiniteMoment 6 ρ) (t : ℝ) :
    (WeightedGenerator.pairing t (weightedRoot 3 ρ hm) G.logSandwich).re =
      ∑ j, ∑' a : G.J × G.J,
        (G.logCoefficient a.1-G.logCoefficient a.2)*
        defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2 := by
  classical
  rw [G.thermalGenerator_logarithmic_trace hk hm t]
  apply Finset.sum_congr rfl
  intro j _
  apply tsum_congr
  intro a
  by_cases he : a.1=a.2
  · simp only [he, sub_self, zero_mul]
  · simp only [centeredMatrix, centeredEntry, he, ↓reduceIte, sub_zero, defectCoefficient]

theorem entropy_production (hk : 0<k) (hm : FiniteMoment 6 ρ) (t : ℝ) (ht : 0<t) :
    (WeightedGenerator.pairing t (weightedRoot 3 ρ hm) G.logSandwich).re/h t =
      (∑ j, ‖G.defect hk t ht j‖^2)-(G.centeredEnergy-(n:ℝ)*t) := by
  rw [G.thermalGenerator_centered_logarithmic_trace hk hm t, Finset.sum_div]
  have hj (j : Fin n) :
      (∑' a : G.J × G.J, (G.logCoefficient a.1-G.logCoefficient a.2)*
        defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2)/h t =
        ‖G.defect hk t ht j‖^2-
        ∑' a : G.J × G.J, defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2 := by
    rw [G.defect_norm_sq hk t ht j]
    have hh := G.centeredMatrix_six_sums hk j
    exact production_series_subtraction t G.probability G.logCoefficient (fun _ => rfl)
      (G.centeredMatrix j) (G.centeredMatrix_defect_summable hk t j)
      (coefficient_series_summable t G.probability (G.centeredMatrix j) hh.1 hh.2.1)
  simp only [hj, Finset.sum_sub_distrib]
  congr 1
  exact centered_K_sum G.basis G.probability G.probability_pos G.spectralColumns
    G.spectralColumns_summable G.spectralColumns_inverse G.spectralColumns_normalized G.annihilationMean t

end EntropyPhotonNumber.GibbsData

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem pairing_rows (b : HilbertBasis J ℂ E) (u v : I → E)
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2))
    (Z : E →L[ℂ] E) :
    HasSum (fun a : I × J => inner ℂ (v a.1) (b a.2)*inner ℂ (b a.2) (Z (u a.1)))
      (pairing u v Z) := by
  have hs : Summable (fun a : I × J => inner ℂ (v a.1) (b a.2)*inner ℂ (b a.2) (Z (u a.1))) := by
    simpa only [mul_comm] using (trace_norm_summable b (applied_summable hu Z) hv).of_norm
  have ht := hs.hasSum.prod_fiberwise (fun i => b.hasSum_inner_mul_inner (v i) (Z (u i)))
  have he := ht.unique (pairing_summable hu hv Z).hasSum
  change HasSum _ (∑' i, inner ℂ (v i) (Z (u i)))
  rw [← he]
  exact hs.hasSum

theorem pairing_columns (b : HilbertBasis J ℂ E) (u v : I → E)
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2))
    (Z : E →L[ℂ] E) :
    HasSum (fun a : I × J => inner ℂ (v a.1) (Z (b a.2))*inner ℂ (b a.2) (u a.1))
      (pairing u v Z) := by
  have hh := pairing_rows b u (fun i => Z.adjoint (v i)) hu (applied_summable hv Z.adjoint)
    (ContinuousLinearMap.id ℂ E)
  simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.adjoint_inner_left, pairing] using hh
end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

def weakDefect (t : ℝ) (x : J → Fock n) (j : Fin n) (μ : ℂ)
    (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  (t+1:ℂ)*CrossEnsemble.pairing (fun r => inverseWeight 3 (x r))
    (fun r => centeredLadder j μ false (x r)) Z-
  (t:ℂ)*CrossEnsemble.pairing (fun r => centeredLadder j μ true (x r))
    (fun r => inverseWeight 3 (x r)) Z

theorem weakDefect_spectral (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ r, 0<p r) (x : J → Fock n) (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (t : ℝ) (j : Fin n) (μ : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun a : J × J => (defectCoefficient t (p a.1) (p a.2):ℂ)*
      conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2)))
      (weakDefect t x j μ Z) := by
  have hw := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hd := centeredLadder_summable x hx j μ false
  have hu := centeredLadder_summable x hx j μ true
  have hr := (Equiv.prodComm J J).hasSum_iff.mpr
    (CrossEnsemble.pairing_rows b (fun r => inverseWeight 3 (x r))
      (fun r => centeredLadder j μ false (x r)) hw hd Z)
  have hl := CrossEnsemble.pairing_columns b (fun r => centeredLadder j μ true (x r))
      (fun r => inverseWeight 3 (x r)) hu hw Z
  have he₁ (a : J × J) :
      inner ℂ (centeredLadder j μ false (x a.2)) (b a.1)*
        inner ℂ (b a.1) (Z (inverseWeight 3 (x a.2)))=
      (p a.2:ℂ)*conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2)) := by
    rw [← inner_conj_symm, centered_lowering_coordinate b p hp x hi, hi, map_smul, inner_smul_right,
      map_mul, Complex.conj_ofReal]
    have hs : (Real.sqrt (p a.2):ℂ)^2=(p a.2:ℂ) := by exact_mod_cast Real.sq_sqrt (hp a.2).le
    linear_combination conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2))*hs
  have he₂ (a : J × J) :
      inner ℂ (inverseWeight 3 (x a.1)) (Z (b a.2))*
        inner ℂ (b a.2) (centeredLadder j μ true (x a.1))=
      (p a.1:ℂ)*conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2)) := by
    rw [centered_raising_coordinate b p hp x hi, hi, inner_smul_left, Complex.conj_ofReal]
    have hs : (Real.sqrt (p a.1):ℂ)^2=(p a.1:ℂ) := by exact_mod_cast Real.sq_sqrt (hp a.1).le
    linear_combination conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2))*hs
  simp only [Equiv.prodComm_apply, Function.comp_def, Prod.swap, he₁] at hr
  simp only [he₂] at hl
  convert! (hr.mul_left (t+1:ℂ)).sub (hl.mul_left (t:ℂ)) using 1
  ext a
  simp only [defectCoefficient, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_mul]
  ring

end WeightedGenerator

namespace ThermalMetric
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem bounded_matrix_summable (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (t : ℝ) (ht : 0<t) (Z : E →L[ℂ] E) :
    Summable (fun a : J × J => metricCoefficient t (p a.1) (p a.2)*
      ‖inner ℂ (b a.1) (Z (b a.2))‖^2) := by
  let u : J → E := fun r => (Real.sqrt (p r):ℂ) • b r
  have hu : Summable (fun r => ‖u r‖^2) := by
    convert! hs using 1
    ext r
    simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hp r).le, b.orthonormal.norm_eq_one r, mul_one]
  have hc : Summable (fun a : J × J => p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2) := by
    have hh := (CrossEnsemble.square_coordinates_summable b (CrossEnsemble.applied_summable hu Z)).prod_symm
    simpa only [Prod.swap, u, map_smul, inner_smul_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hp _).le] using hh
  have hr : Summable (fun a : J × J => p a.1*‖inner ℂ (b a.1) (Z (b a.2))‖^2) := by
    have hh := CrossEnsemble.square_coordinates_summable b (CrossEnsemble.applied_summable hu Z.adjoint)
    simpa only [u, map_smul, inner_smul_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hp _).le,
      ContinuousLinearMap.adjoint_inner_right, norm_inner_symm] using hh
  apply Summable.of_nonneg_of_le
    (fun a => mul_nonneg (metricCoefficient_pos ht (hp _) (hp _)).le (sq_nonneg _)) _
    (((hr.mul_left t).add (hc.mul_left (t+1))).mul_left (h t/2))
  intro a
  have hh := DiagonalForms.System.logMean_le_arithmetic (mul_pos ht (hp a.1))
    (mul_pos (by positivity : 0<t+1) (hp a.2))
  have hm : metricCoefficient t (p a.1) (p a.2) =
      h t*DiagonalForms.System.logMean (t*p a.1) ((t+1)*p a.2) := by
    rw [metricCoefficient, mul_assoc, tilted_logMean ht (hp _) (hp _)]
  rw [hm]
  have hh' := mul_le_mul_of_nonneg_left hh (h_pos ht).le
  nlinarith [mul_le_mul_of_nonneg_right hh' (sq_nonneg ‖inner ℂ (b a.1) (Z (b a.2))‖)]

def matrixVector (t : ℝ) (ht : 0<t) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (z : J × J → ℂ)
    (hz : Summable (fun a : J × J => metricCoefficient t (p a.1) (p a.2)*‖z a‖^2)) :
    lp (fun _ : J × J => ℂ) 2 :=
  weightedVector (fun a : J × J => metricCoefficient t (p a.1) (p a.2)) z hz
    (fun a => (metricCoefficient_pos ht (hp a.1) (hp a.2)).le)

theorem weightedVector_centered (t : ℝ) (ht : 0<t) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (hs : Summable p) (z : J × J → ℂ)
    (hz : Summable (fun a : J × J => metricCoefficient t (p a.1) (p a.2)*‖z a‖^2))
    (hm : HasSum (fun j => (p j:ℂ)*z (j,j)) 0) :
    matrixVector t ht p hp z hz ∈ centeredSpace t ht p hp hs := by
  classical
  have hi := lp.hasSum_inner (𝕜 := ℂ) (identityVector t ht p hp hs)
    (weightedVector (fun a => metricCoefficient t (p a.1) (p a.2)) z hz
      (fun a => (metricCoefficient_pos ht (hp a.1) (hp a.2)).le))
  have hdiag : HasSum (fun a : J × J => if a.1=a.2 then (p a.1:ℂ)*z (a.1,a.1) else 0)
      (inner ℂ (identityVector t ht p hp hs)
        (weightedVector (fun a => metricCoefficient t (p a.1) (p a.2)) z hz
          (fun a => (metricCoefficient_pos ht (hp a.1) (hp a.2)).le))) := by
    convert! hi using 1
    ext a
    by_cases he : a.1=a.2
    · obtain ⟨l,r⟩ := a
      dsimp only [Prod.fst, Prod.snd] at he ⊢
      subst r
      simp only [identityVector, weightedVector_apply, identityEntry, ↓reduceIte, mul_one,
        RCLike.inner_apply, Complex.conj_ofReal, metricCoefficient_self ht (hp l)]
      have hh : (Real.sqrt (p l):ℂ)^2=(p l:ℂ) := by exact_mod_cast Real.sq_sqrt (hp l).le
      linear_combination -z (l,l)*hh
    · simp only [identityVector, weightedVector_apply, identityEntry, he, ↓reduceIte,
        mul_zero, RCLike.inner_apply, map_zero]
  exact hdiag.unique (hasSum_diagonal hm)

end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

def observableVector (t : ℝ) (ht : 0<t) (Z : Fock n →L[ℂ] Fock n) :
    lp (fun _ : G.J × G.J => ℂ) 2 :=
  matrixVector t ht G.probability G.probability_pos
    (fun a => inner ℂ (G.basis a.1) (Z (G.basis a.2)))
    (bounded_matrix_summable G.basis G.probability G.probability_pos
      G.probability_sum.summable t ht Z)

theorem observableVector_mem (t : ℝ) (ht : 0<t) (Z : Fock n →L[ℂ] Fock n)
    (hZ : HasSum (fun r => (G.probability r:ℂ)*inner ℂ (G.basis r) (Z (G.basis r))) 0) :
    G.observableVector t ht Z ∈ centeredSpace t ht G.probability G.probability_pos
      G.probability_sum.summable :=
  weightedVector_centered t ht G.probability G.probability_pos G.probability_sum.summable
    _ _ hZ

theorem defect_on_observable (hk : 0<k) (t : ℝ) (ht : 0<t) (j : Fin n)
    (Z : Fock n →L[ℂ] Fock n)
    (hZ : HasSum (fun r => (G.probability r:ℂ)*inner ℂ (G.basis r) (Z (G.basis r))) 0) :
    G.defect hk t ht j ⟨G.observableVector t ht Z,G.observableVector_mem t ht Z hZ⟩ =
      weakDefect t G.spectralColumns j (G.annihilationMean j) Z := by
  have hv := defectVector_pairing t ht G.probability G.probability_pos
    (G.centeredMatrix j) (G.centeredMatrix_defect_summable hk t j)
    (fun a => inner ℂ (G.basis a.1) (Z (G.basis a.2)))
    (bounded_matrix_summable G.basis G.probability G.probability_pos
      G.probability_sum.summable t ht Z)
  exact hv.unique (weakDefect_spectral G.basis G.probability G.probability_pos
    G.spectralColumns G.spectralColumns_summable G.spectralColumns_inverse
    t j (G.annihilationMean j) Z)

end EntropyPhotonNumber.GibbsData

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ}

theorem lowering_weighted_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    lowering j (inverseWeight 2 x) k=
      (Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  rw [lowering_apply]
  change _ * ((inverseWeight 1 ∘L inverseWeight 2) x) _ = _
  rw [← inverseWeight_add]

theorem raising_weighted_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    raising j (inverseWeight 2 x) k=
      (Real.sqrt (k j:ℝ):ℂ)*inverseWeight 3 x (down j k) := by
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · simp only [raising_zero j _ k hk, hk, Nat.cast_zero, Real.sqrt_zero,
      Complex.ofReal_zero, zero_mul]
  · rw [raising_up]
    change _ * ((inverseWeight 1 ∘L inverseWeight 2) x) _ = _
    rw [← inverseWeight_add, up_same, down_up]
    norm_cast
end Annihilation

namespace EntropyPhotonNumber
open Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

def numberMatrixUnit (a b : NumberIndex n) : Fock n →L[ℂ] Fock n :=
  InnerProductSpace.rankOne ℂ (numberKet a) (numberKet b)

@[simp] theorem numberKet_inner (a : NumberIndex n) (x : Fock n) :
    inner ℂ (numberKet a) x=x a := by
  simp only [numberKet, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

@[simp] theorem inner_numberKet (a : NumberIndex n) (x : Fock n) :
    inner ℂ x (numberKet a)=conj (x a) := by
  rw [← inner_conj_symm, numberKet_inner]

@[simp] theorem numberMatrixUnit_inner (u v : Fock n) (a b : NumberIndex n) :
    inner ℂ v (numberMatrixUnit a b u)=u b*conj (v a) := by
  simp only [numberMatrixUnit, InnerProductSpace.rankOne_apply, inner_smul_right,
    numberKet_inner, inner_numberKet]
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem inverseColumns_entry (x : J → Fock n) (hx : Summable (fun j => ‖x j‖^2))
    (ρ : State n)
    (he : CrossEnsemble.operator (fun j => inverseWeight 3 (x j)) (fun j => inverseWeight 3 (x j))=ρ.op)
    (a b : NumberIndex n) :
    HasSum (fun j => inverseWeight 3 (x j) a*conj (inverseWeight 3 (x j) b)) (entry ρ.op a b) := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  simpa only [he, numberKet_inner, inner_numberKet, entry] using
    CrossEnsemble.entry_hasSum hi hi (numberKet a) (numberKet b)

theorem weakDefect_numberMatrixUnit (t : ℝ) (x : J → Fock n)
    (hx : Summable (fun j => ‖x j‖^2)) (ρ : State n)
    (he : CrossEnsemble.operator (fun j => inverseWeight 3 (x j)) (fun j => inverseWeight 3 (x j))=ρ.op)
    (j : Fin n) (μ : ℂ) (a b : NumberIndex n) :
    weakDefect t x j μ (numberMatrixUnit a b)=
      (t+1:ℂ)*(Real.sqrt ((a j:ℝ)+1):ℂ)*entry ρ.op b (up j a)-
      (t:ℂ)*(Real.sqrt (b j:ℝ):ℂ)*entry ρ.op (down j b) a-
      conj μ*entry ρ.op b a := by
  have hw := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have h₀ := inverseColumns_entry x hx ρ he b a
  have h₁ := inverseColumns_entry x hx ρ he b (up j a)
  have h₂ := inverseColumns_entry x hx ρ he (down j b) a
  have hi (y : Fock n) : inverseWeight 1 (inverseWeight 2 y)=inverseWeight 3 y := by
    change (inverseWeight 1 ∘L inverseWeight 2) y=_
    rw [← inverseWeight_add]
  have hl : CrossEnsemble.pairing (fun r => inverseWeight 3 (x r))
      (fun r => centeredLadder j μ false (x r)) (numberMatrixUnit a b)=
        (Real.sqrt ((a j:ℝ)+1):ℂ)*entry ρ.op b (up j a)-conj μ*entry ρ.op b a := by
    apply (CrossEnsemble.pairing_summable hw (centeredLadder_summable x hx j μ false) _).hasSum.unique
    convert! (h₁.mul_left (Real.sqrt ((a j:ℝ)+1):ℂ)).sub (h₀.mul_left (conj μ)) using 1
    ext r
    simp only [numberMatrixUnit_inner, centeredLadder, Bool.false_eq_true, ↓reduceIte,
      ContinuousLinearMap.comp_apply, sub_apply, smul_apply, lp.coeFn_sub, Pi.sub_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hi, lowering_weighted_apply,
      map_sub, map_mul, Complex.conj_ofReal]
    ring
  have hu : CrossEnsemble.pairing (fun r => centeredLadder j μ true (x r))
      (fun r => inverseWeight 3 (x r)) (numberMatrixUnit a b)=
        (Real.sqrt (b j:ℝ):ℂ)*entry ρ.op (down j b) a-conj μ*entry ρ.op b a := by
    apply (CrossEnsemble.pairing_summable (centeredLadder_summable x hx j μ true) hw _).hasSum.unique
    convert! (h₂.mul_left (Real.sqrt (b j:ℝ):ℂ)).sub (h₀.mul_left (conj μ)) using 1
    ext r
    simp only [numberMatrixUnit_inner, centeredLadder, ↓reduceIte,
      ContinuousLinearMap.comp_apply, sub_apply, smul_apply, lp.coeFn_sub, Pi.sub_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hi, raising_weighted_apply]
    ring
  rw [weakDefect, hl, hu]
  ring
end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open Annihilation WeightedGenerator
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

theorem inverse_spectralColumns_operator :
    CrossEnsemble.operator (fun r => inverseWeight 3 (G.spectralColumns r))
      (fun r => inverseWeight 3 (G.spectralColumns r))=ρ.op := by
  simp only [G.spectralColumns_inverse]
  exact CrossEnsemble.eigenEnsemble_operator G.basis G.probability
    (fun r => (G.probability_pos r).le) G.probability_sum.summable ρ.op ρ.positive.isSymmetric G.eigen

theorem weakDefect_numberMatrixUnit (t : ℝ) (j : Fin n) (a b : NumberIndex n) :
    weakDefect t G.spectralColumns j (G.annihilationMean j) (numberMatrixUnit a b)=
      (t+1:ℂ)*(Real.sqrt ((a j:ℝ)+1):ℂ)*entry ρ.op b (up j a)-
      (t:ℂ)*(Real.sqrt (b j:ℝ):ℂ)*entry ρ.op (down j b) a-
      star (G.annihilationMean j)*entry ρ.op b a :=
  WeightedGenerator.weakDefect_numberMatrixUnit t G.spectralColumns G.spectralColumns_summable
    ρ G.inverse_spectralColumns_operator j (G.annihilationMean j) a b
end EntropyPhotonNumber.GibbsData

end

end OAI
