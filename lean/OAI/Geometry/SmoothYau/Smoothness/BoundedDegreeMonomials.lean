import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.MultilinearPolynomial

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def SmoothJetZero (f : E → F) (N : ℕ) : Prop :=
  ∀ k < N, iteratedFDeriv ℝ k f 0 = 0

namespace SmoothJetZero
lemma mono {f : E → F} {N M : ℕ} (h : SmoothJetZero f N) (hMN : M ≤ N) :
    SmoothJetZero f M := fun k hk => h k (hk.trans_le hMN)
lemma zero (N : ℕ) : SmoothJetZero (0 : E → F) N := by
  intro k _
  exact congrFun (iteratedFDeriv_zero (𝕜 := ℝ) (n := k)) 0
lemma order_zero (f : E → F) : SmoothJetZero f 0 := by intro k hk; omega
lemma add {f g : E → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N : ℕ} (hfj : SmoothJetZero f N) (hgj : SmoothJetZero g N) :
    SmoothJetZero (f + g) N := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  rw [iteratedFDeriv_add_apply (hf.of_le hle).contDiffAt (hg.of_le hle).contDiffAt,
    hfj k hk, hgj k hk, add_zero]
lemma neg {f : E → F} {N : ℕ} (h : SmoothJetZero f N) : SmoothJetZero (-f) N := by
  intro k hk
  rw [iteratedFDeriv_neg_apply, h k hk, neg_zero]
lemma sub {f g : E → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N : ℕ} (hfj : SmoothJetZero f N) (hgj : SmoothJetZero g N) :
    SmoothJetZero (f - g) N := by
  rw [sub_eq_add_neg]
  exact hfj.add hf hg.neg hgj.neg
lemma sum {ι : Type*} (s : Finset ι) (f : ι → E → F)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) {N : ℕ}
    (hj : ∀ i ∈ s, SmoothJetZero (f i) N) : SmoothJetZero (∑ i ∈ s, f i) N := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  rw [iteratedFDeriv_sum_apply (fun i hi => ((hf i hi).of_le hle).contDiffAt)]
  exact Finset.sum_eq_zero (fun i hi => hj i hi k hk)

lemma mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f g : E → A} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N M : ℕ} (hfj : SmoothJetZero f N) (hgj : SmoothJetZero g M) :
    SmoothJetZero (fun x => f x * g x) (N + M) := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  have hb := norm_iteratedFDeriv_mul_le hf hg (0 : E) hle
  have hz : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f 0‖ * ‖iteratedFDeriv ℝ (k - i) g 0‖ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ k := by simpa using Finset.mem_range.mp hi
    by_cases h : i < N
    · simp [hfj i h]
    · simp [hgj (k - i) (by omega)]
  rw [hz] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

lemma mul_right {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f : E → A} (hf : ContDiff ℝ ∞ f) (g : E → A) (hg : ContDiff ℝ ∞ g)
    {N : ℕ} (h : SmoothJetZero f N) : SmoothJetZero (fun x => f x * g x) N := by
  simpa using h.mul hf hg (order_zero g)
lemma mul_left {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (f : E → A) (hf : ContDiff ℝ ∞ f) {g : E → A} (hg : ContDiff ℝ ∞ g)
    {N : ℕ} (h : SmoothJetZero g N) : SmoothJetZero (fun x => f x * g x) N := by
  simpa using (order_zero f).mul hf hg h

lemma fderiv {f : E → F} {N : ℕ} (h : SmoothJetZero f (N + 1)) :
    SmoothJetZero (fderiv ℝ f) N := by
  intro k hk
  apply norm_eq_zero.mp
  rw [norm_iteratedFDeriv_fderiv, h (k + 1) (by omega), norm_zero]

end SmoothJetZero

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
section PolynomialWaves
open MvPolynomial
variable {σ : Type*} [Fintype σ]

def waveDirectionalDerivative (z : σ → ℂ) :
    Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  ∑ i, z i • pderiv i

@[simp] theorem waveDirectionalDerivative_apply (z : σ → ℂ) (f : MvPolynomial σ ℂ) :
    waveDirectionalDerivative z f = ∑ i, z i • pderiv i f := by
  classical
  unfold waveDirectionalDerivative
  have h (s : Finset σ) : (∑ i ∈ s, z i • pderiv i) f =
      ∑ i ∈ s, z i • pderiv i f := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, Derivation.add_apply, Derivation.smul_apply, ih]
  exact h Finset.univ

@[simp] theorem waveDirectionalDerivative_X (z : σ → ℂ) (i : σ) :
    waveDirectionalDerivative z (X i) = C (z i) := by
  classical
  simp [waveDirectionalDerivative_apply, pderiv_X, Pi.single_apply,
    Algebra.smul_def]

@[simp] theorem waveDirectionalDerivative_C (z : σ → ℂ) (c : ℂ) :
    waveDirectionalDerivative z (C c) = 0 := by
  exact MvPolynomial.derivation_C _ _

theorem waveDirectionalDerivative_homogeneous (z : σ → ℂ)
    {f : MvPolynomial σ ℂ} {d : ℕ} (hf : f.IsHomogeneous d) :
    (waveDirectionalDerivative z f).IsHomogeneous (d - 1) := by
  rw [waveDirectionalDerivative_apply]
  apply IsHomogeneous.sum
  intro i _
  simpa only [← C_mul'] using hf.pderiv.C_mul (z i)

theorem waveDirectionalDerivative_degree_zero (z : σ → ℂ)
    {f : MvPolynomial σ ℂ} (hf : f.IsHomogeneous 0) :
    waveDirectionalDerivative z f = 0 := by
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hf
  rw [hf, waveDirectionalDerivative_C]

def wavePrimitiveTerm (z : σ → ℂ) (ℓ : MvPolynomial σ ℂ) :
    ℕ → ℕ → MvPolynomial σ ℂ → MvPolynomial σ ℂ
  | 0, j, f => ((j + 1 : ℕ) : ℂ)⁻¹ • (ℓ ^ (j + 1) * f)
  | d + 1, j, f => ((j + 1 : ℕ) : ℂ)⁻¹ •
      (ℓ ^ (j + 1) * f - wavePrimitiveTerm z ℓ d (j + 1)
        (waveDirectionalDerivative z f))

theorem wavePrimitiveTerm_homogeneous (z : σ → ℂ)
    (ℓ : MvPolynomial σ ℂ) (hℓ : ℓ.IsHomogeneous 1)
    (d j : ℕ) (f : MvPolynomial σ ℂ) (hf : f.IsHomogeneous d) :
    (wavePrimitiveTerm z ℓ d j f).IsHomogeneous (d + j + 1) := by
  induction d generalizing j f with
  | zero =>
      dsimp [wavePrimitiveTerm]
      have h := ((hℓ.pow (j + 1)).mul hf).C_mul (((j + 1 : ℕ) : ℂ)⁻¹)
      simpa only [one_mul, add_zero, zero_add, C_mul'] using h
  | succ d ih =>
      have hdf : (waveDirectionalDerivative z f).IsHomogeneous d := by
        simpa only [Nat.add_sub_cancel] using waveDirectionalDerivative_homogeneous z hf
      have h₁ : (ℓ ^ (j + 1) * f).IsHomogeneous (d + 1 + j + 1) := by
        convert (hℓ.pow (j + 1)).mul hf using 1; omega
      have h₂ : (wavePrimitiveTerm z ℓ d (j + 1)
          (waveDirectionalDerivative z f)).IsHomogeneous (d + 1 + j + 1) := by
        convert ih (j + 1) _ hdf using 1; omega
      dsimp only [wavePrimitiveTerm]
      simpa only [C_mul'] using (h₁.sub h₂).C_mul (((j + 1 : ℕ) : ℂ)⁻¹)

theorem wavePrimitiveTerm_derivative (z : σ → ℂ)
    (ℓ : MvPolynomial σ ℂ) (hℓ : waveDirectionalDerivative z ℓ = 1)
    (d j : ℕ) (f : MvPolynomial σ ℂ) (hf : f.IsHomogeneous d) :
    waveDirectionalDerivative z (wavePrimitiveTerm z ℓ d j f) = ℓ ^ j * f := by
  have hj (j : ℕ) : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hpow (j : ℕ) : waveDirectionalDerivative z (ℓ ^ (j + 1)) =
      ((j + 1 : ℕ) : ℂ) • ℓ ^ j := by
    rw [Derivation.leibniz_pow, hℓ, Nat.add_sub_cancel]
    simp [Algebra.smul_def]
  induction d generalizing j f with
  | zero =>
      rw [wavePrimitiveTerm, Derivation.map_smul, Derivation.leibniz,
        waveDirectionalDerivative_degree_zero z hf, hpow]
      simp only [smul_eq_mul, mul_zero, zero_add, mul_smul_comm, smul_smul,
        inv_mul_cancel₀ (hj j), one_smul, mul_comm]
  | succ d ih =>
      have hdf : (waveDirectionalDerivative z f).IsHomogeneous d := by
        simpa only [Nat.add_sub_cancel] using waveDirectionalDerivative_homogeneous z hf
      rw [wavePrimitiveTerm, Derivation.map_smul, map_sub, Derivation.leibniz,
        hpow, ih (j + 1) _ hdf]
      simp only [smul_eq_mul, add_sub_cancel_left]
      rw [mul_smul_comm, smul_smul, inv_mul_cancel₀ (hj j), one_smul, mul_comm]

def waveNormSq (z : σ → ℂ) : ℝ := ∑ i, Complex.normSq (z i)

theorem waveNormSq_pos (z : σ → ℂ) (hz : z ≠ 0) : 0 < waveNormSq z := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (z j))
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

def waveLinearCoordinate (z : σ → ℂ) : MvPolynomial σ ℂ :=
  ∑ i, (star (z i) / (waveNormSq z : ℂ)) • X i

theorem waveLinearCoordinate_homogeneous (z : σ → ℂ) :
    (waveLinearCoordinate z).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  simpa only [C_mul'] using (isHomogeneous_X ℂ i).C_mul
    (star (z i) / (waveNormSq z : ℂ))

theorem waveLinearCoordinate_derivative (z : σ → ℂ) (hz : z ≠ 0) :
    waveDirectionalDerivative z (waveLinearCoordinate z) = 1 := by
  have hd : (waveNormSq z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (waveNormSq_pos z hz))
  simp only [waveLinearCoordinate, map_sum, Derivation.map_smul,
    waveDirectionalDerivative_X]
  simp only [Algebra.smul_def, algebraMap_eq, ← map_mul, ← map_sum]
  rw [show (1 : MvPolynomial σ ℂ) = C 1 by simp]
  congr 1
  calc
    ∑ i, (star (z i) / (waveNormSq z : ℂ)) * z i =
        (∑ i, z i * star (z i)) / (waveNormSq z : ℂ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (waveNormSq z : ℂ) / (waveNormSq z : ℂ) := by
      congr 1
      simp only [Complex.star_def, Complex.mul_conj, waveNormSq, Complex.ofReal_sum]
    _ = 1 := div_self hd

theorem wave_homogeneous_primitive (z : σ → ℂ) (hz : z ≠ 0)
    (d : ℕ) (f : MvPolynomial σ ℂ) (hf : f.IsHomogeneous d) :
    ∃ F : MvPolynomial σ ℂ,
      F.IsHomogeneous (d + 1) ∧ waveDirectionalDerivative z F = f := by
  refine ⟨wavePrimitiveTerm z (waveLinearCoordinate z) d 0 f, ?_, ?_⟩
  · simpa using wavePrimitiveTerm_homogeneous z (waveLinearCoordinate z)
      (waveLinearCoordinate_homogeneous z) d 0 f hf
  · simpa using wavePrimitiveTerm_derivative z (waveLinearCoordinate z)
      (waveLinearCoordinate_derivative z hz) d 0 f hf
end PolynomialWaves

section CoefficientContinuity
open MvPolynomial
variable {σ X : Type*} [TopologicalSpace X]

def CoeffContinuous (F : X → MvPolynomial σ ℂ) : Prop :=
  ∀ m : σ →₀ ℕ, Continuous (fun x => (F x).coeff m)

namespace CoeffContinuous

theorem const (p : MvPolynomial σ ℂ) : CoeffContinuous (fun _ : X => p) :=
  fun _ => continuous_const

theorem add {F G : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    (hG : CoeffContinuous G) : CoeffContinuous (fun x => F x + G x) := by
  intro m
  convert (hF m).add (hG m) using 1; ext x; simp

theorem neg {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => -F x) := by
  intro m
  convert (hF m).neg using 1; ext x; simp

theorem sub {F G : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    (hG : CoeffContinuous G) : CoeffContinuous (fun x => F x - G x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem smul {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    {c : X → ℂ} (hc : Continuous c) : CoeffContinuous (fun x => c x • F x) := by
  intro m
  convert hc.mul (hF m) using 1; ext x; simp

theorem mul {F G : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    (hG : CoeffContinuous G) : CoeffContinuous (fun x => F x * G x) := by
  classical
  intro m
  simp only [coeff_mul]
  apply continuous_finsetSum
  intro t _
  exact (hF t.1).mul (hG t.2)

theorem pow {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F) (n : ℕ) :
    CoeffContinuous (fun x => F x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using const (X := X) (1 : MvPolynomial σ ℂ)
  | succ n ih => simpa only [pow_succ] using ih.mul hF

theorem sum {ι : Type*} (s : Finset ι) (F : ι → X → MvPolynomial σ ℂ)
    (hF : ∀ i ∈ s, CoeffContinuous (F i)) :
    CoeffContinuous (fun x => ∑ i ∈ s, F i x) := by
  intro m
  simp only [coeff_sum]
  exact continuous_finsetSum s (fun i hi => hF i hi m)

theorem pderiv {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F) (i : σ) :
    CoeffContinuous (fun x => pderiv i (F x)) := by
  intro m
  simpa only [coeff_pderiv] using (hF (m + Finsupp.single i 1)).mul_const (m i + 1)

theorem homogeneousComponent {F : X → MvPolynomial σ ℂ}
    (hF : CoeffContinuous F) (N : ℕ) :
    CoeffContinuous (fun x => homogeneousComponent N (F x)) := by
  intro m
  simp only [coeff_homogeneousComponent]
  split_ifs
  · exact hF m
  · exact continuous_const

end CoeffContinuous

variable [Fintype σ]

theorem waveDirectionalDerivative_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (F : X → MvPolynomial σ ℂ)
    (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => waveDirectionalDerivative (z x) (F x)) := by
  simp only [waveDirectionalDerivative_apply]
  exact CoeffContinuous.sum Finset.univ _ (fun i _ => (hF.pderiv i).smul (hz i))

theorem waveLinearCoordinate_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (hz₀ : ∀ x, z x ≠ 0) :
    CoeffContinuous (fun x => waveLinearCoordinate (z x)) := by
  have hd : Continuous (fun x => waveNormSq (z x)) := by
    exact continuous_finsetSum Finset.univ (fun i _ => Complex.continuous_normSq.comp (hz i))
  apply CoeffContinuous.sum
  intro i _
  apply (CoeffContinuous.const (MvPolynomial.X i)).smul
  exact (continuous_star.comp (hz i)).div (Complex.continuous_ofReal.comp hd)
    (fun x => by exact_mod_cast (ne_of_gt (waveNormSq_pos (z x) (hz₀ x))))

theorem wavePrimitiveTerm_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (ℓ : X → MvPolynomial σ ℂ)
    (hℓ : CoeffContinuous ℓ) (d j : ℕ) (F : X → MvPolynomial σ ℂ)
    (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => wavePrimitiveTerm (z x) (ℓ x) d j (F x)) := by
  induction d generalizing j F with
  | zero => exact ((hℓ.pow (j + 1)).mul hF).smul continuous_const
  | succ d ih =>
      exact (((hℓ.pow (j + 1)).mul hF).sub
        (ih (j + 1) _ (waveDirectionalDerivative_coeffContinuous z hz F hF))).smul continuous_const

theorem canonical_wavePrimitive_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (hz₀ : ∀ x, z x ≠ 0)
    (d : ℕ) (F : X → MvPolynomial σ ℂ) (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => wavePrimitiveTerm (z x) (waveLinearCoordinate (z x)) d 0 (F x)) :=
  wavePrimitiveTerm_coeffContinuous z hz _ (waveLinearCoordinate_coeffContinuous z hz hz₀) d 0 F hF

end CoefficientContinuity

section FiniteJets
open MvPolynomial
variable {σ R : Type*} [CommRing R]

def VanishTo (p : MvPolynomial σ R) (N : ℕ) : Prop :=
  ∀ m : σ →₀ ℕ, m.degree < N → p.coeff m = 0

namespace VanishTo

theorem zero (N : ℕ) : VanishTo (0 : MvPolynomial σ R) N := by
  intro m _
  rfl

theorem order_zero (p : MvPolynomial σ R) : VanishTo p 0 := by
  intro m hm
  omega

theorem mono {p : MvPolynomial σ R} {N M : ℕ} (hp : VanishTo p N)
    (h : M ≤ N) : VanishTo p M := fun m hm => hp m (hm.trans_le h)

theorem add {p q : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (hq : VanishTo q N) : VanishTo (p + q) N := by
  intro m hm
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp m hm, hq m hm, add_zero]

theorem neg {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) : VanishTo (-p) N := by
  intro m hm
  simp only [coeff_neg, hp m hm, neg_zero]

theorem sub {p q : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (hq : VanishTo q N) : VanishTo (p - q) N := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem sum {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial σ R} {N : ℕ}
    (h : ∀ i ∈ s, VanishTo (f i) N) : VanishTo (∑ i ∈ s, f i) N := by
  intro m hm
  simp only [coeff_sum]
  exact Finset.sum_eq_zero (fun i hi => h i hi m hm)

theorem mul {p q : MvPolynomial σ R} {N M : ℕ}
    (hp : VanishTo p N) (hq : VanishTo q M) : VanishTo (p * q) (N + M) := by
  classical
  intro m hm
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro t ht
  have ht' : t.1 + t.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp ht
  have hd : t.1.degree + t.2.degree = m.degree := by
    rw [← map_add, ht']
  by_cases h : t.1.degree < N
  · rw [hp t.1 h, zero_mul]
  · have h' : t.2.degree < M := by omega
    rw [hq t.2 h', mul_zero]

theorem mul_left {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (q : MvPolynomial σ R) : VanishTo (q * p) N := by
  simpa only [zero_add] using (order_zero q).mul hp

theorem mul_right {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (q : MvPolynomial σ R) : VanishTo (p * q) N := by
  simpa only [add_zero] using hp.mul (order_zero q)

theorem smul {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (c : R) : VanishTo (c • p) N := by
  simpa only [C_mul'] using hp.mul_left (C c)

theorem pderiv {p : MvPolynomial σ R} {N : ℕ} (hp : VanishTo p (N + 1))
    (i : σ) : VanishTo (pderiv i p) N := by
  intro m hm
  rw [coeff_pderiv, hp (m + Finsupp.single i 1), zero_mul]
  simpa only [map_add, Finsupp.degree_single, Nat.add_lt_add_iff_right] using hm

theorem of_homogeneous {p : MvPolynomial σ R} {N : ℕ} (hp : p.IsHomogeneous N) :
    VanishTo p N := fun _ hm => hp.coeff_eq_zero (ne_of_lt hm)

theorem of_constantCoeff_eq_zero {p : MvPolynomial σ R}
    (hp : constantCoeff p = 0) : VanishTo p 1 := by
  intro m hm
  have h : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
  simpa only [h, constantCoeff_eq] using hp

theorem constantCoeff_eq_zero {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (hN : 0 < N) : constantCoeff p = 0 := by
  exact hp 0 (by simpa using hN)

theorem constantCoeff_sub (p : MvPolynomial σ R) :
    VanishTo (p - C (constantCoeff p)) 1 := by
  apply of_constantCoeff_eq_zero
  simp

theorem remove_component {p : MvPolynomial σ R} {N : ℕ} (hp : VanishTo p N) :
    VanishTo (p - homogeneousComponent N p) (N + 1) := by
  intro m hm
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases h : m.degree = N
  · simp [h]
  · have h' : m.degree < N := by omega
    simp [h, hp m h']

theorem of_constant_and_linear {p : MvPolynomial σ R}
    (h₀ : constantCoeff p = 0) (h₁ : ∀ i, constantCoeff (MvPolynomial.pderiv i p) = 0) :
    VanishTo p 2 := by
  intro m hm
  by_cases hm₀ : m = 0
  · subst m
    exact h₀
  · have hmdeg : m.degree = 1 := by
      have hne : m.degree ≠ 0 := mt (Finsupp.degree_eq_zero_iff m).mp hm₀
      omega
    obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff m).mp hmdeg
    simpa only [constantCoeff_eq, coeff_pderiv, zero_add, Finsupp.zero_apply,
      Nat.cast_zero, mul_one] using h₁ i

end VanishTo

variable [Fintype σ] [DecidableEq σ]

def waveQuadratic (G : σ → σ → MvPolynomial σ R) (u : σ → MvPolynomial σ R) :
    MvPolynomial σ R := ∑ i, ∑ j, G i j * u i * u j

theorem waveQuadratic_linearization (G : σ → σ → MvPolynomial σ R)
    (u v : σ → MvPolynomial σ R) (z : σ → R) (N : ℕ) (hN : 1 ≤ N)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hu : ∀ i, constantCoeff (u i) = z i) (hv : ∀ i, VanishTo (v i) N) :
    VanishTo (waveQuadratic G (fun i => u i + v i) - waveQuadratic G u -
      2 * ∑ i, C (z i) * v i) (N + 1) := by
  classical
  have hp (i j : σ) : VanishTo
      (G i j * (u i + v i) * (u j + v j) - G i j * u i * u j -
        if i = j then C (z i) * v i + C (z i) * v i else 0) (N + 1) := by
    have hquad : VanishTo (G i j * v i * v j) (N + 1) := by
      exact (((hv i).mul_left (G i j)).mul (hv j)).mono (by omega)
    by_cases hij : i = j
    · subst j
      have hbase : VanishTo (G i i * u i - C (z i)) 1 := by
        apply VanishTo.of_constantCoeff_eq_zero
        simp [hG, hu]
      have hlin : VanishTo ((G i i * u i - C (z i)) * v i) (N + 1) := by
        simpa only [Nat.add_comm 1] using hbase.mul (hv i)
      convert (hlin.add hlin).add hquad using 1
      simp only [ite_true]
      ring
    · have hg : VanishTo (G i j) 1 := by
        apply VanishTo.of_constantCoeff_eq_zero
        simp [hG, hij]
      have hfirst : VanishTo (G i j * u i * v j) (N + 1) := by
        simpa only [Nat.add_comm 1] using (hg.mul_right (u i)).mul (hv j)
      have hsecond : VanishTo (G i j * u j * v i) (N + 1) := by
        simpa only [Nat.add_comm 1] using (hg.mul_right (u j)).mul (hv i)
      convert (hfirst.add hsecond).add hquad using 1
      simp only [hij, ite_false]
      ring
  have H := VanishTo.sum Finset.univ (fun i _ =>
    VanishTo.sum Finset.univ (fun j _ => hp i j))
  simpa [waveQuadratic, Finset.sum_sub_distrib, Finset.sum_add_distrib, two_mul] using H

end FiniteJets

section FiniteEikonal
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def eikonalResidual (G : σ → σ → MvPolynomial σ ℂ) (S : MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ := 1 + waveQuadratic G (fun i => pderiv i S)

theorem eikonal_initial_order (G : σ → σ → MvPolynomial σ ℂ)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hdG : ∀ i j k, constantCoeff (pderiv k (G i j)) = 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i)
    (hnull : ∑ i, z i * z i = -1)
    (hcompat : ∀ k, ∑ i, z i * constantCoeff (pderiv k (pderiv i S)) = 0) :
    VanishTo (eikonalResidual G S) 2 := by
  apply VanishTo.of_constant_and_linear
  · simp [eikonalResidual, waveQuadratic, hG, hS, hnull]
  · intro k
    simp [eikonalResidual, waveQuadratic, hG, hdG, hS,
      Finset.sum_add_distrib, mul_comm, hcompat]

theorem eikonal_linearization (G : σ → σ → MvPolynomial σ ℂ)
    (S F : MvPolynomial σ ℂ) (z : σ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (hF : VanishTo F (N + 1)) :
    VanishTo (eikonalResidual G (S + F) - eikonalResidual G S -
      2 * waveDirectionalDerivative z F) (N + 1) := by
  have h := waveQuadratic_linearization G (fun i => pderiv i S)
    (fun i => pderiv i F) z N hN hG hS (hF.pderiv)
  simpa only [eikonalResidual, map_add, add_sub_add_left_eq_sub,
    waveDirectionalDerivative_apply, C_mul'] using h

theorem eikonal_raise_order (G : σ → σ → MvPolynomial σ ℂ)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i)
    (hE : VanishTo (eikonalResidual G S) N) :
    ∃ F : MvPolynomial σ ℂ, F.IsHomogeneous (N + 1) ∧
      VanishTo (eikonalResidual G (S + F)) (N + 1) := by
  let P := homogeneousComponent N (eikonalResidual G S)
  have hP : P.IsHomogeneous N := homogeneousComponent_isHomogeneous _ _
  have hf : ((-((2 : ℂ)⁻¹)) • P).IsHomogeneous N := by
    simpa only [C_mul'] using hP.C_mul (-((2 : ℂ)⁻¹))
  obtain ⟨F, hF, hDF⟩ := wave_homogeneous_primitive z hz N _ hf
  have hD : 2 * waveDirectionalDerivative z F = -P := by
    rw [hDF, two_mul, ← add_smul]
    norm_num
  have hl := eikonal_linearization G S F z N hN hG hS
    (VanishTo.of_homogeneous hF)
  refine ⟨F, hF, ?_⟩
  have h := hl.add hE.remove_component
  convert h using 1
  rw [hD]
  dsimp [P]
  ring

theorem finite_eikonal_completion (G : σ → σ → MvPolynomial σ ℂ)
    (S₀ : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS₀ : ∀ i, constantCoeff (pderiv i S₀) = z i)
    (hE₀ : VanishTo (eikonalResidual G S₀) 2) (k : ℕ) :
    ∃ S : MvPolynomial σ ℂ,
      VanishTo (S - S₀) 3 ∧ VanishTo (eikonalResidual G S) (k + 2) ∧
      S.totalDegree ≤ max S₀.totalDegree (k + 2) := by
  induction k with
  | zero =>
      exact ⟨S₀, by simpa using VanishTo.zero (σ := σ) (R := ℂ) 3,
        hE₀, le_max_left _ _⟩
  | succ k ih =>
      obtain ⟨S, hdiff, hE, hdeg⟩ := ih
      have hS (i : σ) : constantCoeff (pderiv i S) = z i := by
        have hd := (hdiff.pderiv i).constantCoeff_eq_zero (by decide)
        rw [map_sub, map_sub] at hd
        exact (sub_eq_zero.mp hd).trans (hS₀ i)
      obtain ⟨F, hF, hEF⟩ := eikonal_raise_order G S z hz (k + 2) (by omega) hG hS hE
      refine ⟨S + F, ?_, ?_, ?_⟩
      · have hv : VanishTo F 3 := (VanishTo.of_homogeneous hF).mono (by omega)
        convert hdiff.add hv using 1
        ring
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 2] using hEF
      · have hfdeg := hF.totalDegree_le
        have hd := totalDegree_add S F
        omega

end FiniteEikonal

section FiniteTransport
open MvPolynomial
variable {σ : Type*} [Fintype σ]

def waveTransport (A : σ → MvPolynomial σ ℂ) (B V : MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ := (∑ i, A i * pderiv i V) + B * V

theorem waveTransport_add (A : σ → MvPolynomial σ ℂ) (B V W : MvPolynomial σ ℂ) :
    waveTransport A B (V + W) = waveTransport A B V + waveTransport A B W := by
  simp only [waveTransport, map_add, mul_add, Finset.sum_add_distrib]
  ring

theorem transport_linearization (A : σ → MvPolynomial σ ℂ) (B : MvPolynomial σ ℂ)
    (z : σ → ℂ) (N : ℕ) (hA : ∀ i, constantCoeff (A i) = 2 * z i)
    (F : MvPolynomial σ ℂ) (hF : VanishTo F (N + 1)) :
    VanishTo (waveTransport A B F - 2 * waveDirectionalDerivative z F) (N + 1) := by
  have hd (i : σ) : VanishTo ((A i - C (2 * z i)) * pderiv i F) (N + 1) := by
    have ha : VanishTo (A i - C (2 * z i)) 1 := by
      apply VanishTo.of_constantCoeff_eq_zero
      simp [hA]
    simpa only [Nat.add_comm 1] using ha.mul (hF.pderiv i)
  have H := (VanishTo.sum Finset.univ (fun i _ => hd i)).add (hF.mul_left B)
  convert H using 1
  simp only [waveTransport, waveDirectionalDerivative_apply, sub_mul, Finset.sum_sub_distrib,
    ← C_mul', map_mul, map_ofNat, Finset.mul_sum]
  ring_nf

theorem transport_raise_order (A : σ → MvPolynomial σ ℂ)
    (B V forcing : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0) (N : ℕ)
    (hA : ∀ i, constantCoeff (A i) = 2 * z i)
    (hR : VanishTo (waveTransport A B V + forcing) N) :
    ∃ F : MvPolynomial σ ℂ, F.IsHomogeneous (N + 1) ∧
      VanishTo (waveTransport A B (V + F) + forcing) (N + 1) := by
  let P := homogeneousComponent N (waveTransport A B V + forcing)
  have hP : P.IsHomogeneous N := homogeneousComponent_isHomogeneous _ _
  have hf : ((-((2 : ℂ)⁻¹)) • P).IsHomogeneous N := by
    simpa only [C_mul'] using hP.C_mul (-((2 : ℂ)⁻¹))
  obtain ⟨F, hF, hDF⟩ := wave_homogeneous_primitive z hz N _ hf
  have hD : 2 * waveDirectionalDerivative z F = -P := by
    rw [hDF, two_mul, ← add_smul]
    norm_num
  have hl := transport_linearization A B z N hA F (VanishTo.of_homogeneous hF)
  refine ⟨F, hF, ?_⟩
  have h := hl.add hR.remove_component
  convert h using 1
  rw [hD, waveTransport_add]
  dsimp [P]
  ring

theorem finite_transport_completion (A : σ → MvPolynomial σ ℂ)
    (B forcing : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hA : ∀ i, constantCoeff (A i) = 2 * z i) (c : ℂ) (N : ℕ) :
    ∃ V : MvPolynomial σ ℂ, constantCoeff V = c ∧
      VanishTo (waveTransport A B V + forcing) N ∧ V.totalDegree ≤ N := by
  induction N with
  | zero =>
      exact ⟨C c, by simp, VanishTo.order_zero _, by simp⟩
  | succ N ih =>
      obtain ⟨V, hc, hR, hdeg⟩ := ih
      obtain ⟨F, hF, hRF⟩ := transport_raise_order A B V forcing z hz N hA hR
      refine ⟨V + F, ?_, hRF, ?_⟩
      · have hcf := (VanishTo.of_homogeneous hF).constantCoeff_eq_zero (by omega)
        simp [hc, hcf]
      · exact (totalDegree_add V F).trans (max_le (by omega) hF.totalDegree_le)

end FiniteTransport
section QuadraticSeed
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def wavePhaseSeed (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) : MvPolynomial σ ℂ :=
  C c + (∑ i, C (z i) * X i) +
    (2 : ℂ)⁻¹ • (∑ i, ∑ j, C (Q i j) * X i * X j)

omit [DecidableEq σ] in
@[simp] theorem wavePhaseSeed_constantCoeff (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) :
    constantCoeff (wavePhaseSeed c z Q) = c := by
  simp [wavePhaseSeed]

@[simp] theorem wavePhaseSeed_gradient (c : ℂ) (z : σ → ℂ)
    (Q : σ → σ → ℂ) (k : σ) :
    constantCoeff (pderiv k (wavePhaseSeed c z Q)) = z k := by
  simp [wavePhaseSeed, Pi.single_apply, Finset.sum_add_distrib]

@[simp] theorem wavePhaseSeed_hessian (c : ℂ) (z : σ → ℂ)
    (Q : σ → σ → ℂ) (hQ : ∀ i j, Q i j = Q j i) (k l : σ) :
    constantCoeff (pderiv k (pderiv l (wavePhaseSeed c z Q))) = Q k l := by
  simp [wavePhaseSeed, Pi.single_apply, Finset.sum_add_distrib, hQ l k]
  ring

theorem wavePhaseSeed_eikonal (G : σ → σ → MvPolynomial σ ℂ)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hdG : ∀ i j k, constantCoeff (pderiv k (G i j)) = 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i * z i = -1)
    (hQz : ∀ k, ∑ i, z i * Q k i = 0) :
    VanishTo (eikonalResidual G (wavePhaseSeed c z Q)) 2 := by
  apply eikonal_initial_order G _ z hG hdG (wavePhaseSeed_gradient c z Q) hnull
  intro k
  simpa only [wavePhaseSeed_hessian c z Q hQ] using hQz k

end QuadraticSeed

open MvPolynomial
variable {σ : Type*} [Fintype σ]

def wavePrimitive (z : σ → ℂ) (d : ℕ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  wavePrimitiveTerm z (waveLinearCoordinate z) d 0 p

theorem wavePrimitive_homogeneous (z : σ → ℂ) (d : ℕ)
    (p : MvPolynomial σ ℂ) (hp : p.IsHomogeneous d) :
    (wavePrimitive z d p).IsHomogeneous (d + 1) := by
  simpa only [wavePrimitive, zero_add, add_zero] using
    wavePrimitiveTerm_homogeneous z (waveLinearCoordinate z)
      (waveLinearCoordinate_homogeneous z) d 0 p hp

theorem wavePrimitive_derivative (z : σ → ℂ) (hz : z ≠ 0) (d : ℕ)
    (p : MvPolynomial σ ℂ) (hp : p.IsHomogeneous d) :
    waveDirectionalDerivative z (wavePrimitive z d p) = p := by
  simpa only [wavePrimitive, pow_zero, one_mul] using
    wavePrimitiveTerm_derivative z (waveLinearCoordinate z)
      (waveLinearCoordinate_derivative z hz) d 0 p hp

def eikonalCorrection (G : σ → σ → MvPolynomial σ ℂ) (z : σ → ℂ)
    (N : ℕ) (S : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  wavePrimitive z N (-((2 : ℂ)⁻¹) • homogeneousComponent N (eikonalResidual G S))

theorem eikonalCorrection_homogeneous (G : σ → σ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (N : ℕ) (S : MvPolynomial σ ℂ) :
    (eikonalCorrection G z N S).IsHomogeneous (N + 1) := by
  apply wavePrimitive_homogeneous
  simpa only [C_mul'] using
    (homogeneousComponent_isHomogeneous N (eikonalResidual G S)).C_mul (-((2 : ℂ)⁻¹))

variable [DecidableEq σ]

theorem eikonalCorrection_raises (G : σ → σ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (hz : z ≠ 0) (N : ℕ) (hN : 1 ≤ N) (S : MvPolynomial σ ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i)
    (hE : VanishTo (eikonalResidual G S) N) :
    VanishTo (eikonalResidual G (S + eikonalCorrection G z N S)) (N + 1) := by
  have hp : (-((2 : ℂ)⁻¹) • homogeneousComponent N (eikonalResidual G S)).IsHomogeneous N := by
    simpa only [C_mul'] using
      (homogeneousComponent_isHomogeneous N (eikonalResidual G S)).C_mul (-((2 : ℂ)⁻¹))
  have hd : 2 * waveDirectionalDerivative z (eikonalCorrection G z N S) =
      -homogeneousComponent N (eikonalResidual G S) := by
    rw [eikonalCorrection, wavePrimitive_derivative z hz N _ hp, two_mul, ← add_smul]
    norm_num
  have hl := eikonal_linearization G S (eikonalCorrection G z N S) z N hN hG hS
    (VanishTo.of_homogeneous (eikonalCorrection_homogeneous G z N S))
  have H := hl.add hE.remove_component
  convert H using 1
  rw [hd]
  ring

def eikonalIter (G : σ → σ → MvPolynomial σ ℂ) (z : σ → ℂ)
    (S₀ : MvPolynomial σ ℂ) : ℕ → MvPolynomial σ ℂ
  | 0 => S₀
  | k + 1 => eikonalIter G z S₀ k +
      eikonalCorrection G z (k + 2) (eikonalIter G z S₀ k)

theorem eikonalIter_spec (G : σ → σ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (hz : z ≠ 0) (S₀ : MvPolynomial σ ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS₀ : ∀ i, constantCoeff (pderiv i S₀) = z i)
    (hE₀ : VanishTo (eikonalResidual G S₀) 2) (k : ℕ) :
    VanishTo (eikonalIter G z S₀ k - S₀) 3 ∧
    VanishTo (eikonalResidual G (eikonalIter G z S₀ k)) (k + 2) ∧
    (eikonalIter G z S₀ k).totalDegree ≤ max S₀.totalDegree (k + 2) := by
  induction k with
  | zero =>
    exact ⟨by simpa [eikonalIter] using VanishTo.zero (σ := σ) (R := ℂ) 3,
      hE₀, le_max_left _ _⟩
  | succ k ih =>
    obtain ⟨hdiff, hE, hdeg⟩ := ih
    have hS (i : σ) : constantCoeff (pderiv i (eikonalIter G z S₀ k)) = z i := by
      have hd := (hdiff.pderiv i).constantCoeff_eq_zero (by decide)
      rw [map_sub, map_sub] at hd
      exact (sub_eq_zero.mp hd).trans (hS₀ i)
    have hF := eikonalCorrection_homogeneous G z (k + 2) (eikonalIter G z S₀ k)
    refine ⟨?_, ?_, ?_⟩
    · have hv : VanishTo (eikonalCorrection G z (k + 2) (eikonalIter G z S₀ k)) 3 :=
        (VanishTo.of_homogeneous hF).mono (by omega)
      convert hdiff.add hv using 1
      simp only [eikonalIter]
      ring
    · simpa only [eikonalIter, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 2] using
        eikonalCorrection_raises G z hz (k + 2) (by omega) _ hG hS hE
    · have hfdeg := hF.totalDegree_le
      have hd := totalDegree_add (eikonalIter G z S₀ k)
        (eikonalCorrection G z (k + 2) (eikonalIter G z S₀ k))
      simp only [eikonalIter]
      omega

variable {X : Type*} [TopologicalSpace X]

omit [DecidableEq σ] in
theorem eikonalResidual_coeffContinuous (G : X → σ → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, CoeffContinuous (fun x => G x i j)) (S : X → MvPolynomial σ ℂ)
    (hS : CoeffContinuous S) : CoeffContinuous (fun x => eikonalResidual (G x) (S x)) := by
  apply (CoeffContinuous.const 1).add
  apply CoeffContinuous.sum
  intro i _
  apply CoeffContinuous.sum
  intro j _
  exact ((hG i j).mul (hS.pderiv i)).mul (hS.pderiv j)

omit [DecidableEq σ] in
theorem eikonalIter_coeffContinuous (G : X → σ → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, CoeffContinuous (fun x => G x i j)) (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (hz₀ : ∀ x, z x ≠ 0)
    (S₀ : X → MvPolynomial σ ℂ) (hS₀ : CoeffContinuous S₀) (k : ℕ) :
    CoeffContinuous (fun x => eikonalIter (G x) (z x) (S₀ x) k) := by
  induction k with
  | zero => exact hS₀
  | succ k ih =>
    apply ih.add
    apply canonical_wavePrimitive_coeffContinuous z hz hz₀
    exact ((eikonalResidual_coeffContinuous G hG _ ih).homogeneousComponent (k + 2)).smul
      continuous_const



end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vanishing_jet_norm_bound (f : E → F) (hf : ContDiff ℝ ∞ f)
    (N : ℕ) (r C : ℝ) (hC : 0 ≤ C)
    (hzero : ∀ j < N, iteratedFDeriv ℝ j f 0 = 0)
    (hbound : ∀ x ∈ Metric.ball (0 : E) r, ‖iteratedFDeriv ℝ N f x‖ ≤ C) :
    ∀ k ≤ N, ∀ x ∈ Metric.ball (0 : E) r,
      ‖iteratedFDeriv ℝ (N - k) f x‖ ≤ C * ‖x‖ ^ k := by
  intro k
  induction k with
  | zero =>
    intro _ x hx
    simpa using hbound x hx
  | succ k ih =>
    intro hk x hx
    have hxnorm : ‖x‖ < r := by simpa using hx
    have hyball : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖, y ∈ Metric.ball (0 : E) r := by
      intro y hy
      have hxy : ‖y‖ ≤ ‖x‖ := by simpa using hy
      simpa using hxy.trans_lt hxnorm
    have hd : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖,
        DifferentiableAt ℝ (iteratedFDeriv ℝ (N - (k + 1)) f) y := by
      intro y _
      exact hf.differentiable_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (N - (k + 1)))) y
    have hb : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖,
        ‖fderiv ℝ (iteratedFDeriv ℝ (N - (k + 1)) f) y‖ ≤ C * ‖x‖ ^ k := by
      intro y hy
      rw [norm_fderiv_iteratedFDeriv, show N - (k + 1) + 1 = N - k by omega]
      have h := ih (by omega) y (hyball y hy)
      have hxy : ‖y‖ ≤ ‖x‖ := by simpa using hy
      exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxy _) hC)
    have hm := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le hd hb
      (Metric.mem_closedBall_self (norm_nonneg x))
      (show x ∈ Metric.closedBall (0 : E) ‖x‖ by simp)
    rw [hzero (N - (k + 1)) (by omega), sub_zero, sub_zero] at hm
    simpa only [pow_succ, mul_assoc] using hm

theorem vanishing_jet_local_bound [FiniteDimensional ℝ E]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (N : ℕ) (r : ℝ)
    (hzero : ∀ j < N, iteratedFDeriv ℝ j f 0 = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ N, ∀ x ∈ Metric.ball (0 : E) r,
      ‖iteratedFDeriv ℝ (N - k) f x‖ ≤ C * ‖x‖ ^ k := by
  have hcont : Continuous (iteratedFDeriv ℝ N f) :=
    hf.continuous_iteratedFDeriv
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top N)))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) r).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  apply vanishing_jet_norm_bound f hf N r (max C 1)
    (le_trans zero_le_one (le_max_right _ _)) hzero
  intro x hx
  exact (hC x (Metric.ball_subset_closedBall hx)).trans (le_max_left _ _)


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section ActualEikonal
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem realPolyEval_at_zero (p : MvPolynomial σ ℂ) :
    realPolyEval p 0 = constantCoeff p := by
  simp [realPolyEval]

theorem realTaylorPolynomial_constant {f : (σ → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) {N : ℕ} (hN : 0 < N) :
    constantCoeff (realTaylorPolynomial f N) = f 0 := by
  have h := realTaylorPolynomial_jet hf N 0 hN
  have hh := congrArg (fun B => B (fun i : Fin 0 => nomatch i)) h
  simpa only [iteratedFDeriv_zero_apply, realPolyEval_at_zero] using hh

theorem realTaylorPolynomial_linear {f : (σ → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) {N : ℕ} (hN : 1 < N) (i : σ) :
    constantCoeff (pderiv i (realTaylorPolynomial f N)) =
      fderiv ℝ f 0 (Pi.single i 1) := by
  classical
  have h := realTaylorPolynomial_jet hf N 1 hN
  have hh := congrArg (fun B => B (fun _ => Pi.single i 1)) h
  simpa [iteratedFDeriv_one_apply, fderiv_realPolyEval, Pi.single_apply, apply_ite] using hh

theorem realTaylorPolynomial_remainder {f : (σ → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (N : ℕ) :
    SmoothJetZero (f - realPolyEval (realTaylorPolynomial f N)) N := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  rw [iteratedFDeriv_sub_apply (hf.of_le hle).contDiffAt
    ((contDiff_realPolyEval _).of_le hle).contDiffAt,
    realTaylorPolynomial_jet hf N k hk, sub_self]

omit [DecidableEq σ] in
theorem VanishTo.realPolyEval {p : MvPolynomial σ ℂ} {N : ℕ} (h : VanishTo p N) :
    SmoothJetZero (YauCounterexamples.realPolyEval p) N := by
  intro k hk
  apply realPolyEval_jet_zero_of_coeff
  exact fun d hd => h d (by omega)

def smoothEikonalResidual (g : σ → σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) :
    (σ → ℝ) → ℂ := fun x => 1 + ∑ i, ∑ j,
      g i j x * realPolyEval (pderiv i S) x * realPolyEval (pderiv j S) x

omit [DecidableEq σ] in
theorem contDiff_smoothEikonalResidual (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (S : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (smoothEikonalResidual g S) := by
  apply contDiff_const.add
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact ((hg i j).mul (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)

theorem smoothEikonalResidual_jet (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (S : MvPolynomial σ ℂ) (N : ℕ)
    (hE : VanishTo (eikonalResidual (fun i j => realTaylorPolynomial (g i j) N) S) N) :
    SmoothJetZero (smoothEikonalResidual g S) N := by
  let G := fun i j => realTaylorPolynomial (g i j) N
  let D : σ → σ → (σ → ℝ) → ℂ := fun i j x =>
    (g i j x - realPolyEval (G i j) x) *
      realPolyEval (pderiv i S) x * realPolyEval (pderiv j S) x
  have hd (i j : σ) : ContDiff ℝ ∞ (D i j) :=
    (((hg i j).sub (contDiff_realPolyEval _)).mul
      (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hdj (i j : σ) : SmoothJetZero (D i j) N :=
    ((realTaylorPolynomial_remainder (hg i j) N).mul_right
      ((hg i j).sub (contDiff_realPolyEval _)) _ (contDiff_realPolyEval _)).mul_right
        (((hg i j).sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)) _
        (contDiff_realPolyEval _)
  have hc (i : σ) : ContDiff ℝ ∞ (∑ j, D i j) := by
    simpa only [Finset.sum_fn] using
      (ContDiff.sum (s := Finset.univ) (fun j _ => hd i j))
  have hcs : ContDiff ℝ ∞ (∑ i, ∑ j, D i j) := by
    simpa only [Finset.sum_fn] using
      (ContDiff.sum (s := Finset.univ) (fun i _ => hc i))
  have hds : SmoothJetZero (∑ i, ∑ j, D i j) N :=
    SmoothJetZero.sum Finset.univ _ (fun i _ => hc i)
      (fun i _ => SmoothJetZero.sum Finset.univ _ (fun j _ => hd i j) (fun j _ => hdj i j))
  have heq : smoothEikonalResidual g S =
      realPolyEval (eikonalResidual G S) + ∑ i, ∑ j, D i j := by
    funext x
    simp only [smoothEikonalResidual, eikonalResidual, waveQuadratic, Pi.add_apply,
      Finset.sum_apply, realPolyEval, map_add, map_one, map_sum, map_mul, D]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact hE.realPolyEval.add (contDiff_realPolyEval _)
    hcs hds

theorem smooth_finite_eikonal (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ i j, fderiv ℝ (g i j) 0 = 0)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (hz : z ≠ 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i * z i = -1)
    (hQz : ∀ k, ∑ i, z i * Q k i = 0) (k : ℕ) (r : ℝ) :
    ∃ S : MvPolynomial σ ℂ, ∃ C : ℝ, 0 < C ∧
      SmoothJetZero (realPolyEval S - realPolyEval (wavePhaseSeed c z Q)) 3 ∧
      S.totalDegree ≤ max (wavePhaseSeed c z Q).totalDegree (k + 2) ∧
      (∀ j ≤ k + 2, ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
        ‖iteratedFDeriv ℝ (k + 2 - j) (smoothEikonalResidual g S) x‖ ≤ C * ‖x‖ ^ j) := by
  let G := fun i j => realTaylorPolynomial (g i j) (k + 2)
  have hG (i j : σ) : constantCoeff (G i j) = if i = j then 1 else 0 :=
    (realTaylorPolynomial_constant (hg i j) (by omega)).trans (hg0 i j)
  have hdG (i j l : σ) : constantCoeff (pderiv l (G i j)) = 0 := by
    rw [realTaylorPolynomial_linear (hg i j) (by omega), hdg0 i j]
    rfl
  obtain ⟨S, hS, hE, hdeg⟩ := finite_eikonal_completion G (wavePhaseSeed c z Q) z hz
    hG (wavePhaseSeed_gradient c z Q)
    (wavePhaseSeed_eikonal G c z Q hG hdG hQ hnull hQz) k
  have he := smoothEikonalResidual_jet g hg S (k + 2) hE
  obtain ⟨C, hC, hb⟩ := vanishing_jet_local_bound (smoothEikonalResidual g S)
    (contDiff_smoothEikonalResidual g hg S) (k + 2) r he
  refine ⟨S, C, hC, ?_, hdeg, hb⟩
  convert hS.realPolyEval using 1
  funext x
  simp [realPolyEval]

end ActualEikonal

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def smoothWaveTransport (a : σ → (σ → ℝ) → ℂ) (b : (σ → ℝ) → ℂ)
    (V : MvPolynomial σ ℂ) : (σ → ℝ) → ℂ :=
  fun x => (∑ i, a i x * realPolyEval (pderiv i V) x) + b x * realPolyEval V x

omit [DecidableEq σ] in
theorem contDiff_smoothWaveTransport (a : σ → (σ → ℝ) → ℂ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (b : (σ → ℝ) → ℂ)
    (hb : ContDiff ℝ ∞ b) (V : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (smoothWaveTransport a b V) :=
  (ContDiff.sum (fun i _ => (ha i).mul (contDiff_realPolyEval _))).add
    (hb.mul (contDiff_realPolyEval _))

theorem smoothWaveTransport_jet (a : σ → (σ → ℝ) → ℂ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (b f : (σ → ℝ) → ℂ)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f)
    (V : MvPolynomial σ ℂ) (N : ℕ)
    (hR : VanishTo (waveTransport (fun i => realTaylorPolynomial (a i) N)
      (realTaylorPolynomial b N) V + realTaylorPolynomial f N) N) :
    SmoothJetZero (smoothWaveTransport a b V + f) N := by
  let A := fun i => realTaylorPolynomial (a i) N
  let B := realTaylorPolynomial b N
  let F := realTaylorPolynomial f N
  let D := fun i x => (a i x - realPolyEval (A i) x) * realPolyEval (pderiv i V) x
  let D₀ := fun x => (b x - realPolyEval B x) * realPolyEval V x
  have hD (i : σ) : ContDiff ℝ ∞ (D i) :=
    ((ha i).sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hD₀ : ContDiff ℝ ∞ D₀ :=
    (hb.sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hDs : ContDiff ℝ ∞ (∑ i, D i) := by
    simpa only [Finset.sum_fn] using (ContDiff.sum (s := Finset.univ) (fun i _ => hD i))
  have hj (i : σ) : SmoothJetZero (D i) N :=
    (realTaylorPolynomial_remainder (ha i) N).mul_right
      ((ha i).sub (contDiff_realPolyEval _)) _ (contDiff_realPolyEval _)
  have hj₀ : SmoothJetZero D₀ N :=
    (realTaylorPolynomial_remainder hb N).mul_right
      (hb.sub (contDiff_realPolyEval _)) _ (contDiff_realPolyEval _)
  have hjs : SmoothJetZero (∑ i, D i) N :=
    SmoothJetZero.sum Finset.univ _ (fun i _ => hD i) (fun i _ => hj i)
  have heq : smoothWaveTransport a b V + f =
      realPolyEval (waveTransport A B V + F) +
        ((∑ i, D i) + D₀ + (f - realPolyEval F)) := by
    funext x
    simp only [smoothWaveTransport, waveTransport, Pi.add_apply, Pi.sub_apply,
      Finset.sum_apply, realPolyEval, map_add, map_sum, map_mul, D, D₀]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact hR.realPolyEval.add (contDiff_realPolyEval _)
    ((hDs.add hD₀).add (hf.sub (contDiff_realPolyEval _)))
    ((hjs.add hDs hD₀ hj₀).add (hDs.add hD₀) (hf.sub (contDiff_realPolyEval _))
      (realTaylorPolynomial_remainder hf N))

theorem smooth_finite_transport (a : σ → (σ → ℝ) → ℂ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (b f : (σ → ℝ) → ℂ)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f)
    (z : σ → ℂ) (hz : z ≠ 0) (ha0 : ∀ i, a i 0 = 2 * z i)
    (c : ℂ) (N : ℕ) (r : ℝ) :
    ∃ V : MvPolynomial σ ℂ, realPolyEval V 0 = c ∧ V.totalDegree ≤ N ∧
      ∃ C : ℝ, 0 < C ∧ ∀ j ≤ N, ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
        ‖iteratedFDeriv ℝ (N - j) (smoothWaveTransport a b V + f) x‖ ≤ C * ‖x‖ ^ j := by
  by_cases hN : N = 0
  · subst N
    obtain ⟨C, hC, hbound⟩ := vanishing_jet_local_bound
      (smoothWaveTransport a b (C c) + f)
      ((contDiff_smoothWaveTransport a ha b hb _).add hf) 0 r
      (SmoothJetZero.order_zero _)
    exact ⟨MvPolynomial.C c, by simp, by simp, C, hC, hbound⟩
  · let A := fun i => realTaylorPolynomial (a i) N
    have hA (i : σ) : constantCoeff (A i) = 2 * z i :=
      (realTaylorPolynomial_constant (ha i) (Nat.pos_of_ne_zero hN)).trans (ha0 i)
    obtain ⟨V, hV, hR, hdeg⟩ := finite_transport_completion A
      (realTaylorPolynomial b N) (realTaylorPolynomial f N) z hz hA c N
    have hj := smoothWaveTransport_jet a ha b f hb hf V N hR
    obtain ⟨C, hC, hbound⟩ := vanishing_jet_local_bound (smoothWaveTransport a b V + f)
      ((contDiff_smoothWaveTransport a ha b hb V).add hf) N r hj
    exact ⟨V, by simpa using hV, hdeg, C, hC, hbound⟩



end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ]

def boundedDegreeMonomials (N : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (σ:=σ) N).toFinset

theorem bounded_degree_expansion (p : MvPolynomial σ ℂ) (N : ℕ)
    (hp : p.totalDegree ≤ N) :
    p = ∑ m ∈ boundedDegreeMonomials (σ:=σ) N, monomial m (p.coeff m) := by
  classical
  conv_lhs => rw [p.as_sum]
  apply Finset.sum_subset
  · intro m hm
    exact (Finsupp.finite_of_degree_le (σ:=σ) N).mem_toFinset.mpr ((le_totalDegree hm).trans hp)
  · intro m _ hm
    simp [notMem_support_iff.mp hm]

theorem realPolyEval_bounded_degree (p : MvPolynomial σ ℂ) (N : ℕ)
    (hp : p.totalDegree ≤ N) :
    realPolyEval p = fun x => ∑ m ∈ boundedDegreeMonomials (σ:=σ) N,
      p.coeff m • realPolyEval (monomial m 1) x := by
  classical
  conv_lhs => rw [bounded_degree_expansion p N hp]
  funext x
  simp [realPolyEval,smul_eq_mul,MvPolynomial.eval_monomial]

variable {X : Type*} [TopologicalSpace X]

theorem continuous_polynomial_jets (P : X → MvPolynomial σ ℂ) (hP : CoeffContinuous P)
    (N : ℕ) (hN : ∀ p, (P p).totalDegree ≤ N) (k : ℕ) :
    Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (realPolyEval (P q.1)) q.2) := by
  classical
  have heq (p : X) (x : σ → ℝ) : iteratedFDeriv ℝ k (realPolyEval (P p)) x =
      ∑ m ∈ boundedDegreeMonomials (σ:=σ) N,
        (P p).coeff m • iteratedFDeriv ℝ k (realPolyEval (monomial m 1)) x := by
    rw [realPolyEval_bounded_degree (P p) N (hN p),iteratedFDeriv_fun_sum_apply
      (fun m _ => ((contDiff_realPolyEval (monomial m 1)).const_smul _).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))) |>.contDiffAt)]
    apply Finset.sum_congr rfl
    intro m _
    exact iteratedFDeriv_const_smul_apply'
      ((contDiff_realPolyEval (monomial m 1)).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))) |>.contDiffAt)
  simp only [heq]
  apply continuous_finsetSum
  intro m _
  exact ((hP m).comp continuous_fst).smul
    (((contDiff_realPolyEval (monomial m 1)).continuous_iteratedFDeriv (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).comp continuous_snd)

theorem compact_uniform_polynomial_jets (P : X → MvPolynomial σ ℂ)
    (hP : CoeffContinuous P) (N : ℕ) (hN : ∀ p, (P p).totalDegree ≤ N)
    {K : Set X} (hK : IsCompact K) {B : Set (σ → ℝ)} (hB : IsCompact B) (k : ℕ) :
    ∃ C > 0, ∀ p ∈ K, ∀ x ∈ B, ‖iteratedFDeriv ℝ k (realPolyEval (P p)) x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hK.prod hB).exists_bound_of_continuousOn
    ((continuous_polynomial_jets P hP N hN k).continuousOn)
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro p hp x hx
  exact (hC (p,x) ⟨hp,hx⟩).trans (le_max_left _ _)



end YauCounterexamples
end

end OAI
