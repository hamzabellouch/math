import Mathlib
import OAI.Computability.QuantumFactoring.OrderTrialFurther2

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Integer arithmetic at grid points.  The only root of unity is -i. -/
def minusI : GaussianInt := ⟨0,-1⟩

lemma minusI_cast : (minusI:ℂ) = -Complex.I := by
  simp [minusI, GaussianInt.toComplex_def]

def gridPhaseNumerator (Q y : ℕ) : GaussianInt :=
  ((Q-(4*y)%Q:ℕ):GaussianInt)*minusI^((4*y)/Q) +
    (((4*y)%Q:ℕ):GaussianInt)*minusI^((4*y)/Q+1)

lemma phase_grid_numerator {Q : ℕ} (hQ : 0 < Q) (y : ℕ) :
    phase ((y:ℝ)/Q) = (gridPhaseNumerator Q y:ℂ)/(Q:ℂ) := by
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hQc : (Q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hr : (4*y)%Q < Q := Nat.mod_lt _ hQ
  have hr' : (0:ℝ) ≤ ((4*y)%Q:ℕ) := Nat.cast_nonneg _
  have hle : (((4*y)%Q:ℕ):ℝ) ≤ Q := by exact_mod_cast hr.le
  have ht₀ : 0 ≤ (((4*y)%Q:ℕ):ℝ)/Q := div_nonneg hr' hQ'.le
  have ht₁ : (((4*y)%Q:ℕ):ℝ)/Q ≤ 1 := (div_le_one hQ').mpr hle
  have he : ((((4*y)/Q:ℕ):ℝ)+(((4*y)%Q:ℕ):ℝ)/Q)/4 = (y:ℝ)/Q := by
    have h := Nat.mod_add_div (4*y) Q
    have h' : (((4*y)%Q:ℕ):ℝ)+(Q:ℝ)*((4*y)/Q:ℕ) = 4*y := by exact_mod_cast h
    field_simp
    nlinarith
  have hg := phase_interpolates (((4*y)/Q:ℕ):ℤ) ht₀ ht₁
  rw [show (((4*y)/Q:ℕ):ℤ)+1 = (((4*y)/Q+1:ℕ):ℤ) by simp] at hg
  simp only [Int.cast_natCast, zpow_natCast] at hg
  rw [he] at hg
  rw [hg]
  simp only [gridPhaseNumerator, map_add, map_sub, map_mul, map_pow, map_natCast,
    minusI_cast, Nat.cast_sub hr.le, Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp

/-- A literal finite integer sum, used to prove dyadicity independently of the
bounded-piece evaluator.  This sum is NOT asserted to be polynomial-time. -/
def residueGaussianNumerator (Q d j t : ℕ) : GaussianInt :=
  ∑ x ∈ (Finset.range Q).filter (fun x => x%d=t), gridPhaseNumerator Q (bin Q d j*x)

def residueProbabilityRat (Q d j t : ℕ) : ℚ :=
  ((residueGaussianNumerator Q d j t).norm:ℚ)/(Q:ℚ)^4

lemma residueAmplitude_gaussian {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    residueAmplitude Q d j t = (residueGaussianNumerator Q d j t:ℂ)/(Q:ℂ)^2 := by
  have hph : ∀ x : ℕ, phase ((bin Q d j:ℝ)*x/Q) =
      (gridPhaseNumerator Q (bin Q d j*x):ℂ)/(Q:ℂ) := by
    intro x
    simpa only [Nat.cast_mul] using phase_grid_numerator hQ (bin Q d j*x)
  unfold residueAmplitude
  simp_rw [hph]
  rw [← Finset.sum_div]
  simp only [residueGaussianNumerator, map_sum]
  ring

lemma residueProbabilityRat_cast {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    (residueProbabilityRat Q d j t:ℝ) = residueProbability Q d j t := by
  rw [residueProbability, residueAmplitude_gaussian hQ, norm_div, norm_pow,
    Complex.norm_natCast, div_pow, ← Complex.normSq_eq_norm_sq,
    ← GaussianInt.intCast_real_norm]
  simp only [residueProbabilityRat, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_intCast]
  ring

lemma residueProbabilityRat_nonneg (Q d j t : ℕ) : 0 ≤ residueProbabilityRat Q d j t := by
  unfold residueProbabilityRat
  exact div_nonneg (Int.cast_nonneg (GaussianInt.norm_nonneg _)) (by positivity)

lemma residueProbabilityRat_le_one {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    residueProbabilityRat Q d j t ≤ 1 := by
  have h := residueAmplitude_norm_le hQ d j t
  have h' : (residueProbabilityRat Q d j t:ℝ) ≤ 1 := by
    rw [residueProbabilityRat_cast hQ, residueProbability]
    nlinarith [norm_nonneg (residueAmplitude Q d j t)]
  exact_mod_cast h'

lemma residueProbability_dyadic (b d j t : ℕ) :
    IsDyadic (residueProbabilityRat (2^b) d j t) := by
  refine ⟨b*4,(residueGaussianNumerator (2^b) d j t).norm,?_⟩
  simp only [residueProbabilityRat, Nat.cast_pow, Nat.cast_ofNat, pow_mul]

/-- An explicit 4b-bit denominator, and numerator bounded by that denominator. -/
lemma residueProbability_numerator_bounds {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    0 ≤ (residueGaussianNumerator Q d j t).norm ∧
      (residueGaussianNumerator Q d j t).norm ≤ (Q:ℤ)^4 := by
  refine ⟨GaussianInt.norm_nonneg _,?_⟩
  have h := residueProbabilityRat_le_one hQ d j t
  have he : ((residueGaussianNumerator Q d j t).norm:ℚ) ≤ (Q:ℚ)^4 := by
    exact (div_le_one (by positivity : (0:ℚ) < (Q:ℚ)^4)).mp h
  exact_mod_cast he

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

noncomputable def phaseLabel (m y : ℕ) : ℂ := Complex.I^(y/m)

lemma phaseLabel_mod (m y : ℕ) : phaseLabel m (y%(4*m)) = phaseLabel m y := by
  unfold phaseLabel
  rw [Nat.mod_mul_left_div_self, ← Complex.I_pow_eq_pow_mod]

lemma phaseLabel_tile {m : ℕ} (hm : 0 < m) (a : ℕ) {u : ℕ} (hu : u < m) :
    phaseLabel m (a*m+u) = Complex.I^a := by
  unfold phaseLabel
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hu, zero_add]

lemma phaseLabel_correlation {m : ℕ} (hm : 0 < m) (a q : ℕ) {u s : ℕ}
    (hu : u < m) (hs : s < m) :
    star (phaseLabel m ((a*m+u+(q*m+s))%(4*m))) * phaseLabel m (a*m+u) =
      if u+s < m then (-Complex.I)^q else (-Complex.I)^(q+1) := by
  rw [phaseLabel_mod, phaseLabel_tile hm a hu]
  have he : a*m+u+(q*m+s) = (a+q)*m+(u+s) := by ring
  rw [he]
  by_cases h : u+s < m
  · rw [ite_eq_left h, phaseLabel_tile hm (a+q) h, pow_add]
    simp only [star_mul, star_pow, Complex.star_def, Complex.conj_I]
    have hi : (-Complex.I)^a*Complex.I^a = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = ((-Complex.I)^a*Complex.I^a)*(-Complex.I)^q := by ring
      _ = _ := by rw [hi, one_mul]
  · have hb : u+s-m < m := by omega
    have he : (a+q)*m+(u+s) = (a+(q+1))*m+(u+s-m) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    rw [ite_eq_right h, he, phaseLabel_tile hm (a+(q+1)) hb, pow_add]
    simp only [star_mul, star_pow, Complex.star_def, Complex.conj_I]
    have hi : (-Complex.I)^a*Complex.I^a = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = ((-Complex.I)^a*Complex.I^a)*(-Complex.I)^(q+1) := by ring
      _ = _ := by rw [hi, one_mul]

lemma sum_range_tiles {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a m : ℕ) :
    (∑ y ∈ Finset.range (a*m), f y) =
      ∑ i ∈ Finset.range a, ∑ u ∈ Finset.range m, f (i*m+u) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma sum_if_carry {m s : ℕ} (hs : s ≤ m) (v w : ℂ) :
    (∑ u ∈ Finset.range m, if u+s < m then v else w) = (m-s:ℕ)*v+(s:ℂ)*w := by
  have he := Finset.sum_range_add (fun u => if u+s< m then v else w) (m-s) s
  rw [Nat.sub_add_cancel hs] at he
  rw [he]
  have h₁ : (∑ u ∈ Finset.range (m-s), if u+s< m then v else w) = (m-s:ℕ)*v := by
    calc
      _ = ∑ u ∈ Finset.range (m-s), v := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [ite_eq_left (by have := Finset.mem_range.mp hu; omega)]
      _ = _ := by simp
  have h₂ : (∑ u ∈ Finset.range s, if m-s+u+s< m then v else w) = (s:ℂ)*w := by
    calc
      _ = ∑ u ∈ Finset.range s, w := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [ite_eq_right (by omega)]
      _ = _ := by simp
  rw [h₁,h₂]

/-- Unnormalized correlation of the exactly prepared quarter-step state. -/
noncomputable def phaseOverlapSum (m D : ℕ) : ℂ :=
  ∑ y ∈ Finset.range (4*m), star (phaseLabel m ((y+D)%(4*m))) * phaseLabel m y

lemma phaseOverlapSum_eq {m : ℕ} (hm : 0 < m) (q : ℕ) {s : ℕ} (hs : s < m) :
    phaseOverlapSum m (q*m+s) =
      (4*(m-s):ℕ)*(-Complex.I)^q+(4*s:ℕ)*(-Complex.I)^(q+1) := by
  unfold phaseOverlapSum
  rw [sum_range_tiles]
  have h : ∀ a, (∑ u ∈ Finset.range m,
      star (phaseLabel m ((a*m+u+(q*m+s))%(4*m))) * phaseLabel m (a*m+u)) =
      (m-s:ℕ)*(-Complex.I)^q+(s:ℂ)*(-Complex.I)^(q+1) := by
    intro a
    calc
      _ = ∑ u ∈ Finset.range m, if u+s< m then (-Complex.I)^q else (-Complex.I)^(q+1) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact phaseLabel_correlation hm a q (Finset.mem_range.mp hu) hs
      _ = _ := sum_if_carry hs.le _ _
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  ring

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Exact overlap, with its direction fixed by the forward shift. -/
lemma phaseOverlap_eq {m : ℕ} (hm : 0 < m) (D : ℕ) :
    phaseOverlapSum m D/(4*(m:ℂ)) = phase ((D:ℝ)/(4*(m:ℝ))) := by
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hmc : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hs : D%m < m := Nat.mod_lt _ hm
  have hD : D/m*m+D%m=D := by simpa only [Nat.mul_comm] using Nat.div_add_mod D m
  have hov := phaseOverlapSum_eq hm (D/m) hs
  rw [hD] at hov
  have hph := phase_interpolates ((D/m:ℕ):ℤ)
    (div_nonneg (Nat.cast_nonneg (D%m)) hm'.le)
    ((div_le_one hm').mpr (by exact_mod_cast hs.le))
  have he : ((((D/m:ℕ):ℝ)+((D%m:ℕ):ℝ)/m)/4) = (D:ℝ)/(4*(m:ℝ)) := by
    have he' : ((D/m:ℕ):ℝ)*m+((D%m:ℕ):ℝ)=D := by exact_mod_cast hD
    field_simp
    nlinarith
  rw [show ((D/m:ℕ):ℤ)+1 = ((D/m+1:ℕ):ℤ) by simp] at hph
  simp only [Int.cast_natCast, zpow_natCast] at hph
  rw [he] at hph
  rw [hov,hph]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hs.le,
    Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp

noncomputable def phaseState (m y : ℕ) : ℂ :=
  (Real.sqrt (4*(m:ℝ)):ℂ)⁻¹ * phaseLabel m y

lemma phaseState_overlap {m : ℕ} (hm : 0 < m) (D : ℕ) :
    (∑ y ∈ Finset.range (4*m), star (phaseState m ((y+D)%(4*m))) * phaseState m y) =
      phase ((D:ℝ)/(4*(m:ℝ))) := by
  have hs : (Real.sqrt (4*(m:ℝ)):ℂ)^2 = 4*(m:ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  have h (y : ℕ) : star (phaseState m ((y+D)%(4*m))) * phaseState m y =
      (star (phaseLabel m ((y+D)%(4*m))) * phaseLabel m y)/(4*(m:ℂ)) := by
    unfold phaseState
    simp only [star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    rw [← hs]
    ring
  simp_rw [h]
  rw [← Finset.sum_div]
  exact phaseOverlap_eq hm D

lemma phaseState_normalized {m : ℕ} (hm : 0 < m) :
    (∑ y ∈ Finset.range (4*m), Complex.normSq (phaseState m y)) = 1 := by
  have h := phaseState_overlap hm 0
  have he : ∀ y ∈ Finset.range (4*m),
      star (phaseState m ((y+0)%(4*m)))*phaseState m y =
        (Complex.normSq (phaseState m y):ℂ) := by
    intro y hy
    rw [Nat.add_zero, Nat.mod_eq_of_lt (Finset.mem_range.mp hy)]
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [Finset.sum_congr rfl he] at h
  have hz : phase 0=1 := by simpa using phase_zero_quarter (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)≤1)
  simp only [Nat.cast_zero, zero_div, hz] at h
  exact_mod_cast h

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.Exactness
open scoped BigOperators

/-- Source (completion), with its actual downward integer rounding. -/
def completionCoeff (E : ℕ) (z A : ℚ) : ℚ :=
  (⌊(2:ℚ)^E*(z/A)⌋ : ℤ)/(2:ℚ)^E

def completionRemainder (E : ℕ) (z A : ℚ) : ℚ := z-completionCoeff E z A*A

lemma completion_rounding (E : ℕ) {z A : ℚ} (hz : 0 ≤ z) (hA : 0 < A)
    (hzA : z ≤ A) :
    0 ≤ completionCoeff E z A ∧ completionCoeff E z A ≤ 1 ∧
      0 ≤ completionRemainder E z A ∧ completionRemainder E z A < A/2^E := by
  have hD : (0:ℚ) < 2^E := by positivity
  have hx : 0 ≤ (2:ℚ)^E*(z/A) := mul_nonneg hD.le (div_nonneg hz hA.le)
  have hf := Int.floor_le ((2:ℚ)^E*(z/A))
  have hu := Int.lt_floor_add_one ((2:ℚ)^E*(z/A))
  have hfn : (0:ℚ) ≤ (⌊(2:ℚ)^E*(z/A)⌋ : ℤ) :=
    Int.cast_nonneg (Int.floor_nonneg.mpr hx)
  have hc₀ : 0 ≤ completionCoeff E z A := div_nonneg hfn hD.le
  have hc₁ : completionCoeff E z A ≤ z/A := by
    unfold completionCoeff
    apply (div_le_iff₀ hD).mpr
    nlinarith
  have herr : z/A-completionCoeff E z A < 1/(2:ℚ)^E := by
    apply (mul_lt_mul_iff_right₀ hD).mp
    unfold completionCoeff
    rw [mul_sub, mul_div_cancel₀ _ hD.ne', mul_div_cancel₀ _ hD.ne']
    linarith
  have he : completionRemainder E z A = (z/A-completionCoeff E z A)*A := by
    unfold completionRemainder
    rw [sub_mul, div_mul_cancel₀ _ hA.ne']
  refine ⟨hc₀, hc₁.trans ((div_le_one hA).mpr hzA), ?_, ?_⟩
  · rw [he]
    exact mul_nonneg (sub_nonneg.mpr hc₁) hA.le
  · rw [he]
    calc
      _ < (1/(2:ℚ)^E)*A := mul_lt_mul_of_pos_right herr hA
      _ = _ := by ring

/-- Both branch masses include the choice of branch and the guessing probability. -/
lemma completion_mass (W t : ℕ) (s z : ℚ) :
    (1-1/(2:ℚ)^t)*s * completionCoeff (W+t+2) z ((1-1/(2:ℚ)^t)*s) +
    (1/(2:ℚ)^t)*(1/(2:ℚ)^W)*
      (completionRemainder (W+t+2) z ((1-1/(2:ℚ)^t)*s)*(2:ℚ)^W/(1/(2:ℚ)^t)) = z := by
  unfold completionRemainder
  field_simp
  ring

lemma completion_retention_bounds (W t : ℕ) {s z : ℚ}
    (hs₀ : 0 < s) (hs₁ : s ≤ 1) (ht : 0 < t)
    (hz : 0 < z) (hzA : z ≤ (1-1/(2:ℚ)^t)*s) :
    let A := (1-1/(2:ℚ)^t)*s
    let C := completionCoeff (W+t+2) z A
    let R := completionRemainder (W+t+2) z A
    0 ≤ C ∧ C ≤ 1 ∧ 0 ≤ R*(2:ℚ)^W/(1/(2:ℚ)^t) ∧
      R*(2:ℚ)^W/(1/(2:ℚ)^t) < 1/4 := by
  let A := (1-1/(2:ℚ)^t)*s
  have hδ₀ : (0:ℚ) < 1/2^t := by positivity
  have hδ₁ : (1:ℚ)/2^t < 1 := by
    apply (div_lt_one (by positivity : (0:ℚ) < 2^t)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hA : 0 < A := mul_pos (sub_pos.mpr hδ₁) hs₀
  have hA₁ : A ≤ 1 := by
    calc
      _ ≤ 1*s := mul_le_mul_of_nonneg_right (by linarith : 1-1/(2:ℚ)^t ≤ 1) hs₀.le
      _ ≤ 1 := by simpa using hs₁
  have h := completion_rounding (W+t+2) hz.le hA hzA
  dsimp only
  refine ⟨h.1, h.2.1, div_nonneg (mul_nonneg h.2.2.1 (by positivity)) hδ₀.le, ?_⟩
  have hR : completionRemainder (W+t+2) z A < 1/(2:ℚ)^(W+t+2) :=
    h.2.2.2.trans_le (div_le_div_of_nonneg_right hA₁ (by positivity))
  calc
    _ < (1/(2:ℚ)^(W+t+2))*(2:ℚ)^W/(1/(2:ℚ)^t) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hR (by positivity)) hδ₀
    _ = 1/4 := by rw [pow_add, pow_add]; norm_num; field_simp

/-- The second rounding of Section 6, independent of the transition algorithm. -/
def quarterCoeff (J : ℕ) (p : ℚ) : ℚ := completionCoeff (J+2) (1/2) p

def quarterRemainder (J : ℕ) (p : ℚ) : ℚ := 1/4-p*quarterCoeff J p/2

lemma quarter_retention_bounds (J : ℕ) {p : ℚ} (hp₀ : 1/2 < p) (hp₁ : p ≤ 1) :
    0 ≤ quarterCoeff J p ∧ quarterCoeff J p ≤ 1 ∧
      0 ≤ (2:ℚ)^(J+1)*quarterRemainder J p ∧
      (2:ℚ)^(J+1)*quarterRemainder J p < 1/4 := by
  have h := completion_rounding (J+2) (by norm_num : (0:ℚ) ≤ 1/2)
    (by linarith : 0 < p) hp₀.le
  have he : quarterRemainder J p = completionRemainder (J+2) (1/2) p/2 := by
    unfold quarterRemainder quarterCoeff completionRemainder
    ring
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rw [he]
    exact mul_nonneg (by positivity) (div_nonneg h.2.2.1 (by norm_num))
  · rw [he]
    have hR : completionRemainder (J+2) (1/2) p < 1/(2:ℚ)^(J+2) :=
      h.2.2.2.trans_le (div_le_div_of_nonneg_right hp₁ (by positivity))
    calc
      _ < (2:ℚ)^(J+1)*(1/(2:ℚ)^(J+2)/2) :=
        mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hR (by norm_num)) (by positivity)
      _ = 1/4 := by rw [pow_add, pow_add]; norm_num; field_simp

lemma quarter_mass (J : ℕ) (p : ℚ) :
    (1/2)*p*quarterCoeff J p +
      (1/2)*(1/(2:ℚ)^J)*((2:ℚ)^(J+1)*quarterRemainder J p)=1/4 := by
  unfold quarterRemainder
  rw [pow_succ]
  field_simp
  ring

/-- An explicit elementary discrete bound eliminates a real-calculus asymptotic. -/
lemma step_tenth_power_bound {n : ℕ} (hn : 128 ≤ n) : (n+1)^10 ≤ 2*n^10 := by
  have h₀ : 128*(n+1) ≤ 129*n := by omega
  have h₁ := Nat.pow_le_pow_left h₀ 10
  rw [mul_pow,mul_pow] at h₁
  have hc : 129^10 ≤ 2*128^10 := by norm_num
  have h₂ : 128^10*(n+1)^10 ≤ 128^10*(2*n^10) := by
    calc
      _ ≤ 129^10*n^10 := h₁
      _ ≤ (2*128^10)*n^10 := Nat.mul_le_mul_right _ hc
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h₂ (by norm_num)

lemma tenth_power_exponential {n : ℕ} (hn : 128 ≤ n) : 2*n^10 < 2^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hs := step_tenth_power_bound hn
    calc
      _ ≤ 2*(2*n^10) := Nat.mul_le_mul_left 2 hs
      _ < 2*2^n := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; omega

def knownProbability (n : ℕ) : ℚ := (1-1/(2:ℚ)^n)^(n^10)

lemma knownProbability_bounds {n : ℕ} (hn : 128 ≤ n) :
    1/2 < knownProbability n ∧ knownProbability n ≤ 1 := by
  have hD : (0:ℚ) < 2^n := by positivity
  have hD₁ : (1:ℚ) ≤ 2^n := one_le_pow₀ (by norm_num)
  have hδ : (1:ℚ)/2^n ≤ 1 := (div_le_one hD).mpr hD₁
  have hbin := one_add_mul_le_pow (R:=ℚ)
    (show -2 ≤ -(1/(2:ℚ)^n) by linarith) (n^10)
  have hexp : (2:ℚ)*(n:ℚ)^10 < 2^n := by exact_mod_cast tenth_power_exponential hn
  have hsmall : (n:ℚ)^10/(2:ℚ)^n < 1/2 := by
    apply (div_lt_iff₀ hD).mpr
    linarith
  unfold knownProbability
  constructor
  · simp only [Nat.cast_pow, ← sub_eq_add_neg, mul_neg, mul_one_div] at hbin
    linarith
  · calc
      _ ≤ (1:ℚ)^(n^10) := pow_le_pow_left₀ (by linarith : 0 ≤ 1-1/(2:ℚ)^n)
        (by linarith [le_of_lt (show (0:ℚ) < 1/(2:ℚ)^n by positivity)]) _
      _ = 1 := one_pow _

end ExactQuantumFactoring.Exactness



end

end OAI
