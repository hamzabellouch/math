import OAI.Probability.BenjaminiSchramm.ThinSphereRecurrence
import OAI.Probability.BenjaminiSchramm.OperatorSusceptibility
import OAI.Probability.BenjaminiSchramm.GeneralCriticalFiniteness

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem thin_sphere_volume_scale (C A : ℝ) (hC : 0 < C) (hA : 0 < A)
    (hlarge : 1000*C^2 ≤ A) (r : ℕ) (hr : 0 < r) :
    C / Real.sqrt ((r+1)*(Nat.floor ((r : ℝ)/(10*A))+1) : ℕ) ≤ A/(10*r) := by
  let k := Nat.floor ((r : ℝ)/(10*A))
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hk := (Nat.lt_floor_add_one ((r : ℝ)/(10*A))).le
  have hscale : (r : ℝ)^2/(10*A) ≤ ((r+1)*(k+1) : ℕ) := by
    push_cast
    calc
      _ = (r : ℝ) * ((r : ℝ)/(10*A)) := by ring
      _ ≤ (r : ℝ) * (k+1) := mul_le_mul_of_nonneg_left hk hr0.le
      _ ≤ _ := by nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hs : 0 < Real.sqrt (10*A) := Real.sqrt_pos.mpr (by positivity)
  have hsN : (r : ℝ) / Real.sqrt (10*A) ≤ Real.sqrt ((r+1)*(k+1) : ℕ) := by
    have hh := Real.sqrt_le_sqrt hscale
    rw [Real.sqrt_div (sq_nonneg (r : ℝ)) (10*A),Real.sqrt_sq hr0.le] at hh
    exact hh
  have hcoeff : C * Real.sqrt (10*A) ≤ A/10 := by
    have hm := mul_le_mul_of_nonneg_right hlarge hA.le
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      (C * Real.sqrt (10*A))^2 = C^2*(10*A) := by rw [mul_pow,Real.sq_sqrt (by positivity)]
      _ ≤ (A/10)^2 := by nlinarith
  calc
    _ ≤ C / ((r : ℝ)/Real.sqrt (10*A)) :=
      div_le_div_of_nonneg_left hC.le (div_pos hr0 hs) hsN
    _ = (C*Real.sqrt (10*A)) / r := by field_simp
    _ ≤ (A/10)/r := div_le_div_of_nonneg_right hcoeff hr0.le
    _ = _ := by ring

theorem intrinsic_radius_upper_of_volume [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (C : ℝ) (hC : 0 < C)
    (hvol : ∀ (x : V) (N : ℕ), 0 < N → (law p (volumeEvent G x N)).toReal ≤ C/Real.sqrt N) :
    ∃ A : ℝ, 0 < A ∧ ∀ (S : Set E) x (n : ℕ), 0 < n →
      (law p (domainRadiusEvent G S x n)).toReal ≤ A/n := by
  let A := max 2 (1000*C^2)
  have hA2 : 2 ≤ A := le_max_left _ _
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA2
  have hlarge : 1000*C^2 ≤ A := le_max_right _ _
  refine ⟨A,hA,?_⟩
  suffices H : ∀ n : ℕ, ∀ (S : Set E) x, 0 < n →
      (law p (domainRadiusEvent G S x n)).toReal ≤ A/n from fun S x n hn => H n S x hn
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S x hn
    by_cases hn3 : n < 3
    · apply measureReal_le_one.trans
      apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr
      have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (show n ≤ 2 by omega)
      simpa only [one_mul] using hn2.trans hA2
    · let r := n/3
      have hr : 0 < r := Nat.div_pos (by omega) (by norm_num)
      have hrn : r < n := Nat.div_lt_self hn (by norm_num)
      have h3r : 3*r ≤ n := Nat.mul_div_le n 3
      have hn5 : n ≤ 5*r := by have hh := Nat.mod_lt n (by norm_num : 0 < 3); omega
      have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
      let k := Nat.floor ((r : ℝ)/(10*A))
      let b : ℝ≥0∞ := ENNReal.ofReal (A/r)
      have hb (I : Set E) (z : V) : law p (domainRadiusEvent G I z r) ≤ b := by
        rw [←ENNReal.ofReal_toReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal (ih r hrn I z hr)
      have hrec := radius_thin_sphere_recurrence G hloc p hfin r k hr b hb S x
      have hrecR := ENNReal.toReal_mono
        (show law p (volumeEvent G x ((r+1)*(k+1))) + k*b^2 ≠ ⊤ by finiteness) hrec
      dsimp only [b] at hrecR
      rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness), ENNReal.toReal_mul,
        ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity)] at hrecR
      have hN : 0 < (r+1)*(k+1) := by positivity
      have hV : (law p (volumeEvent G x ((r+1)*(k+1)))).toReal ≤ A/(10*r) :=
        (hvol x _ hN).trans (thin_sphere_volume_scale C A hC hA hlarge r hr)
      have hk : (k : ℝ) ≤ (r : ℝ)/(10*A) := Nat.floor_le (by positivity)
      have hK : (k : ℝ)*(A/r)^2 ≤ A/(10*r) := by
        calc
          _ ≤ ((r : ℝ)/(10*A))*(A/r)^2 := mul_le_mul_of_nonneg_right hk (sq_nonneg _)
          _ = _ := by field_simp
      have hsurv : (law p (domainRadiusEvent G S x (3*r))).toReal ≤ A/(5*r) := by
        calc
          _ ≤ A/(10*r)+A/(10*r) := hrecR.trans (add_le_add hV hK)
          _ = _ := by ring
      calc
        _ ≤ (law p (domainRadiusEvent G S x (3*r))).toReal := by
          apply ENNReal.toReal_mono (measure_ne_top _ _)
          apply measure_mono
          rintro ω ⟨y,hc,hd⟩
          exact ⟨y,hc,h3r.trans hd⟩
        _ ≤ A/(5*r) := hsurv
        _ ≤ A/n := div_le_div_of_nonneg_left hA.le
          (show (0 : ℝ) < n by exact_mod_cast hn) (by exact_mod_cast hn5)

theorem critical_intrinsic_radius_upper_of_operator [Infinite V] [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (hpc1 : (pc G : ℝ) < 1)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) :
    ∃ A : ℝ, 0 < A ∧ ∀ (S : Set E) x (n : ℕ), 0 < n →
      (law (pc G) (domainRadiusEvent G S x n)).toReal ≤ A/n := by
  obtain ⟨C,hC,hvol⟩ := critical_volume_upper_of_operator G hconn hloc hqt hh hpc1 T hT
  exact intrinsic_radius_upper_of_volume G hloc (pc G)
    (critical_finite_general G hconn hloc hqt hpc1) C hC hvol

end Percolation.BenjaminiSchramm

end OAI
