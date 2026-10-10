import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinatePolynomial
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PiFiberMass
import OAI.GroupTheory.PolycyclicRecognition.Analysis.UnivariateRemez

namespace OAI

/-! # A coarse multivariable Remez inequality by slicing

Iterating the elementary interval estimate loses a factor of dimension in the
exponent. The geometric application only requires a fixed polynomial loss.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory

theorem coordinate_polynomial_remez (n D : ℕ) (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∀ f : (Fin n → ℝ) → ℝ, CoordinatePolynomial n D f →
      ∀ R : ℝ, 1 ≤ R → ∀ S : Set (Fin n → ℝ),
      MeasurableSet S → S ⊆ closedBall 0 R → 0 < (volume S).toReal →
      ∀ η : ℝ, 0 ≤ η → (∀ x ∈ S, |f x| ≤ η) →
      ∀ x ∈ closedBall 0 R,
        |f x| ≤ (A * (1 + R) ^ n / (volume S).toReal) ^ (n * D) * η := by
  classical
  obtain ⟨C, hC, hline⟩ := exists_univariate_remez_constant D hD
  induction n with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro f _ R _ S _ _ hm η _ hv x _
    have hne : S.Nonempty := by
      by_contra h
      have he := Set.not_nonempty_iff_eq_empty.mp h
      simp [he] at hm
    obtain ⟨y, hy⟩ := hne
    have he : y = x := Subsingleton.elim _ _
    simpa only [zero_mul, pow_zero, one_mul, he] using hv y hy
  | succ n ih =>
    obtain ⟨A, hA, hind⟩ := ih
    let B := max (2 ^ (n + 1) * C) (4 * A)
    have hB : 0 < B := (by positivity : 0 < 4 * A).trans_le (le_max_right _ _)
    refine ⟨B, hB, ?_⟩
    intro f hf R hR S hS hSR hm η hη hv x hx
    have hRpos : 0 < R := zero_lt_one.trans_le hR
    have hR0 : 0 ≤ R := hRpos.le
    let m := (volume S).toReal
    let q := m / (2 * (2 * R) ^ n)
    have hq : 0 < q := by dsimp [q, m]; positivity
    obtain ⟨T, hT, hTR, hmass, hfib⟩ :=
      exists_large_coordinate_sections n R hRpos S hS hSR hm
    have hTpos : 0 < (volume T).toReal :=
      (div_pos hm (by positivity : 0 < 4 * R)).trans_le hmass
    let b := B * (1 + R) ^ (n + 1) / m
    have hb : 0 < b := by dsimp [b, m]; positivity
    let η' := b ^ D * η
    have hη' : 0 ≤ η' := by dsimp [η']; positivity
    have hx' : x 0 ∈ closedBall 0 R ∧ Fin.tail x ∈ closedBall 0 R :=
      (mem_closedBall_cons R hR0 (x 0) (Fin.tail x)).mp (by simpa only [Fin.cons_self_tail] using hx)
    have hvT (y : Fin n → ℝ) (hy : y ∈ T) : |f (Fin.cons (x 0) y)| ≤ η' := by
      let E := {t : ℝ | Fin.cons t y ∈ S}
      have hE : E ⊆ closedBall 0 R := fun t ht =>
        ((mem_closedBall_cons R hR0 t y).mp (hSR ht)).1
      have hEm : q ≤ (volume E).toReal := hfib y hy
      have hEpos : 0 < (volume E).toReal := hq.trans_le hEm
      obtain ⟨p, hp, he⟩ := hf.head y
      have hh := hline p hp R hR E hE hEpos η hη
        (fun t ht => by rw [he]; exact hv _ ht) (x 0) hx'.1
      rw [he] at hh
      have hratio : C * (1 + R) / (volume E).toReal ≤ b := by
        calc
          C * (1 + R) / (volume E).toReal ≤ C * (1 + R) / q :=
            div_le_div_of_nonneg_left (by positivity) hq hEm
          _ = (2 ^ (n + 1) * C) * (1 + R) * R ^ n / m := by
            dsimp [q]
            rw [mul_pow, pow_succ]
            field_simp
          _ ≤ B * (1 + R) ^ (n + 1) / m := by
            apply div_le_div_of_nonneg_right _ hm.le
            calc
              (2 ^ (n + 1) * C) * (1 + R) * R ^ n ≤
                  B * (1 + R) * (1 + R) ^ n := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
                · exact pow_le_pow_left₀ hR0 (by linarith) n
                · positivity
                · positivity
              _ = B * (1 + R) ^ (n + 1) := by rw [pow_succ]; ring
      exact hh.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hratio D) hη)
    have hpoint := hind (fun y => f (Fin.cons (x 0) y)) (hf.tail (x 0))
      R hR T hT hTR hTpos η' hη' hvT (Fin.tail x) hx'.2
    rw [Fin.cons_self_tail] at hpoint
    have hratio : A * (1 + R) ^ n / (volume T).toReal ≤ b := by
      calc
        A * (1 + R) ^ n / (volume T).toReal ≤
            A * (1 + R) ^ n / (m / (4 * R)) :=
          div_le_div_of_nonneg_left (by positivity) (div_pos hm (by positivity)) hmass
        _ = (4 * A) * R * (1 + R) ^ n / m := by field_simp
        _ ≤ B * (1 + R) ^ (n + 1) / m := by
          apply div_le_div_of_nonneg_right _ hm.le
          calc
            (4 * A) * R * (1 + R) ^ n ≤ B * (1 + R) * (1 + R) ^ n := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul (le_max_right _ _) (by linarith) hR0 hB.le
            _ = B * (1 + R) ^ (n + 1) := by rw [pow_succ]; ring
    calc
      |f x| ≤ (A * (1 + R) ^ n / (volume T).toReal) ^ (n * D) * η' := hpoint
      _ ≤ b ^ (n * D) * η' := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hratio _) hη'
      _ = b ^ ((n + 1) * D) * η := by
        dsimp [η']
        rw [← mul_assoc, ← pow_add]
        congr 2
        ring

end PolycyclicRecognition

end

end OAI
