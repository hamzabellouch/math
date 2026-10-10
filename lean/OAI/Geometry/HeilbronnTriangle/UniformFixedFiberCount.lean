import OAI.Geometry.HeilbronnTriangle.LiftedBadEvent
import OAI.Geometry.HeilbronnTriangle.NonzeroAuxiliaryCount
import OAI.Geometry.HeilbronnTriangle.ZeroCountNormalization
import OAI.Geometry.HeilbronnTriangle.ZeroRowData
import OAI.Geometry.HeilbronnTriangle.AuxiliaryZeroCount

namespace OAI


noncomputable section

namespace Problem355.UniformFixedFiberCount

open Finset

lemma log_four_mul_le {N : ℝ} (hN : 1 ≤ N) :
    Real.log (4 * N) ≤ 2 * Real.log (2 * N) :=
  ZeroCountNormalization.log_four_mul_le_two_log_two_mul hN

lemma normal_log_le_log_square {N : ℝ} (hN : 1 ≤ N) :
    Real.log (4 * N) / Real.log 2 ≤
      (2 / (Real.log 2) ^ 2) * (Real.log (2 * N)) ^ 2 :=
  ZeroCountNormalization.normal_log_le_squared_log hN

def commonConstant (Czero Cnonzero : ℝ) : ℝ :=
  Cnonzero + 2 * Czero / (Real.log 2) ^ 2

lemma commonConstant_nonneg {Czero Cnonzero : ℝ}
    (hzero : 0 ≤ Czero) (hnonzero : 0 ≤ Cnonzero) :
    0 ≤ commonConstant Czero Cnonzero := by
  unfold commonConstant
  positivity

theorem sum_fiber_le {α : Type*} (S : Finset α) (d : α → ℤ) (W : α → ℝ)
    {N U Czero Cnonzero : ℝ} (hN : 1 ≤ N) (hU : 0 ≤ U)
    (hCzero : 0 ≤ Czero) (hCnonzero : 0 ≤ Cnonzero)
    (hzero : (∑ x ∈ S.filter (fun x => d x = 0), W x) ≤
      Czero * (Real.log (4 * N) / Real.log 2) * U)
    (t : ℤ) (hnonzero : t ≠ 0 →
      (∑ x ∈ S.filter (fun x => d x = t), W x) ≤
        Cnonzero * (Real.log (2 * N)) ^ 2 * U) :
    (∑ x ∈ S.filter (fun x => d x = t), W x) ≤
      commonConstant Czero Cnonzero * (Real.log (2 * N)) ^ 2 * U := by
  classical
  by_cases ht : t = 0
  · subst t
    apply hzero.trans
    have habs := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (normal_log_le_log_square hN) hCzero) hU
    have hextra : 0 ≤ Cnonzero * (Real.log (2 * N)) ^ 2 * U := by positivity
    unfold commonConstant
    simp only [div_eq_mul_inv] at habs ⊢
    nlinarith only [habs, hextra]
  · apply (hnonzero ht).trans
    have hextra : 0 ≤ (2 * Czero / (Real.log 2) ^ 2) *
        (Real.log (2 * N)) ^ 2 * U := by positivity
    unfold commonConstant
    simp only [div_eq_mul_inv] at hextra ⊢
    nlinarith only [hextra]

theorem lifted_small_event_le_of_cases
    {X A Ω B : Type*} [DecidableEq X] [DecidableEq A] [Fintype Ω]
    (f : X → A) (g : X → (Fin 3 → B)) (d : X → ℤ)
    (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
    (s h q L : ℕ) (hs : 0 < s) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
    (hw : ∀ ω, 0 ≤ w ω) (S : Finset X)
    {τ : ℤ} (hwidth : 2 * τ < h) (c : ZMod h)
    (hres : ∀ x ∈ S, f x ∈ O → (d x : ZMod h) = c)
    {D E c₀ Czero Cnonzero : ℝ}
    (hD : 0 < D) (hE : 0 < E) (hc₀ : 0 < c₀)
    (hCzero : 0 ≤ Czero) (hCnonzero : 0 ≤ Cnonzero)
    (horbit : c₀ * (h : ℝ) ^ 8 / (D ^ 3 * E ^ 2) ≤ (O.card : ℝ))
    (hzero :
      (∑ x ∈ (S.filter (fun x => f x ∈ O)).filter (fun x => d x = 0),
        LiftingProbability.auxiliaryWeight q s w V (g x)) ≤
          Czero * (Real.log (4 * ((L * (h * q) : ℕ) : ℝ)) / Real.log 2) *
            ((L * (h * q) : ℕ) : ℝ) ^ 6 / (D ^ 2 * E ^ 2))
    (hnonzero : ∀ t : ℤ, |t| ≤ τ → t ≠ 0 →
      (∑ x ∈ (S.filter (fun x => f x ∈ O)).filter (fun x => d x = t),
        LiftingProbability.auxiliaryWeight q s w V (g x)) ≤
          Cnonzero * (Real.log (2 * ((L * (h * q) : ℕ) : ℝ))) ^ 2 *
            ((L * (h * q) : ℕ) : ℝ) ^ 6 / (D ^ 2 * E ^ 2)) :
    (∑ x ∈ S.filter (fun x => |d x| ≤ τ),
      LiftingProbability.liftedMass f g O w V s (L ^ 9) x) ≤
        (commonConstant Czero Cnonzero / c₀) *
          (Real.log (2 * ((L * (h * q) : ℕ) : ℝ))) ^ 2 * (h : ℝ) * D /
            ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  classical
  apply LiftingProbability.lifted_small_event_le f g d O hO w V s h q L
    hs hh hq hL hw S hwidth c hres hD hE hc₀
    (commonConstant_nonneg hCzero hCnonzero) horbit
  intro t ht
  have hN : (1 : ℝ) ≤ ((L * (h * q) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hL (Nat.mul_pos hh hq)
  have hz :
      (∑ x ∈ (S.filter (fun x => f x ∈ O)).filter (fun x => d x = 0),
        LiftingProbability.auxiliaryWeight q s w V (g x)) ≤
          Czero * (Real.log (4 * ((L * (h * q) : ℕ) : ℝ)) / Real.log 2) *
            (((L * (h * q) : ℕ) : ℝ) ^ 6 / (D ^ 2 * E ^ 2)) := by
    simpa only [mul_div_assoc] using hzero
  have hb := sum_fiber_le (S.filter (fun x => f x ∈ O)) d
    (fun x => LiftingProbability.auxiliaryWeight q s w V (g x))
    hN (show 0 ≤ ((L * (h * q) : ℕ) : ℝ) ^ 6 / (D ^ 2 * E ^ 2) by positivity)
    hCzero hCnonzero hz t (fun hne => by
      simpa only [mul_div_assoc] using hnonzero t ht hne)
  simpa only [mul_div_assoc] using hb

theorem matrix_fiber_le_of_zero_count
    {B k q : ℕ} (hB : 0 < B) [Fact q.Prime]
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) (d : PrimePowerData B k C)
    (N : ℝ) (hN : 1 ≤ N) (S : Finset NonzeroWeightedCount.IntMatrix)
    (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
      Section04Orbit.slOrbit C)
    (hbox : ∀ A ∈ S, ∀ j, Homogeneous.InBox N (fun i => (A i j : ℝ)))
    (W : NonzeroWeightedCount.IntMatrix → ℝ) (w Czero : ℝ)
    (hw : 0 ≤ w) (hCzero : 0 ≤ Czero)
    (hW : ∀ A ∈ S,
      AffineIndependent (ZMod q) (fun j i => (A i j : ZMod q)) → W A ≤ w)
    (hzero : (∑ A ∈ S.filter (fun A => A.det = 0), W A) ≤
      Czero * (Real.log (4 * N) / Real.log 2) * N ^ 6 /
        ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2)
    (t : ℤ) (htq : |t| < (q : ℤ)) :
    (∑ A ∈ S.filter (fun A => A.det = t), W A) ≤
      commonConstant Czero (w * NonzeroWeightedCount.boxConstant) *
        Real.log (2 * N) ^ 2 * N ^ 6 /
          ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
  classical
  have hz : (∑ A ∈ S.filter (fun A => A.det = 0), W A) ≤
      Czero * (Real.log (4 * N) / Real.log 2) *
        (N ^ 6 / ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2) := by
    simpa only [mul_div_assoc] using hzero
  have hdiag : C = (d.left : Matrix _ _ _) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ d.b) (B ^ d.e) *
        (d.right : Matrix _ _ _) := by
    simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization
  have hb := sum_fiber_le S Matrix.det W hN
    (show 0 ≤ N ^ 6 / ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 by positivity)
    hCzero (mul_nonneg hw NonzeroWeightedCount.boxConstant_pos.le) hz t (by
      intro ht
      have hc := NonzeroWeightedCount.weighted_orbit_count B k d.b d.e hB
        d.b_le_k d.e_le_k d.b_le_e C d.left d.right hdiag N hN
        (S.filter (fun A => A.det = t))
        (fun A hA => horbit A (Finset.mem_filter.mp hA).1)
        (fun A hA => hbox A (Finset.mem_filter.mp hA).1)
        t ht (fun A hA => (Finset.mem_filter.mp hA).2) W w hw (by
          intro A hA
          obtain ⟨hAS, hAt⟩ := Finset.mem_filter.mp hA
          exact hW A hAS (SmallDeterminantWeight.affineIndependent_columns A
            (by simpa only [hAt] using ht) (by simpa only [hAt] using htq)))
      simpa only [mul_div_assoc] using hc)
  simpa only [mul_div_assoc] using hb

lemma box_height_ne_zero {N : ℕ} (hN : 1 ≤ N)
    (A : NonzeroWeightedCount.IntMatrix)
    (hbox : ∀ j, Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ)))
    (j : Fin 3) : A 2 j ≠ 0 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hp : (0 : ℝ) < A 2 j := hNp.trans_le (hbox j).2.2.2.2.1
  intro hz
  simp only [hz, Int.cast_zero, lt_self_iff_false] at hp

lemma box_abs_le_two_mul {N : ℕ} (A : NonzeroWeightedCount.IntMatrix)
    (hbox : ∀ j, Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ)))
    (i j : Fin 3) : |A i j| ≤ (2 * N : ℕ) := by
  have hr : |(A i j : ℝ)| ≤ 2 * (N : ℝ) := by
    have hj := hbox j
    fin_cases i
    · change |(A 0 j : ℝ)| ≤ 2 * (N : ℝ)
      rw [abs_of_nonneg hj.1]
      linarith [hj.2.1, Nat.cast_nonneg (α := ℝ) N]
    · change |(A 1 j : ℝ)| ≤ 2 * (N : ℝ)
      rw [abs_of_nonneg hj.2.2.1]
      linarith [hj.2.2.2.1, Nat.cast_nonneg (α := ℝ) N]
    · change |(A 2 j : ℝ)| ≤ 2 * (N : ℝ)
      rw [abs_of_nonneg ((Nat.cast_nonneg N).trans hj.2.2.2.2.1)]
      exact hj.2.2.2.2.2.le
  exact_mod_cast hr

def countConstant : ℝ :=
  commonConstant AuxiliaryZeroCount.countConstant (8 * NonzeroWeightedCount.boxConstant)

lemma countConstant_nonneg : 0 ≤ countConstant :=
  commonConstant_nonneg AuxiliaryZeroCount.countConstant_nonneg
    (mul_nonneg (by norm_num) NonzeroWeightedCount.boxConstant_pos.le)

lemma countConstant_pos : 0 < countConstant := by
  unfold countConstant commonConstant
  exact add_pos_of_pos_of_nonneg
    (mul_pos (by norm_num) NonzeroWeightedCount.boxConstant_pos)
    (by have := AuxiliaryZeroCount.countConstant_nonneg; positivity)

theorem matrix_fiber_le
    {B k q : ℕ} (hB : B.Prime) [Fact q.Prime]
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) (d : PrimePowerData B k C)
    (L : AuxiliarySampling.Law q ((B ^ k) ^ 2))
    (hcop : (B ^ k).Coprime q) (hparam : ((B : ℝ) ^ k) ^ 26 ≤ (q : ℝ))
    (N : ℕ) (hN : 1 ≤ N) (S : Finset NonzeroWeightedCount.IntMatrix)
    (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
      Section04Orbit.slOrbit C)
    (hbox : ∀ A ∈ S, ∀ j, Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ)))
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      PlaneRowTransport.projectedColumn A i ≠ PlaneRowTransport.projectedColumn A j)
    (t : ℤ) (htq : |t| < (q : ℤ)) :
    (∑ A ∈ S.filter (fun A => A.det = t),
      LiftingProbability.auxiliaryWeight q L.size L.weight L.sets
        (A.map (Int.castRingHom (ZMod q))).col) ≤
      countConstant * Real.log (2 * (N : ℝ)) ^ 2 * (N : ℝ) ^ 6 /
        ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
  classical
  have hz := AuxiliaryZeroCount.weighted_count_le_log (d.toZeroRowData hB) q N hN
    (d.toZeroRowData_E_isUnit hB hcop)
    (by simpa only [PrimePowerData.toZeroRowData_h] using hparam) L
    (S.filter (fun A => A.det = 0))
    (fun A hA => (Finset.mem_filter.mp hA).2)
    (fun A hA i => d.orbit_rows_mem_toZeroRowData hB A
      (horbit A (Finset.mem_filter.mp hA).1) i)
    (fun A hA => box_height_ne_zero hN A (hbox A (Finset.mem_filter.mp hA).1))
    (fun A hA => hproj A (Finset.mem_filter.mp hA).1)
    (fun A hA => box_abs_le_two_mul A (hbox A (Finset.mem_filter.mp hA).1))
  have hzero : (∑ A ∈ S.filter (fun A => A.det = 0),
      LiftingProbability.auxiliaryWeight q L.size L.weight L.sets
        (A.map (Int.castRingHom (ZMod q))).col) ≤
      AuxiliaryZeroCount.countConstant * (Real.log (4 * (N : ℝ)) / Real.log 2) *
        (N : ℝ) ^ 6 / ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
    rw [d.toZeroRowData_index_real hB] at hz
    convert hz using 1
    ring
  exact matrix_fiber_le_of_zero_count hB.pos C d (N : ℝ)
    (by exact_mod_cast hN) S horbit hbox
    (fun A => LiftingProbability.auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col)
    8 AuxiliaryZeroCount.countConstant (by norm_num)
    AuxiliaryZeroCount.countConstant_nonneg
    (fun A _ hAI => L.weight_le_eight _ hAI) hzero t htq

end Problem355.UniformFixedFiberCount

end

end OAI
