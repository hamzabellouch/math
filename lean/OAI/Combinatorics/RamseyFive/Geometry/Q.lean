import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.SubspacePointsEquiv

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
open scoped Classical
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem sum_weightOnHyperplane_sq (w : ℙ K V → ℝ) :
    ∑ b, weightOnHyperplane w b ^ 2 =
      (((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) -
        ((∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i : ℕ) : ℝ)) *
          (∑ a, w a ^ 2) +
      ((∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i : ℕ) : ℝ) * (∑ a, w a) ^ 2 := by
  classical
  let m : ℝ := (∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ)
  let l : ℝ := (∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i : ℕ)
  have hentry (a a' : ℙ K V) : ∑ b, incidenceEntry a b * incidenceEntry a' b =
      (if a = a' then m - l else 0) + l := by
    rw [sum_entry_mul_entry]
    split_ifs <;> dsimp [m, l] <;> ring
  calc
    ∑ b, weightOnHyperplane w b ^ 2 =
        ∑ b, ∑ a, ∑ a', (incidenceEntry a b * incidenceEntry a' b) * (w a * w a') := by
      apply Finset.sum_congr rfl
      intro b _
      rw [weightOnHyperplane, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro a' _
      ring
    _ = ∑ a, ∑ a', ((if a = a' then m - l else 0) + l) * (w a * w a') := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a' _
      rw [← Finset.sum_mul, hentry]
    _ = (m - l) * (∑ a, w a ^ 2) + l * (∑ a, w a) ^ 2 := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      congr 1
      · simp_rw [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          ← pow_two, ← Finset.mul_sum]
      · rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]

omit [Fintype (ℙ K (Dual K V))] in
lemma sum_entry_column (b : ℙ K (Module.Dual K V)) :
    ∑ a, incidenceEntry a b =
      ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) := by
  classical
  unfold incidenceEntry
  rw [Finset.sum_boole, ← Fintype.card_subtype, Fintype.card_eq_nat_card,
    card_points_on_hyperplane]

def Q (q d : ℕ) : ℕ := ∑ i ∈ Finset.range (d + 1), q ^ i

lemma Q_pos (q d : ℕ) : 0 < Q q d := by
  apply Finset.sum_pos'
  · intros; exact Nat.zero_le _
  · exact ⟨0, Finset.mem_range.mpr (by omega), by simp⟩

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma card_points {d : ℕ} (hdim : finrank K V = d + 1) :
    Fintype.card (ℙ K V) = Q (Nat.card K) d := by
  rw [Fintype.card_eq_nat_card]
  exact Projectivization.card_of_finrank K V hdim

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma card_hyperplanes {d : ℕ} (hdim : finrank K V = d + 1) :
    Fintype.card (ℙ K (Module.Dual K V)) = Q (Nat.card K) d := by
  rw [Fintype.card_eq_nat_card]
  exact Projectivization.card_of_finrank K (Module.Dual K V)
    (Subspace.dual_finrank_eq.trans hdim)

theorem incidence_mean {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (w : ℙ K V → ℝ) :
    (∑ b, weightOnHyperplane w b) / Q (Nat.card K) d =
      ((Q (Nat.card K) (d - 1) : ℝ) / Q (Nat.card K) d) * ∑ a, w a := by
  rw [sum_weightOnHyperplane, hdim]
  have : d - 1 + 1 = d := by omega
  simp only [Nat.add_sub_cancel, Q, this]
  ring

theorem incidence_variance_eq {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (w : ℙ K V → ℝ) :
    ∑ b, (weightOnHyperplane w b -
        ((Q (Nat.card K) (d - 1) : ℝ) / Q (Nat.card K) d) * (∑ a, w a)) ^ 2 =
      (Nat.card K : ℝ) ^ (d - 1) *
        ((∑ a, w a ^ 2) - (∑ a, w a) ^ 2 / Q (Nat.card K) d) := by
  classical
  let n : ℝ := Q (Nat.card K) d
  let m : ℝ := Q (Nat.card K) (d-1)
  let s : ℝ := ∑ a, w a
  let u : ℙ K V → ℝ := fun a => w a - s / n
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast (Q_pos (Nat.card K) d).ne'
  have hc : (Fintype.card (ℙ K V) : ℝ) = n := by rw [card_points hdim]
  have hs : ∑ a, u a = 0 := by
    simp only [u, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    change s - n * (s / n) = 0
    field_simp
    ring
  have hd' : d - 1 + 1 = d := by omega
  have hd'' : d + 1 - 2 = d - 1 := by omega
  have hm : ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) = m := by
    simp only [hdim, Nat.add_sub_cancel, m, Q, hd']
  have hwu (b : ℙ K (Module.Dual K V)) :
      weightOnHyperplane u b = weightOnHyperplane w b - m / n * s := by
    simp only [weightOnHyperplane, u, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, sum_entry_column, hm]
    ring
  have hnorm : ∑ a, u a ^ 2 = (∑ a, w a ^ 2) - s ^ 2 / n := by
    calc
      ∑ a, u a ^ 2 = ∑ a, (w a ^ 2 - 2 * (s/n) * w a + (s/n)^2) := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp [u]
        ring
      _ = (∑ a, w a ^ 2) - 2 * (s/n) * s + n * (s/n)^2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, s]
      _ = (∑ a, w a ^ 2) - s ^ 2 / n := by field_simp; ring
  have hdiff :
      ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) -
        ((∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i : ℕ) : ℝ) =
      (Nat.card K : ℝ) ^ (d - 1) := by
    rw [hdim, Nat.add_sub_cancel, hd'', ← hd', Finset.sum_range_succ]
    push_cast
    ring
  change ∑ b, (weightOnHyperplane w b - m / n * s) ^ 2 = _
  simp_rw [← hwu]
  rw [sum_weightOnHyperplane_sq, hs, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
    hdiff, hnorm]

theorem incidence_variance {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (w : ℙ K V → ℝ) :
    ∑ b, (weightOnHyperplane w b -
        ((Q (Nat.card K) (d - 1) : ℝ) / Q (Nat.card K) d) * (∑ a, w a)) ^ 2 ≤
      (Nat.card K : ℝ) ^ (d - 1) * ∑ a, w a ^ 2 := by
  rw [incidence_variance_eq hdim hd]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sub_le_self _ (by positivity)

theorem incidence_weighted_mixing_sq {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (w : ℙ K V → ℝ) (B : Finset (ℙ K (Module.Dual K V))) :
    ((∑ b ∈ B, weightOnHyperplane w b) -
      ((Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d) * B.card * (∑ a, w a)) ^ 2 ≤
      (Nat.card K : ℝ) ^ (d-1) * (∑ a, w a ^ 2) * B.card := by
  classical
  let f (b : ℙ K (Module.Dual K V)) := weightOnHyperplane w b -
      ((Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d) * (∑ a, w a)
  have hsum : (∑ b ∈ B, f b) = (∑ b ∈ B, weightOnHyperplane w b) -
      ((Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d) * B.card * (∑ a, w a) := by
    simp only [f, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℝ)) f
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [← hsum]
  calc
    (∑ b ∈ B, f b) ^ 2 ≤ (B.card : ℝ) * ∑ b ∈ B, f b ^ 2 := hcs
    _ ≤ (B.card : ℝ) * ∑ b, f b ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_univ_sum_of_nonneg (fun b => sq_nonneg (f b)))
        (by positivity)
    _ ≤ (B.card : ℝ) * ((Nat.card K : ℝ) ^ (d-1) * ∑ a, w a ^ 2) :=
      mul_le_mul_of_nonneg_left (incidence_variance hdim hd w) (by positivity)
    _ = _ := by ring

noncomputable def incidences (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V))) : ℕ :=
  ((A ×ˢ B).filter fun ab => Incident ab.1 ab.2).card

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma incidences_eq_sum (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V))) :
    (incidences A B : ℝ) = ∑ b ∈ B, ∑ a ∈ A, incidenceEntry a b := by
  rw [incidences, ← Finset.sum_boole, Finset.sum_product, Finset.sum_comm]
  rfl

theorem incidence_mixing {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V))) :
    |(incidences A B : ℝ) -
      ((Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d) * A.card * B.card| ≤
      Real.sqrt ((Nat.card K : ℝ) ^ (d-1) * A.card * B.card) := by
  classical
  let w : ℙ K V → ℝ := fun a => if a ∈ A then 1 else 0
  have hw (b : ℙ K (Module.Dual K V)) :
      weightOnHyperplane w b = ∑ a ∈ A, incidenceEntry a b := by
    simp only [weightOnHyperplane, w, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_mem, Finset.univ_inter]
  have hsum : ∑ a, w a = (A.card : ℝ) := by
    simp [w, Finset.sum_ite_mem]
  have hsq : ∑ a, w a ^ 2 = (A.card : ℝ) := by
    simp [w, Finset.sum_ite_mem]
  have h := incidence_weighted_mixing_sq hdim hd w B
  rw [hsum, hsq] at h
  simp_rw [hw] at h
  rw [← incidences_eq_sum] at h
  simpa [mul_assoc, mul_left_comm, mul_comm] using Real.abs_le_sqrt h

lemma Q_recurrence {q d : ℕ} (hd : 1 ≤ d) : Q q d = q * Q q (d-1) + 1 := by
  have he : d - 1 + 1 = d := by omega
  simp only [Q, he]
  exact geom_sum_succ

lemma density_lower {d : ℕ} (hd : 1 ≤ d) :
    1 / (2 * (Nat.card K : ℝ)) ≤
      (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hm : 0 < Q (Nat.card K) (d-1) := Q_pos _ _
  have hn : 0 < Q (Nat.card K) d := Q_pos _ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul, Q_recurrence hd]
  push_cast
  have hq' : (2 : ℝ) ≤ Nat.card K := by exact_mod_cast hq
  have hm' : (1 : ℝ) ≤ Q (Nat.card K) (d-1) := by exact_mod_cast hm
  nlinarith

theorem sparse_rectangle_size {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V)))
    (hsparse : (incidences A B : ℝ) ≤ (A.card : ℝ) * B.card / (4 * Nat.card K)) :
    (A.card : ℝ) * B.card ≤ 16 * (Nat.card K : ℝ) ^ (d+1) := by
  classical
  let q : ℝ := Nat.card K
  let v : ℝ := (A.card : ℝ) * B.card
  let p : ℝ := (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hp : 1 / (2*q) ≤ p := density_lower hd
  have hpv := mul_le_mul_of_nonneg_right hp hv
  have hlow : v / (4*q) ≤ p*v - incidences A B := by
    change (incidences A B : ℝ) ≤ v / (4*q) at hsparse
    have he : (1 / (2*q)) * v = 2 * (v / (4*q)) := by field_simp; ring
    rw [he] at hpv
    linarith
  have hm : |(incidences A B : ℝ) - p*v| ≤ Real.sqrt (q^(d-1)*v) := by
    simpa only [p, q, v, mul_assoc] using incidence_mixing hdim hd A B
  have habs : |(incidences A B : ℝ) - p*v| = p*v - incidences A B := by
    rw [abs_of_nonpos (show (incidences A B : ℝ) - p*v ≤ 0 by
      have hnonneg : 0 ≤ v / (4*q) := by positivity
      linarith)]
    ring
  rw [habs] at hm
  have hs : v / (4*q) ≤ Real.sqrt (q^(d-1)*v) := hlow.trans hm
  have hs2 := (Real.le_sqrt (by positivity) (by positivity)).mp hs
  have he : (v / (4*q))^2 * (16*q^2) = v^2 := by field_simp; ring
  have hm2 := mul_le_mul_of_nonneg_right hs2 (show 0 ≤ 16*q^2 by positivity)
  rw [he] at hm2
  have hexp : q^(d-1)*v*(16*q^2) = (16*q^(d+1))*v := by
    have hd' : d-1 + 2 = d+1 := by omega
    rw [← hd', pow_add]
    ring
  rw [hexp, pow_two] at hm2
  by_cases hv0 : v = 0
  · change v ≤ _
    rw [hv0]
    positivity
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hv (Ne.symm hv0))).mp hm2

end SharpRamseyFive.ProjectiveIncidence

end OAI
