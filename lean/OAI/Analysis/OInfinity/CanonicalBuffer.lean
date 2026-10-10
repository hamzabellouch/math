import OAI.Analysis.OInfinity.TransportedBuffer
import OAI.Analysis.OInfinity.VacuumBufferAbsorption

namespace OAI

/-! # A connected absorption corner from the canonical vacuum split

The finite Fock construction provides the corner, its complementary
isometry, its binary row and the path of the absorption anchor together.
All coefficients inherit commutation with the original source commutant.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private lemma zeroCornerRow_map (F : E →⋆ₐ[ℂ] E) (q a b : E) :
    ∀ n i, F (zeroCornerRow q a b n i) =
      zeroCornerRow (F q) (F a) (F b) n i := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
      intro i
      refine Fin.cases rfl (fun j => ?_) i
      change F (a * zeroCornerRow q a b n j) = _
      rw [map_mul, ih]
      rfl

private lemma zeroCornerRow_star_commutes (q a b y : E)
    (hq : Commute (star q) y) (ha : Commute (star a) y) (hb : Commute (star b) y) :
    ∀ n i, Commute (star (zeroCornerRow q a b n i)) y := by
  intro n
  induction n with
  | zero => intro i; exact hq
  | succ n ih =>
      intro i
      refine Fin.cases hb (fun j => ?_) i
      change Commute (star (a * zeroCornerRow q a b n j)) y
      rw [star_mul]
      exact (ih j).mul_left ha

private lemma finiteRowIsometry_commutes {I : Type*} [Fintype I]
    (s t : I → E) (r q y : E)
    (hs : ∀ i, Commute (s i) y) (ht : ∀ i, Commute (star (t i)) y)
    (hr : Commute r y) (hq : Commute q y) (m : ℕ) :
    Commute (finiteRowIsometry s t r q m) y := by
  have hsum : ∀ k, Commute (finiteRowWordSum s t r q k) y := by
    intro k
    induction k with
    | zero => exact hr.mul_left hq
    | succ k ih =>
        apply (hr.mul_left hq).add_left
        exact Commute.sum_left _ _ _ (fun i _ => ((hs i).mul_left ih).mul_left (ht i))
  exact (hsum m).smul_left _

private lemma finiteRowIsometry_star_commutes {I : Type*} [Fintype I]
    (s t : I → E) (r q y : E)
    (hs : ∀ i, Commute (star (s i)) y) (ht : ∀ i, Commute (t i) y)
    (hr : Commute (star r) y) (hq : Commute (star q) y) (m : ℕ) :
    Commute (star (finiteRowIsometry s t r q m)) y := by
  have hsum : ∀ k, Commute (star (finiteRowWordSum s t r q k)) y := by
    intro k
    induction k with
    | zero => simpa only [finiteRowWordSum, star_mul] using hq.mul_left hr
    | succ k ih =>
        simp only [finiteRowWordSum, star_add, star_mul]
        apply (hq.mul_left hr).add_left
        simp only [finiteCuntzTransfer, star_sum, star_mul, star_star]
        exact Commute.sum_left _ _ _ (fun i _ => (ht i).mul_left (ih.mul_left (hs i)))
  simpa only [finiteRowIsometry, star_smul] using (hsum m).smul_left _

/-- The genuine canonical split has an explicitly connected absorption
anchor and retains its unused generator. Its binary coefficients commute
with every element of the source commutant. -/
lemma exists_canonical_connected_absorption_corner_with_commuting_isometry [Nontrivial E]
    (s : ℕ → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : BufferAbsorptionCorner E,
      Joined (1 : unitary E) D.anchor ∧ D.q ≠ 0 ∧
      D.q * s (n + 2) = 0 ∧
      (∀ i : Fin (n + 1), ‖s i * D.q - D.q * s i‖ < ε) ∧
      (∀ i : Fin (n + 1),
        ‖D.q * s i * D.q - zeroCornerRow D.q D.a D.b n i‖ < ε) ∧
      (∃ z : E, star z * z = 1 ∧ D.q * z = z ∧
        ∀ y : E, (∀ i, Commute (s i) y ∧ Commute (star (s i)) y) → Commute z y) ∧
      (∀ y : E, (∀ i, Commute (s i) y ∧ Commute (star (s i)) y) →
        Commute D.q y ∧ Commute D.w y ∧ Commute D.a y ∧ Commute D.b y) := by
  let r := s (n + 1)
  let z := s (n + 2)
  have hrr : star r * r = 1 := by simpa only [r, ite_true] using hs (n + 1) (n + 1)
  have hzz : star z * z = 1 := by simpa only [z, ite_true] using hs (n + 2) (n + 2)
  obtain ⟨D₀, hq₀, hw₀, _, hanchor, hcomm₀⟩ := exists_connected_buffer_corner
    z (s (n + 3)) (s (n + 4)) hzz
    (by simpa only [ite_true] using hs (n + 3) (n + 3))
    (by simpa only [ite_true] using hs (n + 4) (n + 4))
    (by simp only [z, hs, show n + 2 ≠ n + 3 by omega, ite_false])
    (by simp only [z, hs, show n + 2 ≠ n + 4 by omega, ite_false])
    (by simp only [hs, show n + 3 ≠ n + 4 by omega, ite_false])
  let q := D₀.q
  have hqdef : q = 1 - z * star z := hq₀
  let t := zeroCornerRow q D₀.a D₀.b n
  let S : Fin (n + 1) → E := fun i => s i
  have hq : q * q = q := D₀.projection.isIdempotentElem.eq
  have hqs : star q = q := D₀.projection.isSelfAdjoint.star_eq
  have hS (i j : Fin (n + 1)) : star (S i) * S j = if i = j then 1 else 0 := by
    simpa only [S, Fin.ext_iff] using hs i j
  have hrS (i : Fin (n + 1)) : star r * S i = 0 := by
    dsimp only [r, S]
    rw [hs, ite_eq_right (by omega)]
  have hzS (i : Fin (n + 1)) : star z * S i = 0 := by
    dsimp only [z, S]
    rw [hs, ite_eq_right (by omega)]
  have hzr : star z * r = 0 := by
    dsimp only [z, r]
    rw [hs, ite_eq_right (by omega)]
  have htq (i : Fin (n + 1)) : t i * q = t i :=
    (zeroCornerRow_support q D₀.a D₀.b hq D₀.a_left D₀.b_left D₀.b_right n i).2
  have htt (i j : Fin (n + 1)) : star (t i) * t j = if i = j then q else 0 :=
    zeroCornerRow_gram q D₀.a D₀.b hqs hq D₀.a_gram D₀.b_gram D₀.orthogonal
      D₀.a_left D₀.b_left D₀.b_right n i j
  have ht : ∑ i, t i * star (t i) = q :=
    zeroCornerRow_range_sum q D₀.a D₀.b hqs hq D₀.a_right D₀.ranges n
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < min ε ((ε / 4) ^ 2) by positivity)
  have hmε : ((m : ℝ) + 1)⁻¹ < ε := by
    simpa only [one_div] using hm.trans_le (min_le_left _ _)
  have hmSq : ((m : ℝ) + 1)⁻¹ < (ε / 4) ^ 2 := by
    simpa only [one_div] using hm.trans_le (min_le_right _ _)
  let v := finiteRowIsometry S t r q m
  have hv : star v * v = q := finiteRowIsometry_gram S t r q hq hqs hrr hrS hS htq ht m
  have hvq : v * q = v := relativeIsometry_mul_support v q hv hqs hq
  obtain ⟨u, hu, hue, huq, _, _⟩ := exists_connected_finiteRowCompletion
    S t r q z hq hqs hrr hrS hS htq ht hzz hzr hzS hq₀ m
  let D := D₀.transported u
  let F := (Unitary.conjStarAlgAut ℂ E u).toStarAlgHom
  have hDq : D.q = v * star v := by
    change (u : E) * q * star (u : E) = _
    calc
      _ = ((u : E) * q) * star ((u : E) * q) := by
        rw [star_mul, hqs]
        symm
        calc
          _ = (u : E) * (q * q) * star (u : E) := by noncomm_ring
          _ = _ := by rw [hq]
      _ = _ := by rw [huq]
  have hg (i : Fin (n + 1)) : zeroCornerRow D.q D.a D.b n i = v * t i * star v := by
    have hmapped := zeroCornerRow_map F q D₀.a D₀.b n i
    change F (t i) = zeroCornerRow D.q D.a D.b n i at hmapped
    rw [← hmapped]
    change (u : E) * t i * star (u : E) = _
    have htl : q * t i = t i :=
      (zeroCornerRow_support q D₀.a D₀.b hq D₀.a_left D₀.b_left D₀.b_right n i).1
    calc
      _ = ((u : E) * q) * t i * star ((u : E) * q) := by
        rw [star_mul, hqs]
        rw [show (u : E) * q * t i * (q * star (u : E)) =
          (u : E) * (q * t i) * q * star (u : E) by noncomm_ring, htl,
          show (u : E) * t i * q * star (u : E) =
            (u : E) * (t i * q) * star (u : E) by noncomm_ring, htq]
      _ = _ := by rw [huq]
  have huv (Y : E) (hY : ∀ i, Commute (s i) Y ∧ Commute (star (s i)) Y) :
      Commute (u : E) Y := by
    have hqY : Commute q Y := by
      rw [hqdef]
      exact (Commute.one_left Y).sub_left ((hY (n + 2)).1.mul_left (hY (n + 2)).2)
    have hc₀ := hcomm₀ Y (hY (n + 2)).1 (hY (n + 2)).2
      (hY (n + 3)).1 (hY (n + 3)).2 (hY (n + 4)).1 (hY (n + 4)).2
    have hqstarY : Commute (star q) Y := by simpa only [hqs] using hqY
    have htY (i : Fin (n + 1)) : Commute (t i) Y :=
      zeroCornerRow_commutes q D₀.a D₀.b Y hqY hc₀.1 hc₀.2.2.1 n i
    have htstarY (i : Fin (n + 1)) : Commute (star (t i)) Y :=
      zeroCornerRow_star_commutes q D₀.a D₀.b Y hqstarY hc₀.2.1 hc₀.2.2.2 n i
    have hvY : Commute v Y := finiteRowIsometry_commutes S t r q Y
      (fun i => (hY i).1) htstarY (hY (n + 1)).1 hqY m
    have hvStarY : Commute (star v) Y := finiteRowIsometry_star_commutes S t r q Y
      (fun i => (hY i).2) htY (hY (n + 1)).2 hqstarY m
    rw [hue]
    exact partialIsometryCompletion_commutes z q v Y (hY (n + 2)).1
      (hY (n + 2)).2 hqY (by simpa only [hqs] using hqY) hvY hvStarY
  refine ⟨D, D₀.transported_anchor_joined u hanchor hu, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hvzero : v = 0 := by
      have hvs : (v * star v) * v = v := by rw [mul_assoc, hv, hvq]
      rw [← hDq, hzero, zero_mul] at hvs
      exact hvs.symm
    have hqzero : q = 0 := by rw [← hv, hvzero, star_zero, zero_mul]
    have hqt : q * s (n + 3) = s (n + 3) := by
      rw [hqdef, sub_mul, one_mul, mul_assoc]
      simp only [z, hs, show n + 2 ≠ n + 3 by omega, ite_false, mul_zero, sub_zero]
    rw [hqzero, zero_mul] at hqt
    have h := hs (n + 3) (n + 3)
    rw [← hqt, star_zero, zero_mul] at h
    exact zero_ne_one (by simpa only [ite_true] using h)
  · rw [hDq]
    exact finiteRowRange_unused S t r q z hzr hzS m
  · intro i
    rw [hDq]
    have hbound := finiteRowRange_commutator_bound S t r q hq hqs hrr hrS hS htq ht htt m i
    have hsqrt₁ := Real.sq_sqrt (show 0 ≤ ((m : ℝ) + 1)⁻¹ by positivity)
    have hsqrt₂ := Real.sq_sqrt (show 0 ≤ 2 / ((m : ℝ) + 1) by positivity)
    have hc : 2 / ((m : ℝ) + 1) = 2 * ((m : ℝ) + 1)⁻¹ := by rw [div_eq_mul_inv]
    have h₁ : Real.sqrt (((m : ℝ) + 1)⁻¹) < ε / 4 := by
      nlinarith [Real.sqrt_nonneg (((m : ℝ) + 1)⁻¹)]
    have h₂ : Real.sqrt (2 / ((m : ℝ) + 1)) < ε / 2 := by
      have hsqrt₂' := hsqrt₂.trans hc
      nlinarith [Real.sqrt_nonneg (2 / ((m : ℝ) + 1))]
    exact hbound.trans_lt (by linarith)
  · intro i
    rw [hg, hDq]
    have hcomp : (v * star v) * s i * (v * star v) =
        (((m : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ) • (v * t i * star v) := by
      calc
        _ = v * (star v * S i * v) * star v := by change _ = v * (star v * s i * v) * star v; noncomm_ring
        _ = _ := by
          rw [finiteRowIsometry_compression S t r q hq hqs hrr hrS hS htq ht m i,
            mul_smul_comm, smul_mul_assoc]
    have hgn : ‖v * t i * star v‖ ≤ 1 := by
      rw [← hg]
      have hgD := zeroCornerRow_gram D.q D.a D.b D.projection.isSelfAdjoint.star_eq
        D.projection.isIdempotentElem.eq D.a_gram D.b_gram D.orthogonal
        D.a_left D.b_left D.b_right n i i
      have hn := congrArg norm hgD
      simp only [ite_true, CStarRing.norm_star_mul_self] at hn
      have hqn := IsStarProjection.norm_le D.q D.projection
      nlinarith [norm_nonneg (zeroCornerRow D.q D.a D.b n i)]
    have he : (v * star v) * s i * (v * star v) - v * t i * star v =
        -(((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) • (v * t i * star v)) := by
      rw [hcomp]
      have hc : ((m : ℝ) / ((m : ℝ) + 1)) - 1 = -((m : ℝ) + 1)⁻¹ := by
        have hn : (m : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring
      calc
        _ = (((m : ℝ) / ((m : ℝ) + 1) - 1 : ℝ) : ℂ) • (v * t i * star v) := by push_cast; module
        _ = _ := by rw [hc, Complex.ofReal_neg, neg_smul]
    rw [he, norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ((m : ℝ) + 1)⁻¹)]
    exact (mul_le_of_le_one_right (by positivity) hgn).trans_lt hmε
  · refine ⟨(u : E) * s (n + 3), ?_, ?_, ?_⟩
    · rw [star_mul]
      calc
        _ = star (s (n + 3)) * (star (u : E) * (u : E)) * s (n + 3) := by
          noncomm_ring
        _ = 1 := by rw [u.prop.1, mul_one, hs, ite_eq_left rfl]
    · have hqz₀ : q * s (n + 3) = s (n + 3) := by
        rw [hqdef, sub_mul, one_mul, mul_assoc]
        simp only [z, hs, show n + 2 ≠ n + 3 by omega, ite_false, mul_zero, sub_zero]
      change ((u : E) * q * star (u : E)) * ((u : E) * s (n + 3)) = _
      calc
        _ = (u : E) * q * (star (u : E) * (u : E)) * s (n + 3) := by noncomm_ring
        _ = (u : E) * s (n + 3) := by rw [u.prop.1, mul_one, mul_assoc, hqz₀]
    · intro y hy
      exact (huv y hy).mul_left (hy (n + 3)).1
  · intro y hy
    have hyStar (i : ℕ) : Commute (s i) (star y) ∧ Commute (star (s i)) (star y) := by
      exact ⟨by simpa only [star_star] using (hy i).2.star_star,
        by simpa only [star_star] using (hy i).1.star_star⟩
    have huY := huv y hy
    have huStarY : Commute (star (u : E)) y := by
      simpa only [star_star] using (huv (star y) hyStar).star_star
    have hqY : Commute D₀.q y := by
      rw [hq₀]
      exact (Commute.one_left _).sub_left ((hy (n + 2)).1.mul_left (hy (n + 2)).2)
    have hc := hcomm₀ y (hy (n + 2)).1 (hy (n + 2)).2
      (hy (n + 3)).1 (hy (n + 3)).2 (hy (n + 4)).1 (hy (n + 4)).2
    exact ⟨(huY.mul_left hqY).mul_left huStarY,
      huY.mul_left (by rw [hw₀]; exact (hy (n + 2)).1),
      (huY.mul_left hc.1).mul_left huStarY,
      (huY.mul_left hc.2.2.1).mul_left huStarY⟩


/-- The actual internal unit-isometry, forgetting its commutant data. -/
lemma exists_canonical_connected_absorption_corner_with_isometry [Nontrivial E]
    (s : ℕ → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : BufferAbsorptionCorner E,
      Joined (1 : unitary E) D.anchor ∧ D.q ≠ 0 ∧
      D.q * s (n + 2) = 0 ∧
      (∀ i : Fin (n + 1), ‖s i * D.q - D.q * s i‖ < ε) ∧
      (∀ i : Fin (n + 1),
        ‖D.q * s i * D.q - zeroCornerRow D.q D.a D.b n i‖ < ε) ∧
      (∃ z : E, star z * z = 1 ∧ D.q * z = z) ∧
      (∀ y : E, (∀ i, Commute (s i) y ∧ Commute (star (s i)) y) →
        Commute D.q y ∧ Commute D.w y ∧ Commute D.a y ∧ Commute D.b y) := by
  obtain ⟨D, hanchor, hqne, hqz, hqc, hcomp, ⟨z, hz, hqz', _⟩, hcomm⟩ :=
    exists_canonical_connected_absorption_corner_with_commuting_isometry s hs n ε hε
  exact ⟨D, hanchor, hqne, hqz, hqc, hcomp, ⟨z, hz, hqz'⟩, hcomm⟩

/-- The canonical absorption corner with its source commutant data. -/
lemma exists_canonical_connected_absorption_corner [Nontrivial E]
    (s : ℕ → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : BufferAbsorptionCorner E,
      Joined (1 : unitary E) D.anchor ∧ D.q ≠ 0 ∧
      D.q * s (n + 2) = 0 ∧
      (∀ i : Fin (n + 1), ‖s i * D.q - D.q * s i‖ < ε) ∧
      (∀ i : Fin (n + 1),
        ‖D.q * s i * D.q - zeroCornerRow D.q D.a D.b n i‖ < ε) ∧
      (∀ y : E, (∀ i, Commute (s i) y ∧ Commute (star (s i)) y) →
        Commute D.q y ∧ Commute D.w y ∧ Commute D.a y ∧ Commute D.b y) := by
  obtain ⟨D, hanchor, hqne, hqz, hqc, hcomp, _, hcomm⟩ :=
    exists_canonical_connected_absorption_corner_with_isometry s hs n ε hε
  exact ⟨D, hanchor, hqne, hqz, hqc, hcomp, hcomm⟩

end WeakPureInfiniteness

end

end OAI
