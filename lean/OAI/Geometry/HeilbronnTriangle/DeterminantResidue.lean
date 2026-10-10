import Mathlib

namespace OAI

namespace Problem355.DeterminantResidue

lemma small_eq_of_modEq {h τ a b : ℤ} (hwidth : 2 * τ < h)
    (ha : |a| ≤ τ) (hb : |b| ≤ τ) (hab : a ≡ b [ZMOD h]) : a = b := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hdist : |b - a| < h := by
    rw [abs_lt]
    omega
  have hz := Int.eq_zero_of_abs_lt_dvd (Int.modEq_iff_dvd.mp hab) hdist
  omega

lemma small_eq_of_zmod_eq {h : ℕ} {τ a b : ℤ} (hwidth : 2 * τ < h)
    (ha : |a| ≤ τ) (hb : |b| ≤ τ) (hab : (a : ZMod h) = b) : a = b :=
  small_eq_of_modEq hwidth ha hb ((ZMod.intCast_eq_intCast_iff a b h).mp hab)

lemma small_residue_subsingleton {h : ℕ} {τ : ℤ} (hwidth : 2 * τ < h)
    (c : ZMod h) : Set.Subsingleton {a : ℤ | |a| ≤ τ ∧ (a : ZMod h) = c} := by
  intro a ha b hb
  exact small_eq_of_zmod_eq hwidth ha.1 hb.1 (ha.2.trans hb.2.symm)

lemma small_filter_eq_fiber {α : Type*} [DecidableEq α] (s : Finset α)
    (d : α → ℤ) {h : ℕ} {τ : ℤ} (hwidth : 2 * τ < h)
    (c : ZMod h) (hres : ∀ x ∈ s, (d x : ZMod h) = c)
    {a : α} (ha : a ∈ s) (hasmall : |d a| ≤ τ) :
    s.filter (fun x => |d x| ≤ τ) = s.filter (fun x => d x = d a) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hsmall⟩
    exact ⟨hx, small_eq_of_zmod_eq hwidth hsmall hasmall
      ((hres x hx).trans (hres a ha).symm)⟩
  · rintro ⟨hx, heq⟩
    exact ⟨hx, heq ▸ hasmall⟩

lemma sum_small_le_of_fiber_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (d : α → ℤ) (w : α → ℝ) {h : ℕ} {τ : ℤ}
    (hwidth : 2 * τ < h) (c : ZMod h)
    (hres : ∀ x ∈ s, (d x : ZMod h) = c) {B : ℝ} (hB : 0 ≤ B)
    (hfiber : ∀ t : ℤ, |t| ≤ τ → ∑ x ∈ s.filter (fun x => d x = t), w x ≤ B) :
    ∑ x ∈ s.filter (fun x => |d x| ≤ τ), w x ≤ B := by
  by_cases hempty : (s.filter (fun x => |d x| ≤ τ)).Nonempty
  · obtain ⟨a, ha⟩ := hempty
    have hamem := (Finset.mem_filter.mp ha).1
    have hasmall := (Finset.mem_filter.mp ha).2
    rw [small_filter_eq_fiber s d hwidth c hres hamem hasmall]
    exact hfiber (d a) hasmall
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
    simpa using hB

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma cast_det (h : ℕ) (A : Matrix ι ι ℤ) :
    (A.det : ZMod h) = (A.map (Int.castRingHom (ZMod h))).det := by
  exact (Int.castRingHom (ZMod h)).map_det A

lemma det_residue_of_specialLinear {h : ℕ} (A : Matrix ι ι ℤ)
    (C : Matrix ι ι (ZMod h)) (G : Matrix.SpecialLinearGroup ι (ZMod h))
    (hA : A.map (Int.castRingHom (ZMod h)) = (G : Matrix ι ι (ZMod h)) * C) :
    (A.det : ZMod h) = C.det := by
  rw [cast_det h A, hA, Matrix.det_mul, G.prop, one_mul]

lemma small_determinants_eq_of_same_orbit {h : ℕ} {τ : ℤ}
    (hwidth : 2 * τ < h) (A B : Matrix ι ι ℤ)
    (C : Matrix ι ι (ZMod h))
    (G H : Matrix.SpecialLinearGroup ι (ZMod h))
    (hA : A.map (Int.castRingHom (ZMod h)) = (G : Matrix ι ι (ZMod h)) * C)
    (hB : B.map (Int.castRingHom (ZMod h)) = (H : Matrix ι ι (ZMod h)) * C)
    (ha : |A.det| ≤ τ) (hb : |B.det| ≤ τ) : A.det = B.det :=
  small_eq_of_zmod_eq hwidth ha hb
    ((det_residue_of_specialLinear A C G hA).trans
      (det_residue_of_specialLinear B C H hB).symm)

lemma cast_det_ne_zero_of_abs_lt {q : ℕ} (A : Matrix ι ι ℤ)
    (hne : A.det ≠ 0) (hsmall : |A.det| < q) : (A.det : ZMod q) ≠ 0 := by
  intro hz
  exact hne (Int.eq_zero_of_abs_lt_dvd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd A.det q).mp hz) hsmall)

lemma affineIndependent_cols_mod_of_small_nonzero_det {q : ℕ} [Fact q.Prime]
    (A : Matrix ι ι ℤ) (hne : A.det ≠ 0) (hsmall : |A.det| < q) :
    AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col := by
  apply LinearIndependent.affineIndependent
  apply Matrix.linearIndependent_cols_of_det_ne_zero
  rw [← cast_det q A]
  exact cast_det_ne_zero_of_abs_lt A hne hsmall

lemma sum_small_determinants_le {h : ℕ} {τ : ℤ} (hwidth : 2 * τ < h)
    (s : Finset (Matrix ι ι ℤ)) (C : Matrix ι ι (ZMod h))
    (horbit : ∀ A ∈ s, ∃ G : Matrix.SpecialLinearGroup ι (ZMod h),
      A.map (Int.castRingHom (ZMod h)) = (G : Matrix ι ι (ZMod h)) * C)
    (w : Matrix ι ι ℤ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hfiber : ∀ t : ℤ, |t| ≤ τ →
      ∑ A ∈ s.filter (fun A => A.det = t), w A ≤ B) :
    ∑ A ∈ s.filter (fun A => |A.det| ≤ τ), w A ≤ B := by
  apply sum_small_le_of_fiber_bound s Matrix.det w hwidth C.det _ hB hfiber
  intro A hA
  obtain ⟨G, hG⟩ := horbit A hA
  exact det_residue_of_specialLinear A C G hG

lemma sum_nonzero_det_weights_le {q : ℕ} [Fact q.Prime]
    (s : Finset (Matrix ι ι ℤ)) {t : ℤ} (ht : t ≠ 0) (htq : |t| < q)
    (hdet : ∀ A ∈ s, A.det = t) (w : Matrix ι ι ℤ → ℝ)
    {K M : ℝ} (hK : 0 ≤ K) (hcard : (s.card : ℝ) ≤ M)
    (hw : ∀ A ∈ s,
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col → w A ≤ K) :
    ∑ A ∈ s, w A ≤ M * K := by
  calc
    ∑ A ∈ s, w A ≤ ∑ _A ∈ s, K := by
      apply Finset.sum_le_sum
      intro A hA
      apply hw A hA
      apply affineIndependent_cols_mod_of_small_nonzero_det A
      · simpa [hdet A hA] using ht
      · simpa [hdet A hA] using htq
    _ = (s.card : ℝ) * K := by simp
    _ ≤ M * K := mul_le_mul_of_nonneg_right hcard hK

end Problem355.DeterminantResidue

end OAI
