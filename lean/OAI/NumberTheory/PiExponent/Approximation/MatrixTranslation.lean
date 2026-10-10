import OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix
import OAI.NumberTheory.PiExponent.Approximation.RowTranslation

namespace OAI

namespace PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

noncomputable def periodCoordinate (j : ℕ) (ω : ℂ) : PowerSeries ℂ :=
  PowerSeries.C ((j : ℂ) * ω) + PowerSeries.log ℂ

noncomputable def periodMonomial {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) : MvPolynomial (Fin m) (PowerSeries ℂ) :=
  C ((1 + PowerSeries.X) ^ h) *
    ∏ i, (C (periodCoordinate j ω) + X i) ^ a i

theorem periodMonomial_as_shift {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) :
    periodMonomial j ω h a = C ((1 + PowerSeries.X) ^ h) *
      shift (fun _ => periodCoordinate j ω) (monomial (InterpolationMatrix.exponentVector a) 1) := by
  rw [periodMonomial, shift_monomial_one]
  simp [add_comm]

theorem periodMonomial_coeff {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    (periodMonomial j ω h a).coeff A =
      ((∏ i, (a i).choose (A i) : ℕ) : PowerSeries ℂ) *
        (1 + PowerSeries.X) ^ h * periodCoordinate j ω ^ (∑ i : Fin m, (a i - A i)) := by
  rw [periodMonomial_as_shift, coeff_C_mul]
  change _ * shiftCoefficient _ _ _ = _
  rw [shiftCoefficient_eq, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [InterpolationMatrix.exponentVector_apply, Nat.cast_prod]
  ring

theorem periodMonomial_support_le {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) {A : Fin m →₀ ℕ}
    (hA : A ∈ (periodMonomial j ω h a).support) : ∀ i, A i ≤ a i := by
  intro i
  by_contra hn
  have hi : a i < A i := by omega
  have hzero : (∏ k, (a k).choose (A k) : ℕ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Nat.choose_eq_zero_of_lt hi
  have hz : (periodMonomial j ω h a).coeff A = 0 := by
    rw [periodMonomial_coeff, hzero]
    simp
  exact (MvPolynomial.mem_support_iff.mp hA) hz

theorem periodMonomial_support_weight {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) (w : Fin m → ℝ) (H : ℝ) (hw : ∀ i, 0 ≤ w i)
    (ha : ∑ i, w i * a i ≤ H) {A : Fin m →₀ ℕ}
    (hA : A ∈ (periodMonomial j ω h a).support) :
    ∑ i, w i * A i ≤ H := by
  apply le_trans _ ha
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hw i)
  exact_mod_cast periodMonomial_support_le j ω h a hA i

noncomputable def transverseIndices {m : ℕ} (w : Fin m → ℝ) (H : ℝ) :
    Finset (Fin m →₀ ℕ) :=
  (PiExponent.realWeightedSimplex w H).map Finsupp.equivFunOnFinite.symm.toEmbedding

@[simp] theorem mem_transverseIndices {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 0 < w i) (A : Fin m →₀ ℕ) :
    A ∈ transverseIndices w H ↔ ∑ i, w i * A i ≤ H := by
  classical
  simp only [transverseIndices, Finset.mem_map_equiv, PiExponent.mem_realWeightedSimplex hw]
  rfl

@[simp] theorem card_transverseIndices {m : ℕ} (w : Fin m → ℝ) (H : ℝ) :
    (transverseIndices w H).card = (PiExponent.realWeightedSimplex w H).card := by
  simp [transverseIndices]

theorem periodMonomial_support_subset {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) (w : Fin m → ℝ) (H : ℝ) (hw : ∀ i, 0 < w i)
    (ha : ∑ i, w i * a i ≤ H) :
    (periodMonomial j ω h a).support ⊆ transverseIndices w H := by
  intro A hA
  apply (mem_transverseIndices w H hw A).2
  exact periodMonomial_support_weight j ω h a w H (fun i => (hw i).le) ha hA

theorem transverseIndices_coordinate_le {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 1 ≤ w i) {A : Fin m →₀ ℕ} (hA : A ∈ transverseIndices w H) (i : Fin m) :
    A i ≤ ⌊H⌋₊ := by
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le zero_lt_one (hw i)
  have ha := (mem_transverseIndices w H hwpos A).mp hA
  apply Nat.le_floor
  calc
    (A i : ℝ) ≤ w i * A i := by nlinarith [show (0 : ℝ) ≤ (A i : ℝ) by positivity, hw i]
    _ ≤ ∑ k, w k * A k := Finset.single_le_sum
      (fun k hk => mul_nonneg (hwpos k).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
    _ ≤ H := ha

theorem transverseIndices_card_le {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 1 ≤ w i) :
    (transverseIndices w H).card ≤ (⌊H⌋₊ + 1) ^ m := by
  classical
  let box : Finset (Fin m → ℕ) := Fintype.piFinset (fun _ => Finset.range (⌊H⌋₊ + 1))
  have hcard : (transverseIndices w H).card ≤ box.card := by
    apply Finset.card_le_card_of_injOn (fun A : Fin m →₀ ℕ => fun i => A i)
    · intro A hA
      apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (transverseIndices_coordinate_le w H hw hA i))
    · intro A hA B hB he
      exact Finsupp.ext (fun i => congrFun he i)
  simpa [box, Fintype.card_piFinset] using hcard

theorem row_term_count {m : ℕ} (w : Fin m → ℝ) (H v : ℝ)
    (hw : ∀ i, 1 ≤ w i) (β : Fin m →₀ ℕ) (s : ℕ) (hs : (s : ℝ) ≤ H / v) :
    Fintype.card (RowChoices (transverseIndices w H) β s) ≤
      (⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v⌋₊ + 1) := by
  have h := card_rowChoices_box_le (transverseIndices w H) β s ⌊H⌋₊
    (fun A hA i => transverseIndices_coordinate_le w H hw hA i)
    (by simpa using transverseIndices_card_le w H hw)
  simp only [Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_floor hs) 1))

noncomputable def formalMonomialImage {m : ℕ} (r : Fin m → ℂ)
    (T : Fin m → ℕ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) :=
  MvPolynomial.map Polynomial.coeToPowerSeries.ringHom
    (InterpolationMatrix.monomialImage r (fun i => InterpolationMatrix.truncatedLog (T i)) j h a)

theorem coordinate_translation (j : ℕ) (ω r : ℂ) (T : ℕ) :
    periodCoordinate j ω + (PowerSeries.C ((j : ℂ) * (r - ω)) +
      tail T (PowerSeries.log ℂ)) =
      PowerSeries.C ((j : ℂ) * r) + (InterpolationMatrix.truncatedLog T : PowerSeries ℂ) := by
  unfold periodCoordinate tail InterpolationMatrix.truncatedLog
  calc
    _ = PowerSeries.C ((j : ℂ) * ω) + PowerSeries.C ((j : ℂ) * (r - ω)) +
        (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) := by ring
    _ = _ := by rw [← map_add]; congr 1; congr 1; ring

theorem periodMonomial_shift {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j : ℕ) (ω : ℂ) (h : ℕ) (a : Fin m → ℕ) :
    shift (fun i => PowerSeries.C ((j : ℂ) * (r i - ω)) + tail (T i) (PowerSeries.log ℂ))
      (periodMonomial j ω h a) = formalMonomialImage r T j h a := by
  simp only [periodMonomial, formalMonomialImage, InterpolationMatrix.monomialImage,
    map_mul, map_prod, map_pow, map_add, shift_C, shift_X, MvPolynomial.map_C,
    MvPolynomial.map_X, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_one, Polynomial.coe_X]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  calc
    _ = C (periodCoordinate j ω + (PowerSeries.C ((j : ℂ) * (r i - ω)) +
        tail (T i) (PowerSeries.log ℂ))) + X i := by simp only [map_add, map_mul]; ring
    _ = _ := by rw [coordinate_translation]; simp [map_add]

theorem formalMonomialImage_coeff {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ℕ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ) :
    PowerSeries.coeff s ((formalMonomialImage r T j h a).coeff
      (InterpolationMatrix.exponentVector b)) =
      InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a := by
  simp [formalMonomialImage, MvPolynomial.coeff_map, InterpolationMatrix.entry]

theorem matrix_entry_translation {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ℕ) (ω : ℂ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ)
    (S : Finset (Fin m →₀ ℕ)) (hp : (periodMonomial j ω h a).support ⊆ S) :
    InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a =
      ∑ A ∈ S, ∑ d : (∀ i, Fin (A i - (InterpolationMatrix.exponentVector b) i + 1)),
        ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal s,
          rowScalar (fun i => (j : ℂ) * (r i - ω))
            (fun i => tail (T i) (PowerSeries.log ℂ))
            (InterpolationMatrix.exponentVector b) A d kl.1 *
            PowerSeries.coeff kl.2 ((periodMonomial j ω h a).coeff A) := by
  rw [← formalMonomialImage_coeff r T j s b h a, ← periodMonomial_shift r T j ω h a]
  exact exact_row_identity _ _ _ _ S hp s

theorem matrix_entry_translation_choices {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ℕ) (ω : ℂ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ)
    (S : Finset (Fin m →₀ ℕ)) (hp : (periodMonomial j ω h a).support ⊆ S) :
    InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a =
      ∑ t : RowChoices S (InterpolationMatrix.exponentVector b) s,
        rowScalar (fun i => (j : ℂ) * (r i - ω))
          (fun i => tail (T i) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector b) t.1.1 t.2.1 t.2.2 *
          PowerSeries.coeff (s - t.2.2) ((periodMonomial j ω h a).coeff t.1.1) := by
  classical
  rw [matrix_entry_translation r T j s ω b h a S hp, Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]

theorem det_dependent_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {δ : ι → Type*} [∀ i, Fintype (δ i)]
    (B : ∀ i, δ i → ℂ) (C : ∀ i, δ i → ι → ℂ) :
    Matrix.det (fun i j => ∑ t, B i t * C i t j) =
      ∑ f : (∀ i, δ i), (∏ i, B i (f i)) * Matrix.det (fun i j => C i (f i) j) := by
  classical
  have hm := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum
    (fun i t => B i t • C i t)
  calc
    _ = Matrix.det (fun i => ∑ t, B i t • C i t) := by
      congr 1
      funext i j
      simp
    _ = ∑ f : (∀ i, δ i), Matrix.det (fun i => B i (f i) • C i (f i)) := hm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f hf
      exact Matrix.det_mul_column (fun i => B i (f i)) (fun i j => C i (f i) j)

theorem det_matrix_translation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ι → ℕ) (ω : ℂ) (b : ι → Fin m → ℕ)
    (h : ι → ℕ) (a : ι → Fin m → ℕ) (S : Finset (Fin m →₀ ℕ))
    (hp : ∀ i c, (periodMonomial (j i) ω (h c) (a c)).support ⊆ S) :
    Matrix.det (fun i c => InterpolationMatrix.entry r
      (fun k => InterpolationMatrix.truncatedLog (T k)) (j i) (s i) (b i) (h c) (a c)) =
      ∑ f : (∀ i, RowChoices S (InterpolationMatrix.exponentVector (b i)) (s i)),
        (∏ i, rowScalar (fun k => (j i : ℂ) * (r k - ω))
          (fun k => tail (T k) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector (b i)) (f i).1.1 (f i).2.1 (f i).2.2) *
          Matrix.det (fun i c => PowerSeries.coeff (s i - (f i).2.2)
            ((periodMonomial (j i) ω (h c) (a c)).coeff (f i).1.1)) := by
  have he : (fun i c => InterpolationMatrix.entry r
      (fun k => InterpolationMatrix.truncatedLog (T k)) (j i) (s i) (b i) (h c) (a c)) =
      (fun i c => ∑ t : RowChoices S (InterpolationMatrix.exponentVector (b i)) (s i),
        rowScalar (fun k => (j i : ℂ) * (r k - ω))
          (fun k => tail (T k) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector (b i)) t.1.1 t.2.1 t.2.2 *
          PowerSeries.coeff (s i - t.2.2) ((periodMonomial (j i) ω (h c) (a c)).coeff t.1.1)) := by
    funext i c
    exact matrix_entry_translation_choices r T (j i) (s i) ω (b i) (h c) (a c) S (hp i c)
  rw [he]
  exact det_dependent_row_sum _ _

end PiExponent.MatrixTranslation

end OAI
