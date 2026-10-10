import Mathlib
import OAI.Combinatorics.StripMass.PfaffianIntegration

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian
local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))
lemma integral_laguerreOddIntegrand {n : ℕ} (hn : Odd n) {a : ℝ} (ha : 0 < a) :
    (∫ x, laguerreOddIntegrand n a x ∂Measure.pi (fun _ : Fin n => μ₊)) =
      (n.factorial : ℂ) * (laguerreNormalizer n a : ℂ) := by
  have he : ∀ᵐ x ∂volume.restrict (laguerreDomain n),
      laguerreOddIntegrand n a x = (laguerreDensity n a x : ℂ) :=
    (ae_restrict_mem (isOpen_laguerreDomain n).measurableSet).mono
      fun x hx => laguerreOddIntegrand_eq hn a hx
  rw [integral_symmetric_ordered _
    (fun σ x => determinantPfaffian_symmetric_odd hn _
      (fun r s : ℝ => schurEntry r s) (fun _ => 1) (fun r s => schurEntry_swap _ _) σ x)
    (fun x hx => by
      unfold laguerreOddIntegrand
      rw [evaluationMatrix_det_of_not_injective _ hx, zero_mul])
    (by
      have hi := (integrableOn_laguerreDensity n ha).ofReal (𝕜 := ℂ)
      simp only [RCLike.ofReal_eq_complex_ofReal] at hi
      exact hi.congr (he.mono fun _ h => h.symm))]
  rw [integral_congr_ae he, integral_complex_ofReal]
  rfl

lemma laguerre_doubleIntegrand_eq {n : ℕ} (a : ℝ) (i j : Fin n) (rs : ℝ × ℝ) :
    doubleIntegrand (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) i j rs =
      (gammaSkewIntegrand (a+i.val) (a+j.val) rs : ℂ) := by
  simp only [doubleIntegrand, laguerrePhi, gammaSkewIntegrand, schurEntry,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add]
  rw [add_comm (rs.2 : ℂ) (rs.1 : ℂ)]
  ring

lemma integrable_laguerre_doubleIntegrand {n : ℕ} {a : ℝ} (ha : 0 < a) (i j : Fin n) :
    Integrable (doubleIntegrand (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) i j)
      (μ₊.prod μ₊) := by
  have he : doubleIntegrand (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) i j =
      fun rs => (gammaSkewIntegrand (a+i.val) (a+j.val) rs : ℂ) :=
    funext (laguerre_doubleIntegrand_eq a i j)
  rw [he]
  simpa only [RCLike.ofReal_eq_complex_ofReal] using
    (laguerre_double_moment ha i.val j.val).1.ofReal (𝕜 := ℂ)

lemma laguerre_doubleMomentMatrix_eq {a : ℝ} (n : ℕ) :
    doubleMomentMatrix μ₊ (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) =
      laguerreMomentMatrix n a := by
  ext i j
  simp only [doubleMomentMatrix, laguerre_doubleIntegrand_eq, integral_complex_ofReal,
    laguerreMomentMatrix]

lemma laguerre_singleMoment_eq (n : ℕ) (a : ℝ) :
    singleMoment μ₊ (laguerrePhi n a) (fun _ => 1) = laguerreMomentColumn n a := by
  ext i
  simp only [singleMoment, laguerrePhi, mul_one, integral_complex_ofReal, laguerreMomentColumn]

 

theorem laguerreNormalizer_eq_product (n : ℕ) {a : ℝ} (ha : 0 < a) :
    laguerreNormalizer n a = laguerreNormalizerProduct n a := by
  apply Complex.ofReal_injective
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    have hn : n = m*2 := by omega
    clear hm
    subst n
    have he : Even (m*2) := ⟨m, by omega⟩
    have h := deBruijn_even μ₊ m (laguerrePhi (m*2) a)
      (fun r s : ℝ => schurEntry r s) (fun r s => schurEntry_swap _ _)
        (integrable_laguerre_doubleIntegrand ha)
    change (∫ x, laguerreEvenIntegrand (m*2) a x ∂Measure.pi (fun _ => μ₊)) = _ at h
    rw [integral_laguerreEvenIntegrand he ha, laguerre_doubleMomentMatrix_eq,
      laguerreMomentMatrix_pfaffian_even ha _ he] at h
    exact mul_left_cancel₀ (show ((m*2).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (m*2)) h
  · obtain ⟨m, hm⟩ := hn
    have hn : n = m*2+1 := by omega
    clear hm
    subst n
    have he : Odd (m*2+1) := ⟨m, by omega⟩
    have hs (i : Fin (m*2+1)) : Integrable (fun t => laguerrePhi (m*2+1) a i t * 1) μ₊ := by
      simpa only [IntegrableOn, laguerrePhi, mul_one, RCLike.ofReal_eq_complex_ofReal] using
        (integrableOn_laguerreWeight (show 0 < a+i.val by positivity)).ofReal (𝕜 := ℂ)
    have h := deBruijn_odd μ₊ m (laguerrePhi (m*2+1) a)
      (fun r s : ℝ => schurEntry r s) (fun _ => 1) (fun r s => schurEntry_swap _ _)
        (integrable_laguerre_doubleIntegrand ha) hs
    change (∫ x, laguerreOddIntegrand (m*2+1) a x ∂Measure.pi (fun _ => μ₊)) = _ at h
    rw [integral_laguerreOddIntegrand he ha, laguerre_doubleMomentMatrix_eq,
      laguerre_singleMoment_eq] at h
    rw [laguerreMomentMatrix_pfaffian_odd ha _ he] at h
    exact mul_left_cancel₀ (show ((m*2+1).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (m*2+1)) h

end
end CriticalStrip

 

namespace Matrix
open scoped _root_.Matrix
noncomputable section
open scoped BigOperators

 
lemma sum_det_updateRow_mul {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (f : ι → R) :
    (∑ i, (A.updateRow i (fun j => A i j * f j)).det) = A.det * ∑ j, f j := by
  calc
    _ = ∑ i, ∑ j, A.adjugate j i * (A i j * f j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← _root_.Matrix.cramer_transpose_apply, _root_.Matrix.cramer_eq_adjugate_mulVec, ← _root_.Matrix.adjugate_transpose]
      rfl
    _ = ∑ j, (∑ i, A.adjugate j i * A i j) * f j := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ j, A.det * f j := by
      apply Finset.sum_congr rfl
      intro j _
      change (A.adjugate * A) j j * f j = _
      rw [_root_.Matrix.adjugate_mul]
      simp
    _ = _ := by rw [Finset.mul_sum]

end
end Matrix

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))

def gammaPhi {n : ℕ} (q : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℂ := laguerreWeight (q i) x

def gammaSchurProduct {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  (∏ i, Real.Gamma (q i)) * (∏ i, ∏ j ∈ Finset.Ioi i, (q j - q i)/(q i + q j))

lemma gammaSchurProduct_eq {n : ℕ} (q : Fin n → ℝ) :
    (gammaSchurProduct q : ℂ) =
      (∏ i, (Real.Gamma (q i) : ℂ)) * schurProduct (fun i => (q i : ℂ)) := by
  simp only [gammaSchurProduct, Complex.ofReal_mul, Complex.ofReal_prod, schurProduct,
    schurEntry, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add]

lemma gammaPhi_doubleIntegrand_eq {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) (rs : ℝ × ℝ) :
    doubleIntegrand (gammaPhi q) (fun r s : ℝ => schurEntry r s) i j rs =
      (gammaSkewIntegrand (q i) (q j) rs : ℂ) := by
  simp only [doubleIntegrand, gammaPhi, gammaSkewIntegrand, schurEntry,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add]
  rw [add_comm (rs.2 : ℂ) (rs.1 : ℂ)]
  ring

lemma gammaPhi_doubleMomentMatrix_eq {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 < q i) :
    doubleMomentMatrix μ₊ (gammaPhi q) (fun r s : ℝ => schurEntry r s) =
      fun i j => (Real.Gamma (q i) : ℂ) * schurEntry (q i) (q j) * (Real.Gamma (q j) : ℂ) := by
  ext i j
  unfold doubleMomentMatrix
  rw [funext (gammaPhi_doubleIntegrand_eq q i j), integral_complex_ofReal,
    integral_gammaSkewIntegrand (hq i) (hq j)]
  simp only [schurEntry, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_add]
  ring

lemma integrable_gammaPhi_doubleIntegrand {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 < q i)
    (i j : Fin n) :
    Integrable (doubleIntegrand (gammaPhi q) (fun r s : ℝ => schurEntry r s) i j)
      (μ₊.prod μ₊) := by
  simp only [funext (gammaPhi_doubleIntegrand_eq q i j)]
  simpa only [RCLike.ofReal_eq_complex_ofReal] using
    (integrable_gammaSkewIntegrand (hq i) (hq j)).ofReal (𝕜 := ℂ)

lemma gammaPhi_singleMoment_eq {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 < q i) :
    singleMoment μ₊ (gammaPhi q) (fun _ => 1) = fun i => (Real.Gamma (q i) : ℂ) := by
  ext i
  simp only [singleMoment, gammaPhi, mul_one, integral_complex_ofReal,
    integral_laguerreWeight (hq i)]

 

theorem integral_gamma_determinant_schur {n : ℕ} {q : Fin n → ℝ}
    (hq : ∀ i, 0 < q i) (hqi : Function.Injective q)
    (f : (Fin n → ℝ) → ℝ) (hint : IntegrableOn f (laguerreDomain n))
    (heq : ∀ x ∈ laguerreDomain n,
      (evaluationMatrix (gammaPhi q) x).det * schurProduct (fun i => (x i : ℂ)) = (f x : ℂ)) :
    (∫ x in laguerreDomain n, f x) = gammaSchurProduct q := by
  have hdq (i j : Fin n) : (q i : ℂ) + (q j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact (add_pos (hq i) (hq j)).ne'
  have hqic : Function.Injective (fun i => (q i : ℂ)) := Complex.ofReal_injective.comp hqi
  have hdx {x : Fin n → ℝ} (hx : x ∈ laguerreDomain n) (i j : Fin n) :
      (x i : ℂ) + (x j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact (add_pos (hx.2 i) (hx.2 j)).ne'
  have hxic {x : Fin n → ℝ} (hx : x ∈ laguerreDomain n) :
      Function.Injective (fun i => (x i : ℂ)) := Complex.ofReal_injective.comp hx.1.injective
  apply Complex.ofReal_injective
  rw [gammaSchurProduct_eq, ← integral_complex_ofReal]
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    have hn : n = m*2 := by omega
    clear hm
    subst n
    have he : Even (m*2) := ⟨m, by omega⟩
    let F := fun x => (evaluationMatrix (gammaPhi q) x).det *
      pfaffian (m*2) (schurMatrix (fun i => (x i : ℂ)))
    have hF : ∀ᵐ x ∂volume.restrict (laguerreDomain (m*2)), F x = (f x : ℂ) := by
      filter_upwards [ae_restrict_mem (isOpen_laguerreDomain (m*2)).measurableSet] with x hx
      dsimp [F]
      rw [pfaffian_schur_even _ he _ (hdx hx) (hxic hx)]
      exact heq x hx
    have hFi : IntegrableOn F (laguerreDomain (m*2)) := by
      have hi := hint.ofReal (𝕜 := ℂ)
      simp only [RCLike.ofReal_eq_complex_ofReal] at hi
      exact hi.congr (hF.mono fun _ h => h.symm)
    have hy := integral_symmetric_ordered F
      (fun σ x => determinantPfaffian_symmetric_even he _ _
        (fun r s : ℝ => schurEntry_swap (r:ℂ) s) σ x)
      (fun x hx => by dsimp [F]; rw [evaluationMatrix_det_of_not_injective _ hx, zero_mul]) hFi
    have hb := deBruijn_even μ₊ m (gammaPhi q) (fun r s : ℝ => schurEntry r s)
      (fun r s => schurEntry_swap _ _) (integrable_gammaPhi_doubleIntegrand hq)
    change (∫ x, F x ∂Measure.pi (fun _ => μ₊)) = _ at hb
    rw [hy, integral_congr_ae hF, gammaPhi_doubleMomentMatrix_eq hq,
      pfaffian_weighted_schur_even _ he _ _ hdq hqic] at hb
    exact mul_left_cancel₀ (show ((m*2).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (m*2)) hb
  · obtain ⟨m, hm⟩ := hn
    have hn : n = m*2+1 := by omega
    clear hm
    subst n
    have he : Odd (m*2+1) := ⟨m, by omega⟩
    let F := fun x => (evaluationMatrix (gammaPhi q) x).det *
      pfaffian (m*2+2) (border (schurMatrix (fun i => (x i : ℂ))) (fun _ => 1))
    have hF : ∀ᵐ x ∂volume.restrict (laguerreDomain (m*2+1)), F x = (f x : ℂ) := by
      filter_upwards [ae_restrict_mem (isOpen_laguerreDomain (m*2+1)).measurableSet] with x hx
      dsimp [F]
      rw [pfaffian_schur_odd _ he _ (hdx hx) (hxic hx)]
      exact heq x hx
    have hFi : IntegrableOn F (laguerreDomain (m*2+1)) := by
      have hi := hint.ofReal (𝕜 := ℂ)
      simp only [RCLike.ofReal_eq_complex_ofReal] at hi
      exact hi.congr (hF.mono fun _ h => h.symm)
    have hy := integral_symmetric_ordered F
      (fun σ x => determinantPfaffian_symmetric_odd he _ _ (fun _ => 1)
        (fun r s : ℝ => schurEntry_swap (r:ℂ) s) σ x)
      (fun x hx => by dsimp [F]; rw [evaluationMatrix_det_of_not_injective _ hx, zero_mul]) hFi
    have hs (i : Fin (m*2+1)) : Integrable (fun t => gammaPhi q i t * 1) μ₊ := by
      simpa only [IntegrableOn, gammaPhi, mul_one, RCLike.ofReal_eq_complex_ofReal] using
        (integrableOn_laguerreWeight (hq i)).ofReal (𝕜 := ℂ)
    have hb := deBruijn_odd μ₊ m (gammaPhi q) (fun r s : ℝ => schurEntry r s) (fun _ => 1)
      (fun r s => schurEntry_swap _ _) (integrable_gammaPhi_doubleIntegrand hq) hs
    change (∫ x, F x ∂Measure.pi (fun _ => μ₊)) = _ at hb
    rw [hy, integral_congr_ae hF, gammaPhi_doubleMomentMatrix_eq hq, gammaPhi_singleMoment_eq hq,
      pfaffian_weighted_schur_odd _ he _ _ hdq hqic] at hb
    exact mul_left_cancel₀ (show ((m*2+1).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (m*2+1)) hb

end

noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

 
def inverseExponents (n : ℕ) (a : ℝ) : Fin (n+1) → ℝ :=
  Fin.cons (a-1) (fun i => a+(i.val+1))

lemma inverseExponents_pos {n : ℕ} {a : ℝ} (ha : 1 < a) :
    ∀ i : Fin (n+1), 0 < inverseExponents n a i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [inverseExponents, Fin.cons_zero] using sub_pos.mpr ha
  · simp only [inverseExponents, Fin.cons_succ]
    positivity

lemma inverseExponents_strictMono (n : ℕ) (a : ℝ) : StrictMono (inverseExponents n a) := by
  rw [inverseExponents, Fin.strictMono_cons]
  constructor
  · intro i
    have hi : (0 : ℝ) ≤ i.val := by positivity
    linarith
  · intro i j hij
    have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
    linarith

lemma laguerreWeight_add_one (a : ℝ) {x : ℝ} (hx : 0 < x) :
    laguerreWeight (a+1) x = laguerreWeight a x * x := by
  simpa using laguerreWeight_shift_nat a 1 hx

lemma inverseExponents_determinant {n : ℕ} (a : ℝ) {x : Fin (n+1) → ℝ}
    (hx : ∀ i, 0 < x i) :
    (evaluationMatrix (gammaPhi (inverseExponents n a)) x).det =
      (evaluationMatrix (laguerrePhi (n+1) a) x).det * ∑ i, (x i : ℂ)⁻¹ := by
  classical
  let A := evaluationMatrix (laguerrePhi (n+1) a) x
  have he : evaluationMatrix (gammaPhi (inverseExponents n a)) x =
      A.updateRow 0 (fun j => A 0 j * (x j : ℂ)⁻¹) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Matrix.updateRow_self, evaluationMatrix, gammaPhi, inverseExponents,
        Fin.cons_zero, A, laguerrePhi, Fin.val_zero, Nat.cast_zero, add_zero]
      have h := laguerreWeight_add_one (a-1) (hx j)
      rw [sub_add_cancel] at h
      rw [h, Complex.ofReal_mul, mul_inv_cancel_right₀ (by exact_mod_cast (hx j).ne')]
    · simp only [Matrix.updateRow_ne (Fin.succ_ne_zero i), evaluationMatrix, gammaPhi,
        inverseExponents, Fin.cons_succ, A, laguerrePhi, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  have hs (i : Fin n) : (A.updateRow i.succ (fun j => A i.succ j * (x j : ℂ)⁻¹)).det = 0 := by
    have hr : (fun j => A i.succ j * (x j : ℂ)⁻¹) = A i.castSucc := by
      ext j
      dsimp [A, evaluationMatrix, laguerrePhi]
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, laguerreWeight_add_one _ (hx j),
        Complex.ofReal_mul, mul_inv_cancel_right₀ (by exact_mod_cast (hx j).ne')]
    rw [hr]
    apply Matrix.det_updateRow_eq_zero
    exact fun h => by have hv := congrArg Fin.val h; simp only [Fin.val_castSucc, Fin.val_succ] at hv; omega
  rw [he]
  have h := Matrix.sum_det_updateRow_mul A (fun i => (x i : ℂ)⁻¹)
  simpa only [Fin.sum_univ_succ, hs, Finset.sum_const_zero, add_zero] using h

lemma integrableOn_laguerre_inverseSum {n : ℕ} {a : ℝ} (ha : 1 < a) :
    IntegrableOn (fun r : Fin n → ℝ => (∑ i, (r i)⁻¹) * laguerreDensity n a r)
      (laguerreDomain n) := by
  simp only [Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  simpa only [IntegrableOn, Real.rpow_neg_one] using integrableOn_laguerre_inverse_coordinate
    (by linarith : 0<a) i (p := 1) (by
      have h : (0 : ℝ) ≤ i.val := by positivity
      linarith)

lemma integral_laguerre_inverseSum_eq_gammaProduct {n : ℕ} {a : ℝ} (ha : 1 < a) :
    (∫ x in laguerreDomain (n+1), (∑ i, (x i)⁻¹) * laguerreDensity (n+1) a x) =
      gammaSchurProduct (inverseExponents n a) := by
  apply integral_gamma_determinant_schur (inverseExponents_pos ha)
    (inverseExponents_strictMono n a).injective _ (integrableOn_laguerre_inverseSum ha)
  intro x hx
  rw [inverseExponents_determinant a hx.2, laguerre_evaluation_determinant a hx.2]
  rw [mul_comm _ (∑ i, (x i : ℂ)⁻¹), mul_assoc, vandermonde_schur_density]
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_inv]



lemma orderedPairProduct_cons {α M : Type*} [CommMonoid M] (k : α → α → M)
    {n : ℕ} (x : α) (r : Fin n → α) :
    (∏ i : Fin (n+1), ∏ j ∈ Finset.Ioi i, k ((Fin.cons x r : Fin (n+1) → α) i) ((Fin.cons x r : Fin (n+1) → α) j)) =
      (∏ j, k x (r j)) * ∏ i, ∏ j ∈ Finset.Ioi i, k (r i) (r j) := by
  classical
  have he {m : ℕ} (s : Fin m → α) :
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, k (s i) (s j)) =
        ∏ i : Fin m, ∏ j : Fin m, if i < j then k (s i) (s j) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, he]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    ↓reduceIte, Fin.succ_pos, Fin.not_lt_zero, Fin.succ_lt_succ_iff, one_mul]

lemma gammaSchurProduct_cons {n : ℕ} (r : ℝ) (q : Fin n → ℝ) :
    gammaSchurProduct (Fin.cons r q) =
      Real.Gamma r * (∏ i, (q i - r)/(r + q i)) * gammaSchurProduct q := by
  unfold gammaSchurProduct
  rw [orderedPairProduct_cons (fun r s : ℝ => (s-r)/(r+s))]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

lemma gammaSchurProduct_laguerre (n : ℕ) (a : ℝ) :
    gammaSchurProduct (fun i : Fin n => a+i.val) = laguerreNormalizerProduct n a := by
  unfold gammaSchurProduct laguerreNormalizerProduct
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  congr 1 <;> ring

lemma laguerreNormalizer_succ_product (n : ℕ) {a : ℝ} (ha : 0 < a) :
    laguerreNormalizer (n+1) a = Real.Gamma a *
      (∏ i : Fin n, ((i.val:ℝ)+1)/(2*a+i.val+1)) * laguerreNormalizer n (a+1) := by
  rw [laguerreNormalizer_eq_product _ ha,
    ← gammaSchurProduct_laguerre, laguerreNormalizer_eq_product _ (by linarith : 0<a+1),
    ← gammaSchurProduct_laguerre]
  have hq : (fun i : Fin (n+1) => a+i.val) = Fin.cons a (fun i => (a+1)+i.val) := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simp only [Fin.cons_succ, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring
  rw [hq, gammaSchurProduct_cons]
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  congr 1 <;> ring

lemma gammaSchurProduct_inverse (n : ℕ) {a : ℝ} (ha : 1 < a) :
    gammaSchurProduct (inverseExponents n a) = Real.Gamma (a-1) *
      (∏ i : Fin n, ((i.val:ℝ)+2)/(2*a+i.val)) * laguerreNormalizer n (a+1) := by
  have he : inverseExponents n a = Fin.cons (a-1) (fun i => (a+1)+i.val) := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · simp only [inverseExponents, Fin.cons_succ]
      ring
  rw [he, gammaSchurProduct_cons, gammaSchurProduct_laguerre,
    laguerreNormalizer_eq_product _ (by linarith : 0 < a+1)]
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  congr 1 <;> ring

lemma telescoping_inverse_product (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∏ i : Fin n, ((i.val:ℝ)+2)/(b+i.val)) =
      ((n:ℝ)+1)*(b+n)/b * (∏ i : Fin n, ((i.val:ℝ)+1)/(b+i.val+1)) := by
  induction n with
  | zero => simp [hb.ne']
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [ih]
    have hn : b+(n:ℝ) ≠ 0 := by positivity
    have hn1 : b+(n:ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring

 
end
end CriticalStrip

end OAI
