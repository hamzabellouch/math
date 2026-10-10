import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralWordOrthogonality
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! Normalized dihedral word inclusions on actual tracial Hilbert spaces. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The unnormalized algebraic word inclusion. -/
def dihedralWordMap (Q : StarSubalgebra ℂ R) (V : R →ₗ[ℂ] E) (e d s : R)
    (k : ℕ) : Q →ₗ[ℂ] E where
  toFun a := V (e * (s * d) ^ k * (a : R))
  map_add' a b := by
    change V (e * (s * d) ^ k * ((a : R) + (b : R))) = _
    rw [mul_add, map_add]
  map_smul' c a := by
    change V (e * (s * d) ^ k * (c • (a : R))) = _
    rw [mul_smul_comm, map_smul, RingHom.id_apply]

variable (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
  (htr : ∀ a b, τ (a * b) = τ (b * a))
  (V : R →ₗ[ℂ] E) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (P Q : StarSubalgebra ℂ R) (hf : ScalarFree τ P Q)
  (d s e : R) (hd : d ∈ P) (hs : s ∈ Q) (he : e ∈ P)
  (hd0 : τ d = 0) (hs0 : τ s = 0)
  (hdd : d * d = 1) (hss : s * s = 1)
  (hdstar : star d = d) (hsstar : star s = s)
  (hestar : star e = e) (hee : e * e = e)

include hτ htr hinner hf hd hs he hd0 hs0 hdd hss hdstar hsstar hestar hee in
omit [CompleteSpace E] in
/-- The projection and selfadjointness hypotheses turn the tracial sandwich
formula into the actual Hilbert inner products of the word maps. -/
theorem inner_dihedralWordMap (k j : ℕ) (a b : Q) :
    inner ℂ (dihedralWordMap Q V e d s k a) (dihedralWordMap Q V e d s j b) =
      if k = j then τ e * τ (star (a : R) * (b : R)) else 0 := by
  change inner ℂ (V (e * (s * d) ^ k * (a : R)))
    (V (e * (s * d) ^ j * (b : R))) = _
  rw [hinner]
  have heq : star (e * (s * d) ^ k * (a : R)) * (e * (s * d) ^ j * (b : R)) =
      star (a : R) * (d * s) ^ k * e * (s * d) ^ j * (b : R) := by
    simp only [star_mul, star_pow, hdstar, hsstar, hestar]
    calc
      _ = star (a : R) * (d * s) ^ k * (e * e) * (s * d) ^ j * (b : R) := by
        noncomm_ring
      _ = _ := by rw [hee]
  rw [heq]
  exact dihedral_word_pairing τ hτ hf hd hs hd0 hs0 htr hdd hss he a.property b.property k j

/-- The actual normalization factor `t⁻¹ᐟ²`. -/
def dihedralNormalization (t : ℝ) : ℂ := ((Real.sqrt t)⁻¹ : ℝ)

theorem dihedralNormalization_identity {t : ℝ} (ht : 0 < t) :
    star (dihedralNormalization t) * dihedralNormalization t * (t : ℂ) = 1 := by
  have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hn : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * t = (1 : ℝ) := by
    calc
      _ = (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * (Real.sqrt t * Real.sqrt t) :=
        congrArg (fun z : ℝ => (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * z)
          (Real.mul_self_sqrt ht.le).symm
      _ = 1 := by field_simp
  have hstar : star (dihedralNormalization t) = dihedralNormalization t := by
    simp [dihedralNormalization]
  rw [hstar]
  unfold dihedralNormalization
  exact_mod_cast hn

/-- The normalized algebraic word map whose Hilbert extension is isometric. -/
def normalizedDihedralWordMap (t : ℝ) (k : ℕ) : Q →ₗ[ℂ] E :=
  dihedralNormalization t • dihedralWordMap Q V e d s k

variable (VA : Q →ₗ[ℂ] K)
  (hA : ∀ a b : Q, inner ℂ (VA a) (VA b) = τ (star (a : R) * (b : R)))
  (t : ℝ) (ht : 0 < t) (hte : τ e = (t : ℂ))

include hτ htr hinner hf hd hs he hd0 hs0 hdd hss hdstar hsstar hestar hee hA ht hte in
omit [CompleteSpace E] in
theorem inner_normalizedDihedralWordMap (k j : ℕ) (a b : Q) :
    inner ℂ (normalizedDihedralWordMap V Q d s e t k a)
      (normalizedDihedralWordMap V Q d s e t j b) =
      if k = j then inner ℂ (VA a) (VA b) else 0 := by
  change inner ℂ (dihedralNormalization t • dihedralWordMap Q V e d s k a)
    (dihedralNormalization t • dihedralWordMap Q V e d s j b) = _
  rw [inner_smul_left, inner_smul_right,
    inner_dihedralWordMap τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
      hdstar hsstar hestar hee]
  by_cases hkj : k = j
  · simp only [hkj, ↓reduceIte, hte, hA]
    change star (dihedralNormalization t) *
      (dihedralNormalization t * ((t : ℂ) * τ (star (a : R) * (b : R)))) = _
    calc
      _ = (star (dihedralNormalization t) * dihedralNormalization t * (t : ℂ)) *
          τ (star (a : R) * (b : R)) := by ring
      _ = _ := by rw [dihedralNormalization_identity ht, one_mul]
  · simp only [hkj, ↓reduceIte, mul_zero]

include hτ htr hinner hf hd hs he hd0 hs0 hdd hss hdstar hsstar hestar hee hA ht hte in
omit [CompleteSpace E] in
theorem norm_normalizedDihedralWordMap (k : ℕ) (a : Q) :
    ‖normalizedDihedralWordMap V Q d s e t k a‖ = ‖VA a‖ := by
  have hn : ‖normalizedDihedralWordMap V Q d s e t k a‖ ^ 2 = ‖VA a‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      inner_normalizedDihedralWordMap τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
        hdstar hsstar hestar hee VA hA t ht hte]
    simp
  nlinarith [norm_nonneg (normalizedDihedralWordMap V Q d s e t k a), norm_nonneg (VA a)]

/-- Isometric inclusion of the completed tracial base space as the `k`-th
actual dihedral word space. -/
def dihedralWordIsometry (hdense : DenseRange VA) (k : ℕ) : K →ₗᵢ[ℂ] E :=
  (normalizedDihedralWordMap V Q d s e t k).extendOfIsometry (e := VA) hdense
    (norm_normalizedDihedralWordMap τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
      hdstar hsstar hestar hee VA hA t ht hte k)

@[simp] theorem dihedralWordIsometry_apply (hdense : DenseRange VA) (k : ℕ) (a : Q) :
    dihedralWordIsometry τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
      hdstar hsstar hestar hee VA hA t ht hte hdense k (VA a) =
      dihedralNormalization t • V (e * (s * d) ^ k * (a : R)) := by
  exact LinearMap.extendOfIsometry_eq _ hdense
    (norm_normalizedDihedralWordMap τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
      hdstar hsstar hestar hee VA hA t ht hte k) a

/-- Distinct actual dihedral word inclusions have orthogonal ranges on the
completed tracial Hilbert space. -/
theorem inner_dihedralWordIsometry (hdense : DenseRange VA) (k j : ℕ) (x y : K) :
    inner ℂ
      (dihedralWordIsometry τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
        hdstar hsstar hestar hee VA hA t ht hte hdense k x)
      (dihedralWordIsometry τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
        hdstar hsstar hestar hee VA hA t ht hte hdense j y) =
      if k = j then inner ℂ x y else 0 := by
  refine hdense.induction_on₂ (isClosed_eq (by fun_prop) ?_) ?_ x y
  · by_cases hkj : k = j <;> simp only [hkj, ↓reduceIte] <;> fun_prop
  intro a b
  rw [dihedralWordIsometry_apply, dihedralWordIsometry_apply]
  exact inner_normalizedDihedralWordMap τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
    hdstar hsstar hestar hee VA hA t ht hte k j a b

end KadisonSimilarity

end

end OAI
