import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.Determinant
open MvPolynomial

lemma regular_quotient_of_prime {R : Type*} [CommRing R] [IsDomain R]
    {p h : R} (hp : Prime p) (hph : ¬p ∣ h) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {h}) p) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro q hq
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hq
  obtain ⟨c, hc⟩ := hq
  have hpc : p ∣ c := (hp.dvd_or_dvd (show p ∣ h * c by rw [← hc]; exact dvd_mul_right _ _)).resolve_left hph
  obtain ⟨d, rfl⟩ := hpc
  have hr : r = h * d := by
    apply mul_left_cancel₀ hp.ne_zero
    linear_combination hc
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hr]
  exact dvd_mul_right _ _

abbrev Poly := MvPolynomial (Fin 5) ℂ
abbrev Base := MvPolynomial (Fin 4) ℂ
abbrev Coeff := MvPolynomial (Fin 3) ℂ
abbrev K₀ := FractionRing Coeff
abbrev K := RatFunc K₀

def relation : Poly := X 0 * X 3 - X 2 * X 1 - 1
abbrev T := Poly ⧸ Ideal.span {relation}
def π : Poly →ₐ[ℂ] T := Ideal.Quotient.mkₐ ℂ _
def a : T := π (X 0)
def d : T := π (X 1)
def b : T := π (X 2)
def c : T := π (X 3)
def u : T := π (X 4)
def v : T := a ^ 3 * b - a ^ 2 * u ^ 3 - d ^ 2

def baseEmbedding : Base →ₐ[ℂ] K :=
  (IsScalarTower.toAlgHom ℂ (Polynomial K₀) K).comp
    ((Polynomial.mapAlgHom (IsScalarTower.toAlgHom ℂ Coeff K₀)).comp
      (finSuccEquiv ℂ 3).toAlgHom)

lemma baseEmbedding_injective : Function.Injective baseEmbedding :=
  (RatFunc.algebraMap_injective K₀).comp
    ((Polynomial.map_injective _ (IsFractionRing.injective Coeff K₀)).comp
      (finSuccEquiv ℂ 3).injective)

lemma baseEmbedding_X_zero : baseEmbedding (X 0) = RatFunc.X := by
  change algebraMap (Polynomial K₀) K
    (Polynomial.map (algebraMap Coeff K₀) ((finSuccEquiv ℂ 3) (X 0))) = _
  rw [finSuccEquiv_X_zero, Polynomial.map_X, RatFunc.algebraMap_X]

lemma baseEmbedding_X_succ (i : Fin 3) :
    baseEmbedding (X i.succ) = RatFunc.C (algebraMap Coeff K₀ (X i)) := by
  change algebraMap (Polynomial K₀) K
    (Polynomial.map (algebraMap Coeff K₀) ((finSuccEquiv ℂ 3) (X i.succ))) = _
  rw [finSuccEquiv_X_succ, Polynomial.map_C, RatFunc.algebraMap_C]

def targetValues : Fin 5 → K := ![baseEmbedding (X 1), baseEmbedding (X 2),
  baseEmbedding (X 3), (1 + baseEmbedding (X 3) * baseEmbedding (X 2)) /
    baseEmbedding (X 1), baseEmbedding (X 0)]

def eval : Poly →ₐ[ℂ] K := aeval targetValues

lemma a_field_nonzero : baseEmbedding (X 1) ≠ 0 := by
  intro h
  have hz := baseEmbedding_injective (h.trans (map_zero _).symm)
  exact X_ne_zero (1 : Fin 4) hz

lemma eval_relation : eval relation = 0 := by
  simp only [eval, relation, map_sub, map_mul, map_one, aeval_X]
  simp only [targetValues, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp [a_field_nonzero]
  ring

def embedding : T →ₐ[ℂ] K := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul, eval_relation, zero_mul])

@[simp] lemma embedding_π (r : Poly) : embedding (π r) = eval r :=
  Ideal.Quotient.lift_mk _ _ _

lemma determinant : a*c - b*d = 1 := by
  have h : π relation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [relation, map_sub, map_mul, map_one, a, b, c, d, sub_eq_zero] using h

lemma a_regular : IsLeftRegular a := by
  apply regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun _ : Fin 5 => (0 : ℂ))) h
  simp [relation] at he

def baseValues : Fin 4 → T := ![u,a,d,b]
def baseMap : Base →ₐ[ℂ] T := aeval baseValues

lemma embedding_baseMap (r : Base) : embedding (baseMap r) = baseEmbedding r := by
  have he : embedding.comp baseMap = baseEmbedding := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [baseMap, baseValues, u, a, d, b, embedding_π, eval, targetValues]
  exact DFunLike.congr_fun he r

lemma baseMap_injective : Function.Injective baseMap := by
  intro r s hrs
  apply baseEmbedding_injective
  rw [← embedding_baseMap, ← embedding_baseMap, hrs]

lemma clears_generator (i : Fin 5) :
    ∃ n : ℕ, ∃ f : Base, a^n * π (X i) = baseMap f := by
  fin_cases i
  · exact ⟨0, X 1, by simp [baseMap, baseValues, a]⟩
  · exact ⟨0, X 2, by simp [baseMap, baseValues, d]⟩
  · exact ⟨0, X 3, by simp [baseMap, baseValues, b]⟩
  · refine ⟨1, 1 + X 3 * X 2, ?_⟩
    simp only [pow_one, map_add, map_one, map_mul, baseMap, aeval_X]
    change a*c = 1+b*d
    linear_combination determinant
  · exact ⟨0, X 0, by simp [baseMap, baseValues, u]⟩

lemma clears (r : T) : ∃ n : ℕ, ∃ f : Base, a^n * r = baseMap f := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {relation}) r
  change ∃ n : ℕ, ∃ f : Base, a^n * π r = baseMap f
  induction r using MvPolynomial.induction_on with
  | C z => refine ⟨0, C z, ?_⟩; simp [baseMap, π]
  | add r s hr hs =>
    obtain ⟨n, f, hf⟩ := hr
    obtain ⟨m, g, hg⟩ := hs
    refine ⟨n+m, X 1 ^ m * f + X 1 ^ n * g, ?_⟩
    simp only [map_add, map_mul, map_pow]
    have hb : baseMap (X 1) = a := by simp [baseMap, baseValues]
    rw [hb, ← hf, ← hg, pow_add]
    ring
  | mul_X r i hr =>
    obtain ⟨n, f, hf⟩ := hr
    obtain ⟨m, g, hg⟩ := clears_generator i
    refine ⟨n+m, f*g, ?_⟩
    rw [map_mul, map_mul, ← hf, ← hg, pow_add]
    ring

lemma embedding_injective : Function.Injective embedding := by
  apply (injective_iff_map_eq_zero embedding).mpr
  intro r hr
  obtain ⟨n, f, hf⟩ := clears r
  have h : baseEmbedding f = 0 := by
    rw [← embedding_baseMap, ← hf, map_mul, hr, mul_zero]
  have hfzero : f = 0 := baseEmbedding_injective (h.trans (map_zero _).symm)
  rw [hfzero, map_zero] at hf
  exact isLeftRegular_iff_right_eq_zero_of_mul.mp (a_regular.pow n) r hf

instance : IsDomain T := Function.Injective.isDomain embedding embedding_injective

end ComplexCancellation.Determinant

end

end OAI
