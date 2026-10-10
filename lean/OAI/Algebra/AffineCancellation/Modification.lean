import OAI.Algebra.AffineCancellation.Clearing
import OAI.Algebra.AffineCancellation.DeterminantRigidity

namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] [IsDomain R] (v : R)

abbrev P := MvPolynomial (Fin 2) R
def rel : P R := X 0 ^ 2 * X 1 - C v
abbrev T := P R ⧸ Ideal.span {rel R v}
def π : P R →ₐ[R] T R v := Ideal.Quotient.mkₐ R _
def τ : T R v := π R v (X 0)
def V : T R v := π R v (X 1)

omit [IsDomain R] in
lemma equation : τ R v ^ 2 * V R v = algebraMap R (T R v) v := by
  have h : π R v (rel R v) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  apply sub_eq_zero.mp
  simpa only [rel,map_sub,map_mul,map_pow,τ,V,AlgHom.commutes, MvPolynomial.C_eq_algebraMap] using h

abbrev F := FractionRing R
abbrev K := RatFunc (F R)
def baseEmbedding : Polynomial R →ₐ[R] K R :=
  (IsScalarTower.toAlgHom R (Polynomial (F R)) (K R)).comp
    (Polynomial.mapAlgHom (IsScalarTower.toAlgHom R R (F R)))

lemma baseEmbedding_injective : Function.Injective (baseEmbedding R) :=
  (RatFunc.algebraMap_injective (F R)).comp
    (Polynomial.map_injective _ (IsFractionRing.injective R (F R)))

lemma baseEmbedding_X : baseEmbedding R Polynomial.X = RatFunc.X := by
  change algebraMap (Polynomial (F R)) (K R) (Polynomial.map (algebraMap R (F R)) Polynomial.X) = _
  rw [Polynomial.map_X,RatFunc.algebraMap_X]

lemma X_nonzero : (RatFunc.X : K R) ≠ 0 := RatFunc.X_ne_zero

def values : Fin 2 → K R := ![RatFunc.X, algebraMap R (K R) v / RatFunc.X^2]
def eval : P R →ₐ[R] K R := aeval (values R v)
lemma eval_rel : eval R v (rel R v) = 0 := by
  simp only [rel,eval,map_sub,map_mul,map_pow,aeval_X,aeval_C,values,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp [X_nonzero R]
  ring

def embedding : T R v →ₐ[R] K R := Ideal.Quotient.liftₐ _ (eval R v) (by
  intro r hr
  obtain ⟨s,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_rel,zero_mul])

@[simp] lemma embedding_π (r : P R) : embedding R v (π R v r) = eval R v r :=
  Ideal.Quotient.lift_mk _ _ _

def baseMap : Polynomial R →ₐ[R] T R v := Polynomial.aeval (τ R v)
omit [IsDomain R] in
lemma baseMap_X : baseMap R v Polynomial.X = τ R v := Polynomial.aeval_X _

lemma embedding_baseMap : (embedding R v).comp (baseMap R v) = baseEmbedding R := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply,baseMap_X,baseEmbedding_X,τ,embedding_π,eval,aeval_X]
  rfl

lemma τ_regular (hv : v ≠ 0) : IsLeftRegular (τ R v) := by
  apply Determinant.regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun _ : Fin 2 => (0 : R))) h
  simp [rel,hv] at he

omit [IsDomain R] in
lemma clears (r : T R v) : r ∈ Clearing.subalgebra (baseMap R v) Polynomial.X := by
  have ht : Clearing.subalgebra (baseMap R v) Polynomial.X = ⊤ := by
    apply Clearing.top_of_generators (π R v) (Ideal.Quotient.mkₐ_surjective R _) _ _
    intro i
    fin_cases i
    · exact ⟨0,Polynomial.X,by simp [baseMap_X,τ]⟩
    · refine ⟨2,Polynomial.C v,?_⟩
      rw [baseMap_X]
      change τ R v^2 * V R v = _
      simpa only [baseMap,Polynomial.aeval_C] using equation R v
  rw [ht]
  trivial

lemma embedding_injective (hv : v ≠ 0) : Function.Injective (embedding R v) := by
  apply Clearing.injective_of_clearing (embedding R v) (baseMap R v) Polynomial.X
  · rw [embedding_baseMap]; exact baseEmbedding_injective R
  · rw [baseMap_X]; exact τ_regular R v hv
  · exact top_unique (fun r _ => clears R v r)

lemma isDomain (hv : v ≠ 0) : IsDomain (T R v) :=
  Function.Injective.isDomain (embedding R v) (embedding_injective R v hv)

end ComplexCancellation.AffineModification

end

end OAI
