import OAI.AlgebraicGeometry.StableCoordinate.ZeroFiber

namespace OAI

/-!
# Specializing the five-variable presentation at p = 0

This module proves, by explicit algebra maps, that specializing the hypersurface
presentation before or after imposing its defining equation gives the same
coordinate algebra.  No field, reducedness, or geometric assumptions are used.
-/

noncomputable section
namespace StableCoordinate.ZeroFiber
open MvPolynomial

variable (K : Type*) [CommRing K]

abbrev Five := MvPolynomial (Fin 5) K

def sourceX : Five K := X 1 ^ 2 - X 2 ^ 2 + X 0 * X 3

def sourceH : Five K :=
  sourceX K ^ 2 * X 3 - (1 + 2 * X 1 * sourceX K) * X 4 - X 0 * X 4 ^ 2 - X 2

def sourceIdeal : Ideal (Five K) := Ideal.span {sourceH K}
abbrev Hypersurface := Five K ⧸ sourceIdeal K

def hypersurfaceMk : Five K →ₐ[K] Hypersurface K := Ideal.Quotient.mkₐ K _

def parameterIdeal : Ideal (Hypersurface K) := Ideal.span {hypersurfaceMk K (X 0)}
abbrev SourceRing := Hypersurface K ⧸ parameterIdeal K

def sourceMk : Five K →ₐ[K] SourceRing K :=
  (Ideal.Quotient.mkₐ K (parameterIdeal K)).comp (hypersurfaceMk K)

lemma sourceMk_parameter : sourceMk K (X 0) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

lemma sourceMk_relation : sourceMk K (sourceH K) = 0 := by
  have h : hypersurfaceMk K (sourceH K) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)
  change Ideal.Quotient.mkₐ K (parameterIdeal K) (hypersurfaceMk K (sourceH K)) = 0
  rw [h, map_zero]

def specialize : Five K →ₐ[K] Ring K :=
  aeval ![0, qmk K (X 0), qmk K (X 1), qmk K (X 2), qmk K (X 3)]

lemma specialize_relation : specialize K (sourceH K) = 0 := by
  have h := qmk_relation K
  simpa [specialize, sourceH, sourceX, relation, squareDifference, map_ofNat] using h

lemma specialize_vanishes : ∀ a ∈ sourceIdeal K, specialize K a = 0 := by
  intro a ha
  have h : sourceIdeal K ≤ RingHom.ker (specialize K).toRingHom := by
    rw [sourceIdeal, Ideal.span_le]
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact specialize_relation K
  exact h ha

def specializeHypersurface : Hypersurface K →ₐ[K] Ring K :=
  Ideal.Quotient.liftₐ _ (specialize K) (specialize_vanishes K)

@[simp] lemma specializeHypersurface_mk (a : Five K) :
    specializeHypersurface K (hypersurfaceMk K a) = specialize K a := rfl

lemma specializeHypersurface_vanishes :
    ∀ a ∈ parameterIdeal K, specializeHypersurface K a = 0 := by
  intro a ha
  have h : parameterIdeal K ≤ RingHom.ker (specializeHypersurface K).toRingHom := by
    rw [parameterIdeal, Ideal.span_le]
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    simp [specialize]
  exact h ha

def specializeQuotient : SourceRing K →ₐ[K] Ring K :=
  Ideal.Quotient.liftₐ _ (specializeHypersurface K) (specializeHypersurface_vanishes K)

@[simp] lemma specializeQuotient_mk (a : Five K) :
    specializeQuotient K (sourceMk K a) = specialize K a := rfl

def includeVariables : Four K →ₐ[K] SourceRing K :=
  aeval ![sourceMk K (X 1), sourceMk K (X 2), sourceMk K (X 3), sourceMk K (X 4)]

lemma includeVariables_relation : includeVariables K (relation K) = 0 := by
  have h := sourceMk_relation K
  simp only [sourceH, sourceX, map_sub, map_add, map_mul, map_pow, map_ofNat,
    map_one] at h
  rw [sourceMk_parameter] at h
  simp only [includeVariables, relation, squareDifference, map_sub, map_add, map_mul,
    map_pow, map_ofNat, map_one, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination h

lemma includeVariables_vanishes : ∀ a ∈ relationIdeal K, includeVariables K a = 0 := by
  intro a ha
  have h : relationIdeal K ≤ RingHom.ker (includeVariables K).toRingHom := by
    rw [relationIdeal, Ideal.span_le]
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact includeVariables_relation K
  exact h ha

def includeQuotient : Ring K →ₐ[K] SourceRing K :=
  Ideal.Quotient.liftₐ _ (includeVariables K) (includeVariables_vanishes K)

@[simp] lemma includeQuotient_mk (a : Four K) :
    includeQuotient K (qmk K a) = includeVariables K a := rfl

lemma specialize_include :
    (specializeQuotient K).comp (includeQuotient K) = AlgHom.id K (Ring K) := by
  apply Ideal.Quotient.algHom_ext
  ext i : 1
  change specializeQuotient K (includeQuotient K (qmk K (X i))) = qmk K (X i)
  rw [includeQuotient_mk]
  fin_cases i <;> simp [includeVariables, specialize]

lemma include_specialize :
    (includeQuotient K).comp (specializeQuotient K) = AlgHom.id K (SourceRing K) := by
  apply Ideal.Quotient.algHom_ext
  apply Ideal.Quotient.algHom_ext
  ext i : 1
  change includeQuotient K (specializeQuotient K (sourceMk K (X i))) = sourceMk K (X i)
  rw [specializeQuotient_mk]
  fin_cases i <;> simp [specialize, includeVariables, sourceMk_parameter]

/-- Specialize `p` to zero in the hypersurface presentation. -/
def specializationEquiv : SourceRing K ≃ₐ[K] Ring K :=
  AlgEquiv.ofAlgHom (specializeQuotient K) (includeQuotient K)
    (specialize_include K) (include_specialize K)

/-- The zero fiber of the five-variable hypersurface presentation is a
three-variable polynomial algebra. -/
def sourceZeroFiberEquiv : SourceRing K ≃ₐ[K] Three K :=
  (specializationEquiv K).trans (presentationEquiv K)

end StableCoordinate.ZeroFiber

end

end OAI
