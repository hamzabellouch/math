import OAI.Probability.SwitchChain.SliceCoefficientAlgebra
import OAI.Probability.SwitchChain.GramComparison

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis
open SliceCoefficients

variable {V E : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Coeff (V : Type*) [Fintype V] := EuclideanSpace ℝ (V × V)

def ofMatrix (c : V → V → ℝ) : Coeff V :=
  WithLp.toLp 2 (fun p => c p.1 p.2)

include sectionDecidableEqV in
@[simp] theorem ofMatrix_apply (c : V → V → ℝ) (i j : V) :
    ofMatrix c (i,j) = c i j := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

def synthesis (z : V → V → E) : Coeff V →ₗ[ℝ] E where
  toFun c := ∑ i, ∑ j, c (i,j) • z i j
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [mul_smul, Finset.smul_sum]

include sectionDecidableEqV in
@[simp] theorem synthesis_ofMatrix (z : V → V → E) (c : V → V → ℝ) :
    synthesis z (ofMatrix c) = ∑ i, ∑ j, c i j • z i j := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

def symMatrix (c : Coeff V) (i j : V) : ℝ :=
  if i = j then 0 else (c (i,j) + c (j,i)) / 2

@[simp] theorem symMatrix_diag (c : Coeff V) (i : V) : symMatrix c i i = 0 := by
  simp [symMatrix]

theorem symMatrix_symmetric (c : Coeff V) (i j : V) :
    symMatrix c i j = symMatrix c j i := by simp [symMatrix, eq_comm, add_comm]

theorem synthesis_symMatrix (z : V → V → E)
    (hzsym : ∀ i j, z i j = z j i) (hzdiag : ∀ i, z i i = 0)
    (c : Coeff V) : synthesis z (ofMatrix (symMatrix c)) = synthesis z c := by
  have hterm (i j : V) : symMatrix c i j • z i j =
      (1 / 2 : ℝ) • (c (i,j) • z i j + c (j,i) • z i j) := by
    by_cases hij : i = j
    · subst j; simp [hzdiag]
    · simp only [symMatrix, hij, ite_false, ← add_smul, ← mul_smul]
      congr 1
      ring
  have htranspose : (∑ i, ∑ j, c (j,i) • z i j) = ∑ i, ∑ j, c (i,j) • z i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hzsym]
  rw [synthesis_ofMatrix]
  simp_rw [hterm, ← Finset.smul_sum, Finset.sum_add_distrib]
  rw [htranspose, smul_add, ← add_smul]
  norm_num
  rfl

theorem synthesis_constant (z : V → V → E)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (a : ℝ) : synthesis z (ofMatrix (constantPair a)) = 0 := by
  have hterm (i j : V) : constantPair a i j • z i j = a • z i j := by
    by_cases hij : i = j
    · subst j; simp [hzdiag]
    · simp [constantPair, hij]
  rw [synthesis_ofMatrix]
  simp_rw [hterm, ← Finset.smul_sum]
  rw [hztotal, smul_zero]

include sectionDecidableEqV in
theorem ofMatrix_inner (c d : V → V → ℝ) :
    ⟪ofMatrix c, ofMatrix d⟫ = ∑ i, ∑ j, c i j * d i j := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fintype.sum_prod_type, ofMatrix, mul_comm]

theorem exists_synthesis_decomposition (hcard : 3 ≤ Fintype.card V)
    (z : V → V → E) (hzsym : ∀ i j, z i j = z j i)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (c : Coeff V) :
    ∃ u : V → ℝ, ∃ v : V → V → ℝ,
      (∑ i, u i) = 0 ∧ (∀ i, rowSum v i = 0) ∧
      (∀ i j, v i j = v j i) ∧ (∀ i, v i i = 0) ∧
      synthesis z c = synthesis z (ofMatrix (linearPair u)) + synthesis z (ofMatrix v) ∧
      ⟪ofMatrix (linearPair u), ofMatrix v⟫ = 0 := by
  obtain ⟨a,u,v,hu,hvrow,hvsym,hvdiag,hdecomp⟩ :=
    exists_coefficient_decomposition hcard (symMatrix c)
      (symMatrix_symmetric c) (symMatrix_diag c)
  refine ⟨u,v,hu,hvrow,hvsym,hvdiag,?_,?_⟩
  · rw [← synthesis_symMatrix z hzsym hzdiag c]
    have heq : ofMatrix (symMatrix c) =
        ofMatrix (constantPair a) + ofMatrix (linearPair u) + ofMatrix v := by
      ext p
      exact hdecomp p.1 p.2
    rw [heq, map_add, map_add, synthesis_constant z hzdiag hztotal, zero_add]
  · rw [ofMatrix_inner]
    exact linearPair_orthogonal_rowZero u v hvsym hvdiag hvrow

variable [sectionFiniteDimensionalℝE : FiniteDimensional ℝ E]

include sectionFiniteDimensionalℝE in
theorem synthesis_single (z : V → V → E) (i j : V) :
    synthesis z (EuclideanSpace.single (i,j) 1) = z i j := by
  have retainedsectionFiniteDimensionalℝE := sectionFiniteDimensionalℝE
  simp [synthesis, ite_and]

theorem adjoint_synthesis_apply (z : V → V → E) (x : E) (i j : V) :
    LinearMap.adjoint (synthesis z) x (i,j) = ⟪z i j,x⟫ := by
  have h := (synthesis z).adjoint_inner_right (EuclideanSpace.single (i,j) 1) x
  simpa [synthesis_single, EuclideanSpace.inner_single_left] using h

theorem gram_synthesis_apply (z : V → V → E) (c : Coeff V) (i j : V) :
    LinearMap.adjoint (synthesis z) (synthesis z c) (i,j) =
      ∑ k, ∑ l, c (k,l) * ⟪z i j,z k l⟫ := by
  rw [adjoint_synthesis_apply]
  simp [synthesis, inner_sum, inner_smul_right]

theorem comparison_of_scalar_actions (hcard : 3 ≤ Fintype.card V)
    (z : V → V → E) (hzsym : ∀ i j, z i j = z j i)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric) (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (μ₁ μ₂ lam₁ lam₂ : ℝ) (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂)
    (hbound₁ : μ₁ ≤ lam₁) (hbound₂ : μ₂ ≤ lam₂)
    (hgram₁ : ∀ u : V → ℝ, (∑ i, u i) = 0 →
      LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix (linearPair u))) =
        μ₁ • ofMatrix (linearPair u))
    (hgram₂ : ∀ v : V → V → ℝ, (∀ i, rowSum v i = 0) →
      (∀ i j, v i j = v j i) → (∀ i, v i i = 0) →
      LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix v)) = μ₂ • ofMatrix v)
    (himage₁ : ∀ u : V → ℝ, (∑ i, u i) = 0 →
      G (synthesis z (ofMatrix (linearPair u))) =
        lam₁ • synthesis z (ofMatrix (linearPair u)))
    (himage₂ : ∀ v : V → V → ℝ, (∀ i, rowSum v i = 0) →
      (∀ i j, v i j = v j i) → (∀ i, v i i = 0) →
      G (synthesis z (ofMatrix v)) = lam₂ • synthesis z (ofMatrix v))
    (x : E) : ⟪x, synthesis z (LinearMap.adjoint (synthesis z) x)⟫ ≤ ⟪x, G x⟫ := by
  apply Analytic.gram_comparison_of_two_blocks (synthesis z) G hG hpos
    μ₁ μ₂ lam₁ lam₂ hμ₁ hμ₂ hbound₁ hbound₂
  intro c
  obtain ⟨u,v,hu,hvrow,hvsym,hvdiag,hc,huv⟩ :=
    exists_synthesis_decomposition hcard z hzsym hzdiag hztotal c
  exact ⟨ofMatrix (linearPair u),ofMatrix v,hc,huv,
    hgram₁ u hu,hgram₂ v hvrow hvsym hvdiag,
    himage₁ u hu,himage₂ v hvrow hvsym hvdiag⟩

end Problem315.SliceSynthesis

end

end OAI
