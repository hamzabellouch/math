import OAI.RepresentationTheory.FiniteUnitary.Characters
import OAI.RepresentationTheory.FiniteUnitary.Sampling

namespace OAI

namespace CubeShuffle.FiniteFourier
open scoped BigOperators ComplexConjugate Classical
open UnitaryFinite

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
variable (V : ι → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
variable (hρ : ∀ i, IsUnitary (ρ i))
variable (hneq : ∀ i j, i≠j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
  (hcard : Nat.card (ConjClasses G)≤Fintype.card ι)

abbrev CoefficientIndex := Σ i,Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i))

noncomputable def coefficientFamily (a : CoefficientIndex V) : EuclideanSpace ℂ G :=
  regularCoefficient (ρ a.1) (stdOrthonormalBasis ℂ (V a.1) a.2.1) (stdOrthonormalBasis ℂ (V a.1) a.2.2)

omit [Fintype ι] in
include hρ hneq in
lemma coefficientFamily_orthonormal : Orthonormal ℂ (coefficientFamily V ρ) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,a,b⟩ ⟨j,c,d⟩
  dsimp only [coefficientFamily]
  by_cases hij : i=j
  · subst j
    rw [regularCoefficient_inner _ (hρ i)]
    simp only [(stdOrthonormalBasis ℂ (V i)).inner_eq_ite]
    by_cases hac : a=c <;> by_cases hbd : b=d <;> simp [hac,hbd,eq_comm]
  · rw [regularCoefficient_cross _ _ (hρ j) (hneq j i (Ne.symm hij))]
    rw [ite_eq_right (by intro h; exact hij (congrArg Sigma.fst h))]

include ρ hneq hcard in
lemma coefficientIndex_card : Fintype.card (CoefficientIndex V)=Fintype.card G := by
  simp only [CoefficientIndex,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,←pow_two]
  exact FiniteCharacters.sum_dimension_sq V ρ hneq hcard

noncomputable def coefficientBasis : OrthonormalBasis (CoefficientIndex V) ℂ (EuclideanSpace ℂ G) :=
  OrthonormalBasis.mk (coefficientFamily_orthonormal V ρ hρ hneq)
    (by rw [(coefficientFamily_orthonormal V ρ hρ hneq).linearIndependent.span_eq_top_of_card_eq_finrank'
          (by rw [coefficientIndex_card V ρ hneq hcard,finrank_euclideanSpace])])

lemma coefficientBasis_apply (a : CoefficientIndex V) :
    coefficientBasis V ρ hρ hneq hcard a=coefficientFamily V ρ a := congrFun (OrthonormalBasis.coe_mk _ _) a

include hρ hneq hcard in
/-- Finite-group Plancherel, produced from the actual complete irreducible
coefficient basis rather than postulated as a Fourier hypothesis. -/
theorem parseval (f : EuclideanSpace ℂ G) :
    ∑ a : CoefficientIndex V, ‖inner ℂ (coefficientFamily V ρ a) f‖^2=‖f‖^2 := by
  simpa only [coefficientBasis_apply] using
    (coefficientBasis V ρ hρ hneq hcard).sum_sq_norm_inner_right f

end CubeShuffle.FiniteFourier
namespace CubeShuffle.FiniteFourier
open scoped BigOperators ComplexConjugate Classical
open UnitaryFinite

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
variable (V : ι → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
variable (hρ : ∀ i, IsUnitary (ρ i))
variable (hneq : ∀ i j, i≠j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
  (hcard : Nat.card (ConjClasses G)≤Fintype.card ι)

noncomputable def realVector (p : G → ℝ) : EuclideanSpace ℂ G := WithLp.toLp 2 (fun g => (p g:ℂ))

omit [Fintype ι] [∀ i, Representation.IsIrreducible (ρ i)] in
lemma coefficient_realVector (p : G → ℝ) (a : CoefficientIndex V) :
    inner ℂ (coefficientFamily V ρ a) (realVector p)=
      (Real.sqrt ((Module.finrank ℂ (V a.1):ℝ)/(Fintype.card G:ℝ)):ℂ)*
      inner ℂ (stdOrthonormalBasis ℂ (V a.1) a.2.2)
        (weightedOperator (ρ a.1) p (stdOrthonormalBasis ℂ (V a.1) a.2.1)) := by
  simp only [PiLp.inner_apply,coefficientFamily,regularCoefficient_apply,realVector,
    RCLike.inner_apply,map_mul,Complex.conj_ofReal,inner_conj_symm,
    weightedOperator,sum_apply,smul_apply,
    continuousRepresentation_apply,inner_sum,inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  ring

omit [Fintype ι] [∀ i, Representation.IsIrreducible (ρ i)] in
lemma coefficient_realVector_sq (p : G → ℝ) (a : CoefficientIndex V) :
    ‖inner ℂ (coefficientFamily V ρ a) (realVector p)‖^2=
      ((Module.finrank ℂ (V a.1):ℝ)/(Fintype.card G:ℝ))*
      ‖inner ℂ (stdOrthonormalBasis ℂ (V a.1) a.2.2)
        (weightedOperator (ρ a.1) p (stdOrthonormalBasis ℂ (V a.1) a.2.1))‖^2 := by
  rw [coefficient_realVector,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

include hρ hneq hcard in
lemma parseval_operator (p : G → ℝ) :
    (Fintype.card G:ℝ)*‖realVector p‖^2=
      ∑ i,(Module.finrank ℂ (V i):ℝ)*∑ a : Fin (Module.finrank ℂ (V i)),
        ‖weightedOperator (ρ i) p (stdOrthonormalBasis ℂ (V i) a)‖^2 := by
  rw [←parseval V ρ hρ hneq hcard (realVector p)]
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,coefficient_realVector_sq]
  have hN : (Fintype.card G:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he (a : Fin (Module.finrank ℂ (V i))) :
      (∑ b : Fin (Module.finrank ℂ (V i)),
        (Module.finrank ℂ (V i):ℝ)/(Fintype.card G:ℝ)*
          ‖inner ℂ (stdOrthonormalBasis ℂ (V i) b)
            (weightedOperator (ρ i) p (stdOrthonormalBasis ℂ (V i) a))‖^2)=
        (Module.finrank ℂ (V i):ℝ)/(Fintype.card G:ℝ)*
          ‖weightedOperator (ρ i) p (stdOrthonormalBasis ℂ (V i) a)‖^2 := by
    rw [←Finset.mul_sum,(stdOrthonormalBasis ℂ (V i)).sum_sq_norm_inner_right]
  simp_rw [he]
  rw [←Finset.mul_sum]
  field_simp

include hρ hneq hcard in
lemma realVector_bound (p : G → ℝ) :
    (Fintype.card G:ℝ)*‖realVector p‖^2≤
      ∑ i,(Module.finrank ℂ (V i):ℝ)^2*‖weightedOperator (ρ i) p‖^2 := by
  rw [parseval_operator V ρ hρ hneq hcard]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ (Module.finrank ℂ (V i):ℝ)*∑ _a : Fin (Module.finrank ℂ (V i)),‖weightedOperator (ρ i) p‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro a _
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [(stdOrthonormalBasis ℂ (V i)).norm_eq_one,mul_one] using
        (weightedOperator (ρ i) p).le_opNorm (stdOrthonormalBasis ℂ (V i) a)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

include hρ hneq hcard in
/-- The exact full-group Fourier upper bound, with no marginal replacement. -/
theorem l1_fourier_bound (p : G → ℝ) :
    (∑ g,|p g|)^2≤∑ i,(Module.finrank ℂ (V i):ℝ)^2*‖weightedOperator (ρ i) p‖^2 := by
  apply le_trans _ (realVector_bound V ρ hρ hneq hcard p)
  have he : ‖realVector p‖^2=∑ g,|p g|^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [realVector,PiLp.toLp_apply,Complex.norm_real,Real.norm_eq_abs]
  rw [he]
  simpa only [Finset.card_univ] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun g => |p g|)

end CubeShuffle.FiniteFourier

end OAI
