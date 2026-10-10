import Mathlib
import OAI.NumberTheory.PrimePackets.CharacterPairs
import OAI.NumberTheory.PrimePackets.RadialIntegrals

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
namespace PrimeDegreePackets

lemma integralBasis_discriminant_index {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) :
    ∃ z : ℤ, z ≠ 0 ∧ Algebra.discr ℚ b = (z:ℚ)^2 * (NumberField.discr K : ℚ) := by
  classical
  let e := (NumberField.integralBasis K).indexEquiv b
  let b₀ := (NumberField.integralBasis K).reindex e
  let P := b₀.toMatrix b
  have hP : ∀ i j, IsIntegral ℤ (P i j) := by
    intro i j
    change IsIntegral ℤ ((NumberField.integralBasis K).repr (b j) (e.symm i))
    let x : 𝓞 K := ⟨b j,hb j⟩
    have hx : b j = algebraMap (𝓞 K) K x := rfl
    rw [hx,NumberField.integralBasis_repr_apply]
    exact isIntegral_algebraMap
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.det hP)
  have hz0 : z ≠ 0 := by
    intro h
    have hP0 : P.det = 0 := by rw [← hz,h,_root_.map_zero]
    have hh : P.det * (b.toMatrix b₀).det = 1 := by
      rw [← Matrix.det_mul]
      simp [P]
    rw [hP0,zero_mul] at hh
    exact zero_ne_one hh
  refine ⟨z,hz0,?_⟩
  rw [← b₀.toMatrix_map_vecMul b,Algebra.discr_of_matrix_vecMul]
  change P.det ^ 2 * Algebra.discr ℚ b₀ = _
  rw [← hz]
  congr 1
  simpa only [b₀,Basis.coe_reindex,Algebra.discr_reindex] using
    (NumberField.coe_discr K).symm

 

theorem abs_discr_le_integral_basis {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) :
    |(NumberField.discr K : ℝ)| ≤ |(Algebra.discr ℚ b : ℝ)| := by
  obtain ⟨z,hz,he⟩ := integralBasis_discriminant_index b hb
  have he' : (Algebra.discr ℚ b : ℝ) = (z:ℝ)^2 * (NumberField.discr K : ℝ) := by
    exact_mod_cast he
  rw [he',abs_mul,abs_pow,even_two.pow_abs]
  have hz1 : (1:ℝ) ≤ (z:ℝ)^2 := by
    have hzi : (1:ℤ) ≤ z^2 := by
      have hh : 0 < z^2 := sq_pos_of_ne_zero hz
      omega
    exact_mod_cast hzi
  nlinarith [abs_nonneg (NumberField.discr K : ℝ)]

lemma norm_det_le_factorial_pow {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) {B : ℝ} (_hB : 0 ≤ B) (hA : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A.det‖ ≤ (Fintype.card I).factorial * B ^ Fintype.card I := by
  classical
  rw [Matrix.det_apply']
  calc
    ‖∑ σ : Equiv.Perm I, (Equiv.Perm.sign σ : ℂ) * ∏ i, A (σ i) i‖
        ≤ ∑ σ : Equiv.Perm I, ‖(Equiv.Perm.sign σ : ℂ) * ∏ i, A (σ i) i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm I, B ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul]
      have hs : ‖(Equiv.Perm.sign σ : ℂ)‖ = 1 := by
        simpa only [Complex.norm_intCast] using (abs_unit_intCast (α := ℝ) (Equiv.Perm.sign σ))
      rw [hs,one_mul,norm_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hA (σ i) i)).trans_eq
        (by simp)
    _ = _ := by simp [Fintype.card_perm]

 

theorem abs_discr_le_integral_basis_height {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {B : ℝ} (hB : 0 ≤ B)
    (hheight : ∀ (σ : K →ₐ[ℚ] ℂ) i, ‖σ (b i)‖ ≤ B) :
    |(NumberField.discr K : ℝ)| ≤
      ((Fintype.card I).factorial * B ^ Fintype.card I)^2 := by
  classical
  let e : I ≃ (K →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq (by
    rw [← finrank_eq_card_basis b,AlgHom.card])
  have he := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ b e
  have he' : |(Algebra.discr ℚ b : ℝ)| =
      ‖(Algebra.embeddingsMatrixReindex ℚ ℂ b e).det‖^2 := by
    have h := congrArg norm he
    simpa only [norm_pow,eq_ratCast,Complex.norm_ratCast] using h
  calc
    |(NumberField.discr K : ℝ)| ≤ |(Algebra.discr ℚ b : ℝ)| := abs_discr_le_integral_basis b hb
    _ = _ := he'
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_factorial_pow _ hB (by
      intro i j
      exact hheight (e j) i)) 2

end PrimeDegreePackets

open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
namespace PrimeDegreePackets

 
def orderedEuclideanMap {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (σ : OrderedEmbeddings n K) : K →ₗ[ℚ] EuclideanSpace ℝ (Fin n) where
  toFun x := toLp 2 (fun i => σ i x)
  map_add' x y := by ext i; exact map_add (σ i) x y
  map_smul' q x := by ext i; exact map_rat_smul (σ i) q x

lemma integralEuclideanBasis_exists {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n)
    (bZ : Basis (Fin n) ℤ (𝓞 K)) :
    ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (∀ i, b i = orderedEuclideanMap σ (bZ i)) ∧
      volume (ZSpan.fundamentalDomain b) =
        ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => σ j (bZ i)
  have hdet : A.det ≠ 0 := by
    intro h
    have H := integralEmbeddingMatrix_det_sq σ hn bZ
    change A.det ^ 2 = _ at H
    rw [h,zero_pow (by norm_num)] at H
    exact NumberField.discr_ne_zero K (by exact_mod_cast H.symm)
  let bR : Basis (Fin n) ℝ (Fin n → ℝ) := (Pi.basisFun ℝ (Fin n)).map
    (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n)) A.transpose
      (by simpa only [Matrix.det_transpose] using isUnit_iff_ne_zero.mpr hdet))
  have hbR (i j : Fin n) : bR i j = σ j (bZ i) := by
    simp [bR,Matrix.toLinearEquiv_apply,Matrix.toLin_apply,Matrix.mulVec,
      dotProduct,Pi.single_apply,A]
    rfl
  let u := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  let b := bR.map u.symm.toLinearEquiv
  refine ⟨b,?_,?_⟩
  · intro i
    ext j
    exact hbR i j
  · have hi : u.toLinearEquiv '' ZSpan.fundamentalDomain b =
        ZSpan.fundamentalDomain bR := by
      rw [ZSpan.map_fundamentalDomain]
      congr 1
    have hp : u ⁻¹' ZSpan.fundamentalDomain bR = ZSpan.fundamentalDomain b := by
      rw [← hi]
      exact Set.preimage_image_eq _ u.injective
    have hm := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
      (ZSpan.fundamentalDomain_measurableSet bR).nullMeasurableSet
    change volume (u ⁻¹' ZSpan.fundamentalDomain bR) = _ at hm
    rw [hp,ZSpan.volume_fundamentalDomain] at hm
    have hd : |(Matrix.of bR).det| = Real.sqrt |(NumberField.discr K : ℝ)| := by
      have he : Matrix.of bR = A := by ext i j; exact hbR i j
      rw [he]
      conv_rhs => rw [← integralEmbeddingMatrix_det_sq σ hn bZ,
        abs_of_nonneg (sq_nonneg _),Real.sqrt_sq_eq_abs]
    simpa only [hd] using hm

lemma integralEuclideanBasis_span {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (bZ : Basis (Fin n) ℤ (𝓞 K))
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ i, b i = orderedEuclideanMap σ (bZ i)) {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Submodule.span ℤ (Set.range b)) :
    ∃ a : 𝓞 K, orderedEuclideanMap σ a = v := by
  obtain ⟨z,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  refine ⟨∑ i, z i • bZ i,?_⟩
  simp only [_root_.map_sum,map_zsmul]
  simp_rw [hb]

 

lemma orderedEuclideanMap_integer_shortest {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (a : 𝓞 K) (ha : a ≠ 0) :
    1 ≤ ‖orderedEuclideanMap σ a‖ := by
  have hnorm : (1:ℝ) ≤ |(Algebra.norm ℚ (a : K) : ℝ)| := by
    rw [← Algebra.coe_norm_int]
    exact_mod_cast Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)
  have hprod : |(Algebra.norm ℚ (a : K) : ℝ)| ≤
      ‖orderedEuclideanMap σ a‖^(d+1) := by
    rw [← prod_abs_orderedEmbeddings σ hn]
    calc
      _ ≤ ∏ _i : Fin (d+1), ‖orderedEuclideanMap σ a‖ := by
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro i _
        exact (Real.norm_eq_abs _).symm ▸ PiLp.norm_apply_le (orderedEuclideanMap σ a) i
      _ = _ := by simp
  by_contra h
  have hh := pow_lt_one₀ (norm_nonneg (orderedEuclideanMap σ a)) (lt_of_not_ge h) (by omega : d+1 ≠ 0)
  linarith

 

theorem totallyReal_small_integral_basis {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) :
    ∃ c : Basis (Fin (d+1)) ℚ K,
      (∀ i, IsIntegral ℤ (c i)) ∧
      ∀ (ρ : K →ₐ[ℚ] ℂ) i, ‖ρ (c i)‖ ≤
        (2 / (1 / (2*(d+1)))^d + d / (2*(d+1))) *
          (Real.sqrt |(NumberField.discr K : ℝ)| + 1) := by
  classical
  let bZ : Basis (Fin (d+1)) ℤ (𝓞 K) := (Module.Free.chooseBasis ℤ (𝓞 K)).reindex
    (Fintype.equivFinOfCardEq (by
      rw [← finrank_eq_card_basis (Module.Free.chooseBasis ℤ (𝓞 K)),NumberField.RingOfIntegers.rank,hn]))
  obtain ⟨b,hb,hvol⟩ := integralEuclideanBasis_exists σ hn bZ
  obtain ⟨c,hc⟩ := linear_covolume_real_basis_in_lattice
    (by simp : finrank ℝ (EuclideanSpace ℝ (Fin (d+1))) = d+1)
    (Real.sqrt |(NumberField.discr K : ℝ)|) (Real.sqrt_nonneg _)
    b hvol.le (by
      intro v hv hv0
      obtain ⟨a,rfl⟩ := integralEuclideanBasis_span σ bZ b hb hv
      apply orderedEuclideanMap_integer_shortest σ hn a
      intro ha
      apply hv0
      simp [ha])
  choose a ha using fun i => integralEuclideanBasis_span σ bZ b hb (hc i).1
  have hli : LinearIndependent ℚ (fun i => (a i : K)) := by
    apply LinearIndependent.of_comp (orderedEuclideanMap σ)
    have he : orderedEuclideanMap σ ∘ (fun i => (a i : K)) = c := funext ha
    rw [he]
    exact c.linearIndependent.restrict_scalars (by
      simpa only [Algebra.smul_def,mul_one] using (FaithfulSMul.algebraMap_injective ℚ ℝ))
  let cQ := basisOfLinearIndependentOfCardEqFinrank hli (by simpa using hn.symm)
  have he (i : Fin (d+1)) : cQ i = (a i : K) := by simp [cQ]
  refine ⟨cQ,fun i => he i ▸ (a i).prop,?_⟩
  intro ρ i
  obtain ⟨j,rfl⟩ := (orderedComplexEmbeddings σ hn).surjective ρ
  rw [he]
  change ‖(σ j (a i) : ℂ)‖ ≤ _
  rw [Complex.norm_real]
  calc
    ‖σ j (a i)‖ ≤ ‖orderedEuclideanMap σ (a i)‖ :=
      PiLp.norm_apply_le (orderedEuclideanMap σ (a i)) j
    _ = ‖c i‖ := congrArg norm (ha i)
    _ ≤ _ := (hc i).2

end PrimeDegreePackets


namespace PrimeDegreePackets
open ThetaConstruction

lemma orderedUnitLogOnto_ker_unit_eq_one_or_neg_one {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (z : (orderedUnitLogOnto σ).ker) :
    z.val.toMul = 1 ∨ z.val.toMul = -1 := by
  have hz : orderedUnitLog σ z.val = 0 := by
    have h := congrArg Subtype.val z.property
    exact h
  have he := congrFun (logFlowWeights_orderedUnitLog σ z.val.toMul) 0
  rw [show Additive.ofMul z.val.toMul = z.val from rfl, hz] at he
  have ha : |σ 0 (z.val.toMul : K)| = 1 := by
    simpa [logFlowWeights, restoredLogCoordinates, Fin.snoc] using he.symm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ha with h | h
  · left
    apply Units.ext
    apply NumberField.RingOfIntegers.coe_injective
    apply (σ 0).injective
    simpa using h
  · right
    apply Units.ext
    apply NumberField.RingOfIntegers.coe_injective
    apply (σ 0).injective
    simpa using h

lemma orderedUnitLogOnto_ker_card_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) : Nat.card (orderedUnitLogOnto σ).ker = 2 := by
  classical
  have hneg : Additive.ofMul (-1 : (𝓞 K)ˣ) ∈ (orderedUnitLogOnto σ).ker := by
    rw [orderedUnitLogOnto_ker]
    exact neg_one_mem_torsion
  let : Finite (orderedUnitLogOnto σ).ker := by
    rw [orderedUnitLogOnto_ker]
    let e : (NumberField.Units.torsion K).toAddSubgroup ≃ NumberField.Units.torsion K :=
      ⟨(fun u => ⟨u.val.toMul,u.property⟩),(fun u => ⟨Additive.ofMul u.val,u.property⟩),
        (fun _ => rfl),(fun _ => rfl)⟩
    exact Finite.of_injective e e.injective
  let : Fintype (orderedUnitLogOnto σ).ker := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.mpr ⟨0, ⟨Additive.ofMul (-1),hneg⟩, ?_, ?_⟩
  · intro h
    have he := congrArg (fun z : (orderedUnitLogOnto σ).ker => (z.val.toMul : K)) h
    norm_num at he
  · ext z
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases orderedUnitLogOnto_ker_unit_eq_one_or_neg_one σ z with h | h
    · left
      exact Subtype.ext (congrArg Additive.ofMul h)
    · right
      exact Subtype.ext (congrArg Additive.ofMul h)

end PrimeDegreePackets


namespace PrimeDegreePackets
open ThetaConstruction

theorem lintegral_arithmeticFlowGaussian_units_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) 
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    (a : K) (t : ℝ) :
    (∫⁻ u in S, ∑' z : (𝓞 K)ˣ, arithmeticFlowGaussian σ ((z:K)*a) t u) =
      2*∫⁻ u, arithmeticFlowGaussian σ a t u := by
  simp_rw [arithmeticFlowGaussian_unit_translate]
  let «φ» := orderedUnitLogOnto σ
  let : Finite «φ».ker := Nat.finite_of_card_ne_zero (by rw [orderedUnitLogOnto_ker_card_totallyReal σ ]; decide)
  have H := lintegral_tsum_addHom_fundamentalDomain (orderedLogSubgroup σ ⊤) «φ»
    (orderedUnitLogOnto_surjective σ) hS (arithmeticFlowGaussian σ a t)
    (arithmeticFlowGaussian_measurable σ a t)
  rw [orderedUnitLogOnto_ker_card_totallyReal σ ] at H
  exact H

theorem lintegral_arithmeticFlowGaussian_ideal_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) 
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) :
    (∫⁻ u in S, ∑' a : nonzeroIdealElements I, arithmeticFlowGaussian σ a.1.1 t u) =
      2*∑' J : integralIdealClassFiber I,
        ∫⁻ u, arithmeticFlowGaussian σ (idealElementRepresentative I J).1.1 t u := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := NumberField.RingOfIntegers.coe_injective.countable
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  have HE (u : LogCoordinates d) :
      (∑' a : nonzeroIdealElements I, arithmeticFlowGaussian σ a.1.1 t u) =
      ∑' J : integralIdealClassFiber I, ∑' z : (𝓞 K)ˣ,
        arithmeticFlowGaussian σ ((z:K)*(idealElementRepresentative I J).1.1) t u := by
    simpa only [one_mul] using tsum_relativeElementIdeal I (fun _ => 1)
      (fun a => arithmeticFlowGaussian σ a t u)
  simp_rw [HE]
  rw [lintegral_tsum (fun J => (Measurable.tsum (fun z : (𝓞 K)ˣ =>
    arithmeticFlowGaussian_measurable σ ((z:K)*(idealElementRepresentative I J).1.1) t)).aemeasurable)]
  simp_rw [lintegral_arithmeticFlowGaussian_units_totallyReal σ  hS]
  exact ENNReal.tsum_mul_left

end PrimeDegreePackets


namespace PrimeDegreePackets
open ThetaConstruction

theorem fractionalIdealTheta_unit_unfolding_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ u in S, ENNReal.ofReal ((normalizedTheta
      (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
        (restoredLogCoordinates u)) t - 1).re)) =
      2*∑' J : integralIdealClassFiber I,
        ∫⁻ u, arithmeticFlowGaussian σ (idealElementRepresentative I J).1.1 t u := by
  simp_rw [normalizedTheta_fractionalIdeal_gaussian_sum σ hn I _ ht]
  exact lintegral_arithmeticFlowGaussian_ideal_totallyReal σ  hS I t

end PrimeDegreePackets


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

theorem fractionalIdealTheta_mellin_lintegral_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((d+1 : ℝ)*s/2-1)) *
      ∫⁻ u in S, ENNReal.ofReal ((normalizedTheta
        (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
          (restoredLogCoordinates u)) t-1).re)) =
      2 * ENNReal.ofReal (realHeckeFactor (d+1) s * (FractionalIdeal.absNorm I.val : ℝ)^(-s)) *
        ∑' J : integralIdealClassFiber I,
          ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s)) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  let H (J : integralIdealClassFiber I) (t : ℝ) : ℝ≥0∞ :=
    ENNReal.ofReal (t^((d+1 : ℝ)*s/2-1)) *
      ∫⁻ u, arithmeticFlowGaussian σ (idealElementRepresentative I J).1.1 t u
  have HM (J : integralIdealClassFiber I) : Measurable (H J) := by
    apply Measurable.mul (by fun_prop)
    exact (measurable_arithmeticFlowGaussian_joint σ _).lintegral_prod_right'
  have HE : (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((d+1 : ℝ)*s/2-1)) *
      ∫⁻ u in S, ENNReal.ofReal ((normalizedTheta
        (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
          (restoredLogCoordinates u)) t-1).re)) =
      ∫⁻ t in Ioi 0, 2 * ∑' J, H J t := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [fractionalIdealTheta_unit_unfolding_totallyReal σ hn  I hS ht]
    rw [mul_left_comm, ← ENNReal.tsum_mul_left]
  rw [HE, lintegral_const_mul' _ _ (by norm_num), lintegral_tsum (fun J => (HM J).aemeasurable)]
  have HJ (J : integralIdealClassFiber I) :
      (∫⁻ t in Ioi 0, H J t) =
        ENNReal.ofReal (realHeckeFactor (d+1) s * (FractionalIdeal.absNorm I.val : ℝ)^(-s)) *
          ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s)) := by
    dsimp only [H]
    rw [arithmetic_gaussian_lintegral σ hn (idealElementRepresentative I J).1.ne_zero hs,
      idealElementRepresentative_absNorm,
      Real.mul_rpow (fractionalIdeal_absNorm_pos I).le (fractionalIdeal_absNorm_pos J.1).le,
      ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (realHeckeFactor_nonneg _ hs)
        (Real.rpow_nonneg (fractionalIdeal_absNorm_pos I).le _))]
    simp [realHeckeFactor]
  simp_rw [HJ]
  rw [ENNReal.tsum_mul_left, mul_assoc]

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
