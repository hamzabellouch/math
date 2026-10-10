import OAI.InformationTheory.SecretKey.Purification

namespace OAI

noncomputable section

namespace ZeroKey

section

open Matrix MeasureTheory ProbabilityTheory Filter

universe u

lemma card_keyWord (n : ℕ) : Fintype.card (KeyWord n) = 2^n := by
  induction n with
  | zero => change Fintype.card Unit = 1; exact Fintype.card_unique
  | succ n ih =>
    change Fintype.card (Bool × KeyWord n) = _
    rw [Fintype.card_prod,Fintype.card_bool,ih,pow_succ,mul_comm]

end

section

open MeasureTheory Filter

open scoped ENNReal

universe v11415_0

variable {Ω : Type v11415_0} [inst11415_0 : MeasurableSpace Ω]

def commonPublicLaw (μ : ℕ → Measure Ω) : Measure Ω :=
  Measure.sum (fun n => (2⁻¹ : ℝ≥0∞)^n • μ n)

lemma commonPublicLaw_univ (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)] :
    commonPublicLaw μ Set.univ = 2 := by
  simp only [commonPublicLaw,Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,
    measure_univ,smul_eq_mul,mul_one]
  exact ENNReal.tsum_geometric_two

instance commonPublicLaw_finite (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)] :
    IsFiniteMeasure (commonPublicLaw μ) := ⟨by rw [commonPublicLaw_univ]; norm_num⟩

lemma absolutelyContinuous_commonPublicLaw (μ : ℕ → Measure Ω) (n : ℕ) :
    μ n ≪ commonPublicLaw μ := by
  apply Measure.absolutelyContinuous_sum_right n
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hzero
  have hp : (2⁻¹ : ℝ≥0∞)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  simpa only [Measure.smul_apply,smul_eq_mul,mul_eq_zero,hp,false_or] using hzero

end

section

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe u

namespace KeyImplementation

variable {a b ell : ℕ} {messages : ClassicalRecordSpace.{u}}
  [inst11471_0 : Nonempty (Fin a)] [inst11471_1 : Nonempty (Fin b)]
  (p : KeyImplementation a b ell messages)
  (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : Density R)
  {e : ℕ} (P : Matrix (Fin a × Fin b) (Fin e) ℂ) (hP : P * Pᴴ = R)
  (ν : Measure (ℕ → messages)) [inst11471_2 : SigmaFinite ν] (hμν : p.discussion.transcriptLaw ≪ ν)

lemma uniform_gap (hc : InClass R) (hell : 0 < ell) (sigma : EveDensity ν (Fin e)) :
    1/5 ≤ (p.output R hR P hP ν hμν).idealError sigma := by
  cases ell with
  | zero => omega
  | succ n => exact p.protocol.uniform_purified_key_gap_dominated R hc P hP ν hμν sigma

end KeyImplementation

namespace IsCompletedKeyOutput

variable {a b ell e : ℕ} [inst11506_0 : Nonempty (Fin a)] [inst11506_1 : Nonempty (Fin b)]
  {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} {hR : Density R}
  {P : Matrix (Fin a × Fin b) (Fin e) ℂ} {hP : P * Pᴴ = R}
  {messages : ClassicalRecordSpace.{u}} {ν : Measure (ℕ → messages)} [inst11506_2 : SigmaFinite ν]
  {τ : KeyDensity ν (KeyWord ell) (Fin e)}

lemma of_implementation (p : KeyImplementation a b ell messages)
    (hAC : p.discussion.transcriptLaw ≪ ν) :
    IsCompletedKeyOutput R hR P hP messages ν (p.output R hR P hP ν hAC) := by
  apply (isCompletedKeyOutput_iff_original R hR P hP messages ν _).2
  refine ⟨fun _ => p,fun _ => hAC,?_⟩
  simpa only [KeyDensity.distance_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

theorem uniform_gap (hτ : IsCompletedKeyOutput R hR P hP messages ν τ)
    (hc : InClass R) (hell : 0 < ell) (sigma : EveDensity ν (Fin e)) :
    1/5 ≤ τ.idealError sigma := by
  obtain ⟨p,hAC,hlim⟩ := hτ
  exact KeyDensity.gap_of_traceNorm_limit
    (fun j => (p j).output R hR P hP ν (hAC j)) τ sigma
    (fun j => (p j).uniform_gap R hR P hP ν (hAC j) hc hell sigma) hlim

end IsCompletedKeyOutput

attribute [instance] CompletedKeyTrial.sigmaFinite

namespace CompletedKeyTrial

variable {a b ell : ℕ} [inst11550_0 : Nonempty (Fin a)] [inst11550_1 : Nonempty (Fin b)]
  {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} {hR : Density R}
  (p : CompletedKeyTrial R hR ell)

lemma error_nonneg : 0 ≤ p.error := p.actual.idealError_nonneg p.ideal

lemma uniform_error (hc : InClass R) (hell : 0 < ell) : 1/5 ≤ p.error :=
  p.completed.uniform_gap hc hell p.ideal

end CompletedKeyTrial

end

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

def groupVector {a b c d : ℕ} (u : Fin a × Fin b → ℂ) (v : Fin c × Fin d → ℂ) :
    Fin (a*c) × Fin (b*d) → ℂ := fun i =>
  u (groupIndex a b c d i).1 * v (groupIndex a b c d i).2

lemma outer_groupVector {a b c d : ℕ} (u : Fin a × Fin b → ℂ) (v : Fin c × Fin d → ℂ) :
    outer (groupVector u v) (groupVector u v) = groupTensor (outer u u) (outer v v) := by
  ext i j
  simp only [outer,groupVector,groupTensor,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,star_mul]
  ring

lemma tensorMap_kronecker {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (M : Mat c →ₗ[ℂ] Mat d)
    (A : Mat a) (B : Mat c) : tensorMap L M (A ⊗ₖ B) = L A ⊗ₖ M B := by
  ext ⟨i,k⟩ ⟨j,l⟩
  simp only [tensorMap,Matrix.kronecker_apply]
  have hL := linearMap_matrix_units_apply L A i j
  have hM := linearMap_matrix_units_apply M B k l
  rw [hL,hM]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro w _
  ring

lemma matrixUnit_finProd {a c : ℕ} (x y : Fin (a*c)) :
    (matrixUnit x y).submatrix finProdFinEquiv finProdFinEquiv =
      matrixUnit (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1 ⊗ₖ
      matrixUnit (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2 := by
  ext ⟨i,k⟩ ⟨j,l⟩
  simp only [Matrix.submatrix_apply, matrixUnit, Matrix.kronecker_apply]
  have hx : finProdFinEquiv (i,k) = x ↔ i = (finProdFinEquiv.symm x).1 ∧
      k = (finProdFinEquiv.symm x).2 := by
    rw [← Equiv.eq_symm_apply]
    exact Prod.ext_iff
  have hy : finProdFinEquiv (j,l) = y ↔ j = (finProdFinEquiv.symm y).1 ∧
      l = (finProdFinEquiv.symm y).2 := by
    rw [← Equiv.eq_symm_apply]
    exact Prod.ext_iff
  simp only [hx,hy]
  split_ifs <;> simp_all

lemma tensorLinear_unit {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (M : Mat c →ₗ[ℂ] Mat d)
    (x y : Fin (a*c)) (i j : Fin (b*d)) :
    tensorLinear L M (matrixUnit x y) i j =
    L (matrixUnit (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1)
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
    M (matrixUnit (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2)
      (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  change (tensorMap L M _ _ _) = _
  rw [matrixUnit_finProd,tensorMap_kronecker]
  rfl

lemma tensorMap_groupTensor {a b c d e f g h : ℕ}
    (L : Mat a →ₗ[ℂ] Mat b) (M : Mat c →ₗ[ℂ] Mat d)
    (N : Mat e →ₗ[ℂ] Mat f) (P : Mat g →ₗ[ℂ] Mat h)
    (U : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ)
    (V : Matrix (Fin e × Fin g) (Fin e × Fin g) ℂ) :
    tensorMap (tensorLinear L N) (tensorLinear M P) (groupTensor U V) =
    groupTensor (tensorMap L M U) (tensorMap N P V) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  simp only [tensorMap, tensorLinear_unit,groupTensor,Matrix.submatrix_apply,
    Matrix.kronecker_apply,groupIndex,Equiv.coe_fn_mk]
  simp_rw [← Equiv.sum_comp (finProdFinEquiv : Fin a × Fin e ≃ _)]
  simp_rw [← Equiv.sum_comp (finProdFinEquiv : Fin c × Fin g ≃ _)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  conv_lhs => arg 2; ext xv; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro z _
  conv_lhs => arg 2; ext xv; arg 2; ext yv; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext xv; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w _
  apply Finset.sum_congr rfl; intro xv _
  apply Finset.sum_congr rfl; intro yv _
  apply Finset.sum_congr rfl; intro zv _
  apply Finset.sum_congr rfl; intro wv _
  ring

lemma InClass.groupTensor {a b c d : ℕ}
    {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ}
    {S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ}
    (hR : InClass R) (hS : InClass S) : InClass (groupTensor R S) := by
  obtain ⟨hdR,p,q,L,M,u,hL,hM,hu⟩ := hR
  obtain ⟨hdS,r,s,N,P,v,hN,hP,hv⟩ := hS
  refine ⟨hdR.groupTensor hdS,p*r,q*s,tensorLinear L N,tensorLinear M P,
    groupVector u v,ppt_tensorLinear hL hN,ppt_tensorLinear hM hP,?_⟩
  rw [outer_groupVector,tensorMap_groupTensor,← hu,← hv]

lemma InClass.positiveCopies {a b : ℕ}
    {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} (hR : InClass R) (k : ℕ) :
    InClass (positiveCopies R k) := by
  induction k with
  | zero => exact hR
  | succ k ih => exact ih.groupTensor hR

end ZeroKey

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace ZeroKey

universe u

namespace CompletedKeyScheme

variable {a b : ℕ} [inst11756_0 : Nonempty (Fin a)] [inst11756_1 : Nonempty (Fin b)]
  {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} {hR : Density R}
  (s : CompletedKeyScheme.{u} R hR)

lemma eventually_length_zero (hc : InClass R) (hs : s.Secure) :
    ∀ᶠ k in atTop, s.length k = 0 := by
  have he : ∀ᶠ k in atTop, s.error k < 1/5 := (tendsto_order.mp hs).2 _ (by norm_num)
  filter_upwards [he] with k hk
  by_contra hn
  exact (not_lt_of_ge ((s.trial k).uniform_error (hc.positiveCopies k)
    (Nat.pos_of_ne_zero hn))) hk

lemma lowerRate_zero (hc : InClass R) (hs : s.Secure) : s.lowerRate = 0 := by
  unfold lowerRate
  have he : (fun k : ℕ => (s.length k : ℝ≥0∞) / (k+1 : ℕ)) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [s.eventually_length_zero hc hs] with k hk
    simp [hk]
  rw [Filter.liminf_congr he]
  simp

end CompletedKeyScheme

theorem class_distillableSecretKey_zero {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : Density R) (hc : InClass R) :
    distillableSecretKey.{u} R hR = 0 := by
  apply le_antisymm ?_ bot_le
  apply sSup_le
  intro r hr
  rcases hr with rfl | ⟨s,hs,rfl⟩
  · rfl
  · exact le_of_eq (s.lowerRate_zero hc hs)

end ZeroKey

end

end OAI
