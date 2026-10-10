import Mathlib
import OAI.NumberTheory.PrimePackets.RootInvariance

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
open scoped BigOperators Classical
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
namespace PrimeDegreePackets

 

theorem ae_intrinsicRootLeaf_projective_multiplier_zero (d : ℕ)
    {i j : Fin (d+1)} (hij : i ≠ j) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ p : ℝ × ℝ, projectiveLeafPeriod (intrinsicRootLeaf hij μ x) p →
      p.2 = 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x := ae_intrinsicRootKernel_eq hij μ hfree
  have hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r) := by
    filter_upwards [heq,ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hp
    rwa [hx]
  have H := ae_projectiveLeafPeriod_multiplier_zero μ κ hp (by
    intro c hc
    let T : X (d+1) → X (d+1) := fun x => rightAction x (rootCanonicalFlow d j (Real.log c))
    have hT : MeasurePreserving T μ μ := rootCanonicalFlow_preserving d j (Real.log c) μ hA
    refine ⟨T,hT,?_⟩
    have heqmap : ∀ᵐ x ∂μ.map T, κ x = intrinsicRootLeaf hij μ x := by
      rw [hT.map_eq]
      exact heq
    have heqT : ∀ᵐ x ∂μ, κ (T x) = intrinsicRootLeaf hij μ (T x) :=
      ae_of_ae_map hT.measurable.aemeasurable heqmap
    filter_upwards [heq,heqT,ae_intrinsicRootLeaf_canonical d hij μ hA (Real.log c)] with x hx hTx hcq
    rw [hTx,hx]
    simpa only [Real.exp_log hc,T] using hcq)
  filter_upwards [heq,H] with x hx h
  rwa [hx] at h

lemma projectiveLeafPeriod_zero_multiplier_iff (ν : Measure ℝ) (a : ℝ) :
    projectiveLeafPeriod ν (a,0) ↔ a ∈ realLeafPeriods ν := by
  change (ν.map (fun x => x+a) = ENNReal.ofReal (Real.exp 0) • ν) ↔
    ν.map (fun x => x+a) = ν
  simp only [Real.exp_zero,ENNReal.ofReal_one,one_smul]

 

theorem root_invariant_of_nonzero_intrinsic_projective_period (d : ℕ)
    {i j : Fin (d+1)} (hij : i ≠ j) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hp : ∀ᵐ x ∂μ, ∃ p : ℝ × ℝ, p.1 ≠ 0 ∧
      projectiveLeafPeriod (intrinsicRootLeaf hij μ x) p) (a : ℝ) :
    μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  apply root_invariant_of_nonzero_intrinsic_period d hij μ hA
  filter_upwards [hp,ae_intrinsicRootLeaf_projective_multiplier_zero d hij μ hA] with x hx hm
  obtain ⟨p,hp,hper⟩ := hx
  have hz := hm p hper
  refine ⟨p.1,hp,(projectiveLeafPeriod_zero_multiplier_iff _ _).mp ?_⟩
  have he : p = (p.1,0) := Prod.ext rfl hz
  rwa [he] at hper

 

theorem intrinsicRootLeaf_projective_ergodic_alternative (d : ℕ)
    {i j : Fin (d+1)} (hij : i ≠ j) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    (∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) ∨
      (∀ᵐ x ∂μ, ∀ p : ℝ × ℝ, projectiveLeafPeriod (intrinsicRootLeaf hij μ x) p → p = 0) := by
  rcases intrinsicRootLeaf_periods_ergodic_alternative d hij μ with hinv | hbot
  · exact Or.inl hinv
  · right
    have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
      (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
    filter_upwards [hbot,ae_intrinsicRootLeaf_projective_multiplier_zero d hij μ hA] with x hx hm
    intro p hp
    have hz := hm p hp
    have ha : p.1 ∈ realLeafPeriods (intrinsicRootLeaf hij μ x) := by
      apply (projectiveLeafPeriod_zero_multiplier_iff _ _).mp
      have he : p = (p.1,0) := Prod.ext rfl hz
      rwa [he] at hp
    rw [hx,AddSubgroup.mem_bot] at ha
    exact Prod.ext ha hz

end PrimeDegreePackets

open Module Set Matrix MeasureTheory Filter
namespace PrimeDegreePackets

def rationalPointSpace {n : ℕ} (x : X n) : Submodule ℚ (Fin n → ℝ) :=
  Submodule.span ℚ (pointLattice x : Set (Fin n → ℝ))

lemma rationalPointSpace_mk {n : ℕ} (g : G n) :
    rationalPointSpace (Quotient.mk _ g : X n) =
      Submodule.span ℚ (Set.range fun i => g.1 i) := by
  rw [rationalPointSpace,pointLattice_mk,rowLattice,Submodule.span_span_of_tower]

lemma rationalPointSpace_clear_denominator {n : ℕ} (x : X n)
    (v : Fin n → ℝ) (hv : v ∈ rationalPointSpace x) :
    ∃ z : ℤ, z ≠ 0 ∧ z • v ∈ pointLattice x := by
  obtain ⟨w,hw,z,hz⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors ℤ)).mp hv
  rw [Submodule.span_eq] at hw
  refine ⟨z,mem_nonZeroDivisors_iff_ne_zero.mp z.property,?_⟩
  rw [hz,←IsScalarTower.algebraMap_smul ℚ,smul_smul,
    IsLocalization.mul_mk'_eq_mk'_of_mul,mul_one,IsLocalization.mk'_self,one_smul]
  exact hw

lemma rationalPointSpace_no_coordinate_zero {n : ℕ} (x : X n)
    (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0) :
    ∀ v ∈ rationalPointSpace x, v ≠ 0 → ∀ j, v j ≠ 0 := by
  intro v hv hv0 j hvj
  obtain ⟨z,hz,hzv⟩ := rationalPointSpace_clear_denominator x v hv
  have hn : z • v ≠ 0 := smul_ne_zero hz hv0
  exact hx _ hzv hn j (by simp [Pi.smul_apply,hvj])

instance rationalPointSpace_finite {n : ℕ} (x : X n) :
    Module.Finite ℚ (rationalPointSpace x) := by
  induction x using Quotient.inductionOn with
  | h g =>
    rw [rationalPointSpace_mk]
    exact (Submodule.fg_iff_finiteDimensional _).mp (Submodule.fg_span (Set.finite_range _))

lemma rationalPointSpace_finrank {n : ℕ} (x : X n) :
    Module.finrank ℚ (rationalPointSpace x) = n := by
  induction x using Quotient.inductionOn with
  | h g =>
    rw [rationalPointSpace_mk]
    have H : LinearIndependent ℝ (fun i => g.1 i) :=
      Matrix.linearIndependent_rows_of_det_ne_zero (by rw [g.property]; exact one_ne_zero)
    simpa using finrank_span_eq_card (H.restrict_scalars' ℚ)

lemma rationalPointSpace_real_span {n : ℕ} (x : X n) :
    Submodule.span ℝ (rationalPointSpace x : Set (Fin n → ℝ)) = ⊤ := by
  induction x using Quotient.inductionOn with
  | h g =>
    rw [rationalPointSpace_mk,Submodule.span_span_of_tower]
    have he : (fun i => g.1 i) = (fun i => rowBasis g i) := by
      funext i j
      exact (rowBasis_apply g i j).symm
    rw [he]
    exact (rowBasis g).span_eq

 

theorem ae_rationalPointSpace_no_coordinate_zero (d : ℕ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ v ∈ rationalPointSpace x, v ≠ 0 → ∀ j, v j ≠ 0 := by
  exact (ae_no_coordinate_zero d μ hA).mono fun x hx => rationalPointSpace_no_coordinate_zero x hx

end PrimeDegreePackets


namespace PrimeDegreePackets

 
def diagonalRationalAlgebra {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) :
    Subalgebra ℚ (Fin n → ℝ) where
  carrier := {a | ∀ v ∈ W, a*v ∈ W}
  zero_mem' := by intro v hv; simp
  one_mem' := by intro v hv; simpa using hv
  add_mem' := by
    intro a b ha hb v hv
    rw [add_mul]
    exact W.add_mem (ha v hv) (hb v hv)
  mul_mem' := by
    intro a b ha hb v hv
    rw [mul_assoc]
    exact ha _ (hb v hv)
  algebraMap_mem' := by
    intro q v hv
    simpa only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] using W.smul_mem q hv

instance diagonalRationalAlgebra_module {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) :
    Module (diagonalRationalAlgebra W) W where
  smul a v := ⟨a.val*v.val,a.prop v.val v.prop⟩
  one_smul v := Subtype.ext (one_mul v.val)
  mul_smul a b v := Subtype.ext (mul_assoc a.val b.val v.val)
  smul_zero a := Subtype.ext (mul_zero a.val)
  smul_add a v w := Subtype.ext (mul_add a.val v.val w.val)
  add_smul a b v := Subtype.ext (add_mul a.val b.val v.val)
  zero_smul v := Subtype.ext (zero_mul v.val)

instance diagonalRationalAlgebra_tower {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) :
    IsScalarTower ℚ (diagonalRationalAlgebra W) W where
  smul_assoc q a v := Subtype.ext (smul_mul_assoc q a.val v.val)

@[simp] lemma diagonalRationalAlgebra_smul_val {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (a : diagonalRationalAlgebra W) (v : W) : (a • v : W).val = a.val*v.val := rfl

 

def diagonalRationalEval {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) (v : W) :
    diagonalRationalAlgebra W →ₗ[ℚ] W where
  toFun a := a • v
  map_add' a b := add_smul a b v
  map_smul' q a := Subtype.ext (smul_mul_assoc q a.val v.val)

lemma diagonalRationalEval_injective {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (v : W) (hv : ∀ i, v.val i ≠ 0) : Function.Injective (diagonalRationalEval W v) := by
  intro a b hab
  apply Subtype.ext
  funext i
  exact mul_right_cancel₀ (hv i) (congrArg (fun w : W => w.val i) hab)

lemma diagonalRationalAlgebra_finite {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    [Module.Finite ℚ W] (v : W) (hv : ∀ i, v.val i ≠ 0) :
    Module.Finite ℚ (diagonalRationalAlgebra W) :=
  Module.Finite.of_injective (diagonalRationalEval W v) (diagonalRationalEval_injective W v hv)

 

lemma diagonalRationalAlgebra_coordinate_injective {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hW : ∀ w ∈ W, w ≠ 0 → ∀ i, w i ≠ 0) (i : Fin n) :
    Function.Injective (fun a : diagonalRationalAlgebra W => a.val i) := by
  intro a b hab
  have he : (diagonalRationalEval W v (a-b)).val = 0 := by
    by_contra hn
    apply hW _ (diagonalRationalEval W v (a-b)).prop hn i
    change (a.val i-b.val i)*v.val i = 0
    simp only [hab,sub_self,zero_mul]
  have hz : diagonalRationalEval W v (a-b) = diagonalRationalEval W v 0 := by
    rw [_root_.map_zero]
    exact Subtype.ext he
  exact sub_eq_zero.mp (diagonalRationalEval_injective W v hv hz)

lemma diagonalRationalAlgebra_isDomain {n : ℕ} [Nonempty (Fin n)]
    (W : Submodule ℚ (Fin n → ℝ)) (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hW : ∀ w ∈ W, w ≠ 0 → ∀ i, w i ≠ 0) :
    IsDomain (diagonalRationalAlgebra W) := by
  let i : Fin n := Classical.choice inferInstance
  let f : diagonalRationalAlgebra W →+* ℝ :=
    (Pi.evalRingHom (fun _ : Fin n => ℝ) i).comp (diagonalRationalAlgebra W).val
  exact (diagonalRationalAlgebra_coordinate_injective W v hv hW i).isDomain f

 

theorem diagonalRationalAlgebra_isField {n : ℕ} [Nonempty (Fin n)]
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hW : ∀ w ∈ W, w ≠ 0 → ∀ i, w i ≠ 0) :
    IsField (diagonalRationalAlgebra W) := by
  let := diagonalRationalAlgebra_isDomain W v hv hW
  let := diagonalRationalAlgebra_finite W v hv
  exact IsField.of_isDomain_of_finite ℚ (diagonalRationalAlgebra W)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma diagonalRationalAlgebra_finrank_dvd {n : ℕ} [Nonempty (Fin n)]
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hW : ∀ w ∈ W, w ≠ 0 → ∀ i, w i ≠ 0) :
    Module.finrank ℚ (diagonalRationalAlgebra W) ∣ Module.finrank ℚ W := by
  let := diagonalRationalAlgebra_finite W v hv
  let := (diagonalRationalAlgebra_isField W v hv hW).toField
  exact ⟨Module.finrank (diagonalRationalAlgebra W) W,
    (Module.finrank_mul_finrank ℚ (diagonalRationalAlgebra W) W).symm⟩

 

theorem diagonalRationalAlgebra_prime_degree {n : ℕ} (hn : n.Prime)
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hW : ∀ w ∈ W, w ≠ 0 → ∀ i, w i ≠ 0)
    (hdim : Module.finrank ℚ W = n) :
    diagonalRationalAlgebra W = ⊥ ∨ Module.finrank ℚ (diagonalRationalAlgebra W) = n := by
  let : NeZero n := ⟨hn.ne_zero⟩
  have H := diagonalRationalAlgebra_finrank_dvd W v hv hW
  rw [hdim] at H
  rcases (Nat.dvd_prime hn).mp H with h | h
  · left
    exact Subalgebra.finrank_eq_one_iff.mp h
  · exact Or.inr h

lemma rationalPointSpace_exists_nonzero_coordinates {n : ℕ} (x : X n) :
    ∃ v : rationalPointSpace x, ∀ i, v.val i ≠ 0 := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨z,hz⟩ := exists_integer_row_no_zero_coordinate g
    have hm : integerRowMap g.1 z ∈ pointLattice (Quotient.mk _ g : X n) := by
      rw [pointLattice_mk,←integerRowMap_range]
      exact ⟨z,rfl⟩
    exact ⟨⟨integerRowMap g.1 z,Submodule.subset_span hm⟩,by simpa [integerRowMap_apply] using hz⟩

 

theorem ae_point_diagonalRationalAlgebra_isField (d : ℕ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, IsField (diagonalRationalAlgebra (rationalPointSpace x)) := by
  filter_upwards [ae_rationalPointSpace_no_coordinate_zero d μ hA] with x hx
  obtain ⟨v,hv⟩ := rationalPointSpace_exists_nonzero_coordinates x
  exact diagonalRationalAlgebra_isField _ v hv hx

 

theorem ae_point_diagonalRationalAlgebra_prime_degree (d : ℕ) (hn : (d+1).Prime)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, diagonalRationalAlgebra (rationalPointSpace x) = ⊥ ∨
      Module.finrank ℚ (diagonalRationalAlgebra (rationalPointSpace x)) = d+1 := by
  filter_upwards [ae_rationalPointSpace_no_coordinate_zero d μ hA] with x hx
  obtain ⟨v,hv⟩ := rationalPointSpace_exists_nonzero_coordinates x
  exact diagonalRationalAlgebra_prime_degree hn _ v hv hx (rationalPointSpace_finrank x)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma diagonalRationalEval_surjective {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra W) = Module.finrank ℚ W) :
    Function.Surjective (diagonalRationalEval W v) := by
  let := diagonalRationalAlgebra_finite W v hv
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (diagonalRationalEval_injective W v hv)

 

theorem diagonalRationalAlgebra_separates {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra W) = Module.finrank ℚ W)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤) :
    Function.Injective (fun i : Fin n => fun a : diagonalRationalAlgebra W => a.val i) := by
  intro i j hij
  by_contra hne
  let F : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    v.val j • LinearMap.proj i - v.val i • LinearMap.proj j
  have hF (w : Fin n → ℝ) (hw : w ∈ W) : F w = 0 := by
    obtain ⟨a,ha⟩ := diagonalRationalEval_surjective W v hv hdim ⟨w,hw⟩
    have he : w = a.val * v.val := by
      exact (congrArg Subtype.val ha).symm
    have hab : a.val i = a.val j := congrFun hij a
    simp only [F,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.proj_apply,he,
      Pi.mul_apply,smul_eq_mul,hab]
    ring
  have hker : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ F.ker := by
    rw [←hspan]
    exact Submodule.span_le.mpr hF
  have hs : F (Pi.single i 1) = 0 := hker (by trivial)
  have hz : v.val j = 0 := by
    simpa [F,LinearMap.proj_apply,Pi.single_apply,hne,Ne.symm hne] using hs
  exact hv j hz

 

theorem diagonalRationalAlgebra_eq_bot_of_repeated {n : ℕ} (hn : n.Prime)
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hW : ∀ w ∈ W, w ≠ 0 → ∀ i, w i ≠ 0)
    (hdim : Module.finrank ℚ W = n)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤)
    {i j : Fin n} (hij : i ≠ j)
    (heq : ∀ a : diagonalRationalAlgebra W, a.val i = a.val j) :
    diagonalRationalAlgebra W = ⊥ := by
  rcases diagonalRationalAlgebra_prime_degree hn W v hv hW hdim with h | h
  · exact h
  · exact False.elim (hij (diagonalRationalAlgebra_separates W v hv
      (h.trans hdim.symm) hspan (funext heq)))

 

theorem ae_point_diagonalRationalAlgebra_repeated (d : ℕ) (hn : (d+1).Prime)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ (i j : Fin (d+1)), i ≠ j →
      (∀ a : diagonalRationalAlgebra (rationalPointSpace x), a.val i = a.val j) →
      diagonalRationalAlgebra (rationalPointSpace x) = ⊥ := by
  filter_upwards [ae_rationalPointSpace_no_coordinate_zero d μ hA] with x hx
  intro i j hij heq
  obtain ⟨v,hv⟩ := rationalPointSpace_exists_nonzero_coordinates x
  exact diagonalRationalAlgebra_eq_bot_of_repeated hn _ v hv hx
    (rationalPointSpace_finrank x) (rationalPointSpace_real_span x) hij heq

end PrimeDegreePackets


namespace PrimeDegreePackets

def diagonalCoordinateEmbedding {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) (i : Fin n) :
    diagonalRationalAlgebra W →+* ℝ :=
  (Pi.evalRingHom (fun _ : Fin n => ℝ) i).comp (diagonalRationalAlgebra W).val

def diagonalComplexEmbedding {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) (i : Fin n) :
    diagonalRationalAlgebra W →+* ℂ :=
  Complex.ofRealHom.comp (diagonalCoordinateEmbedding W i)

lemma diagonalComplexEmbedding_injective {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra W) = Module.finrank ℚ W)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤) :
    Function.Injective (diagonalComplexEmbedding W) := by
  intro i j hij
  apply diagonalRationalAlgebra_separates W v hv hdim hspan
  funext a
  exact Complex.ofReal_injective (congrArg (fun f : diagonalRationalAlgebra W →+* ℂ => f a) hij)

 

theorem diagonalComplexEmbedding_surjective {n : ℕ} [Nonempty (Fin n)]
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hW : ∀ w ∈ W, w ≠ 0 → ∀ i, w i ≠ 0)
    (hdimW : Module.finrank ℚ W = n)
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra W) = n)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤) :
    Function.Surjective (diagonalComplexEmbedding W) := by
  let := (diagonalRationalAlgebra_isField W v hv hW).toField
  let := diagonalRationalAlgebra_finite W v hv
  let : NumberField (diagonalRationalAlgebra W) := {
    to_finiteDimensional := by
      convert diagonalRationalAlgebra_finite W v hv using 1
      exact Subsingleton.elim _ _ }
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨?_,?_⟩).2
  · exact diagonalComplexEmbedding_injective W v hv (hdim.trans hdimW.symm) hspan
  · rw [Fintype.card_fin,NumberField.Embeddings.card]
    symm
    convert hdim using 1
    congr 1
    exact Subsingleton.elim _ _

 

theorem diagonalRationalAlgebra_totallyReal {n : ℕ} [Nonempty (Fin n)]
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hW : ∀ w ∈ W, w ≠ 0 → ∀ i, w i ≠ 0)
    (hdimW : Module.finrank ℚ W = n)
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra W) = n)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤) :
    letI := (diagonalRationalAlgebra_isField W v hv hW).toField
    NumberField.IsTotallyReal (diagonalRationalAlgebra W) := by
  let := (diagonalRationalAlgebra_isField W v hv hW).toField
  constructor
  intro w
  rw [NumberField.InfinitePlace.isReal_iff]
  obtain ⟨i,hi⟩ := diagonalComplexEmbedding_surjective W v hv hW hdimW hdim hspan w.embedding
  rw [←hi]
  ext a
  simp [diagonalComplexEmbedding]

 

theorem diagonalRationalAlgebra_module_finrank_one {n : ℕ} [Nonempty (Fin n)]
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0)
    (hW : ∀ w ∈ W, w ≠ 0 → ∀ i, w i ≠ 0)
    (hdimW : Module.finrank ℚ W = n)
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra W) = n) :
    letI := (diagonalRationalAlgebra_isField W v hv hW).toField
    Module.finrank (diagonalRationalAlgebra W) W = 1 := by
  let := (diagonalRationalAlgebra_isField W v hv hW).toField
  let := diagonalRationalAlgebra_finite W v hv
  have H := Module.finrank_mul_finrank ℚ (diagonalRationalAlgebra W) W
  rw [hdim,hdimW] at H
  have hn : 0 < n := by simpa using (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin n)))
  exact Nat.eq_of_mul_eq_mul_left hn (by simpa using H)

end PrimeDegreePackets
end
end

end OAI
