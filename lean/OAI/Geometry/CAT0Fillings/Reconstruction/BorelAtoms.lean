import Mathlib
import OAI.Geometry.CAT0Fillings.Reconstruction.LipschitzPieces
import OAI.Geometry.CAT0Fillings.Reconstruction.GraphAssembly

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

abbrev JointPieceIndex := ℕ × ℕ × ℕ × ℕ

theorem common_zero_current_pieces {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] (S : E → Functional X 0)
    (hI : ∀ᵐ t ∂μ, IsIntegral 0 (S t))
    (hf : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
      LocallyIntegrable (fun t => S t b (fun j => Fin.elim0 j)) μ)
    (ν : Measure E) [IsLocallyFiniteMeasure ν] {C κ : ℝ}
    (hC : 0 ≤ C) (hκ : 0 < κ)
    (hP : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
      ∀ t, ∀ r : ℝ, 0 < r →
      (∫ z in closedBall t r,
        |S z b (fun j => Fin.elim0 j) -
          (⨍ w in closedBall t r, S w b (fun j => Fin.elim0 j) ∂μ)| ∂μ) ≤
        C * r * ν.real (closedBall t (κ*r))) :
    ∃ (K : JointPieceIndex → Set E) (L : JointPieceIndex → ℝ≥0),
      (∀ i, IsCompact (K i) ∧ ∀ t ∈ K i, IsIntegral 0 (S t)) ∧
      (∀ i b, LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
        LipschitzOnWith (L i) (fun t => S t b (fun j => Fin.elim0 j)) (K i)) ∧
      (∀ᵐ t ∂μ, t ∈ ⋃ i, K i) := by
  classical
  obtain ⟨q,hq⟩ := exists_dense_seq (TestClass (X := X) 0 1)
  let f (j : ℕ) (t : E) := TestClass.eval (S t) (q j)
  have hb (p : TestClass (X := X) 0 1) : ∀ x, |p.val.1 x| ≤ 1 := by
    intro x
    simpa only [Nat.cast_one, Real.norm_eq_abs] using (p.val.1.norm_coe_le_norm x).trans p.property.2.1
  have hpi (p : TestClass (X := X) 0 1) :
      (fun i => (p.val.2 i : X → ℝ)) = fun i => Fin.elim0 i := by
    funext i
    exact Fin.elim0 i
  have hf' (j : ℕ) : LocallyIntegrable (f j) μ := by
    simpa only [f,TestClass.eval,hpi] using hf (q j).val.1 (by simpa only [Nat.cast_one] using (q j).property.1) (hb (q j))
  have hP' (j : ℕ) (t : E) (r : ℝ) (hr : 0 < r) :
      (∫ z in closedBall t r, |f j z - (⨍ w in closedBall t r, f j w ∂μ)| ∂μ) ≤
        C * r * ν.real (closedBall t (κ*r)) := by
    simpa only [f,TestClass.eval,hpi] using
      hP (q j).val.1 (by simpa only [Nat.cast_one] using (q j).property.1) (hb (q j)) t r hr
  obtain ⟨K,L,hK,hL,hcover⟩ := common_compact_lipschitz_pieces (μ := μ) f hf' ν hC hκ
    hP' {t | IsIntegral 0 (S t)} hI
  refine ⟨K,L,fun i => ⟨(hK i).1,(hK i).2⟩,?_,hcover⟩
  intro i b hbLip hbOne
  let bc : C(X,ℝ) := ⟨b,hbLip.continuous⟩
  have hn : ‖bc‖ ≤ 1 := (ContinuousMap.norm_le bc (by norm_num)).mpr (by
    simpa only [Real.norm_eq_abs,bc, ContinuousMap.coe_mk] using hbOne)
  let p : TestClass (X := X) 0 1 := ⟨(bc,fun z => Fin.elim0 z),by simpa only [Nat.cast_one,bc,ContinuousMap.coe_mk] using hbLip,
    by simpa only [Nat.cast_one] using hn,fun z => Fin.elim0 z⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hcurx : IsMetricCurrent (S x) := ((hK i).2 hx).1
  have hcury : IsMetricCurrent (S y) := ((hK i).2 hy).1
  have hbound : ∀ p : TestClass (X := X) 0 1,
      dist (TestClass.eval (S x) p) (TestClass.eval (S y) p) ≤ (L i : ℝ)*dist x y := by
    intro p
    exact hq.induction_on p
      (isClosed_le ((Foundations.IsMetricCurrent.testClass_continuous hcurx 1).dist
        (Foundations.IsMetricCurrent.testClass_continuous hcury 1))
        continuous_const) (fun j => (hL i j).dist_le_mul x hx y hy)
  have hpEval (U : Functional X 0) : TestClass.eval U p = U b (fun j => Fin.elim0 j) := by
    unfold TestClass.eval
    rw [hpi p]
    rfl
  simpa only [hpEval] using hbound p

theorem joint_integer_atom_graphs (S : E → Functional X 0)
    (hI : ∀ᵐ t ∂μ, IsIntegral 0 (S t))
    (hf : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
      LocallyIntegrable (fun t => S t b (fun j => Fin.elim0 j)) μ)
    (ν : Measure E) [IsLocallyFiniteMeasure ν] {C κ : ℝ}
    (hC : 0 ≤ C) (hκ : 0 < κ)
    (hP : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
      ∀ t, ∀ r : ℝ, 0 < r →
      (∫ z in closedBall t r,
        |S z b (fun j => Fin.elim0 j) -
          (⨍ w in closedBall t r, S w b (fun j => Fin.elim0 j) ∂μ)| ∂μ) ≤
        C * r * ν.real (closedBall t (κ*r))) :
    ∃ (D : JointPieceIndex × AtomCode → Set E)
      (L : JointPieceIndex × AtomCode → ℝ≥0)
      (γ : ∀ i : JointPieceIndex × AtomCode, D i → Fin i.2.size → X),
      (∀ i, IsCompact (D i)) ∧ (∀ᵐ t ∂μ, t ∈ ⋃ i, D i) ∧
      (∀ i j, LipschitzWith (L i) (fun t => γ i t j)) ∧
      (∀ i (t : D i), IsIntegral 0 (S t)) ∧
      (∀ i (t : D i), UnitRepresentation (S t) i.2.weights (γ i t)) ∧
      (∀ i (t : D i), Function.Injective (γ i t)) ∧
      (∀ i (_ : D i) j, i.2.weights j ≠ 0) := by
  classical
  obtain ⟨K,L,hK,hL,hcover⟩ := common_zero_current_pieces S hI hf ν hC hκ hP
  let D (i : JointPieceIndex × AtomCode) := atomDomain S (K i.1) i.2
  let γ (i : JointPieceIndex × AtomCode) (t : D i) := selectedAtom S (K i.1) i.2 t
  refine ⟨D,fun i => L i.1,γ,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact isCompact_atomDomain S (hK i.1).1 i.2
      (fun b hb hb1 => (hL i.1 b hb hb1).continuousOn)
  · filter_upwards [hcover,hI] with t ht hi
    obtain ⟨i,hit⟩ := mem_iUnion.mp ht
    obtain ⟨c,hc⟩ := integral_mem_atomDomain S hit hi
    exact mem_iUnion.mpr ⟨(i,c),hc⟩
  · intro i j
    exact selectedAtom_lipschitz S (K i.1) i.2 (hL i.1) j
  · intro i t
    exact (hK i.1).2 t t.property.1
  · intro i t
    exact (selectedAtom_spec S (K i.1) i.2 t).2
  · intro i t
    exact atomCode_atoms_injective i.2 t.property.2.1 _
      (selectedAtom_spec S (K i.1) i.2 t).1

  · intro i t j
    exact t.property.2.1.2.2.1 j

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma UnitRepresentation.action {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) {b : X → ℝ} (hb : BoundedLip b)
    (π : Fin 0 → X → ℝ) : S b π = ∑ i, (a i : ℝ)*b (x i) := by
  obtain ⟨K,hK⟩ := hb.1
  obtain ⟨B,hB⟩ := hb.2
  let C : ℝ := max (K : ℝ) (max B 1)
  have hC1 : 1 ≤ C := (le_max_right B 1).trans (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hKC : (K : ℝ) ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left B 1).trans (le_max_right _ _)
  let f : X → ℝ := fun z => C⁻¹*b z
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [f,Real.dist_eq,←mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hC),NNReal.coe_one,one_mul]
    calc
      C⁻¹ * |b z-b w| ≤ C⁻¹*((K : ℝ)*dist z w) :=
        mul_le_mul_of_nonneg_left (hK.dist_le_mul z w) (inv_nonneg.mpr hC.le)
      _ ≤ C⁻¹*(C*dist z w) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hKC dist_nonneg) (inv_nonneg.mpr hC.le)
      _ = dist z w := by field_simp
  have hf1 (z : X) : |f z| ≤ 1 := by
    simp only [f,abs_mul,abs_of_pos (inv_pos.mpr hC)]
    calc
      C⁻¹*|b z| ≤ C⁻¹*C := mul_le_mul_of_nonneg_left ((hB z).trans hBC) (inv_nonneg.mpr hC.le)
      _ = 1 := inv_mul_cancel₀ hC.ne'
  have hs := h f hf hf1
  have hp : π = (fun j => Fin.elim0 j) := funext fun j => Fin.elim0 j
  have hlin := hS.linearFirst b b π C⁻¹ 0 hb hb (fun j => Fin.elim0 j)
  simp only [zero_mul,add_zero] at hlin
  change S f π = C⁻¹*S b π at hlin
  rw [←hp,hlin] at hs
  have hsum : (∑ i, (a i : ℝ)*f (x i)) = C⁻¹*∑ i, (a i : ℝ)*b (x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]
    ring
  rw [hsum] at hs
  exact mul_left_cancel₀ (inv_ne_zero hC.ne') hs

lemma UnitRepresentation.controls {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) :
    Controls S (∑ i, ENNReal.ofReal |(a i : ℝ)| • Measure.dirac (x i)) := by
  classical
  intro b π hb _
  rw [h.action hS hb π,integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,
      ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,←abs_mul]
    exact Finset.abs_sum_le_sum_abs _ _
  · intro i _
    let := finite_atom_measure (a i) (x i)
    exact (integrable_boundedLip _ hb).abs

lemma UnitRepresentation.massMeasure_compl_eq_zero {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) {E : Set X} (hE : MeasurableSet E)
    (hx : ∀ i, x i ∈ E) : currentMassMeasure hS Eᶜ = 0 := by
  classical
  let μ : Measure X := ∑ i, ENNReal.ofReal |(a i : ℝ)| • Measure.dirac (x i)
  let : ∀ i : Fin m, IsFiniteMeasure (ENNReal.ofReal |(a i : ℝ)| • Measure.dirac (x i)) :=
    fun i => finite_atom_measure (a i) (x i)
  have hμ : Controls S μ := h.controls hS
  apply le_antisymm ((currentMassMeasure_le hS hμ Eᶜ).trans ?_) (show (0 : ℝ≥0∞) ≤ _ from bot_le)
  simp only [μ,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  have hz (i : Fin m) : Measure.dirac (x i) Eᶜ = 0 := by
    rw [Measure.dirac_apply' _ hE.compl]
    exact indicator_of_notMem (by simpa only [mem_compl_iff,not_not] using hx i) _
  simp [hz]

lemma UnitRepresentation.borelAction_zero {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) {f : X → ℝ}
    (hf : Measurable f) (hx : ∀ i, f (x i) = 0) (π : Fin 0 → X → ℝ) :
    currentBorelAction S f π = 0 := by
  have hE : MeasurableSet {z : X | f z = 0} := hf (measurableSet_singleton 0)
  have hm := h.massMeasure_compl_eq_zero hS hE hx
  have he : f =ᵐ[currentMassMeasure hS] 0 := by
    exact ae_iff.mpr hm
  rw [currentBorelAction_eq hS,borelAction_congr_ae _ hS he]
  rw [borelAction_of_integrable _ hS (integrable_zero X ℝ _)
    π (fun j => Fin.elim0 j)]
  simp

end CAT0Fillings.SliceReconstruction
end

end OAI
