import OAI.InformationTheory.SecretKey.MatrixMeasure

namespace OAI

noncomputable section

namespace ZeroKey

section

open Matrix MeasureTheory ProbabilityTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v5690_0 v5690_1 v5690_2 v5690_3 v5690_4 v5690_5

variable {O : Type v5690_0} {M : Type v5690_1} {ι : Type v5690_2} {η : Type v5690_3} [inst5690_0 : MeasurableSpace O] [inst5690_1 : MeasurableSpace M]
  [inst5690_2 : Fintype ι] [inst5690_3 : Fintype η] [inst5690_4 : DecidableEq ι] [inst5690_5 : DecidableEq η]
  {A : ℕ → Type v5690_4} {B : ℕ → Type v5690_5}
  [inst5690_6 : ∀ n, AddCommGroup (A n)] [inst5690_7 : ∀ n, Module ℂ (A n)] [inst5690_8 : ∀ n, One (A n)] [inst5690_9 : ∀ n, LE (A n)]
  [inst5690_10 : ∀ n, AddCommGroup (B n)] [inst5690_11 : ∀ n, Module ℂ (B n)] [inst5690_12 : ∀ n, One (B n)] [inst5690_13 : ∀ n, LE (B n)]
  (p : LocalOutcomeSampler O M)
  (κA κB : (n : ℕ) → Kernel (LocalHistory O M n) O)
  [inst5690_14 : ∀ n, IsMarkovKernel (κA n)] [inst5690_15 : ∀ n, IsMarkovKernel (κB n)]
  (eA : LocalObservableExecution (ι := ι) A κA p.sendA)
  (eB : LocalObservableExecution (ι := η) B κB p.sendB)

def globalLocalReferenceA (n : ℕ) (s : Fin n → O) : Matrix ι ι ℂ :=
  eA.reference n (p.extractPrivate true n s,p.publicFrom n s)

def globalLocalReferenceB (n : ℕ) (s : Fin n → O) : Matrix η η ℂ :=
  eB.reference n (p.extractPrivate false n s,p.publicFrom n s)

omit inst5690_14 in
lemma globalLocalReferenceA_measurable [∀ n, IsMarkovKernel (κA n)] (n : ℕ) :
    Measurable (globalLocalReferenceA p κA eA n) :=
  (eA.reference_measurable n).comp
    ((p.measurable_extractPrivate true n).prodMk (p.measurable_publicFrom n))

omit inst5690_15 in
lemma globalLocalReferenceB_measurable [∀ n, IsMarkovKernel (κB n)] (n : ℕ) :
    Measurable (globalLocalReferenceB p κB eB n) :=
  (eB.reference_measurable n).comp
    ((p.measurable_extractPrivate false n).prodMk (p.measurable_publicFrom n))

omit inst5690_14 in
lemma globalLocalReferenceA_mean [∀ n, IsMarkovKernel (κA n)] (n : ℕ) (s : Fin n → O) (i j : ι) :
    (∫ o, globalLocalReferenceA p κA eA (n+1) (Fin.snoc s o) i j
      ∂p.instrumentKernel κA κB n s) = globalLocalReferenceA p κA eA n s i j := by
  unfold globalLocalReferenceA
  simp_rw [p.extractPrivate_snoc, p.publicFrom_snoc]
  unfold LocalOutcomeSampler.instrumentKernel
  cases hrole : p.alice n with
  | true =>
    simp only [↓reduceIte,Kernel.comap_apply]
    exact eA.active_mean n _ i j
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,Kernel.comap_apply]
    change (∫ o, eA.reference (n+1) (localPassive
      (p.extractPrivate true n s,p.publicFrom n s)
      (p.sendB n ((p.extractPrivate false n s,p.publicFrom n s),o))) i j
      ∂κB n (p.extractPrivate false n s,p.publicFrom n s)) = _
    simp only [eA.passive_reference]
    simp

omit inst5690_15 in
lemma globalLocalReferenceB_mean [∀ n, IsMarkovKernel (κB n)] (n : ℕ) (s : Fin n → O) (i j : η) :
    (∫ o, globalLocalReferenceB p κB eB (n+1) (Fin.snoc s o) i j
      ∂p.instrumentKernel κA κB n s) = globalLocalReferenceB p κB eB n s i j := by
  unfold globalLocalReferenceB
  simp_rw [p.extractPrivate_snoc, p.publicFrom_snoc]
  unfold LocalOutcomeSampler.instrumentKernel
  cases hrole : p.alice n with
  | false =>
    simp only [↓reduceIte]
    exact eB.active_mean n _ i j
  | true =>
    simp only [Bool.true_eq_false,↓reduceIte,Kernel.comap_apply]
    change (∫ o, eB.reference (n+1) (localPassive
      (p.extractPrivate false n s,p.publicFrom n s)
      (p.sendA n ((p.extractPrivate true n s,p.publicFrom n s),o))) i j
      ∂κA n (p.extractPrivate true n s,p.publicFrom n s)) = _
    simp only [eB.passive_reference]
    simp

def jointReference (n : ℕ) (s : Fin n → O) : Matrix (ι × η) (ι × η) ℂ :=
  globalLocalReferenceA p κA eA n s ⊗ₖ globalLocalReferenceB p κB eB n s

omit inst5690_14 inst5690_15 in
lemma jointReference_density [∀ n, IsMarkovKernel (κA n)] [∀ n, IsMarkovKernel (κB n)] (n : ℕ) (s : Fin n → O) :
    Density (jointReference p κA κB eA eB n s) := by
  refine ⟨(eA.reference_density n _).1.kronecker (eB.reference_density n _).1,?_⟩
  simp only [jointReference, Matrix.trace_kronecker,globalLocalReferenceA,
    globalLocalReferenceB,(eA.reference_density n _).2,(eB.reference_density n _).2,one_mul]

lemma jointReference_measurable (n : ℕ) :
    Measurable (jointReference p κA κB eA eB n) := by
  have hm : Measurable (fun s i j => jointReference p κA κB eA eB n s i j) := by
    apply Measurable.of_eval; intro i
    apply Measurable.of_eval; intro j
    exact (((Matrix.entryLinearMap ℂ ℂ i.1 j.1).toContinuousLinearMap).measurable.comp
      (globalLocalReferenceA_measurable p κA eA n)).mul
      (((Matrix.entryLinearMap ℂ ℂ i.2 j.2).toContinuousLinearMap).measurable.comp
      (globalLocalReferenceB_measurable p κB eB n))
  have hM : Continuous (Matrix.of : ((ι × η) → (ι × η) → ℂ) → Matrix (ι × η) (ι × η) ℂ) :=
    continuous_matrix (fun i j => continuous_apply_apply i j)
  exact hM.measurable.comp hm

omit inst5690_14 inst5690_15 in
lemma jointReference_mean [∀ n, IsMarkovKernel (κA n)] [∀ n, IsMarkovKernel (κB n)] (n : ℕ) (s : Fin n → O) (i j : ι × η) :
    (∫ o, jointReference p κA κB eA eB (n+1) (Fin.snoc s o) i j
      ∂p.instrumentKernel κA κB n s) = jointReference p κA κB eA eB n s i j := by
  change (∫ o, globalLocalReferenceA p κA eA (n+1) (Fin.snoc s o) i.1 j.1 *
    globalLocalReferenceB p κB eB (n+1) (Fin.snoc s o) i.2 j.2
    ∂p.instrumentKernel κA κB n s) =
    globalLocalReferenceA p κA eA n s i.1 j.1 * globalLocalReferenceB p κB eB n s i.2 j.2
  simp only [globalLocalReferenceA,globalLocalReferenceB]
  simp_rw [p.extractPrivate_snoc,p.publicFrom_snoc]
  unfold LocalOutcomeSampler.instrumentKernel
  cases hrole : p.alice n with
  | true =>
    simp only [Bool.true_eq_false,↓reduceIte,Kernel.comap_apply]
    change (∫ o, eA.reference (n+1) (localActive
      (p.extractPrivate true n s,p.publicFrom n s) o
      (p.sendA n ((p.extractPrivate true n s,p.publicFrom n s),o))) i.1 j.1 *
      eB.reference (n+1) (localPassive (p.extractPrivate false n s,p.publicFrom n s)
      (p.sendA n ((p.extractPrivate true n s,p.publicFrom n s),o))) i.2 j.2
      ∂κA n (p.extractPrivate true n s,p.publicFrom n s)) = _
    simp_rw [eB.passive_reference]
    rw [integral_mul_const,eA.active_mean]
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,Kernel.comap_apply]
    change (∫ o, eA.reference (n+1) (localPassive
      (p.extractPrivate true n s,p.publicFrom n s)
      (p.sendB n ((p.extractPrivate false n s,p.publicFrom n s),o))) i.1 j.1 *
      eB.reference (n+1) (localActive (p.extractPrivate false n s,p.publicFrom n s) o
      (p.sendB n ((p.extractPrivate false n s,p.publicFrom n s),o))) i.2 j.2
      ∂κB n (p.extractPrivate false n s,p.publicFrom n s)) = _
    simp_rw [eA.passive_reference]
    rw [integral_const_mul,eB.active_mean]

end

section

open MeasureTheory ProbabilityTheory Set Function unitInterval

universe v6512_0 v6512_1

theorem exists_adaptive_instrument_sampler {O : Type v6512_0} {M : Type v6512_1} [MeasurableSpace O]
    [StandardBorelSpace O] [Nonempty O] [MeasurableSpace M]
    (alice : (n : ℕ) → (Fin n → M) → Bool) (hq : ∀ n, Measurable (alice n))
    (κA κB : (n : ℕ) → Kernel ((Fin n → (O ⊕ Unit)) × (Fin n → M)) O)
    [∀ n, IsMarkovKernel (κA n)] [∀ n, IsMarkovKernel (κB n)]
    (sendA sendB : (n : ℕ) → ((Fin n → (O ⊕ Unit)) × (Fin n → M)) × O → M)
    (ha : ∀ n, Measurable (sendA n)) (hb : ∀ n, Measurable (sendB n)) :
    ∃ p : AdaptiveOutcomeSampler O M,
      p.alice = alice ∧ p.sendA = sendA ∧ p.sendB = sendB ∧
      (∀ n s, volume.map (fun u => p.sampleA n (s,u)) = κA n s) ∧
      (∀ n s, volume.map (fun u => p.sampleB n (s,u)) = κB n s) := by
  have hA (n : ℕ) := sample_instrument_kernel (κA n)
  have hB (n : ℕ) := sample_instrument_kernel (κB n)
  choose fA hfA hlawA hrestA using hA
  choose fB hfB hlawB hrestB using hB
  exact ⟨⟨alice,hq,fun n pair => fA n pair.1 pair.2,
    fun n pair => fB n pair.1 pair.2,sendA,sendB,hfA,hfB,ha,hb⟩,
    rfl,rfl,rfl,hlawA,hlawB⟩

end

section

open MeasureTheory ProbabilityTheory Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

universe v7283_0 v7283_1 v7283_2

variable {Ω : Type v7283_0} {ι : Type v7283_1} {κ : Type v7283_2} {C A B : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  [inst7283_0 : StandardBorelSpace Ω] [inst7283_1 : Fintype ι] [inst7283_2 : Fintype κ] [inst7283_3 : DecidableEq ι] [inst7283_4 : DecidableEq κ]
  {μ : Measure Ω} [inst7283_5 : IsFiniteMeasure μ]

lemma publicMatrix_positive (W : Ω → Matrix ι ι ℂ)
    (hW : ∀ x, (W x).PosSemidef) (x : Ω) :
    (publicMatrix C μ W x).PosSemidef :=
  (integral_nonneg_of_ae (Filter.Eventually.of_forall (fun y => (hW y).nonneg))).posSemidef

end

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder

namespace PositiveMatrixMeasure

universe v7485_0 v7485_1

variable {Ω : Type v7485_0} {ι : Type v7485_1} {mΩ : MeasurableSpace Ω} [inst7485_0 : Fintype ι] [inst7485_1 : DecidableEq ι]

universe v7524_0

lemma filter_eq_of_filtration {κ : Type v7524_0} [Fintype κ] [DecidableEq κ]
    (W : PositiveMatrixMeasure Ω ι) (V : PositiveMatrixMeasure Ω κ)
    (K : Matrix κ ι ℂ) (F : Filtration ℕ mΩ) (hm : mΩ = ⨆ n, F n)
    (h : ∀ n S, MeasurableSet[F n] S → V.value S = K * W.value S * Kᴴ) :
    V = W.filter K := by
  apply V.ext_on_filtration (W.filter K) F hm
  intro n S hS
  rw [filter_value]
  exact h n S hS

end PositiveMatrixMeasure

end ZeroKey

namespace UnrestrictedQuantum

open Matrix MeasureTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v7551_0 v7551_1 v7551_2

variable {A : Type v7551_0} {B : Type v7551_1} {ι : Type v7551_2} [inst7551_0 : AddCommGroup A] [inst7551_1 : Module ℂ A] [inst7551_2 : One A] [inst7551_3 : LE A]
  [inst7551_4 : AddCommGroup B] [inst7551_5 : Module ℂ B] [inst7551_6 : One B] [inst7551_7 : LE B]
  [inst7551_8 : Fintype ι] [inst7551_9 : DecidableEq ι]
  (J : ObservableInstrument Bool A B) (S : ReferenceFunctional A ι)
  (r : InstrumentRun J S)

include r in
lemma bitReference_total_trace (htrace : trace (S 1) = 1) :
    trace (bitReference J S false) + trace (bitReference J S true) = 1 := by
  rw [← Matrix.trace_add, bitReference_sum J S r, htrace]

universe v7591_0

omit inst7551_9 in
lemma bitReference_filter [DecidableEq ι] {κ : Type v7591_0} [Fintype κ] [DecidableEq κ]
    (K : Matrix κ ι ℂ) (i : Bool) :
    bitReference J (filterFunctional K S) i =
      K * bitReference J S i * Kᴴ := rfl

end UnrestrictedQuantum

open Matrix MeasureTheory

open scoped TensorProduct Kronecker

namespace UnrestrictedQuantum

universe v8007_0 v8007_1 v8007_2 v8007_3 v8007_4 v8007_5

variable {A : Type v8007_0} {A' : Type v8007_1} {B : Type v8007_2} {B' : Type v8007_3}
  [inst8007_0 : AddCommGroup A] [inst8007_1 : Module ℂ A] [inst8007_2 : AddCommGroup A'] [inst8007_3 : Module ℂ A']
  [inst8007_4 : AddCommGroup B] [inst8007_5 : Module ℂ B] [inst8007_6 : AddCommGroup B'] [inst8007_7 : Module ℂ B']
  {ι : Type v8007_4} {η : Type v8007_5}

def tensorReferenceFunctional (S : A →ₗ[ℂ] Matrix ι ι ℂ)
    (T : B →ₗ[ℂ] Matrix η η ℂ) :
    (TensorProduct ℂ A B) →ₗ[ℂ] Matrix (ι × η) (ι × η) ℂ :=
  TensorProduct.lift ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)).compl₁₂ S T)

@[simp]
lemma tensorReferenceFunctional_apply (S : A →ₗ[ℂ] Matrix ι ι ℂ)
    (T : B →ₗ[ℂ] Matrix η η ℂ) (a : A) (b : B) :
    tensorReferenceFunctional S T (a ⊗ₜ[ℂ] b) = S a ⊗ₖ T b := rfl

theorem tensorReferenceFunctional_precompose
    (S : A →ₗ[ℂ] Matrix ι ι ℂ) (T : B →ₗ[ℂ] Matrix η η ℂ)
    (L : A' →ₗ[ℂ] A) (N : B' →ₗ[ℂ] B) :
    (tensorReferenceFunctional S T).comp (TensorProduct.map L N) =
      tensorReferenceFunctional (S.comp L) (T.comp N) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, tensorReferenceFunctional_apply]

lemma product_event_reference [One A] [One B] [One A']
    (S : A →ₗ[ℂ] Matrix ι ι ℂ) (T : B →ₗ[ℂ] Matrix η η ℂ)
    (L : A' →ₗ[ℂ] A) :
    ((tensorReferenceFunctional S T).comp
      (TensorProduct.map L (LinearMap.id : B →ₗ[ℂ] B))) (1 ⊗ₜ[ℂ] 1) =
        S (L 1) ⊗ₖ T 1 := by
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    tensorReferenceFunctional_apply]

end UnrestrictedQuantum

end

end OAI
