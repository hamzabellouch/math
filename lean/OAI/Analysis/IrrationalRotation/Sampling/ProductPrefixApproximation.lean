import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace Invariant233.ProductPrefixApproximation

section General
variable {ι X : Type*} {A : ι → Type*} [∀ i, UniformSpace (A i)]
  {L : Filter X} {Y : Type*}

theorem tendstoUniformly_pi_iff {F : X → Y → ∀ i, A i} {f : Y → ∀ i, A i} :
    TendstoUniformly F f L ↔
      ∀ i, TendstoUniformly (fun n x => F n x i) (fun x => f x i) L := by
  simp only [tendstoUniformly_iff_tendsto, Pi.uniformity, tendsto_iInf,
    tendsto_comap_iff, Function.comp_def]

end General

section Prefix
variable {A : ℕ → Type*} [∀ i, UniformSpace (A i)]

def freeze (a : ∀ i, A i) (n : ℕ) (x : ∀ i, A i) : ∀ i, A i :=
  fun i => if i < n then x i else a i

@[fun_prop] theorem continuous_freeze (a : ∀ i, A i) (n : ℕ) :
    Continuous (freeze a n) := by
  apply continuous_pi
  intro i
  by_cases hi : i < n
  · simpa [freeze, hi] using (continuous_apply i : Continuous (fun x : ∀ i, A i => x i))
  · simpa [freeze, hi] using (continuous_const : Continuous (fun _ : ∀ i, A i => a i))

theorem freeze_tendstoUniformly (a : ∀ i, A i) :
    TendstoUniformly (freeze a) id atTop := by
  rw [tendstoUniformly_pi_iff]
  intro i u hu
  filter_upwards [eventually_gt_atTop i] with n hn
  intro x
  simpa [freeze, hn] using (refl_mem_uniformity hu : (x i, x i) ∈ u)

theorem continuous_freeze_tendstoUniformly [∀ i, CompactSpace (A i)]
    {B : Type*} [UniformSpace B] (a : ∀ i, A i) (f : C((∀ i, A i), B)) :
    TendstoUniformly (fun n x => f (freeze a n x)) f atTop := by
  exact (CompactSpace.uniformContinuous_of_continuous f.continuous).comp_tendstoUniformly
    (freeze_tendstoUniformly a)

end Prefix

namespace Endpoint
open ProductModel

def freeze (a : EndpointPair) (n : ℕ) (xy : EndpointPair) : EndpointPair :=
  (ProductPrefixApproximation.freeze a.1 n xy.1,
    ProductPrefixApproximation.freeze a.2 n xy.2)

@[fun_prop] theorem continuous_freeze (a : EndpointPair) (n : ℕ) :
    Continuous (freeze a n) := by
  exact ((ProductPrefixApproximation.continuous_freeze a.1 n).comp continuous_fst).prodMk
    ((ProductPrefixApproximation.continuous_freeze a.2 n).comp continuous_snd)

theorem freeze_tendstoUniformly (a : EndpointPair) :
    TendstoUniformly (freeze a) id atTop := by
  intro u hu
  exact ((((ProductPrefixApproximation.freeze_tendstoUniformly a.1).comp Prod.fst).prodMk
    ((ProductPrefixApproximation.freeze_tendstoUniformly a.2).comp Prod.snd)) u hu).diag_of_prod

theorem continuous_freeze_tendstoUniformly (a : EndpointPair)
    (f : C(EndpointPair, ℝ)) :
    TendstoUniformly (fun n xy => f (freeze a n xy)) f atTop := by
  exact (CompactSpace.uniformContinuous_of_continuous f.continuous).comp_tendstoUniformly
    (freeze_tendstoUniformly a)

abbrev FinitePair (n : ℕ) := (Fin n → Circle) × (Fin n → Circle)

def restrict (n : ℕ) (xy : EndpointPair) : FinitePair n :=
  (fun i => xy.1 i, fun i => xy.2 i)

@[fun_prop] theorem continuous_restrict (n : ℕ) : Continuous (restrict n) := by
  unfold restrict
  fun_prop

def extend (a : EndpointPair) (n : ℕ) (z : FinitePair n) : EndpointPair :=
  (fun i => if h : i < n then z.1 ⟨i, h⟩ else a.1 i,
    fun i => if h : i < n then z.2 ⟨i, h⟩ else a.2 i)

@[fun_prop] theorem continuous_extend (a : EndpointPair) (n : ℕ) :
    Continuous (extend a n) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    by_cases hi : i < n
    · simpa [extend, hi, Function.comp_def] using
        ((continuous_apply (⟨i, hi⟩ : Fin n)).comp continuous_fst :
          Continuous (fun z : FinitePair n => z.1 ⟨i, hi⟩))
    · simpa [extend, hi, Function.comp_def] using
        (continuous_const : Continuous (fun _ : FinitePair n => a.1 i))
  · apply continuous_pi
    intro i
    by_cases hi : i < n
    · simpa [extend, hi, Function.comp_def] using
        ((continuous_apply (⟨i, hi⟩ : Fin n)).comp continuous_snd :
          Continuous (fun z : FinitePair n => z.2 ⟨i, hi⟩))
    · simpa [extend, hi, Function.comp_def] using
        (continuous_const : Continuous (fun _ : FinitePair n => a.2 i))

@[simp] theorem extend_restrict (a : EndpointPair) (n : ℕ) (xy : EndpointPair) :
    extend a n (restrict n xy) = freeze a n xy := by
  apply Prod.ext <;> funext i <;> by_cases hi : i < n <;>
    simp [extend, restrict, freeze, ProductPrefixApproximation.freeze, hi]

def finiteTest (a : EndpointPair) (n : ℕ) (f : C(EndpointPair, ℝ)) :
    C(FinitePair n, ℝ) :=
  f.comp ⟨extend a n, continuous_extend a n⟩

@[simp] theorem finiteTest_restrict (a : EndpointPair) (n : ℕ)
    (f : C(EndpointPair, ℝ)) (xy : EndpointPair) :
    finiteTest a n f (restrict n xy) = f (freeze a n xy) := by
  simp [finiteTest]

theorem exists_finiteTest_uniformly_near (a : EndpointPair)
    (f : C(EndpointPair, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (g : C(FinitePair n, ℝ)),
      ∀ xy, dist (f xy) (g (restrict n xy)) < ε := by
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformly_iff.mp
    (continuous_freeze_tendstoUniformly a f)) ε hε).exists
  exact ⟨n, finiteTest a n f, by simpa only [finiteTest_restrict] using hn⟩

@[simp] theorem freeze_zero (a xy : EndpointPair) : freeze a 0 xy = a := by
  apply Prod.ext <;> funext i <;>
    simp [freeze, ProductPrefixApproximation.freeze]

end Endpoint
end Invariant233.ProductPrefixApproximation

end

end OAI
