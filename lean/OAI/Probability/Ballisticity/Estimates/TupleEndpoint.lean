import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawPairLocality
import OAI.Probability.Ballisticity.Walk.CoordinateKernelComp

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience.TupleKernel

lemma fin_tsum_product {A : Type*} (n : ℕ) (f : Fin n → A → ℝ≥0∞) :
    (∑' x : Fin n → A, ∏ j, f j (x j)) = ∏ j, ∑' x : A, f j x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]

lemma measurable_countable_measure {A Ω : Type*} [MeasurableSpace A]
    [MeasurableSpace Ω] [Countable A] [MeasurableSingletonClass A]
    (μ : Ω → Measure A) (h : ∀ x, Measurable (fun ω => μ ω {x})) : Measurable μ := by
  have he (ω) : μ ω = Measure.sum (fun x => μ ω {x} • Measure.dirac x) :=
    (Measure.sum_smul_dirac _).symm
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hf : (fun ω => μ ω s) = (fun ω => ∑' x, μ ω {x} * Measure.dirac x s) := by
    funext ω
    conv_lhs => rw [he ω]
    simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  rw [hf]
  exact Measurable.tsum fun x => (h x).mul_const _

lemma measure_le_of_singletons {A : Type*} [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] (μ ν : Measure A)
    (h : ∀ x, μ {x} ≤ ν {x}) : μ ≤ ν := by
  intro s
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  conv_rhs => rw [← Measure.sum_smul_dirac ν]
  simp only [Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul_left (h x) _

lemma countable_pi_mono {A : Type*} [MeasurableSpace A] [Countable A]
    [MeasurableSingletonClass A] (n : ℕ) (μ ν : Fin n → Measure A)
    [∀ j, SigmaFinite (μ j)] [∀ j, SigmaFinite (ν j)]
    (h : ∀ j, μ j ≤ ν j) : Measure.pi μ ≤ Measure.pi ν := by
  apply measure_le_of_singletons
  intro x
  simp only [Measure.pi_singleton]
  exact Finset.prod_le_prod fun j _ => h j {x j}

lemma countable_pi_bind {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (n : ℕ) (μ : Fin n → Measure A) (K : Fin n → A → Measure B)
    [∀ j, SigmaFinite (μ j)] [∀ j x, SigmaFinite (K j x)]
    [∀ j, SigmaFinite ((μ j).bind (K j))] :
    (Measure.pi μ).bind (fun x => Measure.pi (fun j => K j (x j))) =
      Measure.pi (fun j => (μ j).bind (K j)) := by
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable]
  simp_rw [Measure.pi_singleton,Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable,
    lintegral_countable',Measure.pi_singleton,← Finset.prod_mul_distrib]
  exact fin_tsum_product n (fun j a => K j a {y j} * μ j {a})

end TupleKernel

noncomputable def rawTupleEndpointLaw {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) : Measure (Fin k → Lattice d) :=
  Measure.pi (fun j => variableHitKernel ℓ H (ω,x j))

lemma rawTupleEndpointLaw_singleton {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x y : Fin k → Lattice d) :
    rawTupleEndpointLaw ℓ H ω x {y} = ∏ j, variableHitKernel ℓ H (ω,x j) {y j} := by
  exact Measure.pi_singleton _ _

lemma rawTupleEndpointLaw_le_one {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    rawTupleEndpointLaw ℓ H ω x Set.univ ≤ 1 := by
  rw [rawTupleEndpointLaw,Measure.pi_univ]
  exact Finset.prod_le_one fun j _ =>
    hitKernel_total_le_one (disjoint_strip_upper ℓ (x j) H) (ω,x j)

instance rawTupleEndpointLaw_finite {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    IsFiniteMeasure (rawTupleEndpointLaw ℓ H ω x) := by
  unfold rawTupleEndpointLaw
  infer_instance

lemma measurable_rawTupleEndpointLaw {d k : ℕ} (ℓ : Vector d) (H : ℕ) :
    Measurable (fun p : Environment d × (Fin k → Lattice d) => rawTupleEndpointLaw ℓ H p.1 p.2) := by
  apply TupleKernel.measurable_countable_measure
  intro y
  simp_rw [rawTupleEndpointLaw_singleton]
  apply Finset.measurable_prod
  intro j _
  exact (Kernel.measurable_coe (variableHitKernel ℓ H) (measurableSet_singleton _)).comp
    (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

noncomputable def rawTupleMixture {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) : Measure (Fin k → Lattice d) :=
  π.bind (rawTupleEndpointLaw ℓ H ω)

lemma rawTupleMixture_apply {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) (A : Set (Fin k → Lattice d)) :
    rawTupleMixture ℓ H π ω A = ∫⁻ x, rawTupleEndpointLaw ℓ H ω x A ∂π := by
  exact Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable

lemma rawTupleEndpointLaw_comp_le {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    rawTupleMixture (realPosition (step e)) m
      (rawTupleEndpointLaw (realPosition (step e)) h ω x) ω ≤
        rawTupleEndpointLaw (realPosition (step e)) (h+m) ω x := by
  let ℓ := realPosition (step e)
  let K := fun (n : ℕ) (y : Lattice d) => variableHitKernel ℓ n (ω,y)
  have hcomp (y : Lattice d) : (K h y).bind (K m) ≤ K (h+m) y := by
    intro U
    rw [Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]
    change (∫⁻ a, hitKernel (Strip ℓ a (m : ℝ)) (Upper ℓ a (m : ℝ)) (ω,a) U
      ∂hitKernel (Strip ℓ y (h : ℝ)) (Upper ℓ y (h : ℝ)) (ω,y)) ≤
      hitKernel (Strip ℓ y ((h+m : ℕ) : ℝ)) (Upper ℓ y ((h+m : ℕ) : ℝ)) (ω,y) U
    simpa only [ℓ, Nat.cast_add] using coordinate_raw_kernel_comp_le e h m ω y U
  let : ∀ y, IsFiniteMeasure ((K h y).bind (K m)) := fun y =>
    ⟨lt_of_le_of_lt (hcomp y Set.univ) (measure_lt_top _ _)⟩
  change (Measure.pi (fun j => K h (x j))).bind (fun y => Measure.pi (fun j => K m (y j))) ≤
    Measure.pi (fun j => K (h+m) (x j))
  rw [TupleKernel.countable_pi_bind]
  exact TupleKernel.countable_pi_mono k _ _ (fun j => hcomp (x j))

end DirectionalTransience

end

end OAI
