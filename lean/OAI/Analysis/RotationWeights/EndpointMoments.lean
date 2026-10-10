import OAI.Analysis.RotationWeights.RadixDigits

namespace OAI

noncomputable section

universe uX uι uD uΩ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

open Set MeasureTheory Topology
open scoped symmDiff
namespace CircleCoupling

section

section

lemma continuous_measureReal_of_le {X : Type uX} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≤ ν) :
    Continuous (fun s : MeasuredSets ν ↦ μ.real (s : Set X)) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, MeasuredSets.dist_def]
  apply (abs_measureReal_sub_le_measureReal_symmDiff s.2.nullMeasurableSet t.2.nullMeasurableSet).trans
  exact ENNReal.toReal_mono (measure_ne_top _ _) (hμν _)

lemma sq_measure_bound_of_generating_ring {X : Type uX} [mX : MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : Set (Set X)} (hC : IsSetRing C) (hU : univ ∈ C)
    (hgen : mX = MeasurableSpace.generateFrom C) (H : ℝ)
    (hfinite : ∀ A∈C, (ν.real A)^2 ≤ H * μ.real A) :
    ∀ A, MeasurableSet A → (ν.real A)^2 ≤ H * μ.real A := by
  let τ := μ+ν
  have hμ : Continuous (fun s : MeasuredSets τ ↦ μ.real (s : Set X)) :=
    continuous_measureReal_of_le μ τ (Measure.le_add_right le_rfl)
  have hν : Continuous (fun s : MeasuredSets τ ↦ ν.real (s : Set X)) :=
    continuous_measureReal_of_le ν τ (Measure.le_add_left le_rfl)
  have hd : Dense ((SetLike.coe : MeasuredSets τ → Set X) ⁻¹' C) :=
    dense_of_generateFrom_isSetRing hC ⟨{univ}, by simp, by simpa, by simp⟩ hgen
  have hc : IsClosed {s : MeasuredSets τ | (ν.real (s : Set X))^2 ≤ H*μ.real (s : Set X)} :=
    isClosed_le (hν.pow 2) (continuous_const.mul hμ)
  have hh : closure ((SetLike.coe : MeasuredSets τ → Set X) ⁻¹' C) ⊆
      {s : MeasuredSets τ | (ν.real (s : Set X))^2 ≤ H*μ.real (s : Set X)} :=
    closure_minimal (fun s hs ↦ hfinite s hs) hc
  rw [hd.closure_eq] at hh
  intro A hA
  exact hh (show (⟨A,hA⟩ : MeasuredSets τ) ∈ univ from mem_univ _)

lemma sqrt_measure_bound_of_generating_ring {X : Type uX} [mX : MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : Set (Set X)} (hC : IsSetRing C) (hU : univ ∈ C)
    (hgen : mX = MeasurableSpace.generateFrom C) {H : ℝ} (hH : 0 ≤ H)
    (hfinite : ∀ A∈C, ν.real A ≤ H * Real.sqrt (μ.real A)) :
    ∀ A, MeasurableSet A → ν.real A ≤ H * Real.sqrt (μ.real A) := by
  have h : ∀ A, MeasurableSet A → (ν.real A)^2 ≤ H^2 * μ.real A :=
    sq_measure_bound_of_generating_ring μ ν hC hU hgen (H^2) (by
      intro A hA
      have hsq := sq_le_sq₀ (show 0≤ν.real A from measureReal_nonneg)
        (mul_nonneg hH (Real.sqrt_nonneg _)) |>.mpr (hfinite A hA)
      rwa [mul_pow, Real.sq_sqrt measureReal_nonneg] at hsq)
  intro A hA
  apply (sq_le_sq₀ measureReal_nonneg (mul_nonneg hH (Real.sqrt_nonneg _))).mp
  simpa [mul_pow,Real.sq_sqrt measureReal_nonneg] using h A hA

lemma infinitePi_sqrt_bound {ι : Type uι} {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] (μ ν : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    {H : ℝ} (hH : 0≤H)
    (hfinite : ∀ I : Finset ι, ∀ A, MeasurableSet A →
      (Measure.pi (fun i : I ↦ ν i)).real A ≤
        H * Real.sqrt ((Measure.pi (fun i : I ↦ μ i)).real A)) :
    ∀ A, MeasurableSet A → (Measure.infinitePi ν).real A ≤
      H * Real.sqrt ((Measure.infinitePi μ).real A) := by
  have hU : (univ : Set (∀ i, X i)) ∈ measurableCylinders (α := X) := by
    rw [← cylinder_univ (∅ : Finset ι)]
    exact cylinder_mem_measurableCylinders _ _ MeasurableSet.univ
  apply sqrt_measure_bound_of_generating_ring (Measure.infinitePi μ) (Measure.infinitePi ν)
    isSetRing_measurableCylinders hU generateFrom_measurableCylinders.symm hH
  intro A hA
  obtain ⟨I,B,hB,rfl⟩ := (mem_measurableCylinders _).mp hA
  have hν : (Measure.infinitePi ν) (cylinder I B) =
      (Measure.pi (fun i : I ↦ ν i)) B := by
    exact Measure.infinitePi_cylinder _ hB
  have hμ : (Measure.infinitePi μ) (cylinder I B) =
      (Measure.pi (fun i : I ↦ μ i)) B := by
    exact Measure.infinitePi_cylinder _ hB
  simp only [Measure.real,hν,hμ]
  exact hfinite I B hB


lemma infinitePi_l2_bound {ι : Type uι} {D : ι → Type uD}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, MeasurableSingletonClass (D i)] (ν : ∀ i, Measure (D i))
    [∀ i, IsProbabilityMeasure (ν i)] (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    (hs : Summable e)
    (hm : ∀ i, (Fintype.card (D i) : ℝ) * ∑ d, ((ν i).real {d})^2 ≤ 1+e i)
    (A : Set (∀ i, D i)) (hA : MeasurableSet A) :
    (Measure.infinitePi ν).real A ≤ Real.exp ((∑' i, e i)/2) *
      Real.sqrt ((Measure.infinitePi (fun i => (PMF.uniformOfFintype (D i)).toMeasure)).real A) := by
  classical
  apply infinitePi_sqrt_bound _ ν (Real.exp_pos _).le _ A hA
  intro I B _hB
  apply uniform_l2_set_bound _ _ (fun d => by simpa using pi_uniform_singleton_real d) (Real.exp_pos _).le _ B
  rw [pi_second_moment (fun i : I => ν i)]
  calc
    (∏ i : I, (Fintype.card (D i) : ℝ) * ∑ d, ((ν i).real {d})^2) ≤ ∏ i : I, Real.exp (e i) := by
      apply Finset.prod_le_prod₀
      · intro i _; positivity
      · intro i _; exact (hm i).trans (by simpa [add_comm] using Real.add_one_le_exp (e i))
    _ = Real.exp (∑ i : I, e i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' i, e i) := by
      apply Real.exp_le_exp.mpr
      rw [Finset.sum_coe_sort]
      exact hs.sum_le_tsum I (fun i _ => he i)
    _ = Real.exp ((∑' i, e i)/2)^2 := by rw [← Real.exp_nat_mul]; congr 1; ring

open CircleDigits

lemma observedDigits_sqrt_bound {Ω : ℕ → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {b : ℕ → ℕ} [∀ i, NeZero (b i)] (f : ∀ i, Ω i → Fin (b i))
    (hf : ∀ i, Measurable (f i)) (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (hs : Summable e)
    (hm : ∀ i, (b i : ℝ)* ∑ d, ((μ i).real (f i ⁻¹' {d}))^2 ≤ 1+e i)
    (A : Set (Digits b)) (hA : MeasurableSet A) :
    (Measure.infinitePi μ).real ((fun ω i => f i (ω i)) ⁻¹' A) ≤
      Real.exp ((∑' i, e i)/2) * Real.sqrt ((uniformDigits b).real A) := by
  let ν : ∀ i, Measure (Fin (b i)) := fun i => Measure.map (f i) (μ i)
  have hν : ∀ i, IsProbabilityMeasure (ν i) := fun _ => inferInstance
  have hmoment (i : ℕ) : (Fintype.card (Fin (b i)) : ℝ) * ∑ d, ((ν i).real {d})^2 ≤ 1+e i := by
    convert hm i using 1
    simp only [Fintype.card_fin,Measure.real,ν,Measure.map_apply (hf i) (measurableSet_singleton _)]
  have hh := infinitePi_l2_bound ν e he hs hmoment A hA
  rw [← Measure.infinitePi_map_pi μ hf] at hh
  have hobs : Measurable (fun ω : ∀ i, Ω i => fun i => f i (ω i)) :=
    Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i))
  simp only [Measure.real] at hh ⊢
  rw [Measure.map_apply hobs hA] at hh
  exact hh

lemma hybridEndpoint_sqrt_bound {Ω : ℕ → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) [∀ i, NeZero (b i)]
    (f : ∀ i, Ω i → Fin (b i)) (hf : ∀ i, Measurable (f i))
    (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (hs : Summable e)
    (hm : ∀ i, (b i : ℝ)* ∑ d, ((μ i).real (f i ⁻¹' {d}))^2 ≤ 1+e i)
    (A : Set CircleDigits.CircleX) (hA : MeasurableSet A) :
    (Measure.infinitePi μ).real ((fun ω => endpoint b (fun i => f i (ω i))) ⁻¹' A) ≤
      Real.exp ((∑' i, e i)/2) * Real.sqrt (volume.real A) := by
  have hh := observedDigits_sqrt_bound μ f hf e he hs hm ((endpoint b) ⁻¹' A)
    ((measurable_endpoint b) hA)
  have hp := (endpoint_measurePreserving hb).measure_preimage hA.nullMeasurableSet
  simp only [Measure.real,hp] at hh
  exact hh

end
open CircleDigits

lemma hybridEndpoint_absolutelyContinuous {Ω : ℕ → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) [∀ i, NeZero (b i)]
    (f : ∀ i, Ω i → Fin (b i)) (hf : ∀ i, Measurable (f i))
    (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (hs : Summable e)
    (hm : ∀ i, (b i : ℝ)* ∑ d, ((μ i).real (f i ⁻¹' {d}))^2 ≤ 1+e i) :
    Measure.map (fun ω => endpoint b (fun i => f i (ω i))) (Measure.infinitePi μ) ≪ volume := by
  have hobs : Measurable (fun ω : ∀ i, Ω i => endpoint b (fun i => f i (ω i))) :=
    (measurable_endpoint b).comp (Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i)))
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  rw [Measure.map_apply hobs hA]
  apply le_antisymm _ bot_le
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.zero_ne_top).mp
  have hh := hybridEndpoint_sqrt_bound μ hb f hf e he hs hm A hA
  simpa only [Measure.real,hzero,ENNReal.toReal_zero,Real.sqrt_zero,mul_zero] using hh

end
open CircleDigits

structure DigitSystem where
  b₀ : ℕ
  hb₀ : 2 ≤ b₀
  coord : ℕ → CoordinateParameters
namespace DigitSystem
variable (S : DigitSystem)
def radix : ℕ → ℕ | 0 => S.b₀ | n+1 => (S.coord n).l
lemma radix_ge_two (n : ℕ) : 2 ≤ S.radix n := by
  cases n with
  | zero => exact S.hb₀
  | succ n => have := (S.coord n).hl; have := (S.coord n).hm; change 2 ≤ (S.coord n).l; omega
instance (n : ℕ) : NeZero (S.radix n) := ⟨by have := S.radix_ge_two n; omega⟩
abbrev Sample (n : ℕ) := Option (Fin 5) × (Fin (S.radix n) × Fin (S.radix n))
abbrev Samples := ∀ n, S.Sample n

def law (tagged : ℕ → Bool) : (n : ℕ) → Measure (S.Sample n)
  | 0 => labelled none (diagonal (S.radix 0))
  | n+1 => (S.coord n).law (tagged n)
instance (tagged : ℕ → Bool) (n : ℕ) : IsProbabilityMeasure (S.law tagged n) := by
  cases n with
  | zero => change IsProbabilityMeasure (Measure.map _ _); infer_instance
  | succ n => exact (show IsProbabilityMeasure ((S.coord n).law (tagged n)) from inferInstance)
def probability (tagged : ℕ → Bool) : Measure S.Samples := Measure.infinitePi (S.law tagged)
instance (tagged : ℕ → Bool) : IsProbabilityMeasure (S.probability tagged) := by unfold probability; infer_instance

def observe (e : ℕ → Bool) (ω : S.Samples) : Digits S.radix := fun i => digitEndpoint (e i) (ω i).2
def endpoint (e : ℕ → Bool) (ω : S.Samples) : CircleDigits.CircleX := CircleDigits.endpoint S.radix (S.observe e ω)
lemma measurable_observe (e : ℕ → Bool) : Measurable (S.observe e) := by
  apply Measurable.of_eval
  intro i
  exact (digitEndpoint_measurable (e i)).comp (measurable_snd.comp (measurable_pi_apply i))
lemma measurable_endpoint (e : ℕ → Bool) : Measurable (S.endpoint e) :=
  (CircleDigits.measurable_endpoint _).comp (S.measurable_observe e)

def error (tagged : ℕ → Bool) : ℕ → ℝ
  | 0 => 0
  | n+1 => (60*(S.coord n).κ^2+10*(if tagged n then 1 else 0))/(S.coord n).m
lemma error_nonneg (tagged : ℕ → Bool) (n : ℕ) : 0 ≤ S.error tagged n := by
  cases n with
  | zero => exact le_refl 0
  | succ n => dsimp [error]; split <;> positivity
lemma moment (tagged : ℕ → Bool) (n : ℕ) (e : Bool) :
    (S.radix n:ℝ)*∑ d : Fin (S.radix n), ((S.law tagged n).real {ω | digitEndpoint e ω.2=d})^2 ≤
      1+S.error tagged n := by
  cases n with
  | zero =>
    have h (d : Fin (S.radix 0)) : (S.law tagged 0).real {ω | digitEndpoint e ω.2=d} = (S.radix 0:ℝ)⁻¹ := by
      rw [Measure.real,law,labelled_fiber _ _ _ (digitEndpoint_measurable e)]
      cases e
      · change ((diagonal (S.radix 0)) {z | z.1=d}).toReal = _
        simpa only [Set.preimage,Set.mem_singleton_iff,ENNReal.toReal_inv,ENNReal.toReal_natCast] using congrArg ENNReal.toReal (diagonal_fiber_fst (S.radix 0) d)
      · change ((diagonal (S.radix 0)) {z | z.2=d}).toReal = _
        simpa only [Set.preimage,Set.mem_singleton_iff,ENNReal.toReal_inv,ENNReal.toReal_natCast] using congrArg ENNReal.toReal (diagonal_fiber_snd (S.radix 0) d)
    simp only [h,error,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,add_zero]
    have hz : (S.radix 0:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (S.radix 0)
    field_simp
    norm_num
  | succ n => exact (S.coord n).law_second_moment (tagged n) e

lemma hybrid_sqrt_bound (tagged e : ℕ → Bool) (hs : Summable (S.error tagged))
    (A : Set CircleDigits.CircleX) (hA : MeasurableSet A) :
    (S.probability tagged).real (S.endpoint e ⁻¹' A) ≤
      Real.exp ((∑' n, S.error tagged n)/2)*Real.sqrt (volume.real A) :=
  hybridEndpoint_sqrt_bound (S.law tagged) S.radix_ge_two
    (fun i ω => digitEndpoint (e i) ω.2) (fun i => (digitEndpoint_measurable (e i)).comp measurable_snd)
    (S.error tagged) (S.error_nonneg tagged) hs (fun i => S.moment tagged i (e i)) A hA

lemma hybrid_ac (tagged e : ℕ → Bool) (hs : Summable (S.error tagged)) :
    Measure.map (S.endpoint e) (S.probability tagged) ≪ volume :=
  hybridEndpoint_absolutelyContinuous (S.law tagged) S.radix_ge_two
    (fun i ω => digitEndpoint (e i) ω.2) (fun i => (digitEndpoint_measurable (e i)).comp measurable_snd)
    (S.error tagged) (S.error_nonneg tagged) hs (fun i => S.moment tagged i (e i))

lemma ae_hybrid_gridFree (tagged e : ℕ → Bool) (hs : Summable (S.error tagged)) :
    ∀ᵐ ω ∂S.probability tagged, S.endpoint e ω ∈ gridFree S.radix := by
  have h := (S.hybrid_ac tagged e hs).ae_le (ae_gridFree S.radix S.radix_ge_two)
  exact (ae_map_iff (S.measurable_endpoint e).aemeasurable (by
    unfold gridFree
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun n => ((measurable_const_smul (denominator S.radix n)) (measurableSet_singleton 0)).compl))).mp h

lemma ae_digit_order (tagged : ℕ → Bool) :
    ∀ᵐ ω ∂S.probability tagged, ∀ i, (ω i).2.1 ≤ (ω i).2.2 := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ z ∂S.law tagged i, z.2.1 ≤ z.2.2 := by
    cases i with
    | zero =>
      apply ae_labelled _ _ _ (by measurability)
      unfold diagonal
      apply (ae_map_iff (by fun_prop) (by measurability)).mpr
      exact ae_of_all _ (fun _ => le_rfl)
    | succ n => exact (S.coord n).law_order (tagged n)
  exact (measurePreserving_eval_infinitePi (S.law tagged) i).quasiMeasurePreserving.ae h

lemma ae_coordinate_order (tagged : ℕ → Bool) (hs : Summable (S.error tagged)) :
    ∀ᵐ ω ∂S.probability tagged, ∀ i,
      ((AddCircle.measurableEquivIco 1 0 (denominator S.radix i • S.endpoint (fun _ => false) ω)).val : ℝ) ≤
      ((AddCircle.measurableEquivIco 1 0 (denominator S.radix i • S.endpoint (fun _ => true) ω)).val : ℝ) := by
  filter_upwards [S.ae_digit_order tagged,S.ae_hybrid_gridFree tagged (fun _ => false) hs,
    S.ae_hybrid_gridFree tagged (fun _ => true) hs] with ω hω hx hy
  intro i
  dsimp only [DigitSystem.endpoint] at hx hy ⊢
  rw [scaledTail_repr S.radix_ge_two _ hx,scaledTail_repr S.radix_ge_two _ hy]
  exact scaledTail_mono S.radix_ge_two hω i
end DigitSystem
end CircleCoupling

end

end OAI
