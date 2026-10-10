import Mathlib
import OAI.Probability.ParisiFinite.HorizonGrid

namespace OAI

/-! Innovation Euler Mem Lp. -/

noncomputable section

open MeasureTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace ParisiPath
open ProbabilityTheory
open scoped BigOperators ENNReal
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {Z : ℕ → Ω → ℝ}

lemma innovationEuler_memLp (hl : ∀ k,HasLaw (Z k) (gaussianReal 0 1) P)
    (b : Drift K M) (T : ℝ≥0) (n k : ℕ) {p : ℝ≥0∞} (hp : p≠∞) :
    MemLp (fun ω => innovationEuler b T n k (fun j => Z j ω)) p P := by
  let : IsProbabilityMeasure P := (hl 0).isProbabilityMeasure
  induction k with
  | zero => exact memLp_const 0
  | succ k ih =>
    have hi := scalar_euler_increment_memLp (hl k) M ((T:ℝ)*mesh n)
      (u := fun ω => b.val ((T:ℝ)*grid n k) (innovationEuler b T n k (fun j => Z j ω)))
      ((b.lipschitz ((T:ℝ)*grid n k)).continuous.measurable.comp_aemeasurable
        ih.aemeasurable) (fun ω => b.bound _ _) hp
    convert! ih.add hi using 1
    first | rfl | (funext ω; simp only [innovationEuler,Pi.add_apply];ring)

lemma CubicTest.integrable_comp (f : CubicTest) {X : Ω → ℝ}
    (hX : Integrable X P) [IsProbabilityMeasure P] : Integrable (fun ω => f.val (X ω)) P := by
  have hLip : LipschitzWith f.c1 (fun x => f.val x-f.val 0) := by
    intro x y
    simpa only [edist_sub_right] using f.lipschitz x y
  have h := hLip.comp_memLp (by simp) ((memLp_one_iff_integrable).mpr hX)
  have hh := (h.add (memLp_const (f.val 0))).integrable (by rfl : (1:ℝ≥0∞)≤1)
  convert! hh using 1
  ext ω
  simp only [Function.comp_def,Pi.add_apply,sub_add_cancel]

 
def generator (f : CubicTest) (b : Drift K M) (t x : ℝ) : ℝ :=
  deriv f.val x*b.val t x+(1/2:ℝ)*iteratedDeriv 2 f.val x

lemma generator_bound (f : CubicTest) (b : Drift K M) (t x : ℝ) :
    ‖generator f b t x‖≤(f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2 := by
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have h1 := mul_le_mul (f.bound1 x) (b.bound t x) (norm_nonneg _) f.c1.coe_nonneg
  have h2 := mul_le_mul_of_nonneg_left (f.bound2 x) (by norm_num : (0:ℝ)≤1/2)
  simp only [Real.norm_eq_abs] at h1 h2
  dsimp [generator]
  nlinarith

lemma mesh_le_one (n : ℕ) : mesh n≤1 := by
  dsimp [mesh]
  apply (div_le_one (by positivity)).mpr
  norm_num

lemma innovationEuler_generator_step (hZ : iIndepFun Z P)
    (hl : ∀ k,HasLaw (Z k) (gaussianReal 0 1) P)
    (b : Drift K M) (f : CubicTest) {T : ℝ≥0} (hT : T≤1) (n k : ℕ) :
    ‖((∫ ω,f.val (innovationEuler b T n (k+1) (fun j => Z j ω)) ∂P)-
      (∫ ω,f.val (innovationEuler b T n k (fun j => Z j ω)) ∂P))-
      ((T:ℝ)*mesh n)*(∫ ω,generator f b ((T:ℝ)*grid n k)
        (innovationEuler b T n k (fun j => Z j ω)) ∂P)‖≤
      (((T:ℝ)*mesh n)*Real.sqrt ((T:ℝ)*mesh n))*
        ((f.c3:ℝ)/6*thirdMomentBound M+(f.c2:ℝ)*(M:ℝ)^2/2) := by
  let : IsProbabilityMeasure P := (hl 0).isProbabilityMeasure
  have hi (k : ℕ) := f.integrable_comp (innovationEuler_memLp hl b T n k
    (p:=1) (by norm_num) |>.integrable le_rfl)
  have hδ : (T:ℝ)*mesh n≤1 := by
    exact (mul_le_mul (show (T:ℝ)≤1 from hT) (mesh_le_one n) (mesh_pos n).le
      (by norm_num)).trans_eq (by norm_num)
  have hh := weak_step_error (innovationEuler_aemeasurable (fun k => (hl k).aemeasurable) b T n k)
    (hl k) (innovationEuler_independent hZ (fun k => (hl k).aemeasurable) b T n k)
    f (b.lipschitz ((T:ℝ)*grid n k)).continuous.measurable M (b.bound ((T:ℝ)*grid n k))
    (mul_nonneg T.coe_nonneg (mesh_pos n).le) hδ
  rw [←integral_sub (hi (k+1)) (hi k)]
  simpa only [generator,innovationEuler,add_assoc] using hh

 
lemma innovationEuler_generator_sum (hZ : iIndepFun Z P)
    (hl : ∀ k,HasLaw (Z k) (gaussianReal 0 1) P)
    (b : Drift K M) (f : CubicTest) {T : ℝ≥0} (hT : T≤1) (n N : ℕ) :
    ‖((∫ ω,f.val (innovationEuler b T n N (fun j => Z j ω)) ∂P)-f.val 0)-
      ((T:ℝ)*mesh n)*(∑ k∈Finset.range N,∫ ω,generator f b ((T:ℝ)*grid n k)
        (innovationEuler b T n k (fun j => Z j ω)) ∂P)‖≤
      (N:ℝ)*(((T:ℝ)*mesh n)*Real.sqrt ((T:ℝ)*mesh n))*
        ((f.c3:ℝ)/6*thirdMomentBound M+(f.c2:ℝ)*(M:ℝ)^2/2) := by
  let : IsProbabilityMeasure P := (hl 0).isProbabilityMeasure
  have he : ((∫ ω,f.val (innovationEuler b T n N (fun j => Z j ω)) ∂P)-f.val 0)-
      ((T:ℝ)*mesh n)*(∑ k∈Finset.range N,∫ ω,generator f b ((T:ℝ)*grid n k)
        (innovationEuler b T n k (fun j => Z j ω)) ∂P)=
      ∑ k∈Finset.range N, (((∫ ω,f.val (innovationEuler b T n (k+1) (fun j => Z j ω)) ∂P)-
        (∫ ω,f.val (innovationEuler b T n k (fun j => Z j ω)) ∂P))-
        ((T:ℝ)*mesh n)*(∫ ω,generator f b ((T:ℝ)*grid n k)
          (innovationEuler b T n k (fun j => Z j ω)) ∂P)) := by
    rw [Finset.sum_sub_distrib,
      Finset.sum_range_sub (fun k => ∫ ω,f.val (innovationEuler b T n k (fun j => Z j ω)) ∂P),
      ←Finset.mul_sum]
    simp [innovationEuler]
  rw [he]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun k _ =>
    innovationEuler_generator_step hZ hl b f hT n k)).trans_eq (by simp;ring))

end ParisiPath

namespace ParisiPath
open ProbabilityTheory
open scoped BigOperators ENNReal
variable {K M : ℝ≥0}

 
def frozenEuler (b : Drift K M) (W : Path) (n : ℕ) (t : ℝ) : ℝ :=
  euler b W n ⌊t*(n+1:ℕ)⌋₊

lemma freeze_index_le (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ⌊t*(n+1:ℕ)⌋₊≤n+1 := by
  exact_mod_cast (Nat.floor_le (mul_nonneg ht.1 (by positivity))).trans
    (show t*(n+1:ℕ)≤(n+1:ℕ) by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ht.2 (Nat.cast_nonneg (n+1)))

lemma frozenEuler_tendsto (b : Drift K M) (W : Path)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ContinuousAt (fun s => b.val s (extend (solution b W) s)) t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => frozenEuler b W n t) atTop (𝓝 (extend (solution b W) t)) := by
  have h0 : Tendsto (fun n => frozenEuler b W n t-
      extend (solution b W) (freeze n t)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => euler_error_bound b W n _ (freeze_index_le n ht))
    simpa only [zero_mul] using (totalResidual_tendsto_zero b (solution b W) hc).mul_const
      (Real.exp (K:ℝ))
  have h1 := (continuous_extend (solution b W)).continuousAt.tendsto.comp (freeze_tendsto ht.1)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using h0.add h1

lemma reference_ae_continuous_of_joint (b : Drift K M)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ∀ x : ℝ, ContinuousAt (uncurry b.val) (t,x)) (X : Path) :
    ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ContinuousAt (fun s => b.val s (extend X s)) t := by
  filter_upwards [hc] with t ht hmem
  exact (ht hmem (extend X t)).comp (f := fun s : ℝ => (s,extend X s))
    (continuous_id.continuousAt.prodMk
    (continuous_extend X).continuousAt)

section Brownian
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

 
def brownianPath (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : Path :=
  ContinuousMap.mkD (fun t : Time => W ⟨t,t.property.1⟩ ω) 0

lemma brownianPath_eq_ae (hW : IsBrownianReal W P) :
    ∀ᵐ ω ∂P, ∀ t : Time, brownianPath W ω t = W ⟨t,t.property.1⟩ ω := by
  filter_upwards [hW.cont] with ω hω
  have hc : Continuous (fun t : Time => W ⟨t,t.property.1⟩ ω) :=
    hω.comp (continuous_subtype_val.subtype_mk _)
  intro t
  exact ContinuousMap.mkD_apply_of_continuous hc

lemma brownianPath_aemeasurable_eval (hW : IsBrownianReal W P) (t : Time) :
    AEMeasurable (fun ω => brownianPath W ω t) P :=
  (hW.aemeasurable ⟨t,t.property.1⟩).congr
    ((brownianPath_eq_ae hW).mono fun _ hω => (hω t).symm)

lemma innovationEuler_eq_euler (hW : IsBrownianReal W P) (b : Drift K M) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,k≤n+1 →
      innovationEuler b 1 n k (fun j => standardStep W 1 n j ω)=
        euler b (brownianPath W ω) n k := by
  filter_upwards [brownianPath_eq_ae hW,hW.eval_zero_ae_eq_zero] with ω hω h0
  intro k hk
  induction k with
  | zero =>
    simp only [innovationEuler,euler,extend_of_mem _ (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)]
    rw [hω]
    exact h0.symm
  | succ k ih =>
    rw [innovationEuler,euler,ih (by omega)]
    have hg (j : ℕ) (hj : j≤n+1) : extend (brownianPath W ω) (grid n j)=
        W (horizonGrid 1 n j) ω := by
      rw [extend_of_mem _ (grid_mem n j hj),hω]
      congr 1
      apply NNReal.coe_injective
      change grid n j=(1:ℝ)*grid n j
      ring
    rw [hg _ hk,hg _ (by omega)]
    simp only [NNReal.coe_one,one_mul,standardStep]
    have hs : Real.sqrt (mesh n)≠0 := (Real.sqrt_pos.mpr (mesh_pos n)).ne'
    field_simp
    ring

lemma brownian_solution_integrable (hW : IsBrownianReal W P) (b : Drift K M) (t : Time) :
    Integrable (fun ω => solution b (brownianPath W ω) t) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hd : Integrable (fun ω => solution b (brownianPath W ω) t-brownianPath W ω t) P :=
    Integrable.of_bound ((aemeasurable_solution_eval b (brownianPath W)
      (brownianPath_aemeasurable_eval hW) t).sub (brownianPath_aemeasurable_eval hW t)).aestronglyMeasurable
      ((M:ℝ)*(t:ℝ)) (ae_of_all _ fun ω => norm_solution_sub_driver b (brownianPath W ω) t)
  have hw : Integrable (fun ω => brownianPath W ω t) P :=
    (hW.integrable_eval ⟨t,t.property.1⟩).congr
      ((brownianPath_eq_ae hW).mono fun ω hω => (hω t).symm)
  convert! hd.add hw using 1
  ext ω
  simp only [Pi.add_apply,sub_add_cancel]

lemma generator_aemeasurable (hW : IsBrownianReal W P) (b : Drift K M) (f : CubicTest)
    (t : ℝ) : AEMeasurable (fun ω => generator f b t (extend (solution b (brownianPath W ω)) t)) P := by
  have hx := aemeasurable_solution_eval b (brownianPath W)
    (brownianPath_aemeasurable_eval hW) (projIcc 0 1 zero_le_one t)
  exact ((f.continuous_d1.measurable.comp_aemeasurable hx).mul
    ((b.lipschitz t).continuous.measurable.comp_aemeasurable hx)).add
    ((f.continuous_d2.measurable.comp_aemeasurable hx).const_mul (1/2:ℝ))

lemma generator_frozen_aemeasurable (hW : IsBrownianReal W P) (b : Drift K M) (f : CubicTest)
    (n : ℕ) (t : ℝ) : AEMeasurable (fun ω => generator f b (freeze n t)
      (frozenEuler b (brownianPath W ω) n t)) P := by
  have hx := aemeasurable_euler b (brownianPath W) (brownianPath_aemeasurable_eval hW)
    n ⌊t*(n+1:ℕ)⌋₊
  exact ((f.continuous_d1.measurable.comp_aemeasurable hx).mul
    ((b.lipschitz _).continuous.measurable.comp_aemeasurable hx)).add
    ((f.continuous_d2.measurable.comp_aemeasurable hx).const_mul (1/2:ℝ))

 
def expectedFrozenGenerator (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (b : Drift K M) (f : CubicTest) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ ω,generator f b (freeze n t) (frozenEuler b (brownianPath W ω) n t) ∂P

def expectedGenerator (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (b : Drift K M) (f : CubicTest) (t : ℝ) : ℝ :=
  ∫ ω,generator f b t (extend (solution b (brownianPath W ω)) t) ∂P

lemma expectedFrozenGenerator_measurable (b : Drift K M) (f : CubicTest) (n : ℕ) :
    Measurable (expectedFrozenGenerator P W b f n) :=
  (measurable_of_countable (f:=fun k : ℕ => ∫ ω,generator f b (grid n k)
    (euler b (brownianPath W ω) n k) ∂P)).comp (by fun_prop)

lemma expectedGenerator_bound (hW : IsBrownianReal W P) (b : Drift K M) (f : CubicTest) (t : ℝ) :
    ‖expectedGenerator P W b f t‖≤(f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2 := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (norm_integral_le_of_norm_le_const (ae_of_all _ fun ω => generator_bound f b t _)).trans_eq
    (by simp)

lemma expectedFrozenGenerator_bound (hW : IsBrownianReal W P) (b : Drift K M) (f : CubicTest) (n : ℕ) (t : ℝ) :
    ‖expectedFrozenGenerator P W b f n t‖≤(f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2 := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (norm_integral_le_of_norm_le_const (ae_of_all _ fun ω => generator_bound f b (freeze n t) _)).trans_eq
    (by simp)

lemma expectedFrozenGenerator_tendsto (hW : IsBrownianReal W P) (b : Drift K M) (f : CubicTest)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ∀ x : ℝ, ContinuousAt (uncurry b.val) (t,x)) :
    ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → Tendsto (fun n => expectedFrozenGenerator P W b f n t)
      atTop (𝓝 (expectedGenerator P W b f t)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  filter_upwards [hc] with t ht hmem
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)
    (fun n => (generator_frozen_aemeasurable hW b f n t).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω => generator_bound f b _ _)
  exact ae_of_all _ fun ω => by
    have hx := frozenEuler_tendsto b (brownianPath W ω)
      (reference_ae_continuous_of_joint b hc _) hmem
    have hd := (ht hmem _).tendsto.comp ((freeze_tendsto hmem.1).prodMk_nhds hx)
    exact ((f.continuous_d1.continuousAt.tendsto.comp hx).mul hd).add
      ((f.continuous_d2.continuousAt.tendsto.comp hx).const_mul (1/2:ℝ))

end Brownian
end ParisiPath

namespace ParisiPath
open ProbabilityTheory
open scoped BigOperators ENNReal
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma expectedFrozenGenerator_intervalIntegrable (hW : IsBrownianReal W P)
    (b : Drift K M) (f : CubicTest) (n : ℕ) (a c : ℝ) :
    IntervalIntegrable (expectedFrozenGenerator P W b f n) volume a c := by
  apply (intervalIntegrable_const (c := (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)).mono_fun'
    (expectedFrozenGenerator_measurable b f n).aestronglyMeasurable
  exact Eventually.of_forall fun t => expectedFrozenGenerator_bound hW b f n t

lemma expectedFrozenGenerator_integral_tendsto (hW : IsBrownianReal W P)
    (b : Drift K M) (f : CubicTest)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ∀ x : ℝ, ContinuousAt (uncurry b.val) (t,x)) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1, expectedFrozenGenerator P W b f n t)
      atTop (𝓝 (∫ t in (0:ℝ)..1,expectedGenerator P W b f t)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)
    (Eventually.of_forall fun n => (expectedFrozenGenerator_measurable b f n).aestronglyMeasurable.restrict)
    (Eventually.of_forall fun n => ae_of_all _ fun t _ => expectedFrozenGenerator_bound hW b f n t)
    (intervalIntegrable_const) ?_
  filter_upwards [expectedFrozenGenerator_tendsto hW b f hc] with t ht hmem
  rw [uIoc_of_le zero_le_one] at hmem
  exact ht ⟨hmem.1.le,hmem.2⟩

lemma freeze_index_on_cell (n k : ℕ) {t : ℝ}
    (ht : t ∈ Ico (grid n k) (grid n (k+1))) : ⌊t*(n+1:ℕ)⌋₊=k := by
  have h := freeze_on_cell n k ht
  dsimp only [freeze,grid] at h
  exact Nat.cast_injective (mul_right_cancel₀ (mesh_pos n).ne' h)

lemma expectedFrozenGenerator_cell_integral (_hW : IsBrownianReal W P)
    (b : Drift K M) (f : CubicTest) (n k : ℕ) :
    (∫ t in (grid n k)..(grid n (k+1)),expectedFrozenGenerator P W b f n t)=
      mesh n*(∫ ω,generator f b (grid n k) (euler b (brownianPath W ω) n k) ∂P) := by
  have hnot : ∀ᵐ s ∂volume,s≠grid n (k+1) := by simp [ae_iff,measure_singleton]
  calc
    _ = ∫ _ in (grid n k)..(grid n (k+1)),
        (∫ ω,generator f b (grid n k) (euler b (brownianPath W ω) n k) ∂P) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hnot] with t ht hmem
      rw [uIoc_of_le (grid_mono n (Nat.le_succ k))] at hmem
      have hcell : t∈Ico (grid n k) (grid n (k+1)) := ⟨hmem.1.le,hmem.2.lt_of_ne ht⟩
      simp only [expectedFrozenGenerator,frozenEuler,freeze_on_cell n k hcell,
        freeze_index_on_cell n k hcell]
    _ = _ := by rw [intervalIntegral.integral_const,grid_succ];simp

lemma expectedFrozenGenerator_integral_eq_sum (hW : IsBrownianReal W P)
    (b : Drift K M) (f : CubicTest) (n : ℕ) :
    (∫ t in (0:ℝ)..1,expectedFrozenGenerator P W b f n t)=
      mesh n*(∑ k∈Finset.range (n+1),∫ ω,generator f b (grid n k)
        (euler b (brownianPath W ω) n k) ∂P) := by
  rw [Finset.mul_sum]
  simp_rw [← expectedFrozenGenerator_cell_integral hW b f n]
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => expectedFrozenGenerator_intervalIntegrable hW b f n _ _),grid_zero,grid_end]

lemma brownianEuler_weak_error (hW : IsBrownianReal W P)
    (b : Drift K M) (f : CubicTest) (n : ℕ) :
    ‖(∫ ω,f.val (euler b (brownianPath W ω) n (n+1)) ∂P)-f.val 0-
      (∫ t in (0:ℝ)..1,expectedFrozenGenerator P W b f n t)‖≤
        Real.sqrt (mesh n)*((f.c3:ℝ)/6*thirdMomentBound M+(f.c2:ℝ)*(M:ℝ)^2/2) := by
  have he := innovationEuler_eq_euler hW b n
  have hh := innovationEuler_generator_sum (standardStep_independent hW 1 n)
    (standardStep_hasLaw hW (by norm_num : (0:ℝ≥0)<1) n) b f (by norm_num : (1:ℝ≥0)≤1) n (n+1)
  have hf : (∫ ω,f.val (innovationEuler b 1 n (n+1) (fun j => standardStep W 1 n j ω)) ∂P)=
      (∫ ω,f.val (euler b (brownianPath W ω) n (n+1)) ∂P) :=
    integral_congr_ae (he.mono fun ω hω => congrArg f.val (hω (n+1) le_rfl))
  have hg : (∑ k∈Finset.range (n+1),∫ ω,generator f b (grid n k)
      (innovationEuler b 1 n k (fun j => standardStep W 1 n j ω)) ∂P)=
      ∑ k∈Finset.range (n+1),∫ ω,generator f b (grid n k)
        (euler b (brownianPath W ω) n k) ∂P := by
    apply Finset.sum_congr rfl
    intro k hk
    exact integral_congr_ae (he.mono fun ω hω => congrArg (generator f b (grid n k))
      (hω k (Finset.mem_range.mp hk).le))
  simp only [NNReal.coe_one,one_mul] at hh
  rw [hf,hg,←expectedFrozenGenerator_integral_eq_sum hW b f n] at hh
  have hn : (n+1:ℕ)*mesh n=1 := grid_end n
  convert hh using 1
  rw [←mul_assoc,hn,one_mul]

lemma brownianEuler_integrable (hW : IsBrownianReal W P) (b : Drift K M) (n : ℕ) :
    Integrable (fun ω => euler b (brownianPath W ω) n (n+1)) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply (innovationEuler_memLp (standardStep_hasLaw hW (by norm_num : (0:ℝ≥0)<1) n)
    b 1 n (n+1) (p:=1) (by norm_num) |>.integrable le_rfl).congr
  exact (innovationEuler_eq_euler hW b n).mono fun ω hω => hω (n+1) le_rfl

lemma brownianEuler_expected_test_tendsto (hW : IsBrownianReal W P) (b : Drift K M) (f : CubicTest)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ∀ x : ℝ, ContinuousAt (uncurry b.val) (t,x)) :
    Tendsto (fun n => ∫ ω,f.val (euler b (brownianPath W ω) n (n+1)) ∂P) atTop
      (𝓝 (∫ ω,f.val (solution b (brownianPath W ω) ⟨1,by simp⟩) ∂P)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let X (ω : Ω) := solution b (brownianPath W ω) ⟨1,by simp⟩
  have hx : Integrable (fun ω => f.val (X ω)) P := f.integrable_comp (brownian_solution_integrable hW b _)
  have hn (n : ℕ) := f.integrable_comp (brownianEuler_integrable hW b n)
  have hlim : Tendsto (fun n => ∫ ω,(f.val (euler b (brownianPath W ω) n (n+1))-f.val (X ω)) ∂P)
      atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ:=P)
      (F:=fun n ω => f.val (euler b (brownianPath W ω) n (n+1))-f.val (X ω)) (f:=fun _=> (0:ℝ))
      (fun _ => (f.c1:ℝ)*(2*(M:ℝ))) (fun n => ((hn n).sub hx).aestronglyMeasurable)
      (integrable_const _) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · simpa only [integral_zero] using hh
    · calc
        _ ≤ (f.c1:ℝ)*‖euler b (brownianPath W ω) n (n+1)-X ω‖ := f.lipschitz.norm_sub_le _ _
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ f.c1.coe_nonneg
          simpa only [grid_end,extend_of_mem _ (show (1:ℝ)∈Icc (0:ℝ) 1 by simp),X] using
            euler_error_uniform_bound b (brownianPath W ω) n (n+1) le_rfl
    · have hs := euler_terminal_tendsto b (brownianPath W ω) (reference_ae_continuous_of_joint b hc _)
      have ht := (f.continuous.continuousAt.tendsto.comp hs).sub_const (f.val (X ω))
      simpa only [Function.comp_def,extend_of_mem _ (show (1:ℝ)∈Icc (0:ℝ) 1 by simp),X,sub_self] using ht
  simp_rw [integral_sub (hn _) hx] at hlim
  simpa only [sub_add_cancel,zero_add] using hlim.add_const (∫ ω,f.val (X ω) ∂P)

lemma mesh_tendsto_zero : Tendsto mesh atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1:ℝ)/(n+1:ℕ)) atTop (𝓝 0)
  simpa only [Nat.cast_add,Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))

 

theorem brownian_solution_generator_identity (hW : IsBrownianReal W P)
    (b : Drift K M) (f : CubicTest)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ∀ x : ℝ, ContinuousAt (uncurry b.val) (t,x)) :
    (∫ ω,f.val (solution b (brownianPath W ω) ⟨1,by simp⟩) ∂P)-f.val 0=
      ∫ t in (0:ℝ)..1,expectedGenerator P W b f t := by
  have he : Tendsto (fun n => (∫ ω,f.val (euler b (brownianPath W ω) n (n+1)) ∂P)-f.val 0-
        (∫ t in (0:ℝ)..1,expectedFrozenGenerator P W b f n t)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (brownianEuler_weak_error hW b f)
    simpa only [Real.sqrt_zero,zero_mul] using (mesh_tendsto_zero.sqrt).mul_const
      ((f.c3:ℝ)/6*thirdMomentBound M+(f.c2:ℝ)*(M:ℝ)^2/2)
  exact sub_eq_zero.mp (tendsto_nhds_unique
    (((brownianEuler_expected_test_tendsto hW b f hc).sub_const (f.val 0)).sub
      (expectedFrozenGenerator_integral_tendsto hW b f hc)) he)

end ParisiPath

open ContinuousLinearMap
open scoped Convolution
namespace ParisiPath
 
structure QuadraticTest where
  val : ℝ → ℝ
  d1 : ℝ → ℝ
  d2 : ℝ → ℝ
  hasD1 : ∀ x, HasDerivAt val (d1 x) x
  hasD2 : ∀ x, HasDerivAt d1 (d2 x) x
  continuousD2 : Continuous d2
  c1 : ℝ≥0
  c2 : ℝ≥0
  bound1 : ∀ x, ‖d1 x‖ ≤ c1
  bound2 : ∀ x, ‖d2 x‖ ≤ c2

namespace QuadraticTest
lemma continuous (f : QuadraticTest) : Continuous f.val :=
  continuous_iff_continuousAt.mpr fun x => (f.hasD1 x).continuousAt
lemma continuous_d1 (f : QuadraticTest) : Continuous f.d1 :=
  continuous_iff_continuousAt.mpr fun x => (f.hasD2 x).continuousAt
lemma lipschitz (f : QuadraticTest) : LipschitzWith f.c1 f.val := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (f.hasD1 x).differentiableAt)
  intro x
  rw [(f.hasD1 x).deriv]
  exact_mod_cast f.bound1 x
end QuadraticTest

def smoothConvolution (φ : ContDiffBump (0:ℝ)) (f : ℝ → ℝ) : ℝ → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ,volume] f

lemma smoothConvolution_eq (φ : ContDiffBump (0:ℝ)) (f : ℝ → ℝ) (x : ℝ) :
    smoothConvolution φ f x = ∫ z,φ.normed volume z * f (x-z) := rfl

lemma smoothConvolution_integrable (φ : ContDiffBump (0:ℝ)) {f : ℝ → ℝ}
    (hf : Continuous f) (x : ℝ) : Integrable (fun z => φ.normed volume z * f (x-z)) :=
  φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ) φ.continuous_normed
    hf.locallyIntegrable x

lemma hasDerivAt_smoothConvolution (φ : ContDiffBump (0:ℝ)) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x,HasDerivAt f (g x) x)
    {C : ℝ≥0} (hb : ∀ x,‖g x‖≤C) (x₀ : ℝ) :
    HasDerivAt (smoothConvolution φ f) (smoothConvolution φ g x₀) x₀ := by
  change HasDerivAt (fun x => ∫ z,φ.normed volume z * f (x-z))
    (∫ z,φ.normed volume z * g (x₀-z)) x₀
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball x₀ 1) (bound := fun z => φ.normed volume z * C)
    (F' := fun x z => φ.normed volume z*g (x-z))
    (Metric.ball_mem_nhds _ zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun x =>
      (φ.continuous_normed.mul (hf.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact smoothConvolution_integrable φ hf x₀
  · exact (φ.continuous_normed.mul (hg.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact ae_of_all _ fun z x _ => by
      rw [norm_mul,Real.norm_of_nonneg (φ.nonneg_normed z)]
      exact mul_le_mul_of_nonneg_left (hb _) (φ.nonneg_normed z)
  · exact φ.integrable_normed.mul_const _
  · exact ae_of_all _ fun z x _ => by
      convert! ((hd (x-z)).comp x ((hasDerivAt_id x).sub_const z)).const_mul
        (φ.normed volume z) using 1
      first | rfl | simp only [mul_one]

lemma smoothConvolution_bound (φ : ContDiffBump (0:ℝ)) {g : ℝ → ℝ}
    (hg : Continuous g) {C : ℝ≥0} (hb : ∀ x,‖g x‖≤C) (x : ℝ) :
    ‖smoothConvolution φ g x‖≤C := by
  rw [smoothConvolution_eq]
  calc
    _ ≤ ∫ z,‖φ.normed volume z*g (x-z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z,φ.normed volume z*C := by
      apply integral_mono (smoothConvolution_integrable φ hg x).norm
        (φ.integrable_normed.mul_const _)
      intro z
      dsimp only
      rw [norm_mul,Real.norm_of_nonneg (φ.nonneg_normed z)]
      exact mul_le_mul_of_nonneg_left (hb _) (φ.nonneg_normed z)
    _ = C := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma smoothConvolution_smooth (φ : ContDiffBump (0:ℝ)) {f : ℝ → ℝ}
    (hf : Continuous f) : ContDiff ℝ 3 (smoothConvolution φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
    hf.locallyIntegrable

lemma smoothConvolution_d1 (φ : ContDiffBump (0:ℝ)) (f : QuadraticTest) :
    deriv (smoothConvolution φ f.val)=smoothConvolution φ f.d1 := by
  funext x
  exact (hasDerivAt_smoothConvolution φ f.continuous f.continuous_d1 f.hasD1 f.bound1 x).deriv

lemma smoothConvolution_d2 (φ : ContDiffBump (0:ℝ)) (f : QuadraticTest) :
    iteratedDeriv 2 (smoothConvolution φ f.val)=smoothConvolution φ f.d2 := by
  rw [iteratedDeriv_succ,iteratedDeriv_one,smoothConvolution_d1]
  funext x
  exact (hasDerivAt_smoothConvolution φ f.continuous_d1 f.continuousD2 f.hasD2 f.bound2 x).deriv

lemma smoothConvolution_d3 (φ : ContDiffBump (0:ℝ)) (f : QuadraticTest) :
    iteratedDeriv 3 (smoothConvolution φ f.val)=
      (deriv (φ.normed volume) ⋆[lsmul ℝ ℝ,volume] f.d2) := by
  rw [show (3:ℕ)=2+1 by rfl,iteratedDeriv_succ,smoothConvolution_d2]
  funext x
  exact (φ.hasCompactSupport_normed.hasDerivAt_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed f.continuousD2.locallyIntegrable x).deriv

lemma smoothConvolution_d3_bound (φ : ContDiffBump (0:ℝ)) (f : QuadraticTest) (x : ℝ) :
    ‖iteratedDeriv 3 (smoothConvolution φ f.val) x‖≤
      (∫ z,‖deriv (φ.normed volume) z‖)*(f.c2:ℝ) := by
  rw [smoothConvolution_d3]
  change ‖∫ z,deriv (φ.normed volume) z*f.d2 (x-z)‖≤_
  have hkc : Continuous (deriv (φ.normed volume)) :=
    (φ.contDiff_normed (n:=1)).continuous_deriv (by norm_num)
  have hk := (φ.hasCompactSupport_normed (μ:=volume)).deriv
  calc
    _ ≤ ∫ z,‖deriv (φ.normed volume) z*f.d2 (x-z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z,‖deriv (φ.normed volume) z‖*(f.c2:ℝ) := by
      apply integral_mono
        (hk.convolutionExists_left (lsmul ℝ ℝ) hkc f.continuousD2.locallyIntegrable x).norm
        (hkc.integrable_of_hasCompactSupport hk |>.norm.mul_const _)
      intro z
      dsimp only
      rw [lsmul_apply,smul_eq_mul,norm_mul]
      exact mul_le_mul_of_nonneg_left (f.bound2 _) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

def QuadraticTest.mollify (f : QuadraticTest) (φ : ContDiffBump (0:ℝ)) : CubicTest where
  val := smoothConvolution φ f.val
  smooth := smoothConvolution_smooth φ f.continuous
  c1 := f.c1
  c2 := f.c2
  c3 := ⟨(∫ z,‖deriv (φ.normed volume) z‖)*(f.c2:ℝ),by positivity⟩
  bound1 := fun x => by simpa only [smoothConvolution_d1] using
    smoothConvolution_bound φ f.continuous_d1 f.bound1 x
  bound2 := fun x => by simpa only [smoothConvolution_d2] using
    smoothConvolution_bound φ f.continuousD2 f.bound2 x
  bound3 := smoothConvolution_d3_bound φ f

 
def shrinkingBump (n : ℕ) : ContDiffBump (0:ℝ) where
  rIn := (1:ℝ)/(n+1:ℕ)/2
  rOut := (1:ℝ)/(n+1:ℕ)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < (1:ℝ)/(n+1:ℕ) := by positivity
    linarith

lemma shrinkingBump_tendsto : Tendsto (fun n => (shrinkingBump n).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump,Nat.cast_add,Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))

lemma smoothConvolution_tendsto {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun n => smoothConvolution (shrinkingBump n) f x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto hf x

lemma smoothConvolution_error {C : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith C f)
    (φ : ContDiffBump (0:ℝ)) (x : ℝ) :
    ‖smoothConvolution φ f x-f x‖≤(C:ℝ)*φ.rOut := by
  rw [←dist_eq_norm]
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le C.coe_nonneg)

end ParisiPath

namespace ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma QuadraticTest.integrable_comp (f : QuadraticTest) {X : Ω → ℝ}
    (hX : Integrable X P) [IsProbabilityMeasure P] : Integrable (fun ω => f.val (X ω)) P := by
  have hLip : LipschitzWith f.c1 (fun x => f.val x-f.val 0) := by
    intro x y
    simpa only [edist_sub_right] using f.lipschitz x y
  have h := hLip.comp_memLp (by simp) ((memLp_one_iff_integrable).mpr hX)
  have hh := (h.add (memLp_const (f.val 0))).integrable (by rfl : (1:ℝ≥0∞)≤1)
  convert! hh using 1
  ext ω
  simp only [Function.comp_def,Pi.add_apply,sub_add_cancel]

lemma mollify_expected_test_tendsto (f : QuadraticTest) {X : Ω → ℝ}
    (hX : Integrable X P) [IsProbabilityMeasure P] :
    Tendsto (fun n => ∫ ω,(f.mollify (shrinkingBump n)).val (X ω) ∂P) atTop
      (𝓝 (∫ ω,f.val (X ω) ∂P)) := by
  have hn (n : ℕ) := (f.mollify (shrinkingBump n)).integrable_comp hX
  have hh := f.integrable_comp hX
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (show Tendsto (fun n => (f.c1:ℝ)*(shrinkingBump n).rOut) atTop (𝓝 0) from
      by simpa only [mul_zero] using shrinkingBump_tendsto.const_mul (f.c1:ℝ))
  rw [←integral_sub (hn n) hh]
  exact (norm_integral_le_of_norm_le_const (ae_of_all _ fun ω =>
    smoothConvolution_error f.lipschitz (shrinkingBump n) (X ω))).trans_eq (by simp)

lemma expectedGenerator_aestronglyMeasurable (hW : IsBrownianReal W P)
    (b : Drift K M) (f : CubicTest)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ∀ x : ℝ, ContinuousAt (uncurry b.val) (t,x)) :
    AEStronglyMeasurable (expectedGenerator P W b f) (volume.restrict (Ioc (0:ℝ) 1)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (expectedFrozenGenerator_measurable (P:=P) (W:=W) b f n).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_of_ae (expectedFrozenGenerator_tendsto hW b f hc),
    ae_restrict_mem measurableSet_Ioc] with t ht hmem
  exact ht ⟨hmem.1.le,hmem.2⟩

def generatorC2 (f : QuadraticTest) (b : Drift K M) (t x : ℝ) : ℝ :=
  f.d1 x*b.val t x+(1/2:ℝ)*f.d2 x

def expectedGeneratorC2 (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (b : Drift K M) (f : QuadraticTest) (t : ℝ) : ℝ :=
  ∫ ω,generatorC2 f b t (extend (solution b (brownianPath W ω)) t) ∂P

lemma mollify_generator_tendsto (b : Drift K M) (f : QuadraticTest) (t x : ℝ) :
    Tendsto (fun n => generator (f.mollify (shrinkingBump n)) b t x) atTop
      (𝓝 (generatorC2 f b t x)) := by
  simp only [generator,QuadraticTest.mollify,smoothConvolution_d1,smoothConvolution_d2]
  exact ((smoothConvolution_tendsto f.continuous_d1 x).mul_const (b.val t x)).add
    ((smoothConvolution_tendsto f.continuousD2 x).const_mul (1/2:ℝ))

lemma mollify_expectedGenerator_tendsto (hW : IsBrownianReal W P)
    (b : Drift K M) (f : QuadraticTest) (t : ℝ) :
    Tendsto (fun n => expectedGenerator P W b (f.mollify (shrinkingBump n)) t) atTop
      (𝓝 (expectedGeneratorC2 P W b f t)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)
    (fun n => (generator_aemeasurable hW b (f.mollify (shrinkingBump n)) t).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω => generator_bound _ b _ _)
  exact ae_of_all _ fun ω => mollify_generator_tendsto b f t _

lemma mollify_generator_integral_tendsto (hW : IsBrownianReal W P)
    (b : Drift K M) (f : QuadraticTest)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ∀ x : ℝ, ContinuousAt (uncurry b.val) (t,x)) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1,expectedGenerator P W b (f.mollify (shrinkingBump n)) t)
      atTop (𝓝 (∫ t in (0:ℝ)..1,expectedGeneratorC2 P W b f t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)
    (Eventually.of_forall fun n => ?_)
    (Eventually.of_forall fun n => ae_of_all _ fun t _ => expectedGenerator_bound hW b _ t)
    (intervalIntegrable_const) (ae_of_all _ fun t _ => mollify_expectedGenerator_tendsto hW b f t)
  rw [uIoc_of_le zero_le_one]
  exact expectedGenerator_aestronglyMeasurable hW b _ hc

 

theorem brownian_solution_generator_identity_C2 (hW : IsBrownianReal W P)
    (b : Drift K M) (f : QuadraticTest)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ∀ x : ℝ, ContinuousAt (uncurry b.val) (t,x)) :
    (∫ ω,f.val (solution b (brownianPath W ω) ⟨1,by simp⟩) ∂P)-f.val 0=
      ∫ t in (0:ℝ)..1,expectedGeneratorC2 P W b f t := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hv := mollify_expected_test_tendsto f (brownian_solution_integrable hW b ⟨1,by simp⟩)
  have h0 := smoothConvolution_tendsto f.continuous 0
  have he : (fun n => (∫ ω,(f.mollify (shrinkingBump n)).val
      (solution b (brownianPath W ω) ⟨1,by simp⟩) ∂P)-(f.mollify (shrinkingBump n)).val 0)=
      (fun n => ∫ t in (0:ℝ)..1,expectedGenerator P W b (f.mollify (shrinkingBump n)) t) := by
    funext n
    exact brownian_solution_generator_identity hW b _ hc
  exact tendsto_nhds_unique (hv.sub h0) (he ▸ mollify_generator_integral_tendsto hW b f hc)

end ParisiPath

end

end OAI
