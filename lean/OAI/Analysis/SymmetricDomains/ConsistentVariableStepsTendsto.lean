import Mathlib
import OAI.Analysis.SymmetricDomains.GeneratorDeterminantDerivZero

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (completeGeneratorSpace hU hc hbd Γ hhol))
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
include ha0 ham

theorem generatorDeterminant_flow_eq_one_of_fixed (p : U)
    (hfix : ∀ t, (a t).toHomeomorph p=p) (t : ℝ) :
    generatorDeterminant hU hc hbd Γ hhol b (a t)=1 := by
  let d := generatorDeterminant hU hc hbd Γ hhol b
  have hK := (bounded_divisible_automorphism_evaluation_proper hU hc.isPreconnected hbd Γ hhol p).isCompact_preimage (isCompact_singleton (x := p))
  obtain ⟨B,hB⟩ := (hK.image (generatorDeterminant_continuous hU hc hbd Γ hhol b)).bddAbove
  have hb (s : ℝ) : d (a s)≤B := hB ⟨a s,by simpa only [mem_preimage,mem_singleton_iff] using hfix s,rfl⟩
  have hp (s : ℝ) (k : ℕ) : d (a (k*s))=d (a s)^k := by
    induction k with
    | zero => simp only [Nat.cast_zero,zero_mul,ha0,map_one,pow_zero]
    | succ k hk => rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,ham,map_mul,hk,pow_succ]
  have hle (s : ℝ) : d (a s)≤1 := by
    by_contra hn
    obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt B (lt_of_not_ge hn)
    exact (not_lt_of_ge (hb (k*s))) (by rwa [hp])
  apply le_antisymm (hle t)
  have hm : d (a t)*d (a (-t))=1 := by rw [← map_mul,← ham,add_neg_cancel,ha0,map_one]
  have hn := generatorDeterminant_flow_pos hU hc hbd Γ hhol b a ham t
  nlinarith [hle (-t)]

include b in

theorem generator_trace_ad_eq_zero_of_fixed (p : U)
    (hfix : ∀ t, (a t).toHomeomorph p=p) :
    LinearMap.trace ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
      (LieAlgebra.ad ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
        (oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham))=0 := by
  have he : (fun t : ℝ => generatorDeterminant hU hc hbd Γ hhol b (a t))=fun _ => 1 := by
    funext t
    exact generatorDeterminant_flow_eq_one_of_fixed hU hc hbd Γ hhol b a ha0 ham p hfix t
  have hd := generatorDeterminant_hasDerivAt_zero hU hc hbd Γ hhol b a ha ha0 ham
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  exact neg_eq_zero.mp hz
end Biholomorph

open Set Filter Topology Metric
open scoped NNReal

theorem consistent_variable_steps_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} (l : Filter ι) [NeBot l]
    (q : ι → E → E) (h : ι → ℝ) (N : ι → ℕ) (X : E → E) (K : Set E)
    {L : ℝ≥0} (hL : LipschitzOnWith L X K)
    (hpos : ∀ i, 0≤h i) (hsmall : Tendsto h l (𝓝 0))
    (hcons : ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ x∈K,
      ‖q i x-x-h i • X x‖≤ε*h i)
    (p : E) (α : ℝ → E) {T t : ℝ} (hT : 0≤T) (hα0 : α 0=p)
    (hduration : ∀ i, (N i:ℝ)*h i≤T)
    (ht : Tendsto (fun i => (N i:ℝ)*h i) l (𝓝 t))
    (hαK : ∀ s∈Icc 0 T, α s∈K)
    (hαd : ∀ s∈Icc 0 T, HasStrictDerivAt α (X (α s)) s)
    (hαv : ∀ s∈Icc 0 T, ContinuousAt (fun s => X (α s)) s)
    (hit : ∀ᶠ i in l, ∀ j≤N i, ((q i)^[j]) p∈K) :
    Tendsto (fun i => ((q i)^[N i]) p) l (𝓝 (α t)) := by
  have hs (i : ι) {j : ℕ} (hj : j≤N i) : (j:ℝ)*h i∈Icc 0 T :=
    ⟨mul_nonneg (Nat.cast_nonneg _) (hpos i),
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (hpos i)).trans (hduration i)⟩
  have htmem : t∈Icc 0 T := isClosed_Icc.mem_of_tendsto ht
    (Eventually.of_forall fun i => hs i le_rfl)
  have hαt : Tendsto (fun i => α ((N i:ℝ)*h i)) l (𝓝 (α t)) :=
    (hαd t htmem).hasDerivAt.continuousAt.tendsto.comp ht
  have hdist : Tendsto (fun i => dist (((q i)^[N i]) p) (α ((N i:ℝ)*h i))) l (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun i => ha.trans_le (dist_nonneg)
    · intro η hη
      let C : ℝ := 2*T*Real.exp (L*T)
      have hC : 0≤C := by dsimp [C]; positivity
      let ε : ℝ := η/(C+1)
      have hε : 0<ε := div_pos hη (by linarith)
      have hεC : ε*C<η := by
        have he : ε*(C+1)=η := div_mul_cancel₀ η (by linarith)
        nlinarith
      have hy := hsmall.eventually (uniform_curve_taylor α (fun s => X (α s))
        (Icc 0 T) isCompact_Icc hαv hαd hε)
      filter_upwards [hcons ε hε,hy,hit] with i hqi hai hiti
      let x : ℕ → E := fun j => ((q i)^[j]) p
      let y : ℕ → E := fun j => α ((j:ℝ)*h i)
      have hxj (j : ℕ) (hj : j<N i) : x j∈K := hiti j hj.le
      have hyj (j : ℕ) (hj : j<N i) : y j∈K := hαK _ (hs i hj.le)
      have hxe (j : ℕ) (hj : j<N i) : ‖x (j+1)-x j-h i • X (x j)‖≤ε*|h i| := by
        simpa only [x,Function.iterate_succ_apply',abs_of_nonneg (hpos i)] using hqi (x j) (hxj j hj)
      have hye (j : ℕ) (hj : j<N i) : ‖y (j+1)-y j-h i • X (y j)‖≤ε*|h i| := by
        have he := hai ((j:ℝ)*h i) (hs i hj.le)
        have hj' : ((j+1:ℕ):ℝ)*h i=(j:ℝ)*h i+h i := by rw [Nat.cast_add,Nat.cast_one]; ring
        simpa only [y,hj'] using he
      have hv := finite_euler_comparison X K hL x y hε.le (by simp [x,y,hα0]) hxj hyj hxe hye
      have hb : (N i:ℝ)*(2*ε*|h i|)*Real.exp ((N i:ℝ)*L*|h i|)≤ε*C := by
        rw [abs_of_nonneg (hpos i)]
        have hE : (N i:ℝ)*L*h i≤L*T := by
          calc
            (N i:ℝ)*L*h i = L*((N i:ℝ)*h i) := by ring
            _ ≤ L*T := mul_le_mul_of_nonneg_left (hduration i) L.coe_nonneg
        have he : (N i:ℝ)*(2*ε*h i)≤2*ε*T := by
          nlinarith [mul_le_mul_of_nonneg_left (hduration i) (by positivity : 0≤2*ε)]
        calc
          _ ≤ (2*ε*T)*Real.exp (L*T) := mul_le_mul he (Real.exp_le_exp.mpr hE)
            (Real.exp_nonneg _) (by positivity)
          _ = ε*C := by dsimp [C]; ring
      simpa only [dist_eq_norm,x,y] using (hv.trans hb).trans_lt hεC
  exact hαt.congr_dist (by simpa only [dist_comm] using hdist)
end Release061

end

end OAI
