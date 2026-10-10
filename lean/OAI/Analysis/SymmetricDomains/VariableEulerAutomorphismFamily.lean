import Mathlib
import OAI.Analysis.SymmetricDomains.ConsistentVariableStepsTendsto

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

theorem floor_steps_tendsto {ι : Type*} (l : Filter ι) (h : ι → ℝ)
    (hp : ∀ i, 0<h i) (hh : Tendsto h l (𝓝 0)) {t : ℝ} (ht : 0≤t) :
    Tendsto (fun i => (⌊t/h i⌋₊ : ℝ)*h i) l (𝓝 t) := by
  have hle (i : ι) : (⌊t/h i⌋₊ : ℝ)*h i≤t := by
    exact (le_div_iff₀ (hp i)).mp (Nat.floor_le (div_nonneg ht (hp i).le))
  have hlt (i : ι) : t-(⌊t/h i⌋₊ : ℝ)*h i≤h i := by
    have hh' := (div_lt_iff₀ (hp i)).mp (Nat.lt_floor_add_one (t/h i))
    nlinarith
  have hzero : Tendsto (fun i => t-(⌊t/h i⌋₊ : ℝ)*h i) l (𝓝 0) :=
    squeeze_zero (fun i => sub_nonneg.mpr (hle i)) hlt hh
  have hconst : Tendsto (fun _ : ι => t) l (𝓝 t) := tendsto_const_nhds
  have hfinal := hconst.sub hzero
  simpa only [sub_sub_cancel,sub_zero] using hfinal

theorem iterate_displacement_of_bound {E : Type*} [NormedAddCommGroup E]
    (q : E → E) (p x : E) {R B : ℝ} {N : ℕ} (hB : 0≤B)
    (hsize : dist x p+(N:ℝ)*B≤R)
    (hstep : ∀ y∈closedBall p R, ‖q y-y‖≤B) :
    ∀ j≤N, dist ((q^[j]) x) p≤dist x p+(j:ℝ)*B := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hjN : j≤N := (Nat.le_succ j).trans hj
    have hi := ih hjN
    have hmem : (q^[j]) x∈closedBall p R := hi.trans
      ((add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjN) hB)).trans hsize)
    rw [Function.iterate_succ_apply']
    calc
      dist (q ((q^[j]) x)) p ≤ dist (q ((q^[j]) x)) ((q^[j]) x)+dist ((q^[j]) x) p := dist_triangle _ _ _
      _ ≤ B+(dist x p+(j:ℝ)*B) := add_le_add (by simpa only [dist_eq_norm] using hstep _ hmem) hi
      _ = dist x p+((j+1:ℕ):ℝ)*B := by rw [Nat.cast_add,Nat.cast_one]; ring

open Set Filter Topology Metric
open scoped NNReal
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem variable_Euler_automorphism_family (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0<h i) (hh : Tendsto h l (𝓝 0))
    (p : U) (X : Affine n → Affine n) {R r M T : ℝ}
    (hr : 0<r) (hM : 0≤M) (hT : 0<T) (hsize : r+M*T≤R)
    (hRU : closedBall p.val R⊆U) {L : ℝ≥0}
    (hL : LipschitzOnWith L X (closedBall p.val R))
    (hstep : ∀ᶠ i in l, ∀ y∈closedBall p.val R, ‖(q i).ambientAut y-y‖≤M*h i)
    (hcons : ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ y∈closedBall p.val R,
      ‖(q i).ambientAut y-y-h i • X y‖≤ε*h i)
    (α : Affine n → ℝ → Affine n)
    (hα0 : ∀ x∈closedBall p.val r, α x 0=x)
    (hα : ∀ x∈closedBall p.val r, ∀ t∈Icc 0 T,
      α x t∈closedBall p.val R ∧ HasStrictDerivAt (α x) (X (α x t)) t ∧
        ContinuousAt (fun s => X (α x s)) t)
    (hαc : ContinuousOn (fun z : Affine n × ℝ => α z.1 z.2) (closedBall p.val r ×ˢ Icc 0 T)) :
    ∃ g : ℝ → Biholomorph U U, g 0=1 ∧ ContinuousOn g (Icc 0 T) ∧
      (∀ t∈Icc 0 T, Tendsto (fun i => (q i)^⌊t/h i⌋₊) l (𝓝 (g t))) ∧
      ∀ x∈closedBall p.val r, ∀ t∈Icc 0 T, (g t).ambientAut x=α x t := by
  let N : ℝ → ι → ℕ := fun t i => ⌊t/h i⌋₊
  have hNt (t : ℝ) (ht : 0≤t) (i : ι) : (N t i:ℝ)*h i≤t :=
    (le_div_iff₀ (hp i)).mp (Nat.floor_le (div_nonneg ht (hp i).le))
  have hNr {t : ℝ} (ht : t∈Icc 0 T) {i : ι} {j : ℕ} (hj : j≤N t i) : (j:ℝ)*(M*h i)≤M*T := by
    calc
      (j:ℝ)*(M*h i) = M*((j:ℝ)*h i) := by ring
      _ ≤ M*T := mul_le_mul_of_nonneg_left
        (((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (hp i).le).trans (hNt t ht.1 i)).trans ht.2) hM
  have hrR : r≤R := (le_add_of_nonneg_right (mul_nonneg hM hT.le)).trans hsize
  have hball : closedBall p.val r⊆U := (closedBall_subset_closedBall hrR).trans hRU
  have hit (x : Affine n) (hx : x∈closedBall p.val r) (t : ℝ) (ht : t∈Icc 0 T) :
      ∀ᶠ i in l, ∀ j≤N t i, (((q i).ambientAut)^[j]) x∈closedBall p.val R := by
    filter_upwards [hstep] with i hi
    intro j hj
    have hb : 0≤M*h i := mul_nonneg hM (hp i).le
    have hn : dist x p.val+(N t i:ℝ)*(M*h i)≤R :=
      (add_le_add (mem_closedBall.mp hx) (hNr ht le_rfl)).trans hsize
    exact (iterate_displacement_of_bound (q i).ambientAut p.val x hb hn hi j hj).trans
      ((add_le_add (mem_closedBall.mp hx) (hNr ht hj)).trans hsize)
  have htend (x : Affine n) (hx : x∈closedBall p.val r) (t : ℝ) (ht : t∈Icc 0 T) :
      Tendsto (fun i => ((q i).ambientAut^[N t i]) x) l (𝓝 (α x t)) := by
    exact consistent_variable_steps_tendsto l (fun i => (q i).ambientAut) h (N t) X _ hL
      (fun i => (hp i).le) hh hcons x (α x) hT.le (hα0 x hx)
      (fun i => (hNt t ht.1 i).trans ht.2) (floor_steps_tendsto l h hp hh ht.1)
      (fun s hs => (hα x hx s hs).1) (fun s hs => (hα x hx s hs).2.1)
      (fun s hs => (hα x hx s hs).2.2) (hit x hx t ht)
  let V : Set U := Subtype.val ⁻¹' closedBall p.val R
  have hV : IsCompact V := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    simpa only [V,image_preimage_eq_inter_range,Subtype.range_coe_subtype,ofPred_mem_eq,
      inter_eq_left.mpr hRU] using isCompact_closedBall p.val R
  let K : Set (Biholomorph U U) := (fun e : Biholomorph U U => e.toHomeomorph p) ⁻¹' V
  have hK : IsCompact K :=
    (bounded_divisible_automorphism_evaluation_proper hU hc hbd Γ hhol p).isCompact_preimage hV
  have hpow (t : ℝ) (ht : t∈Icc 0 T) : ∀ᶠ i in l, (q i)^(N t i)∈K := by
    filter_upwards [hit p.val (mem_closedBall_self hr.le) t ht] with i hi
    have he := hi (N t i) le_rfl
    change ((q i)^(N t i)).toHomeomorph p∈V
    change (((q i)^(N t i)).toHomeomorph p).val∈closedBall p.val R
    simpa only [ambientAut_iterate] using he
  have hex (t : ℝ) : ∃ e : Biholomorph U U, t∈Icc 0 T →
      Tendsto (fun i => (q i)^(N t i)) l (𝓝 e) ∧
      EqOn e.ambientAut (fun x => α x t) (closedBall p.val r) := by
    by_cases ht : t∈Icc 0 T
    · obtain ⟨e,he,heq⟩ := exists_tendsto_of_compact_local_pointwise hU hc l
        (fun i => (q i)^(N t i)) K hK (hpow t ht) p hr hball (fun x => α x t) (by
          intro x hx
          simpa only [ambientAut_iterate (p := ⟨x,hball hx⟩),ambientAut_apply (p := ⟨x,hball hx⟩)] using htend x hx t ht)
      exact ⟨e,fun _ => ⟨he,heq⟩⟩
    · exact ⟨1,fun h => (ht h).elim⟩
  choose g hg using hex
  have hgK (t : ℝ) (ht : t∈Icc 0 T) : g t∈K := hK.isClosed.mem_of_tendsto (hg t ht).1 (hpow t ht)
  have hg0 : g 0=1 := by
    have he := (hg 0 ⟨le_rfl,hT.le⟩).1
    have he' : Tendsto (fun _ : ι => (1 : Biholomorph U U)) l (𝓝 (g 0)) := by simpa only [N,zero_div,Nat.floor_zero,pow_zero] using he
    exact tendsto_nhds_unique he' tendsto_const_nhds
  have hgc : ContinuousOn g (Icc 0 T) := by
    intro t ht
    have : NeBot (𝓝[Icc 0 T] t) := nhdsWithin_neBot_of_mem ht
    have hv (x : Affine n) (hx : x∈closedBall p.val r) :
        Tendsto (fun s => (g s).ambientAut x) (𝓝[Icc 0 T] t) (𝓝 (α x t)) := by
      have hpath : ContinuousOn (fun s => α x s) (Icc 0 T) := hαc.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hx,hs⟩)
      apply (hpath t ht).tendsto.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact ((hg s hs).2 hx).symm
    obtain ⟨e,he,heq⟩ := exists_tendsto_of_compact_local_pointwise hU hc
      (𝓝[Icc 0 T] t) g K hK (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact hgK s hs) p hr hball (fun x => α x t) hv
    have hegt : e=g t := eq_of_ambientAut_eventuallyEq hU hc p (by
      filter_upwards [closedBall_mem_nhds p.val hr] with x hx
      exact (heq hx).trans ((hg t ht).2 hx).symm)
    change Tendsto g (𝓝[Icc 0 T] t) (𝓝 (g t))
    rwa [hegt] at he
  exact ⟨g,hg0,hgc,(fun t ht => (hg t ht).1),(fun x hx t ht => (hg t ht).2 hx)⟩
end Biholomorph
end Release061

end

end OAI
