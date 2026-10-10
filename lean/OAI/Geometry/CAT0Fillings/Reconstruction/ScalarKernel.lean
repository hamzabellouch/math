import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Negation
import OAI.Geometry.CAT0Fillings.Currents.Addition
import OAI.Geometry.CAT0Fillings.Slices.Approximation

namespace OAI

section

open Set Filter Metric TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction

noncomputable def realCone (φ : ℝ → ℝ) (K : ℝ≥0) (q : ℝ) (x : ℝ) : ℝ :=
  φ q + (K : ℝ)*dist x q

lemma realCone_lipschitz (φ : ℝ → ℝ) (K : ℝ≥0) (q : ℝ) :
    LipschitzWith K (realCone φ K q) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [realCone,Real.dist_eq,add_sub_add_left_eq_sub,←mul_sub,
    abs_mul,abs_of_nonneg K.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub _ _ |>.trans_eq
    (by congr 1; ring)) K.coe_nonneg

noncomputable def coneApprox (φ : ℝ → ℝ) (K : ℝ≥0) : ℕ → ℝ → ℝ
  | 0 => realCone φ K (denseSeq ℝ 0)
  | n+1 => fun x => min (coneApprox φ K n x) (realCone φ K (denseSeq ℝ (n+1)) x)

lemma coneApprox_lipschitz (φ : ℝ → ℝ) (K : ℝ≥0) (n : ℕ) :
    LipschitzWith K (coneApprox φ K n) := by
  induction n with
  | zero => exact realCone_lipschitz φ K _
  | succ n ih => simpa only [coneApprox,max_self] using ih.min (realCone_lipschitz φ K _)

lemma le_coneApprox {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (n : ℕ) (x : ℝ) :
    φ x ≤ coneApprox φ K n x := by
  induction n with
  | zero => exact hφ.le_add_mul _ _
  | succ n ih => exact le_min ih (hφ.le_add_mul _ _)

lemma coneApprox_antitone (φ : ℝ → ℝ) (K : ℝ≥0) (x : ℝ) :
    Antitone (fun n => coneApprox φ K n x) :=
  antitone_nat_of_succ_le fun _ => min_le_left _ _

lemma coneApprox_le_cone (φ : ℝ → ℝ) (K : ℝ≥0) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    coneApprox φ K n x ≤ realCone φ K (denseSeq ℝ m) x := by
  apply (coneApprox_antitone φ K x hm).trans
  cases m with
  | zero => exact le_rfl
  | succ m => exact min_le_right _ _

lemma coneApprox_tendsto {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (x : ℝ) :
    Tendsto (fun n => coneApprox φ K n x) atTop (𝓝 (φ x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (le_coneApprox hφ n x)
  · intro b hb
    have hD : 0 < 2*(K : ℝ)+1 := by positivity
    obtain ⟨m,hm⟩ := (denseRange_denseSeq ℝ).exists_dist_lt x (div_pos (sub_pos.mpr hb) hD)
    filter_upwards [eventually_ge_atTop m] with n hn
    have hcone := coneApprox_le_cone φ K hn x
    have hq := hφ.le_add_mul (denseSeq ℝ m) x
    rw [dist_comm (denseSeq ℝ m) x] at hq
    have hdist : dist x (denseSeq ℝ m) < (b-φ x)/(2*(K : ℝ)+1) := by
      simpa only [dist_comm] using hm
    have hsmall := (lt_div_iff₀ hD).mp hdist
    dsimp only [realCone] at hcone
    nlinarith [dist_nonneg (x := x) (y := denseSeq ℝ m)]

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients

lemma scalar_update {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] (u v : X → ℝ) :
    Function.update (fun _ : Fin 1 => u) 0 v = fun _ : Fin 1 => v := by
  funext i
  fin_cases i
  simp

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {T : Functional X 1} (μ : Measure X) [IsFiniteMeasure μ]

def ScalarKernel (hT : IsMetricCurrent T) (u : X → ℝ) : Prop :=
  ∀ (f : X → ℝ), Integrable f μ → borelAction μ hT f (fun _ : Fin 1 => u) = 0

lemma ScalarKernel.const (hT : IsMetricCurrent T) (hμ : Controls T μ) (c : ℝ) :
    ScalarKernel μ hT (fun _ => c) := by
  intro f hf
  exact borelAction_const_coord μ hT hμ hf _ (fun _ => ⟨0,LipschitzWith.const c⟩) 0 c (fun _ => rfl)

lemma ScalarKernel.linear {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {u v : X → ℝ} (hu : ∃ K, LipschitzWith K u) (hv : ∃ K, LipschitzWith K v)
    (hku : ScalarKernel μ hT u) (hkv : ScalarKernel μ hT v) (a c : ℝ) :
    ScalarKernel μ hT (fun x => a*u x+c*v x) := by
  intro f hf
  have hh := borelAction_linearCoord μ hT hμ hf (fun _ : Fin 1 => u) (fun _ => hu) 0 v hv a c
  rw [scalar_update,scalar_update,hku f hf,hkv f hf] at hh
  simpa using hh

lemma ScalarKernel.min {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {u v : X → ℝ} (hu : ∃ K, LipschitzWith K u) (hv : ∃ K, LipschitzWith K v)
    (hku : ScalarKernel μ hT u) (hkv : ScalarKernel μ hT v) :
    ScalarKernel μ hT (fun x => Min.min (u x) (v x)) := by
  obtain ⟨K,hK⟩ := hu
  obtain ⟨L,hL⟩ := hv
  intro f hf
  let E := {x | u x ≤ v x}
  have hE : MeasurableSet E := measurableSet_le hK.continuous.measurable hL.continuous.measurable
  have hπ : ∀ j : Fin 1, ∃ M, LipschitzWith M (fun x => Min.min (u x) (v x)) :=
    fun _ => ⟨Max.max K L,hK.min hL⟩
  have h1 := borelAction_congr_coord_on_support μ hT hμ (hf.indicator hE)
    (fun _ : Fin 1 => fun x => Min.min (u x) (v x)) hπ 0 u ⟨K,hK⟩ (by
      intro x hx
      have hxE : x ∈ E := by
        by_contra hh
        exact hx (indicator_of_notMem hh _)
      exact min_eq_left hxE)
  have h2 := borelAction_congr_coord_on_support μ hT hμ (hf.indicator hE.compl)
    (fun _ : Fin 1 => fun x => Min.min (u x) (v x)) hπ 0 v ⟨L,hL⟩ (by
      intro x hx
      have hxE : x ∈ Eᶜ := by
        by_contra hh
        exact hx (indicator_of_notMem hh _)
      exact min_eq_right (le_of_not_ge hxE))
  rw [scalar_update,hku _ (hf.indicator hE)] at h1
  rw [scalar_update,hkv _ (hf.indicator hE.compl)] at h2
  have heq : f = fun x => E.indicator f x+Eᶜ.indicator f x := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [heq]
  change borelAction μ hT (E.indicator f + Eᶜ.indicator f) (fun _ => fun x => Min.min (u x) (v x)) = 0
  rw [borelAction_add μ hT (hf.indicator hE) (hf.indicator hE.compl) _ hπ,h1,h2]
  simp

lemma ScalarKernel.neg {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {u : X → ℝ} (hu : ∃ K, LipschitzWith K u) (hku : ScalarKernel μ hT u) :
    ScalarKernel μ hT (fun x => -u x) := by
  simpa using hku.linear μ hμ hu hu hku (-1) 0

lemma ScalarKernel.max {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {u v : X → ℝ} (hu : ∃ K, LipschitzWith K u) (hv : ∃ K, LipschitzWith K v)
    (hku : ScalarKernel μ hT u) (hkv : ScalarKernel μ hT v) :
    ScalarKernel μ hT (fun x => Max.max (u x) (v x)) := by
  have hnu : ∃ K, LipschitzWith K (fun x => -u x) := ⟨hu.choose,hu.choose_spec.neg⟩
  have hnv : ∃ K, LipschitzWith K (fun x => -v x) := ⟨hv.choose,hv.choose_spec.neg⟩
  have hm := (hku.neg μ hμ hu).min μ hμ hnu hnv (hkv.neg μ hμ hv)
  have hLm : ∃ K, LipschitzWith K (fun x => Min.min (-u x) (-v x)) :=
    ⟨Max.max hnu.choose hnv.choose,hnu.choose_spec.min hnv.choose_spec⟩
  convert hm.neg μ hμ hLm using 1
  funext x
  by_cases hx : u x ≤ v x
  · simp only [max_eq_right hx,min_eq_right (neg_le_neg hx),neg_neg]
  · have hx' := le_of_not_ge hx
    simp only [max_eq_left hx',min_eq_left (neg_le_neg hx'),neg_neg]

lemma ScalarKernel.limit {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {us : ℕ → X → ℝ} {u : X → ℝ} (hs : ∀ n, ScalarKernel μ hT (us n))
    {K : ℝ≥0} (hK : ∀ n, LipschitzWith K (us n))
    (hlim : ∀ x, Tendsto (fun n => us n x) atTop (𝓝 (u x))) : ScalarKernel μ hT u := by
  intro f hf
  have ht := borelAction_sequentialContinuity μ hT hμ hf (fun _ : Fin 1 => u)
    (fun n _ => us n) (fun _ => ⟨K,hK⟩) (fun _ x => hlim x)
  simp only [hs _ f hf] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma ScalarKernel.cone {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {u : X → ℝ} (hu : ∃ L, LipschitzWith L u) (hku : ScalarKernel μ hT u)
    (φ : ℝ → ℝ) (K : ℝ≥0) (q : ℝ) :
    ScalarKernel μ hT (fun x => realCone φ K q (u x)) := by
  let v₁ : X → ℝ := fun x => (K : ℝ)*u x+1*(φ q-(K : ℝ)*q)
  let v₂ : X → ℝ := fun x => -(K : ℝ)*u x+1*(φ q+(K : ℝ)*q)
  have h₁ : ScalarKernel μ hT v₁ := hku.linear μ hμ hu
    ⟨0,LipschitzWith.const _⟩ (ScalarKernel.const μ hT hμ _) K 1
  have h₂ : ScalarKernel μ hT v₂ := hku.linear μ hμ hu
    ⟨0,LipschitzWith.const _⟩ (ScalarKernel.const μ hT hμ _) (-K) 1
  have hL₁ : ∃ L, LipschitzWith L v₁ :=
    ⟨_,(lipschitz_mul_real hu.choose_spec K).add (LipschitzWith.const _)⟩
  have hL₂ : ∃ L, LipschitzWith L v₂ :=
    ⟨_,(lipschitz_mul_real hu.choose_spec (-K)).add (LipschitzWith.const _)⟩
  have hm := h₁.max μ hμ hL₁ hL₂ h₂
  convert hm using 1
  funext x
  dsimp [realCone,v₁,v₂]
  rw [Real.dist_eq]
  by_cases hx : 0 ≤ u x-q
  · rw [abs_of_nonneg hx,max_eq_left (by nlinarith [K.coe_nonneg])]
    ring
  · rw [abs_of_neg (lt_of_not_ge hx),max_eq_right (by nlinarith [K.coe_nonneg])]
    ring

lemma ScalarKernel.comp {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (hku : ScalarKernel μ hT u)
    {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ScalarKernel μ hT (fun x => φ (u x)) := by
  have hs : ∀ n, ScalarKernel μ hT (fun x => coneApprox φ K n (u x)) := by
    intro n
    induction n with
    | zero => exact hku.cone μ hμ ⟨L,hu⟩ φ K _
    | succ n ih =>
      exact ih.min μ hμ ⟨K*L,(coneApprox_lipschitz φ K n).comp hu⟩
        ⟨K*L,(realCone_lipschitz φ K _).comp hu⟩ (hku.cone μ hμ ⟨L,hu⟩ φ K _)
  exact ScalarKernel.limit μ hμ hs (fun n => (coneApprox_lipschitz φ K n).comp hu)
    (fun x => coneApprox_tendsto hφ (u x))

lemma ScalarKernel.of_boundedLip {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {u : X → ℝ} (hu : ∃ L, LipschitzWith L u)
    (hz : ∀ b, BoundedLip b → T b (fun _ : Fin 1 => u) = 0) : ScalarKernel μ hT u := by
  intro f hf
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation μ hf
  have ht := borelAction_tendsto μ hT hμ hf
    (fun n => integrable_boundedLip μ (g n).property) hg (fun _ : Fin 1 => u) (fun _ => hu)
  have he (n : ℕ) : borelAction μ hT (g n).val (fun _ : Fin 1 => u) = 0 := by
    rw [borelAction_eq μ hT hμ ⟨(g n).property,fun _ => hu⟩]
    exact hz (g n).val (g n).property
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem current_eq_zero_on_scalar_graph {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {D : Set ℝ} (hD : IsCompact D) (γ : D → X) {L : ℝ≥0} (hγ : LipschitzWith L γ)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (hbase : ∀ t : D, u (γ t) = t)
    (hsupp : μ (Set.range γ)ᶜ = 0)
    (hz : ∀ b, BoundedLip b → T b (fun _ : Fin 1 => u) = 0) : T = fun _ _ => 0 := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  have hE : MeasurableSet (Set.range γ) := (isCompact_range hγ.continuous).measurableSet
  have hker := ScalarKernel.of_boundedLip μ (hT := hT) hμ ⟨K,hu⟩ hz
  funext b π
  by_cases hab : Admissible b π
  · obtain ⟨J,hJ⟩ := hab.2 0
    let g : ℝ → ℝ := fun t => if ht : t ∈ D then π 0 (γ ⟨t,ht⟩) else 0
    have hg : LipschitzOnWith (J*L) g D := by
      apply LipschitzOnWith.of_dist_le_mul
      intro s hs t ht
      simpa only [g,dite_eq_left hs,dite_eq_left ht,Subtype.dist_eq,Function.comp_apply] using
        (hJ.comp hγ).dist_le_mul ⟨s,hs⟩ ⟨t,ht⟩
    obtain ⟨φ,hφ,heq⟩ := hg.extend_real
    have he : ∀ t : D, φ t = π 0 (γ t) := by
      intro t
      simpa only [g,dite_eq_left t.property] using (heq t.property).symm
    have hπeq : π = fun _ : Fin 1 => π 0 := by
      funext i
      fin_cases i
      rfl
    rw [hπeq]
    have hb := integrable_boundedLip μ hab.1
    have hbE := hb.indicator hE
    have hbe : (Set.range γ).indicator b =ᵐ[μ] b := by
      filter_upwards [show ∀ᵐ x ∂μ, x ∈ Set.range γ from ae_iff.mpr hsupp] with x hx
      exact indicator_of_mem hx _
    rw [←borelAction_eq μ hT hμ ⟨hab.1,fun _ => ⟨J,hJ⟩⟩,
      ←borelAction_congr_ae μ hT hbe]
    have hc := borelAction_congr_coord_on_support μ hT hμ hbE (fun _ : Fin 1 => π 0)
      (fun _ => ⟨J,hJ⟩) 0 (fun x => φ (u x)) ⟨(J*L)*K,hφ.comp hu⟩ (by
        intro x hx
        have hxE : x ∈ Set.range γ := by
          by_contra hh
          exact hx (indicator_of_notMem hh _)
        obtain ⟨t,rfl⟩ := hxE
        rw [hbase t,he t])
    rw [scalar_update] at hc
    exact hc.trans ((hker.comp μ hμ hu hφ) _ hbE)
  · exact hT.offDomain b π hab

theorem current_eq_on_scalar_graph {U : Functional X 1}
    (hT : IsMetricCurrent T) (hU : IsMetricCurrent U)
    (hμ : Controls T μ) (ν : Measure X) [IsFiniteMeasure ν] (hν : Controls U ν)
    {D : Set ℝ} (hD : IsCompact D) (γ : D → X) {L : ℝ≥0} (hγ : LipschitzWith L γ)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (hbase : ∀ t : D, u (γ t) = t)
    (hsupp : μ (Set.range γ)ᶜ = 0) (hsupp' : ν (Set.range γ)ᶜ = 0)
    (hbaseact : ∀ b, BoundedLip b → T b (fun _ : Fin 1 => u) = U b (fun _ => u)) :
    T = U := by
  have hd : IsMetricCurrent (T + -U) := hT.add hU.neg
  have hc : Controls (T + -U) (μ+ν) := controls_add hμ (controls_neg_iff.mpr hν)
  have hz := current_eq_zero_on_scalar_graph (μ+ν) (hT := hd) hc hD γ hγ hu hbase
    (by simp only [Measure.add_apply,hsupp,hsupp',add_zero]) (by
      intro b hb
      change T b (fun _ => u) + -U b (fun _ => u) = 0
      rw [hbaseact b hb]
      exact add_neg_cancel _)
  funext b π
  have he := congrFun (congrFun hz b) π
  change T b π + -U b π = 0 at he
  linarith

end CAT0Fillings.SliceReconstruction
end

end OAI
