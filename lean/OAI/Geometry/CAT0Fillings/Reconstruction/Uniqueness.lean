import Mathlib
import OAI.Geometry.CAT0Fillings.Slices.JointKernel
import OAI.Geometry.CAT0Fillings.BV.JointPoincare

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.BorelCoefficients
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

lemma borelAction_congr_coords_on_support (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π ρ : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (heq : ∀ i x, x ∈ Function.support f → π i x = ρ i x) :
    borelAction μ hT f π = borelAction μ hT f ρ := by
  classical
  let mix (s : Finset (Fin k)) := fun i => if i ∈ s then ρ i else π i
  have hmix (s : Finset (Fin k)) : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (mix s i) := by
    intro i
    by_cases hi : i ∈ s
    · simpa only [mix,ite_eq_left hi] using hρ i
    · simpa only [mix,ite_eq_right hi] using hπ i
  have hs (s : Finset (Fin k)) : borelAction μ hT f π = borelAction μ hT f (mix s) := by
    induction s using Finset.induction_on with
    | empty => simp only [mix,Finset.notMem_empty,ite_false]
    | @insert i s hi ih =>
      have he := borelAction_congr_coord_on_support μ hT hμ hf (mix s) (hmix s) i (ρ i) (hρ i) (by
        intro x hx
        simpa only [mix,ite_eq_right hi] using heq i x hx)
      have hu : Function.update (mix s) i (ρ i) = mix (insert i s) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [mix]
        · simp [mix,hj]
      rw [hu] at he
      exact ih.trans he
  simpa only [mix,Finset.mem_univ,ite_true] using hs Finset.univ

end CAT0Fillings.BorelCoefficients
namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [Nonempty X]
variable {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

lemma graph_coord_extension {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X]
    {D : Set (Euc k)} (γ : D → X) {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (π : Fin k → X → ℝ) (hbase : ∀ t : D, coordinateMap π (γ t) = t)
    {v : X → ℝ} {J : ℝ≥0} (hv : LipschitzWith J v) :
    ∃ (ψ : (Fin k → ℝ) → ℝ) (K : ℝ≥0), LipschitzWith K ψ ∧
      ∀ t : D, ψ (fun i => π i (γ t)) = v (γ t) := by
  classical
  let g : Euc k → ℝ := fun t => if ht : t ∈ D then v (γ ⟨t,ht⟩) else 0
  have hg : LipschitzOnWith (J*L) g D := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [g,dite_eq_left hs,dite_eq_left ht,Subtype.dist_eq,Function.comp_apply] using
      (hv.comp hγ).dist_le_mul ⟨s,hs⟩ ⟨t,ht⟩
  obtain ⟨φ,hφ,heq⟩ := hg.extend_real
  refine ⟨fun z => φ (parameterEquiv k z),_,
    hφ.comp (parameterEquiv k).toContinuousLinearMap.lipschitzWith,?_⟩
  intro t
  change φ (coordinateMap π (γ t)) = v (γ t)
  rw [hbase t]
  simpa only [g,dite_eq_left t.property] using (heq t.property).symm

lemma baseTuple_lipschitz {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∃ K : ℝ≥0, LipschitzWith K (fun x i => π i x) := by
  classical
  choose K hK using hπ
  refine ⟨Finset.univ.sup K,LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (Finset.univ.sup K).coe_nonneg dist_nonneg)).mpr
  intro i
  exact ((hK i).weaken (Finset.le_sup (Finset.mem_univ i))).dist_le_mul x y

theorem current_eq_zero_on_joint_graph {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X) {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hbase : ∀ t : D, coordinateMap π (γ t) = t)
    (hsupp : μ (Set.range γ)ᶜ = 0)
    (hz : ∀ (ρ : Fin k → Fin k) b, BoundedLip b → T b (π ∘ ρ) = 0) :
    T = fun _ _ => 0 := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  have hE : MeasurableSet (Set.range γ) := (isCompact_range hγ.continuous).measurableSet
  obtain ⟨K,hK⟩ := baseTuple_lipschitz π hπ
  have hgen (ρ : Fin k → Fin k) : TupleKernel μ hT (fun i x => π (ρ i) x) := by
    apply TupleKernel.of_boundedLip μ hμ (fun i => hπ (ρ i))
    exact hz ρ
  funext b σ
  by_cases hab : Admissible b σ
  · have hext (i : Fin k) := graph_coord_extension γ hγ π hbase (hab.2 i).choose_spec
    choose ψ J hJ hψ using hext
    have hker := tupleKernel_comp_pi μ hμ hK hgen ψ (fun i => ⟨J i,hJ i⟩)
    have hb := integrable_boundedLip μ hab.1
    have hbE := hb.indicator hE
    have hbe : (Set.range γ).indicator b =ᵐ[μ] b := by
      filter_upwards [show ∀ᵐ x ∂μ, x ∈ Set.range γ from ae_iff.mpr hsupp] with x hx
      exact indicator_of_mem hx _
    rw [←borelAction_eq μ hT hμ hab,←borelAction_congr_ae μ hT hbe]
    calc
      _ = borelAction μ hT ((Set.range γ).indicator b) (fun i x => ψ i (fun j => π j x)) := by
        apply borelAction_congr_coords_on_support μ hT hμ hbE σ _ hab.2
          (fun i => ⟨J i*K,hJ i |>.comp hK⟩)
        intro i x hx
        have hxE : x ∈ Set.range γ := by
          by_contra hh
          exact hx (indicator_of_notMem hh _)
        obtain ⟨t,rfl⟩ := hxE
        exact (hψ i t).symm
      _ = 0 := hker _ hbE
  · exact hT.offDomain b σ hab

theorem current_eq_on_joint_graph {U : Functional X k}
    (hT : IsMetricCurrent T) (hU : IsMetricCurrent U)
    (hμ : Controls T μ) (ν : Measure X) [IsFiniteMeasure ν] (hν : Controls U ν)
    {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X) {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hbase : ∀ t : D, coordinateMap π (γ t) = t)
    (hsupp : μ (Set.range γ)ᶜ = 0) (hsupp' : ν (Set.range γ)ᶜ = 0)
    (hbaseact : ∀ (ρ : Fin k → Fin k) b, BoundedLip b → T b (π ∘ ρ) = U b (π ∘ ρ)) :
    T = U := by
  have hd : IsMetricCurrent (T + -U) := hT.add hU.neg
  have hc : Controls (T + -U) (μ+ν) := controls_add hμ (controls_neg_iff.mpr hν)
  have hz := current_eq_zero_on_joint_graph (μ+ν) (hT := hd) hc hD γ hγ π hπ hbase
    (by simp only [Measure.add_apply,hsupp,hsupp',add_zero]) (by
      intro ρ b hb
      change T b (π ∘ ρ) + -U b (π ∘ ρ) = 0
      rw [hbaseact ρ b hb]
      exact add_neg_cancel _)
  funext b σ
  have he := congrFun (congrFun hz b) σ
  change T b σ + -U b σ = 0 at he
  linarith

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma fullSlice_cost_integrable_of_boundedLip {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) :
    Integrable (fun z : Euc k => ((fullSlice_approx h π z).cost : ℝ)) := by
  classical
  choose K hK using fun i => (hπ i).1
  let K' : ℝ≥0 := Finset.univ.sup K
  have hK' i : LipschitzWith K' (π i) := (hK i).weaken (Finset.le_sup (Finset.mem_univ i))
  choose R hR using fun i => (hπ i).2
  let R' : ℝ := max 0 (∑ i, |R i|)
  have hR' i x : |π i x| ≤ R' := by
    apply (hR i x).trans
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i)).trans (le_max_right _ _))
  exact (fullSlice_cost_integrable h hX π hK' hR').1

lemma fullSlice_borel_integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {f : X → ℝ} (hf : Measurable f) (B : ℝ≥0) (hfB : ∀ x, |f x| ≤ B) :
    ActionIntegralAgreement volume T π (fullSlice h π) (fun j => Fin.elim0 j) f := by
  apply ActionIntegralAgreement.bounded_measurable (fun i => (hπ i).1)
    (fun j => Fin.elim0 j) (Eventually.of_forall fun z => (fullSlice_approx h π z).metric)
    (fullSlice_cost_integrable_of_boundedLip h hX π hπ)
    (Eventually.of_forall fun z => Nat.cast_nonneg _)
    (Eventually.of_forall fun z => (fullSlice_approx h π z).mass_le_cost) ?_ hf B hfB
  intro b hb
  have he : (fun z => fullSlice h π z b (fun j => Fin.elim0 j)) =
      (fun z => currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)) := by
    funext z
    exact (currentBorelAction_eq_action (fullSlice_approx h π z).metric ⟨hb,fun j => Fin.elim0 j⟩).symm
  refine ⟨?_,?_⟩
  · rw [←he]
    exact fullSlice_eval_integrable h hX π hπ hb _
  · rw [currentBorelAction_eq_action h.metric ⟨hb,fun i => (hπ i).1⟩,←he]
    exact fullSlice_action_integral h hX π hπ hb

end CAT0Fillings.Slicing
end

end OAI
