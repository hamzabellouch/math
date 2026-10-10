import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CompactUpdateLp
import OAI.Analysis.Conductivity.Scalarization.WeakCellFast

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

lemma weak_tendsto_zero_of_inner_tendsto_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (z : ℕ → V) (hz : ∀ v, Tendsto (fun n => inner ℝ v (z n)) atTop (𝓝 0)) :
    Tendsto (fun n => toWeakSpace ℝ V (z n)) atTop (𝓝 0) := by
  have hB : Function.Injective ((topDualPairing ℝ V).flip) := by
    intro x y h
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    exact LinearMap.congr_fun h L
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℝ V).flip hB).mpr
  intro L
  change Tendsto (fun n => L (z n)) atTop (𝓝 (L 0))
  simpa only [InnerProductSpace.toDual_symm_apply, map_zero]
    using hz ((InnerProductSpace.toDual ℝ V).symm L)

lemma fine_cells_weak_L2_tendsto_zero
    {X V : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopologyEither X V]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {K : Set X} (hK : IsCompact K)
    (N : ℕ → ℕ) (f : (n : ℕ) → Fin (N n) → X → V)
    (center : (n : ℕ) → Fin (N n) → X)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hf : ∀ n i, Continuous (f n i)) (hc : ∀ n i, HasCompactSupport (f n i))
    (hmean : ∀ n i, (∫ x, f n i x ∂μ) = 0)
    (hdis : ∀ n, Pairwise (fun i j => Disjoint (tsupport (f n i)) (tsupport (f n j))))
    (hsK : ∀ n i, tsupport (f n i) ⊆ K)
    (hsball : ∀ n i, tsupport (f n i) ⊆ Metric.ball (center n i) (δ n))
    (hLp : ∀ n, MemLp (fun x => ∑ i, f n i x) 2 μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n, ‖(hLp n).toLp _‖ ≤ C) :
    Tendsto (fun n => toWeakSpace ℝ (Lp V 2 μ) ((hLp n).toLp _)) atTop (𝓝 0) := by
  apply weak_tendsto_zero_of_inner_tendsto_zero
  apply inner_tendsto_zero_of_dense_tests
    (BoundedContinuousFunction.toLp 2 μ ℝ : (X →ᵇ V) →L[ℝ] Lp V 2 μ)
    (BoundedContinuousFunction.toLp_denseRange V μ ℝ (by simp)) _ hC hbound
  intro φ
  have h := fine_cells_continuous_pairing_tendsto_zero μ hK N f center δ hδ
    hf hc hmean hdis hsK hsball hLp hC hbound φ φ.continuous
  convert h using 1
  ext n
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 2 μ ℝ, (hLp n).coeFn_toLp] with x hx hy
  rw [hx,hy]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma CompactGlobalUpdate.gradient_mean_zero_on_superset
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {O U : Set Coord3} (hOU : O ⊆ U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ O u A) :
    (∫ x, voltageGradient R.du x ∂μ.restrict U) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact voltageGradient_mean_zero μ R.smooth_du R.compact_du
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport
      (fun hs => hx (hOU (R.support_du (tsupport_voltageGradient hs))))

lemma CompactGlobalUpdate.flux_mean_zero_on_superset
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {O U : Set Coord3} (hOU : O ⊆ U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ O u A) :
    (∫ x, fieldVector (R.dF x) ∂μ.restrict U) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact R.flux_mean_zero μ
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hOU (R.support_dF hs)))]
    exact map_zero fieldVectorCLM

lemma fine_updates_weak_tendsto_zero
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (N : ℕ → ℕ) (O : (n : ℕ) → Fin (N n) → Set Coord3)
    (center : (n : ℕ) → Fin (N n) → Coord3)
    (R : ∀ n i, CompactGlobalUpdate μ (O n i) u A)
    (S : ℕ → CompactGlobalUpdate μ U u A)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hOU : ∀ n i, O n i ⊆ U)
    (hsmall : ∀ n i, O n i ⊆ Metric.ball (center n i) (δ n))
    (hdis : ∀ n, Pairwise (fun i j => Disjoint (O n i) (O n j)))
    (hsu : ∀ n, (S n).du = fun x => ∑ i, (R n i).du x)
    (hsF : ∀ n, (S n).dF = fun x => ∑ i, (R n i).dF x)
    {CE CF : ℝ} (hCE : 0 ≤ CE) (hCF : 0 ≤ CF)
    (hbE : ∀ n, ‖((S n).memLp_gradient_correction μ).toLp _‖ ≤ CE)
    (hbF : ∀ n, ‖((S n).memLp_flux_correction μ).toLp _‖ ≤ CF) :
    Tendsto (fun n => toWeakSpace ℝ (Lp FieldVector 2 (μ.restrict U))
      (((S n).memLp_gradient_correction μ).toLp _)) atTop (𝓝 0) ∧
    Tendsto (fun n => toWeakSpace ℝ (Lp FieldVector 2 (μ.restrict U))
      (((S n).memLp_flux_correction μ).toLp _)) atTop (𝓝 0) := by
  classical
  have heq : ∀ n, voltageGradient (S n).du = fun x => ∑ i, voltageGradient (R n i).du x := by
    intro n
    rw [hsu n]
    exact funext (voltageGradient_sum _ (fun i => (R n i).smooth_du.differentiable (by simp)))
  have hfq : ∀ n, (fun x => fieldVector ((S n).dF x)) =
      fun x => ∑ i, fieldVector ((R n i).dF x) := by
    intro n
    funext x
    rw [hsF n]
    exact map_sum fieldVectorCLM _ _
  have hsE : ∀ n i, tsupport (voltageGradient (R n i).du) ⊆ O n i :=
    fun n i => tsupport_voltageGradient.trans (R n i).support_du
  have hsF' : ∀ n i, tsupport (fun x => fieldVector ((R n i).dF x)) ⊆ O n i :=
    fun n i => (tsupport_comp_subset (map_zero fieldVectorCLM) _).trans (R n i).support_dF
  constructor
  · have hLp : ∀ n, MemLp (fun x => ∑ i, voltageGradient (R n i).du x) 2 (μ.restrict U) := by
      intro n
      rw [← heq n]
      exact (S n).memLp_gradient_correction μ
    have ht := fine_cells_weak_L2_tendsto_zero (μ.restrict U) hUb.isCompact_closure
      N (fun n i => voltageGradient (R n i).du) center δ hδ
      (fun n i => continuous_voltageGradient (R n i).smooth_du)
      (fun n i => compact_voltageGradient (R n i).compact_du)
      (fun n i => (R n i).gradient_mean_zero_on_superset μ (hOU n i))
      (fun n i j hij => (hdis n hij).mono (hsE n i) (hsE n j))
      (fun n i => (hsE n i).trans ((hOU n i).trans subset_closure))
      (fun n i => (hsE n i).trans (hsmall n i)) hLp hCE
      (fun n => by simpa only [← heq n] using hbE n)
    simpa only [← heq] using ht
  · have hLp : ∀ n, MemLp (fun x => ∑ i, fieldVector ((R n i).dF x)) 2 (μ.restrict U) := by
      intro n
      rw [← hfq n]
      exact (S n).memLp_flux_correction μ
    have ht := fine_cells_weak_L2_tendsto_zero (μ.restrict U) hUb.isCompact_closure
      N (fun n i x => fieldVector ((R n i).dF x)) center δ hδ
      (fun n i => fieldVectorCLM.continuous.comp (R n i).smooth_dF.continuous)
      (fun n i => (R n i).compact_dF.comp_left (map_zero fieldVectorCLM))
      (fun n i => (R n i).flux_mean_zero_on_superset μ (hOU n i))
      (fun n i j hij => (hdis n hij).mono (hsF' n i) (hsF' n j))
      (fun n i => (hsF' n i).trans ((hOU n i).trans subset_closure))
      (fun n i => (hsF' n i).trans (hsmall n i)) hLp hCF
      (fun n => by simpa only [← hfq n] using hbF n)
    simpa only [← hfq] using ht

end ScalarConductivity

end
end

end OAI
