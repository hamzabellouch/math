import OAI.Probability.DilutedSpin.InsertionStability

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I] {M : ℕ}

lemma integral_fullRootLaw_reordered
    (ξ : Fin M → Measure Y) [∀ i,IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hf : ∀ k n,Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n a,|F h k x n a|≤B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z,packRoot F z ∂fullRootLaw ξ μ ν r s) =
      ∫ h,∫ a : Sigma (RootPath I),∫ x : Sigma (RootPath X),F h x.1 x.2 a.1 a.2
        ∂compoundRootLaw μ r ∂compoundRootLaw ν s ∂rootLaw M ξ := by
  rw [fullRootLaw,integral_prod _ (fullRoot_integrable_quadratic ξ μ ν r s hf hb)]
  apply integral_congr_ae
  filter_upwards [] with h
  have hmf : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      F h z.1.1 z.1.2 z.2.1 z.2.2) :=
    (measurable_packRoot hf).comp (measurable_const.prodMk measurable_id)
  exact integral_prod_symm _ (twoCompound_integrable_quadratic μ ν r s hmf (hb h))

lemma count_linear_le_quadratic {B C D : ℝ} (hC : 0≤C) (hD : 0≤D) (k n : ℕ) :
    B+C*k+D*n ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2 := by
  have hk : (k:ℝ)≤k^2 := by exact_mod_cast Nat.le_self_pow (by omega : 2≠0) k
  have hn : (n:ℝ)≤n^2 := by exact_mod_cast Nat.le_self_pow (by omega : 2≠0) n
  nlinarith

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open Filter
open scoped Topology BigOperators
variable {p : ℕ} {X : Type} [MeasurableSpace X]

lemma randomInsertion_comparison (M : Model p) (C H : ℝ) (N L : ℕ) (hN : 0<N)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → (Fin a → Spin) → ℝ) (hFm : Measurable F) {D : ℝ}
    (hD : 0≤D) (hF : ∀ x s, |F x s|≤D) (K : ℕ) :
    |(∫ x, reservoirInsertion M C H N L u a (F x) ∂μ)-
      (∫ x, trialLog L (reservoirTrialLaw M C H N L u)
        (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F x)) ∂μ)| ≤
      2*(∑' k : ℕ, |insertionRadius D|^(k+K+1)/(k+K+1))+
      ∑ k∈Finset.range K, |insertionRadius D|^(k+1)/(k+1)*((a:ℝ)*
        qExpect (grid (L+1) 0 (L+1)) (reservoirShapeDeviation M C H N L u) k (single (L+1))) := by
  have hi := MeasureMean.bounded_integrable μ
    ((reservoirInsertion_lipschitz M C H N L u a).continuous.measurable.comp hFm)
    (fun x => reservoirInsertion_bound M C H N L u a (F x) (hF x))
  have hj := MeasureMean.bounded_integrable μ
    ((reservoirTrialLog_lipschitz M C H N L u a).continuous.measurable.comp hFm)
    (fun x => reservoirTrialLog_bound M C H N L u a (F x) (hF x))
  simp only [Function.comp_def] at hi hj
  rw [← integral_sub hi hj]
  exact abs_integral_le_bound (μ := μ) (fun x => reservoirInsertion_comparison M C H N L hN u a (F x) hD (hF x) K)

/-- The bounded-insertion limit is uniform in independent physical disorder;
 the physical law is integrated without exchanging the two ordered limits. -/
theorem randomInsertion_comparison_tendsto (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L, Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L))
    (a : ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → (Fin a → Spin) → ℝ) (hFm : Measurable F) {D : ℝ}
    (hD : 0≤D) (hF : ∀ x s, |F x s|≤D) :
    Tendsto (fun L => limsup (fun n =>
      |(∫ x, reservoirInsertion M C H (Ns L n+1) L (us L n) a (F x) ∂μ)-
        (∫ x, trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F x)) ∂μ)|) atTop) atTop (𝓝 0) := by
  let f := fun k L n => qExpect (grid (L+1) 0 (L+1))
    (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))
  have hf (k L : ℕ) : IsBoundedUnder (·≤·) atTop (f k L) := by
    refine isBoundedUnder_of_eventually_le (a := (2:ℝ)^(k+1)*2) (Eventually.of_forall (fun n => ?_))
    apply qExpect_shape_bound _ (grid_strictMono (by omega)).monotone grid_nonneg
      (by simp [grid]) (grid_last (by omega))
    intro S
    exact reservoirShapeDeviation_bound _ _ _ _ _ _ _
  apply series_double_limit _ f (fun k => |insertionRadius D|^(k+1)/(k+1)*(a:ℝ))
    (fun K => 2*(∑' k : ℕ, |insertionRadius D|^(k+K+1)/(k+K+1)))
  · intros; exact abs_nonneg _
  · intro L
    refine isBoundedUnder_of_eventually_le (a := 2*D) (Eventually.of_forall (fun n => ?_))
    have h1 := abs_integral_le_bound (μ := μ) (fun x => reservoirInsertion_bound M C H (Ns L n+1) L (us L n) a (F x) (hF x))
    have h2 := abs_integral_le_bound (μ := μ) (fun x => reservoirTrialLog_bound M C H (Ns L n+1) L (us L n) a (F x) (hF x))
    exact (abs_sub _ _).trans (by linarith)
  · intro k; positivity
  · exact hf
  · exact reservoirShapeError_tendsto M hα C H Ns hNs us hcontrol
  · exact logSeries_tail_tendsto D
  · intro K L n
    simpa only [f,mul_assoc] using randomInsertion_comparison M C H (Ns L n+1) L
      (by omega) (us L n) a μ F hFm hD hF K
end DilutedSpinGlass.UniversalDictionary

end

end OAI
