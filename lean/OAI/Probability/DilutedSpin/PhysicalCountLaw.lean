import OAI.Probability.DilutedSpin.CountArrayBridge
import OAI.Probability.DilutedSpin.FullRootCounts

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower SizeCoupling
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ} [NeZero N]

lemma fixed_root_countedMean
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) (k l : ℕ) :
    (∫ a : RootPath (I × Fin N) l,∫ x : RootPath (X × (Fin p → Fin N)) k,∫ h : RootPath Y N,
      rootSample (indexedPotential theta) field (fun i : I × Fin N => Q i.1)
        m (locatedFactor ψ) h k x l a
      ∂rootLaw N (fun _ => ξ)
      ∂rootLaw k (fun _ => μ.prod (finiteUniform (Fin p → Fin N)))
      ∂rootLaw l (fun _ => ν.prod (finiteUniform (Fin N)))) =
      countedMean (N := N) μ ξ ν theta field Q m ψ k l := by
  let F (a : Fin l → I) (w : Fin l → Fin N) (z : (Fin k → X) × (Fin k → Fin p → Fin N)) :=
    ∫ h : RootPath Y N,arrayRoot theta field Q m ψ a z.1 h z.2 w ∂rootLaw N (fun _ => ξ)
  have hf (a : Fin l → I) (w : Fin l → Fin N) : Measurable (F a w) := by
    apply measurable_from_prod_countable_left
    intro j
    exact (arrayRoot_measurable theta field hθm hhm Q m ψ a j w).stronglyMeasurable.integral_prod_right'.measurable
  have hb (a : Fin l → I) (w : Fin l → Fin N) (z) : |F a w z|≤H*N+C*k+D*l :=
    abs_integral_le_const _ (fun h => arrayRoot_bound theta field Q m hm ψ hθ hh hψ a z.1 h z.2 w)
  let G (z : (Fin l → I) × (Fin l → Fin N)) :=
    ∫ x : Fin k → X,(FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
      (fun j => F z.1 z.2 (x,j)) ∂Measure.pi (fun _ : Fin k => μ)
  have hG : Measurable G := measurable_of_countable G
  have hGb (z) : |G z|≤H*N+C*k+D*l :=
    abs_integral_le_const _ (fun x => FiniteLaw.abs_expect_le _ (fun j => hb z.1 z.2 (x,j)))
  calc
    _ = ∫ a : RootPath (I × Fin N) l,
        G ((fun i => (rootArray l a i).1),(fun i => (rootArray l a i).2))
        ∂rootLaw l (fun _ => ν.prod (finiteUniform (Fin N))) := by
      apply integral_congr_ae
      filter_upwards [] with a
      simp_rw [rootSample_eq_spinRoot]
      exact integral_root_prod_finite μ k
        (F (fun i => (rootArray l a i).1) (fun i => (rootArray l a i).2)) (hf _ _) (hb _ _)
    _ = ∫ a : Fin l → I,(FiniteLaw.uniform : FiniteLaw (Fin l → Fin N)).expect
        (fun w => G (a,w)) ∂Measure.pi (fun _ : Fin l => ν) :=
      integral_root_prod_finite ν l G hG hGb
    _ = countedMean (N := N) μ ξ ν theta field Q m ψ k l := by
      rw [countedMean_eq_arrays]
      apply integral_congr_ae
      filter_upwards [] with a
      exact arrayRoot_swap_expect μ ξ theta field hθm hhm Q m hm ψ hθ hh hψ a

lemma fullRoot_countedMean
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    (∫ z,packRoot (rootSample (indexedPotential theta) field
      (fun i : I × Fin N => Q i.1) m (locatedFactor ψ)) z
      ∂fullRootLaw (fun _ : Fin N => ξ) (μ.prod (finiteUniform (Fin p → Fin N)))
        (ν.prod (finiteUniform (Fin N))) r s) =
      twoPoissonMean r s (countedMean (N := N) μ ξ ν theta field Q m ψ) := by
  let V : X × (Fin p → Fin N) → (Fin N → Spin) → ℝ := indexedPotential theta
  let Q' := fun i : I × Fin N => Q i.1
  let f := locatedFactor (N := N) ψ
  have hV : Measurable V := measurable_indexedPotential theta hθm
  have hVb : ∀ x σ, |V x σ| ≤ C := fun x σ => hθ x.1 _
  have hfb : ∀ i y a, |Real.log (f i y a)| ≤ D := fun i y a => hψ i.1 _ a
  let F := rootSample V field Q' m f
  have hfm : ∀ k l, Measurable (fun z : (RootPath Y N × RootPath (X × (Fin p → Fin N)) k) ×
      RootPath (I × Fin N) l => F z.1.1 k z.1.2 l z.2) :=
    measurable_rootSample V field hV hhm Q' m f
  have hfl : ∀ h k x l a, |F h k x l a| ≤ H*N+C*k+D*l :=
    rootSample_bound V field Q' m hm f hVb hh hfb
  have hfbq : ∀ h k x l a, |F h k x l a| ≤ H*N+C*(k:ℝ)^2+D*(l:ℝ)^2 :=
    fun h k x l a => (hfl h k x l a).trans (count_linear_le_quadratic hC hD k l)
  change (∫ z,packRoot F z ∂fullRootLaw (fun _ : Fin N => ξ)
    (μ.prod (finiteUniform (Fin p → Fin N))) (ν.prod (finiteUniform (Fin N))) r s) = _
  rw [integral_fullRootLaw_counts (fun _ : Fin N => ξ)
    (μ.prod (finiteUniform (Fin p → Fin N))) (ν.prod (finiteUniform (Fin N))) r s hfm hfbq]
  unfold twoPoissonMean
  apply integral_congr_ae
  filter_upwards [] with k
  apply integral_congr_ae
  filter_upwards [] with l
  exact fixed_root_countedMean μ ξ ν theta field hθm hhm Q m hm ψ hθ hh hψ k l

end DilutedSpinGlass.PhysicalRoot

end

end OAI
