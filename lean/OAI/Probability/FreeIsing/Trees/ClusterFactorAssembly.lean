import OAI.Probability.FreeIsing.Estimates.FiniteBondMask
import OAI.Probability.FreeIsing.Factors.Transfer
import OAI.Probability.FreeIsing.Model
import OAI.Probability.FreeIsing.Trees.FiniteClusterLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.ClusterAssembly

theorem lintegral_finite_statistic
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Fintype E] [MeasurableSingletonClass E]
    (μ : Measure Ω) (A : Ω → E) (hA : Measurable A)
    (weight : E → ENNReal)
    (hlaw : ∀ e, μ {ω | A ω = e} = weight e) (f : E → ENNReal) :
    (∫⁻ ω, f (A ω) ∂μ) = ∑ e, weight e * f e := by
  rw [← lintegral_map (measurable_of_finite f) hA, lintegral_fintype]
  apply Finset.sum_congr rfl
  intro e he
  rw [Measure.map_apply hA (measurableSet_singleton e)]
  change f e * μ {ω | A ω = e} = weight e * f e
  rw [hlaw, mul_comm]

theorem map_prod_apply_eq_finite_mixture
    {Ω C E S : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [MeasurableSpace E] [MeasurableSpace S]
    [Fintype E] [MeasurableSingletonClass E]
    (μ : Measure Ω) (ν : Measure C) [SFinite ν]
    (A : Ω → E) (hA : Measurable A)
    (F : Ω × C → S) (hF : Measurable F)
    (s : Set S) (hs : MeasurableSet s)
    (weight color : E → ENNReal)
    (hlaw : ∀ e, μ {ω | A ω = e} = weight e)
    (hcolor : ∀ᵐ ω ∂μ, ν {c | F (ω, c) ∈ s} = color (A ω)) :
    Measure.map F (μ.prod ν) s = ∑ e, weight e * color e := by
  rw [Measure.map_apply hF hs, Measure.prod_apply (hs.preimage hF)]
  calc
    (∫⁻ ω, ν (Prod.mk ω ⁻¹' (F ⁻¹' s)) ∂μ) = ∫⁻ ω, color (A ω) ∂μ := by
      apply lintegral_congr_ae
      exact hcolor
    _ = ∑ e, weight e * color e :=
      lintegral_finite_statistic μ A hA weight hlaw color

theorem map_compProd_snd_apply_eq_finite_mixture
    {Ω E S : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace S] [Fintype E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [SFinite μ] (κ : Kernel Ω S) [IsSFiniteKernel κ]
    (A : Ω → E) (hA : Measurable A)
    (s : Set S) (hs : MeasurableSet s)
    (weight color : E → ENNReal)
    (hlaw : ∀ e, μ {ω | A ω = e} = weight e)
    (hcolor : ∀ᵐ ω ∂μ, κ ω s = color (A ω)) :
    Measure.map Prod.snd (μ ⊗ₘ κ) s = ∑ e, weight e * color e := by
  rw [Measure.map_apply measurable_snd hs,
    Measure.compProd_apply (hs.preimage measurable_snd)]
  calc
    (∫⁻ ω, κ ω (Prod.mk ω ⁻¹' (Prod.snd ⁻¹' s)) ∂μ) =
        ∫⁻ ω, color (A ω) ∂μ := by
      apply lintegral_congr_ae
      exact hcolor
    _ = ∑ e, weight e * color e :=
      lintegral_finite_statistic μ A hA weight hlaw color

theorem cluster_mixture_sum {d : ℕ} {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    (∑ A : (inducedEdges D).powerset,
      ENNReal.ofReal (FiniteCluster.bondWeight theta (inducedEdges D) A.val) *
        ENNReal.ofReal (FiniteCluster.colorWeight (inducedEdges D) A.val eta)) =
      freeCylinderWeight theta D eta := by
  classical
  rw [Finset.sum_coe_sort (inducedEdges D).powerset (fun A =>
    ENNReal.ofReal (FiniteCluster.bondWeight theta (inducedEdges D) A) *
      ENNReal.ofReal (FiniteCluster.colorWeight (inducedEdges D) A eta))]
  rw [← FiniteCluster.marginal_eq_freeCylinderWeight theta D eta]
  rw [ENNReal.ofReal_sum_of_nonneg (fun A _ =>
    mul_nonneg (FiniteCluster.bondWeight_nonneg h0 h1 _ _)
      (FiniteCluster.colorWeight_nonneg _ _ _))]
  apply Finset.sum_congr rfl
  intro A hA
  exact (ENNReal.ofReal_mul (FiniteCluster.bondWeight_nonneg h0 h1 _ _)).symm

lemma measurableSet_spinCylinder {d : ℕ} (D : Finset (TreeVertex d))
    (eta : TreeVertex d → IsingSpin) :
    MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} := by
  classical
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro v
  apply MeasurableSet.iInter
  intro hv
  convert (show MeasurableSet ({eta v} : Set IsingSpin) by trivial).preimage
    (measurable_pi_apply v : Measurable (fun x : TreeVertex d → IsingSpin => x v)) using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]

theorem hasFreeIsingLaw_map_prod_of_cluster_conditionals
    {d : ℕ} {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    (μ : Measure Ω) (ν : Measure C) [SFinite ν]
    {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (F : Ω × C → TreeVertex d → IsingSpin) (hF : Measurable F)
    (A : (D : Finset (TreeVertex d)) → Ω → (inducedEdges D).powerset)
    (hA : ∀ D, Measurable (A D))
    (hmask : ∀ D, ConnectedFinset D → ∀ a : (inducedEdges D).powerset,
      μ {ω | A D ω = a} =
        ENNReal.ofReal (FiniteCluster.bondWeight theta (inducedEdges D) a.val))
    (hcolor : ∀ D, ConnectedFinset D → ∀ eta : TreeVertex d → IsingSpin,
      ∀ᵐ ω ∂μ, ν {c | ∀ v ∈ D, F (ω, c) v = eta v} =
        ENNReal.ofReal (FiniteCluster.colorWeight (inducedEdges D) (A D ω).val eta)) :
    HasFreeIsingLaw theta (Measure.map F (μ.prod ν)) := by
  intro D hD eta
  rw [map_prod_apply_eq_finite_mixture μ ν (A D) (hA D) F hF _
    (measurableSet_spinCylinder D eta)
    (fun a => ENNReal.ofReal (FiniteCluster.bondWeight theta (inducedEdges D) a.val))
    (fun a => ENNReal.ofReal (FiniteCluster.colorWeight (inducedEdges D) a.val eta))
    (hmask D hD) (hcolor D hD eta)]
  exact cluster_mixture_sum h0 h1 D eta

theorem hasFreeIsingLaw_compProd_of_cluster_conditionals
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ]
    (κ : Kernel Ω (TreeVertex d → IsingSpin)) [IsSFiniteKernel κ]
    {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (A : (D : Finset (TreeVertex d)) → Ω → (inducedEdges D).powerset)
    (hA : ∀ D, Measurable (A D))
    (hmask : ∀ D, ConnectedFinset D → ∀ a : (inducedEdges D).powerset,
      μ {ω | A D ω = a} =
        ENNReal.ofReal (FiniteCluster.bondWeight theta (inducedEdges D) a.val))
    (hcolor : ∀ D, ConnectedFinset D → ∀ eta : TreeVertex d → IsingSpin,
      ∀ᵐ ω ∂μ, κ ω {x | ∀ v ∈ D, x v = eta v} =
        ENNReal.ofReal (FiniteCluster.colorWeight (inducedEdges D) (A D ω).val eta)) :
    HasFreeIsingLaw theta (Measure.map Prod.snd (μ ⊗ₘ κ)) := by
  intro D hD eta
  rw [map_compProd_snd_apply_eq_finite_mixture μ κ (A D) (hA D) _
    (measurableSet_spinCylinder D eta)
    (fun a => ENNReal.ofReal (FiniteCluster.bondWeight theta (inducedEdges D) a.val))
    (fun a => ENNReal.ofReal (FiniteCluster.colorWeight (inducedEdges D) a.val eta))
    (hmask D hD) (hcolor D hD eta)]
  exact cluster_mixture_sum h0 h1 D eta

theorem hasFreeIsingLaw_map_prod_of_independent_bonds
    {d : ℕ} {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    (μ : Measure Ω) (ν : Measure C) [SFinite ν]
    {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (X : (TreeVertex d × TreeVertex d) → Ω → Bool)
    (hX : ∀ e, Measurable (X e))
    (hindep : ∀ D : Finset (TreeVertex d),
      iIndepFun (fun e : inducedEdges D => X e.val) μ)
    (htrue : ∀ D : Finset (TreeVertex d), ∀ e ∈ inducedEdges D,
      μ {ω | X e ω = true} = ENNReal.ofReal theta)
    (hfalse : ∀ D : Finset (TreeVertex d), ∀ e ∈ inducedEdges D,
      μ {ω | X e ω = false} = ENNReal.ofReal (1 - theta))
    (F : Ω × C → TreeVertex d → IsingSpin) (hF : Measurable F)
    (hcolor : ∀ D, ConnectedFinset D → ∀ eta : TreeVertex d → IsingSpin,
      ∀ᵐ ω ∂μ, ν {c | ∀ v ∈ D, F (ω, c) v = eta v} =
        ENNReal.ofReal (FiniteCluster.colorWeight (inducedEdges D)
          (openMask (inducedEdges D) X ω).val eta)) :
    HasFreeIsingLaw theta (Measure.map F (μ.prod ν)) := by
  classical
  apply hasFreeIsingLaw_map_prod_of_cluster_conditionals μ ν h0 h1 F hF
    (fun D => openMask (inducedEdges D) X)
    (fun D => measurable_openMask _ _ (fun e _ => hX e)) _ hcolor
  intro D hD A
  exact openMask_atom_measure_ofReal_restricted μ (inducedEdges D) X
    (hindep D) h0 h1 (htrue D) (hfalse D) A

end Problem367.ClusterAssembly

end

end OAI
