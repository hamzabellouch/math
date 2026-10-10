import OAI.Probability.GammaPassage.GridCounting
import OAI.Probability.GammaPassage.GridConnection

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

lemma measurableSet_gridBinGood (shape rate b m K : ℝ) (X h w l : ℤ) (j : ℕ) :
    MeasurableSet (gridBinGood shape rate b m K X h w l j) := by
  have ht : MeasurableSet {weights : Edge → ℝ | ∃ t : Fin (j^2),
      weights ∈ crossingEvent b m K w l (gridTrialTranslate b X h w t)} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun _ => measurableSet_crossingEvent ..)
  have hv (S : Finset Edge) : MeasurableSet {weights : Edge → ℝ |
      (∑ e ∈ S, weights e) ≤ 100*shape/rate*((j : ℝ)^2*w)} :=
    measurableSet_le (Finset.measurable_sum _ (fun e _ => measurable_pi_apply e)) measurable_const
  simpa only [gridBinGood, Grid.binGood, Finset.mem_univ, true_and, Set.ofPred_and] using
    ht.inter ((hv (Grid.transverseIntervalEdges b X (Grid.gridIntervalLower h w)
      (Grid.gridIntervalUpper j h w))).inter
        (hv (Grid.transverseIntervalEdges b (X+l) (Grid.gridIntervalLower h w)
          (Grid.gridIntervalUpper j h w))))

noncomputable def gridTestsEvent (shape rate b m₀ K A R : ℝ) (k m J : ℕ) : Set (Edge → ℝ) :=
  {weights | ∀ n ∈ Finset.range (gridLastLevel m+1-J),
    ∀ ih ∈ gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k) (gridMesh m (n+J)) (gridWidth k (n+J)),
      weights ∈ gridBinGood shape rate b m₀ K ((gridMesh m (n+J))*ih.1) ih.2
        (gridWidth k (n+J)) (gridMesh m (n+J)) (n+J)}

noncomputable def gridConnectionsEvent (shape rate b m₀ K A R : ℝ) (k m J : ℕ) : Set (Edge → ℝ) :=
  {weights | (∀ e, 0 ≤ weights e) ∧ weights ∈ gridTestsEvent shape rate b m₀ K A R k m J}

lemma measurableSet_gridConnectionsEvent (shape rate b m₀ K A R : ℝ) (k m J : ℕ) :
    MeasurableSet (gridConnectionsEvent shape rate b m₀ K A R k m J) := by
  have hp : MeasurableSet {weights : Edge → ℝ | ∀ e, 0 ≤ weights e} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun e => measurableSet_le measurable_const (measurable_pi_apply e))
  have ht : MeasurableSet (gridTestsEvent shape rate b m₀ K A R k m J) := by
    simp only [gridTestsEvent,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iInter
    intro _
    apply MeasurableSet.iInter
    intro ih
    exact MeasurableSet.iInter (fun _ => measurableSet_gridBinGood ..)
  exact hp.inter ht

/-- On the constructed event, all endpoint pairs in all bins connect, with
the Gamma cost and localization allowance K+200*shape/rate. -/
theorem gridConnectionsEvent_paths (weights : Edge → ℝ)
    (shape rate b m₀ K A R : ℝ) (hs : 0 < shape) (hrate : 0 < rate) (hK : 100 ≤ K) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : weights ∈ gridConnectionsEvent shape rate b m₀ K A R k m J)
    (j : ℕ) (hj : J ≤ j ∧ j ≤ gridLastLevel m) (i : ℤ)
    (hi : -(A+4)*(2 : ℝ)^m ≤ ((gridMesh m j*i : ℤ) : ℝ) ∧
      ((gridMesh m j*i+gridMesh m j : ℤ) : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (r₀ : ℝ) (hr : |r₀| ≤ R*(2 : ℝ)^k)
    (p q : Vertex)
    (hp : p.1=gridMesh m j*i ∧ |transverse b p-r₀| ≤ 1)
    (hq : q.1=gridMesh m j*i+gridMesh m j ∧ |transverse b q-r₀| ≤ 1) :
    ∃ ds, p+displacement ds=q ∧
      pathCost weights p ds ≤ m₀*(gridMesh m j)+(Grid.attachmentAllowance shape rate K)*(j : ℝ)^2*(gridWidth k j) ∧
      PathIn p ds {z | gridMesh m j*i-gridMesh m j ≤ z.1 ∧
        z.1 ≤ gridMesh m j*i+2*gridMesh m j ∧
        |transverse b z-r₀| ≤ (Grid.attachmentAllowance shape rate K)*(j : ℝ)^2*(gridWidth k j)} := by
  have hn : j-J ∈ Finset.range (gridLastLevel m+1-J) := by rw [Finset.mem_range]; omega
  have he : j-J+J=j := by omega
  have htest := hg.2 (j-J) hn
  rw [he] at htest
  have hpos := gridMesh_pos m j
  have hpos' : (0 : ℝ) < gridMesh m j := by exact_mod_cast hpos
  have hi' : -(A+4)*(2 : ℝ)^m ≤ ((gridMesh m j*i : ℤ) : ℝ) ∧
      ((gridMesh m j*i : ℤ) : ℝ) ≤ (A+4)*(2 : ℝ)^m := by
    refine ⟨hi.1,?_⟩
    have hh := hi.2
    push_cast at hh ⊢
    linarith
  have hm := grid_interval_index_mem A R ((2 : ℝ)^m) ((2 : ℝ)^k)
    (gridMesh m j) (gridWidth k j) hpos (gridWidth_pos k j) i r₀ hi' hr
  exact gridBinGood_connection weights hg.1 shape rate b m₀ K hs hrate hK _ _ _ _ hpos.le j
    (by omega) (gridWidth_pos k j) (htest _ hm) r₀
    (grid_bin_floor (gridWidth k j) (gridWidth_pos k j) r₀) p q hp hq

end GammaFPP.CrossingBridge

end OAI
