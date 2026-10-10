import Mathlib
import OAI.Analysis.AffineBernstein.ActualLogGrowth
import OAI.Analysis.AffineBernstein.ModelPositiveSigma

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ModelPositiveLogMass
open Metric Filter
lemma positiveClosedRectangle_sub_logBox {k : ℕ} {α β : ℝ} (hα : 0 < α) :
    ∃ T : ℕ, positiveClosedRectangle (k := k) α β ⊆ logSpace ⁻¹' logarithmicBox k T := by
  obtain ⟨T,hT⟩ := exists_nat_gt (max |Real.log α| |Real.log β|)
  refine ⟨T,?_⟩
  intro s hs i
  rw [logSpace_apply]
  apply abs_le.mpr
  have h1 : |Real.log α| ≤ (T:ℝ) := (le_max_left _ _).trans hT.le
  have h2 : |Real.log β| ≤ (T:ℝ) := (le_max_right _ _).trans hT.le
  have hsi := (hs i)
  have hlogs := Real.log_le_log hα hsi.1
  have hlogt := Real.log_le_log (hα.trans_le hsi.1) hsi.2
  exact ⟨(neg_le_neg h1).trans ((neg_abs_le _).trans hlogs),hlogt.trans ((le_abs_self _).trans h2)⟩

/-- A fixed log box has strictly positive actual sigma mass, uniformly along
any normalized actual epigraph approximation. Local finiteness is proved from
smooth compact fibers, and the positive mass is produced from the original PDE. -/
theorem normalized_model_positive_log_mass {n k m d : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hm : 1 ≤ m) (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
    {r R₀ : ℝ} (hr : 0 < r)
    (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) :
    ∃ T : ℕ, ∃ c > 0, ∀ᶠ j in atTop,
      c ≤ (affineEpigraphLogMeasure volume
        (regularPositiveFiberDomain (affineEpigraphPullback Ω u (a j) (L j))) Ω u (a j) (L j)
        ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE)).real (logarithmicBox k T) := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨α,hα,β,hβ,c,hc,hrect⟩ := normalized_model_positive_sigma_rectangle hn hk hm e eE f
    hΩ hne hcv hu hp hmP hcomplete a L hC hlim hr hin hout
  obtain ⟨T,hT⟩ := positiveClosedRectangle_sub_logBox (k := k) (β := β) hα
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hclj j : IsClosed (affineEpigraphPullback Ω u (a j) (L j)) := affineEpigraphPullback_isClosed hclosed _ _
  have hcvj j : Convex ℝ (affineEpigraphPullback Ω u (a j) (L j)) :=
    ((sourceEpigraph_convex hΩ hcv hu hp).translate_preimage_right (a j)).linear_preimage (L j).toLinearMap
  have hnej j : (affineEpigraphPullback Ω u (a j) (L j)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  have havail := hlim.eventually_regular_logBox hC hclj hcvj hnej hr hin hout T
  refine ⟨T,c,hc,?_⟩
  filter_upwards [hrect,havail] with j hj ha
  let Cj := affineEpigraphPullback Ω u (a j) (L j)
  let D := regularPositiveFiberDomain Cj
  let H := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈ Cj} q.2
  let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
  let W := fun q => tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE q * tubeLogMassWeight H q
  have hmass : ENNReal.ofReal c ≤ affineEpigraphLogMeasure volume D Ω u (a j) (L j) bE (logarithmicBox k T) := by
    refine hj.2.trans (logTubeMeasure_cell_le_apply volume D W
      (logarithmicBox_isClosed k T).measurableSet ?_)
    exact fun s hs => ⟨hj.1 hs,hT hs⟩
  have hfin := affineEpigraphLogMeasure_box_finite (μ := volume) hΩ hcv hu hp (a j) (L j)
    (regularPositiveFiberDomain_isOpen Cj) (regularPositiveFiberDomain_positive Cj)
    (fun _ hs => regularPositiveFiberDomain_compact Cj hs)
    (fun _ hs => regularPositiveFiberDomain_zero Cj hs) bE ha
  exact (ENNReal.toReal_ofReal hc.le).symm.trans_le (ENNReal.toReal_mono hfin hmass)
end ModelPositiveLogMass


end
end AffineBernstein
end

end OAI
