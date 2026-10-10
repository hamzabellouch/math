import Mathlib
import OAI.Analysis.AffineBernstein.RegularFiberDomain
import OAI.Analysis.AffineBernstein.ModelFaceMass
import OAI.Analysis.AffineBernstein.FaceSigmaTransport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ModelPositiveSigma
open Metric Filter

def positiveClosedRectangle {k : ℕ} (a b : ℝ) : Set (Space k) :=
  {s | ∀ i, a ≤ s i ∧ s i ≤ b}

lemma isCompact_positiveClosedRectangle {k : ℕ} (a b : ℝ) :
    IsCompact (positiveClosedRectangle (k := k) a b) := by
  convert! (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ : Fin k => (isCompact_Icc : IsCompact (Icc a b))) using 1
  ext s
  simp only [positiveClosedRectangle,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_univ_pi,Set.mem_Icc]
  rfl

/-- The face mass cannot disappear in the true weighted sigma measure. This is
an eventual lower bound on one fixed physical rectangle, derived from the
original PDE and Euclidean graph completeness, not a mass premise. -/
theorem normalized_model_positive_sigma_rectangle {n k m d : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
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
    ∃ α > 0, ∃ β, 1 ≤ β ∧ ∃ c > 0, ∀ᶠ j in atTop,
      positiveClosedRectangle (k := k) α β ⊆ regularPositiveFiberDomain (affineEpigraphPullback Ω u (a j) (L j)) ∧
      let H := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u (a j) (L j)} q.2
      ENNReal.ofReal c ≤ ∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
          ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE) (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
          ∂(volume.restrict (positiveClosedRectangle α β)).prod (volume : Measure (Space m)).toSphere := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨CA,hCA,htransport⟩ := affineEpigraph_face_sigma_transport hn hm e eE f
  obtain ⟨R,hR,ε,hε,c,hc,hface⟩ := normalized_model_positive_face_mass hn hk hm e eE
    hΩ hne hcv hu hp hmP hcomplete a L hC hlim hr hin hout
  let α := min ε 1 / 2
  let β := max R 1 + 1
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by dsimp [α]; linarith [min_le_right ε (1:ℝ)]
  have hαε : α ≤ ε := by dsimp [α]; linarith [min_le_left ε (1:ℝ)]
  have hβ : 1 ≤ β := by dsimp [β]; linarith [le_max_right R (1:ℝ)]
  have hRβ : R ≤ β := by dsimp [β]; linarith [le_max_left R (1:ℝ)]
  let Q : Set (Space k) := positiveClosedRectangle α β
  have hQ : MeasurableSet Q := (isCompact_positiveClosedRectangle α β).measurableSet
  have hQfin : volume Q ≠ ⊤ := (isCompact_positiveClosedRectangle α β).measure_ne_top
  let Cj := fun j => affineEpigraphPullback Ω u (a j) (L j)
  let D := fun j => regularPositiveFiberDomain (Cj j)
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hclj j : IsClosed (Cj j) := affineEpigraphPullback_isClosed hclosed _ _
  have hcvj j : Convex ℝ (Cj j) :=
    ((sourceEpigraph_convex hΩ hcv hu hp).translate_preimage_right (a j)).linear_preimage (L j).toLinearMap
  have hnej j : (Cj j).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  let M : ℝ := max (Real.sqrt k * max 1 (k*(2*β)+1)) (max 1 (k*(2*β)+1)*R₀)+1
  have hM : 0 ≤ M := by
    have hh : 0 ≤ Real.sqrt k * max 1 ((k:ℝ)*(2*β)+1) := mul_nonneg (Real.sqrt_nonneg _) (by positivity)
    dsimp only [M]
    linarith [le_max_left (Real.sqrt k * max 1 ((k:ℝ)*(2*β)+1)) (max 1 ((k:ℝ)*(2*β)+1)*R₀)]
  have hfib := hlim.eventually_normalized_fibers hC hclj hcvj hnej hr
    (half_pos hα) (show α/2 ≤ 1 by linarith) (show 1 ≤ 2*β by linarith) hin hout
  let F : ℝ≥0∞ := ((m:ℝ≥0∞)^2 * volume (closedBall (0:Space m) (M+1))) * volume Q
  have hF : F ≠ ⊤ := by
    dsimp [F]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      ((isCompact_closedBall (0:Space m) (M+1)).measure_ne_top)) hQfin
  let B : ℝ≥0∞ := ENNReal.ofReal CA * ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) * F^(1-2/((n:ℝ)+2))
  have hy : 0 ≤ 1-2/((n:ℝ)+2) := by
    have hh : 2/((n:ℝ)+2) ≤ 1 := (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  have hB : B ≠ ⊤ := by
    dsimp only [B]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg hy hF)
  obtain ⟨δ,hδ,hδlower⟩ := exists_pos_lower_of_rpow hB hc (show 0 < 2/((n:ℝ)+2) by positivity)
  refine ⟨α,hα,β,hβ,δ,hδ,?_⟩
  filter_upwards [hface,hfib] with j hj hf
  have hQbox (s : Space k) (hs : s ∈ Q) : ∀ i, s i ∈ Icc (α/2) (2*β) := by
    intro i
    have hi := hs i
    exact ⟨by linarith [hi.1],by linarith [hi.2]⟩
  have hQD : Q ⊆ D j := by
    apply Set.Subset.trans (b := {s : Space k | ∀ i, α/2 < s i ∧ s i < 2*β})
    · intro s hs i
      have hi := hs i
      exact ⟨by linarith [hi.1],by linarith [hi.2]⟩
    · exact openBox_subset_regularPositiveFiberDomain (hclj j) (half_pos hα)
        (fun s hs => (hf s hs).2)
  have hDj : IsOpen (D j) := regularPositiveFiberDomain_isOpen _
  have hKj : ∀ s ∈ D j, IsCompact {y | (s,y) ∈ Cj j} := fun _ hs => regularPositiveFiberDomain_compact _ hs
  have hzero : ∀ s ∈ D j, (0:Space m) ∈ interior {y | (s,y) ∈ Cj j} := fun _ hs => regularPositiveFiberDomain_zero _ hs
  have hbound : ∀ s ∈ Q, ∀ y : Space m, (s,y) ∈ Cj j → ‖y‖ ≤ M := by
    intro s hs y hy
    exact mem_closedBall_zero_iff.mp ((hf s (hQbox s hs)).2.2 hy)
  obtain ⟨K,hKO,hKQ,harea⟩ := hj
  have hKQ' : ∀ x ∈ K, ((L j).symm ((x,u x)-a j)).1 ∈ Q := by
    intro x hx i
    exact ⟨hαε.trans (hKQ x hx i).1,(hKQ x hx i).2.trans hRβ⟩
  refine ⟨hQD,hδlower _ ?_⟩
  exact (ENNReal.ofReal_le_ofReal harea).trans
    (htransport hΩ hcv hu hp (a j) (L j) hDj hKj hzero hQ hQD hM hbound hKO hKQ')
end ModelPositiveSigma


end
end AffineBernstein
end

end OAI
