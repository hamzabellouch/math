import Mathlib
import OAI.Analysis.AffineBernstein.UniformSigmaCaps
import OAI.Analysis.AffineBernstein.NormalizedCaps
import OAI.Analysis.AffineBernstein.NormalizedCellGeometry

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Metric Filter

/-- A normalized maximal model and local convergence produce the full literal
geometric hypotheses of the sigma-cell estimate. The uniform constant is fixed
before the model, original solution or approximating affine coordinates. -/
theorem normalized_model_uniform_actual_sigma {n k m d : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ Cσ : ℝ≥0∞, Cσ ≠ ⊤ ∧ ∀ {Ω : Set (Space n)}, IsOpen Ω → Ω.Nonempty → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u → EuclideanGraphComplete Ω u →
      ∀ (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
      (C : Set (Space k × Space m)), IsModelShape C →
      closedBall 0 r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) →
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R →
      LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C →
      ∀ᶠ j in atTop,
      let H := fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u (a j) (L j)} q.2
      let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
      (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
          (q.1,q.2) * tubeLogMassWeight H (q.1,q.2))
        ∂(volume.restrict (normalizedCell k)).prod (volume : Measure (Space m)).toSphere) ≤ Cσ := by
  let : NeZero k := ⟨by omega⟩
  let : NeZero m := ⟨by omega⟩
  let T : ℝ := 5*((k:ℝ)+1)
  let B : ℝ := T+1
  let Rcap : ℝ := max (Real.sqrt k * max 1 B) (max 1 B*R)+1
  let M : ℝ := max (Real.sqrt k * max 1 ((k:ℝ)*4+1)) (max 1 ((k:ℝ)*4+1)*R)+1
  let o : Space k × Space m := (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)),0)
  have hRc : 0 ≤ Rcap := by
    dsimp [Rcap]
    exact add_nonneg
      ((mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hR).trans (le_max_right _ _))
      zero_le_one
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hT : 0 < B := by dsimp [B,T]; positivity
  have hogap (j : Fin k) : capTiltedForm j o.1 < T+1 := by
    rw [show o.1 = WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)) from rfl,capTiltedForm_center]
    dsimp [T]
    have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hDh (j : Fin k) (s : Space k) (hs : s ∈ normalizedCellDomain k) : capTiltedForm j s ≤ T+1 := by
    have hh := capTiltedForm_coord_bound (fun i => (hs i).2.le) j
    dsimp [T]
    have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hQh (j : Fin k) (s : Space k) (hs : s ∈ normalizedCell k) : capTiltedForm j s ≤ T-1 := by
    have hh := capTiltedForm_coord_bound (fun i => (hs i).2) j
    dsimp [T]
    have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  obtain ⟨Cσ,hCσ,hprod⟩ := complete_affineMaximal_uniform_sigma_bound hn hk hm e eE f
    (isOpen_normalizedCellDomain k) (convex_normalizedCellDomain k) (isCompact_normalizedCell k)
    (normalizedCell_subset_domain k) o (ε:=1) (r₀:=min (1/4) (r/4)) (r₁:=1/8) (α:=1/2)
    (ρ:=r/8) (M:=M) (R:=Rcap) (T:=T) (RQ:=Real.sqrt k*2)
    (by norm_num) (lt_min (by norm_num) (by positivity)) (by norm_num) (by norm_num)
    (by positivity) hM hRc hogap hDh hQh (fun s hs i => (hs i).1)
    (fun s hs => normalizedCell_margin hs)
    (fun s hs => norm_le_sqrt_card_mul_of_coord_le (by norm_num : (0:ℝ)<2)
      (fun i => by rw [abs_of_nonneg (by linarith [(hs i).1])]; exact (hs i).2))
  refine ⟨Cσ,hCσ,?_⟩
  intro Ω hΩ hne hcv u hu hp hmP hcomplete a L C hC hin hout hlim
  have hclj (j : ℕ) : IsClosed (affineEpigraphPullback Ω u (a j) (L j)) :=
    affineEpigraphPullback_isClosed (sourceEpigraph_closed hΩ hne hcv hu hp hcomplete) (a j) (L j)
  have hcvj (j : ℕ) : Convex ℝ (affineEpigraphPullback Ω u (a j) (L j)) :=
    ((sourceEpigraph_convex hΩ hcv hu hp).translate_preimage_right (a j)).linear_preimage
      (L j).toLinearMap
  have hnej (j : ℕ) : (affineEpigraphPullback Ω u (a j) (L j)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  have hcaps : ∀ᶠ j in atTop, ∀ i : Fin k, ∀ p ∈ affineEpigraphPullback Ω u (a j) (L j),
      capTiltedForm i p.1 ≤ T+1 → ‖p‖ ≤ Rcap := by
    apply (Filter.eventually_all.mpr (fun i => hlim.eventually_normalized_cap_radius hC hclj hcvj hnej
      (a:=capTiltedCovector i) (α:=1) hT zero_lt_one (capTiltedCovector_one_le i) hout)).mono
    intro j hj i p hp hb
    have he : positiveBaseForm (capTiltedCovector i) p = capTiltedForm i p.1 := by
      simp only [positiveBaseForm_apply,capTiltedForm_apply]
    have hh := hj i (show p ∈ affineEpigraphPullback Ω u (a j) (L j) ∩
      {p | positiveBaseForm (capTiltedCovector i) p ≤ B} from ⟨hp,by change positiveBaseForm (capTiltedCovector i) p ≤ B; simpa only [he,B] using hb⟩)
    have hh' : ‖p‖ < Rcap := by simpa only [div_one,Metric.mem_ball,dist_zero_right,Rcap] using hh
    exact hh'.le
  have hballs := hlim.eventually_normalized_center_ball hC hclj hcvj hnej hr hin
  have hfibers := hlim.eventually_normalized_fibers hC hclj hcvj hnej hr
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)≤1) (by norm_num : (1:ℝ)≤4) hin hout
  filter_upwards [hcaps,hballs,hfibers] with j hcj hbj hfj
  apply hprod hΩ hne hcv hu hp hmP hcomplete (a j) (L j) hcj hbj
  · intro s hs
    have hh := (hfj s (fun i => ⟨(hs i).1.le,(hs i).2.le⟩)).1
    simpa only [show (1/4:ℝ)*r/2 = r/8 by ring,modelFiber] using hh
  · intro s hs y hy
    exact mem_closedBall_zero_iff.mp ((hfj s (fun i => ⟨(hs i).1.le,(hs i).2.le⟩)).2.2 hy)

/- A symmetric form with radial null vector has its full adjugate equal to
its transverse principal minor times the radial outer product. This includes
all empty transverse blocks and needs no invertibility of the full matrix. -/

/- The full cofactor trace recovers the transverse determinant in every flat
normal chart. No unit-normal constraint is imposed away from the chart center. -/

end AffineBernstein

end

end OAI
