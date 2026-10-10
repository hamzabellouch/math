import OAI.Geometry.RCD.Coordinates.FirstOrderFrameConvergence
import OAI.Geometry.RCD.Metric.MeasurablePointedApproximation
import OAI.Geometry.RCD.Metric.PointedPhysicalScale

namespace OAI

/-! # The Euclidean-flat consequence of almost splitting

Measured-coordinate estimates imply a Euclidean coordinate approximation.
The harmonic functions are fixed throughout the compactness argument.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.flat_splitting_coordinates {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hMeasured : LocalMeasuredCoordinateInput hX) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧
      ∀ (p : X) (r : ℝ), 0 < r → -ε ≤ K*r^2 →
        ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
          FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v →
          (∃ f : X → Euclidean n, IsPointedApproximation p 0 r 2 τ f) →
          IsPointedApproximation p 0 r (1/2) ρ (fun x => r⁻¹ • (v x-v p)) := by
  classical
  by_contra hnot
  push Not at hnot
  let e := fun k : ℕ => 1/((k : ℝ)+1)
  have hepos (k : ℕ) : 0 < e k := by dsimp only [e]; positivity
  have he1 (k : ℕ) : e k ≤ 1 := by
    dsimp only [e]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose δ hδ hmeasure using (fun k => hMeasured hn 5 (e k) (by norm_num) (hepos k))
  let a := fun k => min (e k) (min (δ k) (1/256))
  have hapos (k : ℕ) : 0 < a k := lt_min (hepos k) (lt_min (hδ k) (by norm_num))
  have hae (k : ℕ) : a k ≤ e k := min_le_left _ _
  have haδ (k : ℕ) : a k ≤ δ k := (min_le_right _ _).trans (min_le_left _ _)
  have ha256 (k : ℕ) : a k ≤ 1/256 := (min_le_right _ _).trans (min_le_right _ _)
  have hex (k : ℕ) := hnot (δ k/25) (a k) (div_pos (hδ k) (by norm_num)) (hapos k)
  choose p R hR hcurv u v hsplit hflat hbad using hex
  choose f hf using hflat
  let r := fun k => R k/5
  have hr (k : ℕ) : 0 < r k := div_pos (hR k) (by norm_num)
  have hbig (k : ℕ) : -1 ≤ K*(80*r k)^2 := by
    have hh := hcurv k
    have hs := ha256 k
    dsimp only [r]
    nlinarith
  have hsmall (k : ℕ) : -(δ k) ≤ K*(r k)^2 := by
    have hh := hcurv k
    have hs := haδ k
    dsimp only [r]
    by_cases hK : 0≤K
    · exact (neg_nonpos.mpr (hδ k).le).trans (mul_nonneg hK (sq_nonneg _))
    · nlinarith
  have hfs (k : ℕ) : IsPointedApproximation (p k) 0 (r k) 10 (δ k/5)
      (fun x => (5:ℝ) • f k x) := by
    have hf' : IsPointedApproximation (p k) 0 (5*r k) 2 (δ k/25) (f k) := by
      simpa only [show 5*r k=R k by dsimp only [r]; ring] using hf k
    have hh := hf'.change_scale (hr k) (by norm_num : (0:ℝ)<5)
    simpa only [show (5:ℝ)*2=10 by norm_num,
      show (5:ℝ)*(δ k/25)=δ k/5 by ring] using hh
  have hm (k : ℕ) : ∃ V : X → Euclidean n,
      IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (e k) V := by
    obtain ⟨V,hVm,hV⟩ := (hfs k).exists_measurable (hr k) (by norm_num)
      (div_pos (hδ k) (by norm_num))
    refine ⟨V,hmeasure k (p k) (r k) (hr k) (hsmall k) V hVm ?_⟩
    convert hV using 1 <;> ring
  choose V hV using hm
  have hs (k : ℕ) : FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (e k) (u k) (v k) := by
    have hh := (hsplit k).mono_error _ _ (hapos k).le (hae k)
    simpa only [show 80*r k=16*R k by dsimp only [r]; ring] using hh
  have happ := hX.first_order_frame_convergence hn p r e V hr hbig
    (fun k => (hepos k).le) he1 helim hV u v hs (5*ρ) (by positivity)
  obtain ⟨k,hk⟩ := happ.exists
  have hk' : IsPointedApproximation (p k) 0 ((1/5)*R k) (5/2) (5*ρ)
      (fun x => (r k)⁻¹ • (v k x-v k (p k))) := by
    simpa only [show (1/5)*R k=r k by dsimp only [r]; ring] using hk
  have hout := hk'.change_scale (hR k) (by norm_num : (0:ℝ)<1/5)
  apply hbad k
  simpa only [show (1/5:ℝ)*(5/2)=1/2 by norm_num,
    show (1/5:ℝ)*(5*ρ)=ρ by ring,smul_smul,
    show (1/5:ℝ)*(r k)⁻¹=(R k)⁻¹ by dsimp only [r]; field_simp] using hout

theorem NoncollapsedRCD.flatSplittingInput_of_measured {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hMeasured : LocalMeasuredCoordinateInput hX) : LocalFlatSplittingInput hX := by
  intro hn ρ hρ
  exact hX.flat_splitting_coordinates hn hMeasured hρ

end RegularPointCoordinates

end

end OAI
