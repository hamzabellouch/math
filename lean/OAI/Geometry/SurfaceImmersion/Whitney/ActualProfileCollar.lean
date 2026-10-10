import OAI.Geometry.SurfaceImmersion.Primitive.ActualProfileCurve

namespace OAI

/-! The positive boundary invariant on the zero-amplitude collar survives
small errors in the five profiles. No large angular derivative is needed there. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

private def collarInvariant (J : BoundaryProfile) (v : ℝ × ℝ × ℝ) : ℝ :=
  (profileCoefficients J 1 * v.1 + profileCoefficients J 0 * v.2.1)^2 + v.2.2 * v.1^2

private lemma continuousAt_collarInvariant {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) (v : ℝ × ℝ × ℝ) :
    ContinuousAt (fun w : BoundaryProfile × (ℝ × ℝ × ℝ) => collarInvariant w.1 w.2) (J,v) := by
  have hc : ContinuousAt (fun w : BoundaryProfile × (ℝ × ℝ × ℝ) =>
      profileCoefficients w.1) (J,v) :=
    ContinuousAt.comp (f := fun w : BoundaryProfile × (ℝ × ℝ × ℝ) => w.1)
      (x := (J,v)) (contDiffAt_profileCoefficients hJ).continuousAt continuous_fst.continuousAt
  have hS := (continuous_apply 0).continuousAt.comp hc
  have hD := (continuous_apply 1).continuousAt.comp hc
  have hb : ContinuousAt (fun w : BoundaryProfile × (ℝ × ℝ × ℝ) => w.2.1) (J,v) :=
    (continuous_fst.comp continuous_snd).continuousAt
  have hcc : ContinuousAt (fun w : BoundaryProfile × (ℝ × ℝ × ℝ) => w.2.2.1) (J,v) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt
  have hk : ContinuousAt (fun w : BoundaryProfile × (ℝ × ℝ × ℝ) => w.2.2.2) (J,v) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt
  exact (((hD.mul hb).add (hS.mul hcc)).pow 2).add (hk.mul (hb.pow 2))

theorem compact_profile_collar {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {J : X → BoundaryProfile} (hJ : Continuous J)
    (hreg : ∀ x, J x ∈ regularBoundaryProfiles)
    {b c k : X → ℝ} (hb : Continuous b) (hc : Continuous c) (hk : Continuous k)
    (hpos : ∀ x, 0 < (profileCoefficients (J x) 1 * b x +
      profileCoefficients (J x) 0 * c x)^2 + k x * b x^2) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : X, ∀ H : BoundaryProfile, ‖H-J x‖ < η →
      H ∈ regularBoundaryProfiles ∧
      0 < (profileCoefficients H 1 * b x + profileCoefficients H 0 * c x)^2 + k x * b x^2 := by
  let V : Set (BoundaryProfile × (ℝ × ℝ × ℝ)) := regularBoundaryProfiles ×ˢ univ
  let O : Set (BoundaryProfile × (ℝ × ℝ × ℝ)) :=
    V ∩ (fun w => collarInvariant w.1 w.2) ⁻¹' Ioi 0
  have hcont : ContinuousOn (fun w => collarInvariant w.1 w.2) V := by
    intro w hw
    exact (continuousAt_collarInvariant hw.1 w.2).continuousWithinAt
  have hO : IsOpen O := hcont.isOpen_inter_preimage
    (isOpen_regularBoundaryProfiles.prod isOpen_univ) isOpen_Ioi
  let f : X → BoundaryProfile × (ℝ × ℝ × ℝ) := fun x => (J x,b x,c x,k x)
  have hf : Continuous f := hJ.prodMk (hb.prodMk (hc.prodMk hk))
  have hfO : range f ⊆ O := by
    rintro _ ⟨x,rfl⟩
    exact ⟨⟨hreg x,mem_univ _⟩,hpos x⟩
  obtain ⟨η,hη,hsub⟩ := (isCompact_range hf).exists_cthickening_subset_open hO hfO
  refine ⟨η,hη,?_⟩
  intro x H hclose
  have hH : (H,b x,c x,k x) ∈ Metric.cthickening η (range f) := by
    apply Metric.thickening_subset_cthickening
    apply Metric.mem_thickening_iff.mpr
    refine ⟨f x,mem_range_self x,?_⟩
    change dist (H,(b x,c x,k x)) (J x,(b x,c x,k x)) < η
    rw [dist_prod_same_right,dist_eq_norm]
    exact hclose
  exact ⟨(hsub hH).1.1,(hsub hH).2⟩

/-- Transfer collar positivity to nonvanishing and antipode avoidance for the
actual second form, using the intrinsic curvature lower bound. -/
theorem compact_actual_profile_collar {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {J : X → BoundaryProfile} (hJ : Continuous J)
    (hreg : ∀ x, J x ∈ regularBoundaryProfiles)
    {b c k : X → ℝ} (hb : Continuous b) (hc : Continuous c) (hk : Continuous k)
    (hpos : ∀ x, 0 < (profileCoefficients (J x) 1 * b x +
      profileCoefficients (J x) 0 * c x)^2 + k x * b x^2) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : X, ∀ F : RField 4, ContDiff ℝ ∞ F →
      ∀ z : ℝ, ∀ p : Base, ‖realBoundaryProfile F z p-J x‖ < η →
      k x ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      realSecondForm F (b x,c x) (b x,c x) p ≠ 0 ∧
      normalize (realSecondForm F (b x,c x) (b x,c x) p) ≠
        -profilePreferred (realBoundaryProfile F z p) := by
  obtain ⟨η,hη,hclose⟩ := compact_profile_collar hJ hreg hb hc hk hpos
  refine ⟨η,hη,?_⟩
  intro x F hF z p herr hcurv
  obtain ⟨hactual,hpositive⟩ := hclose x (realBoundaryProfile F z p) herr
  obtain ⟨f,hn,_,hcoef⟩ := exists_profile_secondFormFrame hF z p hactual
  have hpositive' : 0 < (f.D*b x+f.S*c x)^2+k x*b x^2 := by
    simpa only [hcoef,Matrix.cons_val_zero,Matrix.cons_val_one] using hpositive
  have hactualpos : 0 < (f.D*b x+f.S*c x)^2+
      coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p*b x^2 :=
    hpositive'.trans_le (add_le_add_right (mul_le_mul_of_nonneg_right hcurv (sq_nonneg _)) _)
  have hcomp := pure_first_positive_of_collar (N := f.N) (L := f.L) f.size_pos hactualpos
  simpa only [hn] using f.actual_curve_avoidance hF (b x) (c x) (Or.inl hcomp)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
