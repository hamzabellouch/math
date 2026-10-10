import Mathlib
import OAI.Geometry.NearbyLagrangian.HomogeneousFunctions
import OAI.Geometry.NearbyLagrangian.CylinderTransport
import OAI.Geometry.NearbyLagrangian.Isotopies
import OAI.Geometry.NearbyLagrangian.PolarCharts

namespace OAI

/-! Smooth cylinder cutoffs and compact extension of isotopies. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.PolarCylinder
open scoped ContDiff Topology
open Set Filter Metric Function

def squareBump {νc ν : ℝ} (hνc : 0 < νc) (hν : νc < ν) : ContDiffBump (0:ℝ) where
  rIn := νc
  rOut := (νc+ν)/2
  rIn_pos := hνc
  rIn_lt_rOut := by linarith

def squareCutoff {νc ν : ℝ} (hνc : 0 < νc) (hν : νc < ν) (a : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  squareBump hνc hν (radialCoordinates a).1 * squareBump hνc hν (radialCoordinates a).2

lemma contDiff_squareCutoff {νc ν : ℝ} (hνc : 0 < νc) (hν : νc < ν) :
    ContDiff ℝ ∞ (squareCutoff hνc hν) :=
  ((squareBump hνc hν).contDiff.comp (contDiff_fst.comp radialCoordinates.contDiff)).mul
    ((squareBump hνc hν).contDiff.comp (contDiff_snd.comp radialCoordinates.contDiff))

lemma squareCutoff_mem_Icc {νc ν : ℝ} (hνc : 0 < νc) (hν : νc < ν) (a : EuclideanSpace ℝ (Fin 2)) :
    squareCutoff hνc hν a ∈ Icc (0:ℝ) 1 := by
  unfold squareCutoff
  exact ⟨mul_nonneg (squareBump hνc hν).nonneg (squareBump hνc hν).nonneg,
    (mul_le_of_le_one_left (squareBump hνc hν).nonneg (squareBump hνc hν).le_one).trans
      (squareBump hνc hν).le_one⟩

lemma squareCutoff_eq_one {νc ν : ℝ} (hνc : 0 < νc) (hν : νc < ν)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ radialSquare νc) : squareCutoff hνc hν a = 1 := by
  obtain ⟨h₁,h₂⟩ := (mem_radialSquare_iff νc a).mp ha
  have h₁' : (radialCoordinates a).1 ∈ closedBall (0:ℝ) νc := by
    simpa only [mem_closedBall,Real.dist_eq,sub_zero,abs_le] using ⟨h₁.1.le,h₁.2.le⟩
  have h₂' : (radialCoordinates a).2 ∈ closedBall (0:ℝ) νc := by
    simpa only [mem_closedBall,Real.dist_eq,sub_zero,abs_le] using ⟨h₂.1.le,h₂.2.le⟩
  rw [squareCutoff,(squareBump hνc hν).one_of_mem_closedBall h₁',
    (squareBump hνc hν).one_of_mem_closedBall h₂',one_mul]

lemma squareCutoff_eventuallyEq_one {νc ν : ℝ} (hνc : 0 < νc) (hν : νc < ν)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ radialSquare νc) :
    squareCutoff hνc hν =ᶠ[𝓝 a] fun _ => (1:ℝ) := by
  filter_upwards [(radialSquare νc).isOpen.mem_nhds ha] with b hb
  exact squareCutoff_eq_one hνc hν hb

lemma squareCutoff_support {νc ν : ℝ} (hνc : 0 < νc) (hν : νc < ν) :
    HasCompactSupport (squareCutoff hνc hν) ∧ tsupport (squareCutoff hνc hν) ⊆ radialSquare ν := by
  let r := (νc+ν)/2
  let C := radialCoordinates.symm '' (closedBall (0:ℝ) r ×ˢ closedBall (0:ℝ) r)
  have hC : IsCompact C := ((isCompact_closedBall (0:ℝ) r).prod (isCompact_closedBall (0:ℝ) r)).image
    radialCoordinates.symm.continuous
  have hs : Function.support (squareCutoff hνc hν) ⊆ C := by
    intro a ha
    have hne := mul_ne_zero_iff.mp ha
    have h₁ : (radialCoordinates a).1 ∈ ball (0:ℝ) r := by
      change _ ∈ ball (0:ℝ) (squareBump hνc hν).rOut
      rw [← (squareBump hνc hν).support_eq]
      exact hne.1
    have h₂ : (radialCoordinates a).2 ∈ ball (0:ℝ) r := by
      change _ ∈ ball (0:ℝ) (squareBump hνc hν).rOut
      rw [← (squareBump hνc hν).support_eq]
      exact hne.2
    exact ⟨radialCoordinates a,⟨ball_subset_closedBall h₁,ball_subset_closedBall h₂⟩,
      radialCoordinates.symm_apply_apply a⟩
  have ht : tsupport (squareCutoff hνc hν) ⊆ C := closure_minimal hs hC.isClosed
  refine ⟨HasCompactSupport.of_support_subset_isCompact hC hs,?_⟩
  intro a ha
  obtain ⟨x,hx,rfl⟩ := ht ha
  apply (mem_radialSquare_iff ν _).mpr
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  have hx₁ : |x.1| ≤ r := by simpa only [mem_closedBall,Real.dist_eq,sub_zero] using hx.1
  have hx₂ : |x.2| ≤ r := by simpa only [mem_closedBall,Real.dist_eq,sub_zero] using hx.2
  have hr : r < ν := by dsimp [r]; linarith
  have h₁ := abs_le.mp hx₁
  have h₂ := abs_le.mp hx₂
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma squareCutoff_gradient_bound {νc ν : ℝ} (hνc : 0 < νc) (hν : νc < ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖gradient (squareCutoff hνc hν) a‖ ≤ C := by
  have hc := (squareCutoff_support hνc hν).1.fderiv ℝ
  have hf := (contDiff_squareCutoff hνc hν).continuous_fderiv (by simp)
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf
  refine ⟨max C 0,le_max_right _ _,fun a => ?_⟩
  have hg : ‖gradient (squareCutoff hνc hν) a‖ = ‖fderiv ℝ (squareCutoff hνc hν) a‖ := by
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.norm_map _
  rw [hg]
  exact (hC a).trans (le_max_left _ _)

def momentumBump (R : ℝ) (hR : 0 < R) : ContDiffBump (0:EuclideanSpace ℝ (Fin 2)) where
  rIn := R
  rOut := R+1
  rIn_pos := hR
  rIn_lt_rOut := by linarith

lemma momentumBump_plateau (R : ℝ) (hR : 0 < R) {p : EuclideanSpace ℝ (Fin 2)}
    (hp : ‖p‖ ≤ R) : momentumBump R hR p = 1 :=
  (momentumBump R hR).one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right,momentumBump] using hp)

end NearbyLagrangian.PolarCylinder

namespace NearbyLagrangian
open Set Filter Function TopologicalSpace Transport SmoothFlow RadialExtension PolarCylinder
open scoped Manifold ContDiff Topology NNReal

lemma antisymmetric_CLM_zero_right {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V →L[ℝ] ℝ) (d : V →L[ℝ] V) (u : V) :
    A (d u) (d 0) - A (d 0) (d u) = 0 := by
  simp only [map_zero,zero_apply,sub_zero]

lemma symplecticForm_zero_right {n : ℕ} (z : Cotangent n)
    (u : TangentSpace (cotangentModel n) z) : symplecticForm z u 0 = 0 := by
  exact antisymmetric_CLM_zero_right (V:=CotangentVector n) _ _ u

theorem IsCompactHamiltonianIsotopy.cylinder_extension {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {νc ν : ℝ} (hνc : 0 < νc) (hν : νc < ν)
    (U : Opens (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) =
      (radialSquare ν : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ
        (univ : Set (EuclideanSpace ℝ (Fin 2)))) (W : Opens (E × E))
    (e : Diffeomorph ((cotangentModel n).prod
      𝓘(ℝ,EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) 𝓘(ℝ,E × E)
      (Cotangent n × U) W ∞)
    (he : IsSymplecticCylinderChart U W e (fun z u v => symplecticForm z u v))
    {H : ℝ → Cotangent n → ℝ} {φ : ℝ → CotangentDiffeomorph n}
    (h : IsCompactHamiltonianIsotopy H φ) :
    ∃ (K : ℝ × (E × E) → ℝ) (F : SupportedHamiltonianEvolution W K),
      ∀ (L N : Set (Cotangent n)), φ 1 '' L = N →
      (fun z : Cotangent n × U => evolution F.flow ((0,(e z:E × E)),1)) ''
          {z | z.1 ∈ L ∧ (z.2:EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)).2 = 0} ∩
        (fun z : Cotangent n × U => (e z:E × E)) ''
          {z | (z.2:EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)).1 ∈ radialSquare νc} =
        (fun z : Cotangent n × U => (e z:E × E)) ''
          {z | z.1 ∈ N ∧
            (z.2:EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)).1 ∈ radialSquare νc ∧
            (z.2:EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)).2 = 0} := by
  obtain ⟨B,hB,hb⟩ := h.flatten.uniform_bound
  obtain ⟨C,hC,hζC⟩ := squareCutoff_gradient_bound hνc hν
  let ζ := squareCutoff hνc hν
  have hζd : ContDiff ℝ ∞ ζ := contDiff_squareCutoff hνc hν
  have hζc : HasCompactSupport ζ := (squareCutoff_support hνc hν).1
  have hpos : 0 < B*C+1 := by positivity
  let ξ := momentumBump (B*C+1) hpos
  have hξd : ContDiff ℝ ∞ ξ := ξ.contDiff
  have hξc : HasCompactSupport ξ := ξ.hasCompactSupport
  have hUU : tsupport ζ ×ˢ tsupport ξ ⊆ (U:Set _) := by
    rw [hU]
    exact prod_mono (squareCutoff_support hνc hν).2 (subset_univ _)
  obtain ⟨S,hS,hSS⟩ := h.2.2.1
  obtain ⟨F⟩ := exists_cylinderEvolution U W e hS hSS h.1 hζd hξd hζc hξc hUU
  refine ⟨cylinderHamiltonian U W e H ζ ξ,F,fun L N himage => ?_⟩
  have hKH : ∀ t ∈ Icc (0:ℝ) 1, ∀ x : W,
      cylinderHamiltonian U W e H ζ ξ (t,(x:E × E)) =
        (cutoffHamiltonian (flattenHamiltonian H t) ζ ξ ∘ radialInclusion U) (e.symm x) := by
    intro t _ x
    exact cylinderHamiltonian_apply U W e H ζ ξ t x
  have hHd : ∀ t ∈ Icc (0:ℝ) 1,
      MDifferentiable (cotangentModel n) 𝓘(ℝ,ℝ) (flattenHamiltonian H t) :=
    fun t ht x => timeSlice_mdifferentiable (cotangentModel n) h.flatten.1 ht x
  have hψd : ∀ q, ∀ t ∈ Icc (0:ℝ) 1,
      MDifferentiableWithinAt 𝓘(ℝ,ℝ) (cotangentModel n)
        (fun s => flattenIsotopy φ s q) (Icc (0:ℝ) 1) t := by
    intro q t _
    exact ((contMDiff_timeSlice (contMDiff_flattenIsotopy h.2.1) q).mdifferentiableAt
      (by simp)).mdifferentiableWithinAt
  apply supported_motion_cylinder_image U W e (fun z u v => symplecticForm z u v)
    symplecticForm_zero_right he F hKH hHd (hζd.differentiable (by simp))
    (hξd.differentiable (by simp)) hB.le hC hb hζC
    (fun w => ⟨ξ.nonneg,ξ.le_one⟩) (fun w hw => momentumBump_plateau _ _ hw)
    (fun a ha => squareCutoff_eventuallyEq_one hνc hν ha)
    (fun t q => flattenIsotopy φ t q) h.flatten.2.2.2.1 hψd (fun q t ht v => h.flatten.2.2.2.2 t ht q v)
  simpa only [flattenIsotopy_one] using himage

end NearbyLagrangian

end

end OAI
