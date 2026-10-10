import OAI.Analysis.CircleDomains.Selection.PreparedHeightSelection
import OAI.Analysis.CircleDomains.Topology.FixedDiskCutoffs
import OAI.Analysis.CircleDomains.Selection.RestrictedFlattenedSelection
import OAI.Analysis.CircleDomains.Transfer.ModelFixedWorkingBounds
import OAI.Analysis.CircleDomains.Sobolev.SmallSelectedBarrierEnergy
import OAI.Analysis.CircleDomains.Selection.SelectedOuterMargin
import OAI.Analysis.CircleDomains.Selection.SelectedOldError
import OAI.Analysis.CircleDomains.Modulus.TranslatedPhysicalBarrier

namespace OAI

/-! The actual finite appending construction, before choosing its inner
contours. The resulting fields concern the original source functions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

structure AppendingPairData (G : Set Sphere) {m : ℕ}
    (u : Fin m → EuclideanPlane → ℝ)
    (Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)) (a δ η : ℝ) where
  old : Fin m → EuclideanPlane → ℝ
  p : EuclideanPlane → ℝ
  q : EuclideanPlane → ℝ
  old_continuous : ∀ i, Continuous (old i)
  old_compact : ∀ i, HasCompactSupport (old i)
  old_witness : ∀ i, DeGiorgi.MemW1pWitness 2 (old i) (physicalPlaneDomain G)
  old_close : ∀ i x, |old i x-u i x| < δ
  old_error : ∀ i, (eLpNorm (fun x => (old_witness i).weakGrad x-(Wold i).weakGrad x) 2
    (volume.restrict (physicalPlaneDomain G))).toReal < δ
  p_continuous : Continuous p
  q_continuous : Continuous q
  p_compact : HasCompactSupport p
  q_compact : HasCompactSupport q
  p_witness : DeGiorgi.MemW1pWitness 2 p (physicalPlaneDomain G)
  q_witness : DeGiorgi.MemW1pWitness 2 q (physicalPlaneDomain G)
  pair_null : ∀ i j : Fin (m+2), i ≠ j → volume ((fun x =>
    (sphereFromPlaneFunction (appendScalarPair old p q i) x,
      sphereFromPlaneFunction (appendScalarPair old p q j) x)) '' Gᶜ) = 0
  barrier : EuclideanPlane → ℝ
  radius : ℝ
  radius_pos : 0 < radius
  barrier_smooth : ContDiff ℝ ∞ barrier
  barrier_compact : HasCompactSupport barrier
  barrier_support : tsupport barrier ⊆ ball 0 (4*a)
  barrier_unit : ∀ x, barrier x ∈ Icc (0 : ℝ) 1
  barrier_one : ∀ x ∈ ball 0 radius, barrier x = 1
  small_energy : ∀ c : EuclideanPlane,
    ∃ V : DeGiorgi.MemW1pWitness 2 (fun x => barrier (planePair (p x) (q x)-c))
      (physicalPlaneDomain G ∩ ball 0 (65*a)),
      (eLpNorm V.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η
  trace_bound : ∀ z ∈ Gᶜ, ‖planePair (sphereFromPlaneFunction p z) (sphereFromPlaneFunction q z)‖ ≤ 8*a
  outer_margin : ∀ x ∈ physicalPlaneDomain G, 63*a ≤ ‖x‖ → ‖x‖ ≤ 65*a →
    ∀ c : EuclideanPlane, ‖c‖ ≤ 8*a → 5*a ≤ ‖planePair (p x) (q x)-c‖

 theorem exists_appending_pair_data
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ)
    (hB : IsCompact {z : ℂ | (z : Sphere) ∉ G})
    (hBne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hpairs : ∀ i j, i ≠ j → volume ((fun x =>
      (sphereFromPlaneFunction (u i) x,sphereFromPlaneFunction (u j) x)) '' Gᶜ) = 0)
    (hne : Nonempty (CompactScalarModel G u))
    {a δ η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hη : 0 < η)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G) :
    Nonempty (AppendingPairData G u Wold a δ η) := by
  obtain ⟨ζ,hζ,hsζ,hsζ66,hζunit,hζ65⟩ := exists_complex_disk_cutoff
    (show 65*a < 66*a by linarith)
  obtain ⟨θ,Cθ,hCθ,hθ,hsθ,hsθ100,hθunit,hθ85,hθd⟩ := exists_physical_disk_cutoff
    (show 85*a < 100*a by linarith)
  obtain ⟨Φ,r,M₁,M₂,hr,hM₁,hM₂,hΦ,hsΦ,hsΦ4,hΦunit,hΦone,hΦE,hΦD,hΦDD⟩ :=
    exists_physical_small_barrier (show 0 < 4*a by positivity)
      (show 0 < (η/3)^2 by positivity)
  let N := 2*(Real.pi*(85*a)^2+1)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  obtain ⟨t,ht,htbudget⟩ := exists_barrier_error_budget hη hM₁ hM₂ hN
  let b := min t (min δ (min (δ^2) a))
  have hb : 0 < b := by dsimp only [b]; positivity
  obtain ⟨e,he,heb,d,hd,hde,M,H,S,hH,hS,E,hHz,hE⟩ := exists_small_selected_height_data
    hsolver hprincipal hgreen harea hsard hsch hcoarea hG hconn hinf hTD hB hBne
    hu hs Wold hne ha hsource (hBa.trans (ball_subset_ball (show a ≤ 2*a by linarith)))
    (100*a) (67*a) θ hθ hsθ hsθ100 hCθ hθunit hθd hb ht
  have het : e ≤ t := (heb.trans_le (min_le_left _ _)).le
  have heδ : e ≤ δ := (heb.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have heδsq : e ≤ δ^2 := (heb.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))).le
  have hea : e ≤ a := (heb.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hζB : ∀ z : ℂ, (z : Sphere) ∉ G → ζ z = 1 := fun z hz =>
    hζ65 z (ball_subset_closedBall ((ball_subset_ball (show a ≤ 65*a by linarith)) (hBa hz)))
  have hθF : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1 := by
    intro x hx
    apply hθ85
    have hbnd := (M.uniform_omitted_and_image_bound harea hG ha hsource).1
      (complexPlaneCoordinates x) hx
    rw [mem_closedBall_zero_iff]
    have hn : ‖x‖ ≤ 3*a := by simpa only [complexPlaneCoordinates_norm] using hbnd
    linarith
  have hsζ67 : tsupport ζ ⊆ ball 0 (67*a) :=
    hsζ66.trans (ball_subset_ball (by linarith))
  obtain ⟨hc,hcomp,⟨Wt⟩,hpair⟩ := S.compact_tests M hsard hsch hcoarea
    hG hconn hinf hTD hu hs hpairs H hHz Wold ζ hζ hsζ hζB hsζ67 θ hθ hsθ hsθ100 hθF
  let p := M.compactPrioritySource S.cutoff S.value ζ
  let q := M.compactHeightSource H (flattenValues S.heightValues) θ
  have hpc : Continuous p := hc (Fin.succ (0 : Fin (m+1)))
  have hqc' : Continuous q := hc 0
  have hps : HasCompactSupport p := hcomp (Fin.succ (0 : Fin (m+1)))
  have hqs : HasCompactSupport q := hcomp 0
  let Wp : DeGiorgi.MemW1pWitness 2 p (physicalPlaneDomain G) := Wt (Fin.succ (0 : Fin (m+1)))
  let Wq : DeGiorgi.MemW1pWitness 2 q (physicalPlaneDomain G) := Wt 0
  have hopen := (isOpen_physicalPlaneDomain hG).inter (isOpen_ball (x := (0 : EuclideanPlane)) (ε := 65*a))
  let Wp65 := Wp.restrict hopen inter_subset_left
  let Wq65 := Wq.restrict hopen inter_subset_left
  obtain ⟨⟨Wx⟩,⟨Wy⟩⟩ := M.working_coordinate_witnesses hG hinf (65*a)
  let S65 := S.restrictWorking M hG hinf (show 65*a ≤ 67*a by linarith)
  have hζwork : ∀ z ∈ {z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 (65*a), ζ z = 1 :=
    fun z hz => hζ65 z (ball_subset_closedBall hz.2)
  have hθwork : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 (65*a),
      θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1 := by
    intro x hx
    apply hθ85
    rw [mem_closedBall_zero_iff]
    have hbnd := M.fixed_working_image_bound harea hG ha hsource hx.1
      (show ‖complexPlaneCoordinates x‖ ≤ 67*a by
        rw [complexPlaneCoordinates_norm]; have := mem_ball_zero_iff.mp hx.2; linarith)
    simpa only [← complexPlaneCoordinates_norm (complexPlaneCoordinates.symm _),
      complexPlaneCoordinates.apply_symm_apply] using hbnd
  have hheight : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 (65*a),
      |H.height (M.function (complexPlaneCoordinates x))-(M.function (complexPlaneCoordinates x)).im| ≤ e := by
    intro x hx
    apply (hH _ _).le
    rw [mem_closedBall_zero_iff]
    have hbnd := M.fixed_working_image_bound harea hG ha hsource hx.1
      (show ‖complexPlaneCoordinates x‖ ≤ 67*a by
        rw [complexPlaneCoordinates_norm]; have := mem_ball_zero_iff.mp hx.2; linarith)
    linarith
  have hNwork := M.working_joint_norm_le hG hinf (65*a)
    (show 0 ≤ 85*a by positivity) (fun z hz hzn => M.fixed_working_image_bound harea hG ha hsource hz
      (by have := mem_ball_zero_iff.mp hzn; linarith)) Wx Wy
  have hsmall : ∀ c : EuclideanPlane,
      ∃ V : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair (p x) (q x)-c))
        (physicalPlaneDomain G ∩ ball 0 (65*a)),
        (eLpNorm V.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η := by
    intro c
    obtain ⟨hcs,hcc,_,hcu,_,hcD,hcDD⟩ := translatedPhysicalBarrier_data hΦ hsΦ hsΦ4 hΦunit hΦone hΦD hΦDD c
    have hcE : (∫ x, ‖planeCovectorGradient (fderiv ℝ (translatedPhysicalBarrier Φ c) x)‖^2) ≤ (η/3)^2 := by
      rw [translatedPhysicalBarrier_energy (hΦ.differentiable (by simp))]
      exact hΦE.le
    exact M.small_selected_barrier_energy hG hinf H S65 he.le het ht.le hη ζ θ hζwork hθwork
      hpc hqc' Wp65 Wq65 Wx Wy E hE.le hheight hNwork hcs hcc
      (show (0 : ℝ) ≤ 1 by norm_num) hM₁ hM₂
      (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hcu z).1]; exact (hcu z).2)
      hcD hcDD hcE htbudget
  refine ⟨{
    old := fun i => flattenValues (S.oldValues i) ∘ u i
    p := p, q := q, old_continuous := ?_, old_compact := ?_
    old_witness := S.oldWitness
    old_close := fun i => (S.old_errors M hδ heδ heδsq i).1
    old_error := fun i => (S.old_errors M hδ heδ heδsq i).2
    p_continuous := hpc, q_continuous := hqc', p_compact := hps, q_compact := hqs
    p_witness := Wp, q_witness := Wq, pair_null := hpair
    barrier := Φ, radius := r, radius_pos := hr, barrier_smooth := hΦ, barrier_compact := hsΦ
    barrier_support := hsΦ4, barrier_unit := hΦunit, barrier_one := hΦone
    small_energy := hsmall, trace_bound := ?_, outer_margin := ?_ }⟩
  · intro i
    exact (flattenValues_lipschitz (S.old_open i).measurableSet).continuous.comp (hu i)
  · intro i
    exact (hs i).comp_left (flattenValues_zero _)
  · intro z hz
    cases z using OnePoint.rec with
    | infty => exact (hz hinf).elim
    | coe z =>
      have hh := M.selected_pair_trace_bound hsard hsch hG hconn hinf hTD H S
        (M.uniform_omitted_and_image_bound harea hG ha hsource).1
        (fun z hz => (hH z (closedBall_subset_closedBall (show 3*a ≤ 100*a by linarith) hz)).le)
        ζ hζB θ hθF hz
      exact hh.trans (by linarith)
  · intro x hx hx63 hx65 c hc
    have hζx := hζ65 (complexPlaneCoordinates x)
      (mem_closedBall_zero_iff.mpr (by simpa only [complexPlaneCoordinates_norm] using hx65))
    have himage := M.fixed_working_image_bound harea hG ha hsource hx
      (show ‖complexPlaneCoordinates x‖ ≤ 67*a by rw [complexPlaneCoordinates_norm]; linarith)
    have hθx := hθ85 (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x)))
      (mem_closedBall_zero_iff.mpr (by
        simpa only [← complexPlaneCoordinates_norm (complexPlaneCoordinates.symm _),
          complexPlaneCoordinates.apply_symm_apply] using himage))
    have hHx := (hH (M.function (complexPlaneCoordinates x))
      (mem_closedBall_zero_iff.mpr (by linarith))).le
    have hxs : complexPlaneCoordinates x ∉ ⋃ n, support (S.cutoff n) := by
      intro hh
      obtain ⟨n,hn⟩ := mem_iUnion.mp hh
      have hn' := mem_ball_zero_iff.mp (hS n hn)
      rw [complexPlaneCoordinates_norm] at hn'
      linarith
    have hm := M.selected_pair_outer_margin (r := 4*a) (σ := a) (C := 8*a) (v := e)
      harea H S ha hsource ζ θ hx hζx hθx hHx hxs
      (show 2*a ≤ ‖x‖ by linarith) hc (by linarith)
    calc
      5*a = 4*a+a := by ring
      _ ≤ ‖planePair (p x) (q x)-c‖ := hm

end CircleDomainRigidity

end

end OAI
