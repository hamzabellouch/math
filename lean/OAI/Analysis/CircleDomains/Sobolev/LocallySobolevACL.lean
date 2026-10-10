import OAI.Analysis.CircleDomains.Sobolev.LocallySobolevPartials

namespace OAI

/-! Coordinate absolute continuity for continuous local W1,2 functions,
obtained from compact cutoffs without assumptions at infinity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma compact_core_sobolev_coordinate_ACL
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u Ω) (i : Fin 2) :
    ∃ V : Set EuclideanPlane, IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∀ᵐ y ∂volume, ∀ a b : ℝ, MapsTo (physicalCoordinateLine i y) (uIcc a b) V →
        AbsolutelyContinuousOnInterval (fun s => u (physicalCoordinateLine i y s)) a b := by
  obtain ⟨η, V, hη, hsη, _, hηΩ, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro p hp
    apply hηΩ
    apply subset_tsupport η
    change η p ≠ 0
    rw [hone p hp]
    exact one_ne_zero
  let w : EuclideanPlane → ℝ := fun p => η p*u p
  obtain ⟨Ww⟩ := exists_global_compact_cutoff_witness hΩ W.memW1p hη hsη hηΩ
  have heq : EqOn w u V := fun p hp => by dsimp only [w]; rw [hone p hp, one_mul]
  refine ⟨V, hV, hKV, hVΩ, ?_⟩
  filter_upwards [sobolev_coordinate_absolutelyContinuous (hη.continuous.mul hu) hsη.mul_right Ww i]
    with y hy
  intro a b hab
  exact (hy a b).congr (fun t ht => heq (hab ht))

lemma locally_sobolev_coordinate_absolutelyContinuous {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun s => u (physicalCoordinateLine i y s)) a b := by
  have hsub (n : ℕ) : closedBall (0 : EuclideanPlane) n ⊆ ball 0 (n+1) := by
    intro p hp
    exact (mem_closedBall.mp hp).trans_lt (by linarith)
  choose O hO hKO hOsub hac using fun n : ℕ =>
    compact_core_sobolev_coordinate_ACL isOpen_ball (isCompact_closedBall (0 : EuclideanPlane) n)
      (hsub n) hu (scalarBallWeakWitness hu hw hLp (n+1)) i
  have hall : ∀ᵐ y ∂volume, ∀ n : ℕ, ∀ a b : ℝ,
      MapsTo (physicalCoordinateLine i y) (uIcc a b) (O n) →
        AbsolutelyContinuousOnInterval (fun s => u (physicalCoordinateLine i y s)) a b :=
    ae_all_iff.mpr hac
  filter_upwards [hall] with y hy
  intro a b
  obtain ⟨B, hB⟩ := isCompact_uIcc.bddAbove_image
    ((physicalCoordinateLine_contDiff i y).continuous.norm.continuousOn)
  obtain ⟨n, hn⟩ := exists_nat_gt B
  apply hy n a b
  intro t ht
  apply hKO n
  rw [mem_closedBall, dist_zero_right]
  exact (hB (mem_image_of_mem _ ht)).trans hn.le

end CircleDomainRigidity

end

end OAI
