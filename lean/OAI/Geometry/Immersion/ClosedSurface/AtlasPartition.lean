import OAI.Geometry.Immersion.ClosedSurface.GlobalPartition

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

lemma finite_positive_threshold {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧ ∀ i, z ≤ v i := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image v)
  have hs : s.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs,?_,Finset.min'_le s 1 (Finset.mem_insert_self _ _),?_⟩
  · have hm := s.min'_mem hs
    simp only [s,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hm
    rcases hm with he | ⟨i,hi⟩
    · rw [he]; norm_num
    · rw [← hi]; exact hv i
  · intro i
    exact Finset.min'_le s (v i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]




theorem exists_manifold_polynomial_square_partition :
    ∃ (t : Finset M) (r : t → ℝ) (ψ : t → M → ℝ),
    ∃ z₀ D : ℝ, ∃ J : ℕ → ℝ,
      0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < D ∧ (∀ j, 1 ≤ J j) ∧
      (∀ i : t, 0 < r i) ∧
      (∀ i : t, Metric.closedBall (coordinateCenter (i : M)) (r i) ⊆ coordinateDomain (i : M)) ∧
      (∀ i : t, ContMDiff planeModel 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ z : ℝ, 0 < z → z ≤ z₀ → ∃ s : t → Finset Index,
        (∑ i, ((s i).card : ℝ)) ≤ D/z^12 ∧
        (∀ i : t, chartSupport (i : M) (ψ i) ⊆ coverRegion (s i) (z^6)) ∧
        (∀ i : t, coverRegion (s i) (z^6) ⊆ Metric.ball (coordinateCenter (i : M)) (r i)) ∧
        (∀ (i : t) a, ContMDiff planeModel 𝓘(ℝ) ∞ (refinedCutoff (i : M) (ψ i) (s i) (z^6) a)) ∧
        (∀ (i : t) a, HasCompactSupport (refinedCutoff (i : M) (ψ i) (s i) (z^6) a)) ∧
        (∀ (i : t) a, tsupport (refinedCutoff (i : M) (ψ i) (s i) (z^6) a) ⊆ tsupport (ψ i) ∩
          chartCoordinates (i : M) ⁻¹' tsupport (normalizedCutoff (s i) (z^6) a)) ∧
        (∀ (i : t) a j x, x ∈ coverRegion (s i) (z^6) →
          ‖iteratedFDeriv ℝ j (normalizedCutoff (s i) (z^6) a) x‖ ≤ J j/z^(6*j)) ∧
        (∀ q, ∑ i, ∑ a ∈ s i, (refinedCutoff (i : M) (ψ i) (s i) (z^6) a q)^2 = 1)) := by
  classical
  obtain ⟨t,r,ψ,hr,hdomain,hψ,hcompact,hsource,hK,hKsub,hnonneg,hsquares⟩ :=
    exists_fixed_convex_coordinate_cover (M := M)
  have hlocal (i : t) := compact_polynomial_square_partition (hK i)
    (Metric.isOpen_ball (x := coordinateCenter (i : M)) (ε := r i))
    ((hKsub i).trans (Metric.ball_subset_ball (show r i/2 ≤ r i by linarith [hr i])))
  choose zi Di Ji hzi hzi1 hDi hJi hpart using hlocal
  obtain ⟨z₀,hz₀,hz₀1,hzi0⟩ := finite_positive_threshold zi hzi
  let D : ℝ := 1 + ∑ i, Di i
  let J (j : ℕ) : ℝ := 1 + ∑ i, Ji i j
  have hD : 0 < D := by
    have hh : 0 ≤ ∑ i, Di i := Finset.sum_nonneg (fun i _ => (hDi i).le)
    change 0 < 1 + ∑ i, Di i
    linarith
  have hJ (j : ℕ) : 1 ≤ J j := by
    have hh : 0 ≤ ∑ i, Ji i j := Finset.sum_nonneg (fun i _ => zero_le_one.trans (hJi i j))
    change 1 ≤ 1 + ∑ i, Ji i j
    linarith
  refine ⟨t,r,ψ,z₀,D,J,hz₀,hz₀1,hD,hJ,hr,hdomain,hψ,?_⟩
  intro z hz hzsmall
  have hd (i : t) := hpart i z hz (hzsmall.trans (hzi0 i))
  choose s hcard hopen hinner houter hsub hsmooth hderiv hsum hsupp using hd
  obtain ⟨hsm,hcomp,hsp,hsq⟩ := global_grid_square_partition (fun i : t => (i : M)) ψ
    hψ hsource hcompact hsquares s (z^6) (pow_pos hz _) hinner
  refine ⟨s,?_,hinner,houter,hsm,hcomp,hsp,?_,hsq⟩
  · calc
      (∑ i, ((s i).card : ℝ)) ≤ ∑ i, Di i / z^12 := Finset.sum_le_sum (fun i _ => hcard i)
      _ = (∑ i, Di i)/z^12 := (Finset.sum_div _ _ _).symm
      _ ≤ D/z^12 := div_le_div_of_nonneg_right (by dsimp [D]; linarith) (pow_pos hz _).le
  · intro i a j x hx
    apply (hderiv i a j x hx).trans
    apply div_le_div_of_nonneg_right _ (pow_pos hz _).le
    have hi : Ji i j ≤ ∑ k, Ji k j := Finset.single_le_sum
      (fun k _ => zero_le_one.trans (hJi k j)) (Finset.mem_univ i)
    change Ji i j ≤ 1 + ∑ k, Ji k j
    linarith

end ClosedSurfaceR4

end

end OAI
