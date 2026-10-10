import Mathlib
import OAI.GroupTheory.FiniteType.CoveringCellGeometryHausdorff

namespace OAI

noncomputable section
namespace PresentationGeometry.CellCoverExtension
open Set Cells Metric CategoryTheory HomologicalComplex SingularChains
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k d : ℕ} (f : C(boundary k d,X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k d,Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

lemma any_attaching_lift_nullhomotopic {n : ℕ} (hd : d = n+3) (i : Fin k)
    (t : C(SphereCover.Sphere (Fin d → ℝ),Z.TotalSpace))
    (ht : ∀ v, Z.proj (t v) = f (boundarySlice i v)) :
    ∃ z : (coveringCore f b Z pot s hs hpot).TotalSpace,
      ((oldLift f b Z pot s hs hpot).comp t).Homotopic (ContinuousMap.const _ z) := by
  subst d
  let : SimplyConnectedSpace (SphereCover.Sphere (Fin (n+3) → ℝ)) :=
    SphereCover.normed_simplyConnected n (by simp)
  let : ContractibleSpace (Disk (n+3)) := Metric.contractibleSpace_closedBall (by norm_num)
  exact CoveringCellGeometry.boundary_nullhomotopic
    (coveringCore_isCoveringMap f b Z pot s hs hpot) (attachedDisk f i) sphereInDisk
    ((oldLift f b Z pot s hs hpot).comp t)
    (by
      funext v
      exact (congrArg (Adjunction.old f) (ht v)).trans (attachedDisk_boundary f i v).symm)
    (Classical.arbitrary _)

lemma any_attaching_homology_killed {n : ℕ} (hd : d = n+3) (i : Fin k)
    (t : C(SphereCover.Sphere (Fin d → ℝ),Z.TotalSpace))
    (ht : ∀ v, Z.proj (t v) = f (boundarySlice i v)) (j : ℕ) (hj : j ≠ 0) :
    homologyMap (map t) j ≫ homologyMap (map (oldLift f b Z pot s hs hpot)) j = 0 := by
  obtain ⟨z,hz⟩ := any_attaching_lift_nullhomotopic f b Z pot s hs hpot hd i t ht
  rw [← homologyMap_comp,← map_comp,homologyMap_of_homotopic hz,homologyMap_const_zero j hj z]

lemma deck_attaching_homology_killed {n : ℕ} (hd : d = n+3) (i : Fin k) (q : Q)
    (j : ℕ) (hj : j ≠ 0) :
    homologyMap (map (s.comp (boundarySlice i))) j ≫
      homologyMap (map (⟨CoreDeck.right Z q,CoreDeck.continuous_right Z (CoreDeck.of_potential Z pot hpot) q⟩ : C(Z.TotalSpace,Z.TotalSpace))) j ≫
        homologyMap (map (oldLift f b Z pot s hs hpot)) j = 0 := by
  rw [← Category.assoc,← homologyMap_comp,← map_comp]
  apply any_attaching_homology_killed f b Z pot s hs hpot hd i _ _ j hj
  intro v
  exact hs (boundarySlice i v)
end PresentationGeometry.CellCoverExtension

open Set Topology Metric
namespace SimplexDisk

def Fat (n : ℕ) : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

lemma closed (n : ℕ) : IsClosed (Fat n) := by
  have h : Fat n = (⋂ i, {x : Fin n → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x; simp [Fat]
  rw [h]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_le (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)

lemma convex (n : ℕ) : Convex ℝ (Fat n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a*x i + b*y i) ≤ 1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

lemma bounded (n : ℕ) : Bornology.IsBounded (Fat n) := by
  apply (isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset
  intro x hx
  rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
  intro i
  rw [Real.norm_eq_abs,abs_of_nonneg (hx.1 i)]
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

lemma interior_nonempty (n : ℕ) : (interior (Fat n)).Nonempty := by
  let O : Set (Fin n → ℝ) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
  have hO : IsOpen O := by
    have h : O = (⋂ i, {x : Fin n → ℝ | 0 < x i}) ∩ {x | ∑ i, x i < 1} := by
      ext x; simp [O]
    rw [h]
    exact (isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))).inter
      (isOpen_lt (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)
  have hsub : O ⊆ Fat n := fun x hx => ⟨fun i => (hx.1 i).le,hx.2.le⟩
  refine ⟨fun _ => 1 / ((n:ℝ)+1), hO.subset_interior_iff.mpr hsub ?_⟩
  constructor
  · intro i
    positivity
  · dsimp
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)

def fstEquiv (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+1)) ≃ₜ Fat n where
  toFun s := ⟨fun i => s.weights (Fin.succ i),⟨fun i => s.weights_nonneg _,by
    have h := s.total_of_fintype
    rw [Fin.sum_univ_succ] at h
    linarith [s.weights_nonneg 0]⟩⟩
  invFun x := {
    weights := Finsupp.equivFunOnFinite.symm (Fin.cons (1-∑i, x.1 i) x.1)
    nonneg := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using sub_nonneg.mpr x.2.2
      · simpa using x.2.1 j
    total := by simp [Finsupp.sum_fintype, Fin.sum_univ_succ] }
  left_inv s := by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 1 - ∑ j : Fin n, s.weights j.succ = s.weights 0
      have h := s.total_of_fintype
      rw [Fin.sum_univ_succ] at h
      linarith
    · rfl
  right_inv x := by apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.succ i)
  continuous_invFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun x : Fat n => 1 - ∑ j, x.1 j)
      exact continuous_const.sub (continuous_finsetSum _
        (fun j _ => (continuous_apply j).comp continuous_subtype_val))
    · change Continuous (fun x : Fat n => x.1 j)
      exact (continuous_apply j).comp continuous_subtype_val

lemma exists_ambient (n : ℕ) : ∃ h : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
    h '' interior (Fat n) = ball 0 1 ∧ h '' Fat n = closedBall 0 1 ∧
      h '' frontier (Fat n) = sphere 0 1 := by
  simpa only [(closed n).closure_eq] using
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex n) (interior_nonempty n) (bounded n)

lemma interior_pos {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ interior (Fat n)) (i : Fin n) :
    0 < x i := by
  have h : x ∈ interior ((fun x : Fin n → ℝ => x i) ⁻¹' Ici 0) :=
    interior_mono (fun _ hy => hy.1 i) hx
  have h' := (isOpenMap_eval i).interior_preimage_subset_preimage_interior h
  simpa only [interior_Ici,mem_preimage,mem_Ioi] using h'

def sumCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i

@[simp] lemma sumCLM_apply (n : ℕ) (x : Fin n → ℝ) : sumCLM n x = ∑ i, x i := by
  simp [sumCLM]

lemma sumCLM_surj (n : ℕ) : Function.Surjective (sumCLM (n+1)) := by
  intro r
  refine ⟨Pi.single (0 : Fin (n+1)) r, ?_⟩
  simp [sumCLM_apply]

lemma interior_sum_lt {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ interior (Fat n)) :
    ∑ i, x i < 1 := by
  cases n with
  | zero => simp
  | succ n =>
    have h : x ∈ interior ((sumCLM (n+1)) ⁻¹' Iic 1) :=
      interior_mono (fun _ hy => by simpa using hy.2) hx
    have h' := ((sumCLM (n+1)).isOpenMap (sumCLM_surj n)).interior_preimage_subset_preimage_interior h
    simpa only [interior_Iic,mem_preimage,mem_Iio,sumCLM_apply] using h'

lemma fstEquiv_frontier {n : ℕ} (s : Convexity.StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1))
    (hj : s.weights j = 0) : (fstEquiv n s).1 ∈ frontier (Fat n) := by
  rw [mem_frontier_iff_notMem_interior (fstEquiv n s).2]
  intro hi
  revert hj
  refine Fin.cases ?_ (fun k => ?_) j
  · intro h0
    have hs := interior_sum_lt hi
    change ∑ i : Fin n, s.weights i.succ < 1 at hs
    have hsum := s.total_of_fintype
    rw [Fin.sum_univ_succ,h0,zero_add] at hsum
    linarith
  · intro hk
    have hp := interior_pos hi k
    change 0 < s.weights k.succ at hp
    linarith

def ambient (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) := Classical.choose (exists_ambient n)

lemma ambient_image (n : ℕ) : ambient n '' Fat n = closedBall 0 1 :=
  (Classical.choose_spec (exists_ambient n)).2.1

lemma ambient_frontier (n : ℕ) : ambient n '' frontier (Fat n) = sphere 0 1 :=
  (Classical.choose_spec (exists_ambient n)).2.2

def diskEquiv (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+1)) ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (fstEquiv n).trans (((ambient n).image (Fat n)).trans (Homeomorph.setCongr (ambient_image n)))

@[simp] lemma diskEquiv_val (n : ℕ) (s : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (diskEquiv n s).1 = ambient n (fstEquiv n s).1 := rfl

lemma diskEquiv_boundary {n : ℕ} (s : Convexity.StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1))
    (hj : s.weights j = 0) : ‖(diskEquiv n s).1‖ = 1 := by
  have h : (diskEquiv n s).1 ∈ sphere (0 : Fin n → ℝ) 1 := by
    rw [diskEquiv_val,← ambient_frontier]
    exact ⟨_,fstEquiv_frontier s j hj,rfl⟩
  simpa only [mem_sphere,dist_zero_right] using h

lemma interior_of_pos {n : ℕ} {x : Fin n → ℝ}
    (hp : ∀ i, 0 < x i) (hs : ∑ i, x i < 1) : x ∈ interior (Fat n) := by
  let O : Set (Fin n → ℝ) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
  have hO : IsOpen O := by
    have h : O = (⋂ i, {x : Fin n → ℝ | 0 < x i}) ∩ {x | ∑ i, x i < 1} := by
      ext x; simp [O]
    rw [h]
    exact (isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))).inter
      (isOpen_lt (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)
  exact hO.subset_interior_iff.mpr (show O ⊆ Fat n from fun x hx => ⟨fun i => (hx.1 i).le,hx.2.le⟩) ⟨hp,hs⟩

lemma diskEquiv_boundary_iff {n : ℕ} (s : Convexity.StdSimplex ℝ (Fin (n+1))) :
    ‖(diskEquiv n s).1‖ = 1 ↔ ∃ j, s.weights j = 0 := by
  refine ⟨fun h => ?_,fun ⟨j,hj⟩ => diskEquiv_boundary s j hj⟩
  by_contra! hne
  have hp : ∀ j, 0 < s.weights j := fun j => lt_of_le_of_ne (s.weights_nonneg j) (hne j).symm
  have hi : (fstEquiv n s).1 ∈ interior (Fat n) := by
    apply interior_of_pos
    · intro i; exact hp i.succ
    · change ∑ i : Fin n, s.weights i.succ < 1
      have hsum := s.total_of_fintype
      rw [Fin.sum_univ_succ] at hsum
      linarith [hp 0]
  have hb : (diskEquiv n s).1 ∈ sphere (0 : Fin n → ℝ) 1 := by
    simpa only [mem_sphere,dist_zero_right] using h
  rw [diskEquiv_val,← ambient_frontier] at hb
  obtain ⟨x,hx,he⟩ := hb
  have he' : x = (fstEquiv n s).1 := (ambient n).injective he
  subst x
  exact hx.2 hi

end SimplexDisk

end

end OAI
