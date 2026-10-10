import OAI.MeasureTheory.Falconer.Angular.NorthRotation
import OAI.MeasureTheory.Falconer.Measures.BorelProductPartition
import OAI.MeasureTheory.Falconer.Estimates.Availability
import Mathlib.Topology.Algebra.ConstMulAction

namespace OAI

/-! # Common similarities for original pairs

Only a common orthogonal map and a positive dilation are used. The direction
map is exactly orthogonal, so the original radial cap constants are unchanged.
-/
namespace Falconer
open Set MeasureTheory NormedSpace

noncomputable def pairHomeomorph {d : ℕ} (f : Space d ≃ₜ Space d) :
    (Space d × Space d) ≃ₜ (Space d × Space d) := f.prodCongr f

@[simp] theorem pairHomeomorph_apply {d : ℕ} (f : Space d ≃ₜ Space d)
    (z : Space d × Space d) : pairHomeomorph f z = (f z.1,f z.2) := rfl

noncomputable def scaledIsometry {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) : Space d ≃ₜ Space d :=
  e.toHomeomorph.trans (Homeomorph.smulOfNeZero a ha.ne')

@[simp] theorem scaledIsometry_apply {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x : Space d) : scaledIsometry e a ha x = a • e x := rfl

theorem scaledIsometry_dist {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x y : Space d) :
    dist (scaledIsometry e a ha x) (scaledIsometry e a ha y) = a*dist x y := by
  simp only [scaledIsometry_apply,dist_smul₀,Real.norm_eq_abs,abs_of_pos ha,e.dist_map]

theorem scaledIsometry_normalize_sub {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x y : Space d) :
    normalize (scaledIsometry e a ha x-scaledIsometry e a ha y) = e (normalize (x-y)) := by
  rw [scaledIsometry_apply,scaledIsometry_apply,← smul_sub,normalize_smul_of_pos ha]
  exact linearIsometryEquiv_normalize_sub e x y

theorem scaledIsometry_radial {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x y : Space d) :
    radialDirection (scaledIsometry e a ha x) (scaledIsometry e a ha y) = e (radialDirection x y) :=
  scaledIsometry_normalize_sub e a ha y x

theorem scaledIsometry_ball_preimage {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x : Space d) (r : ℝ) :
    scaledIsometry e a ha ⁻¹' Metric.ball x r =
      Metric.ball ((scaledIsometry e a ha).symm x) (r/a) := by
  ext y
  simp only [mem_preimage,Metric.mem_ball]
  have he : dist (scaledIsometry e a ha y) x =
      a*dist y ((scaledIsometry e a ha).symm x) := by
    calc
      _ = dist (scaledIsometry e a ha y)
        (scaledIsometry e a ha ((scaledIsometry e a ha).symm x)) := by
          rw [(scaledIsometry e a ha).apply_symm_apply]
      _ = _ := scaledIsometry_dist e a ha _ _
  rw [he,lt_div_iff₀ ha,mul_comm a]

theorem HasBorelProductPartition.homeomorph {d : ℕ} {G : Set (Space d × Space d)}
    {K : ℝ} (h : HasBorelProductPartition G K) (f : Space d ≃ₜ Space d) :
    HasBorelProductPartition (pairHomeomorph f '' G) K := by
  obtain ⟨n,hn,A,B,hm,hd,rfl⟩ := h
  refine ⟨n,hn,(fun i => f '' A i),(fun i => f '' B i),?_,?_,?_⟩
  · intro i
    exact ⟨f.measurableEmbedding.measurableSet_image.mpr (hm i).1,
      f.measurableEmbedding.measurableSet_image.mpr (hm i).2⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro ⟨x,y⟩ ⟨⟨x₁,hx₁,hx⟩,⟨y₁,hy₁,hy⟩⟩ ⟨⟨x₂,hx₂,hx'⟩,⟨y₂,hy₂,hy'⟩⟩
    have hxx : x₁ = x₂ := f.injective (hx.trans hx'.symm)
    have hyy : y₁ = y₂ := f.injective (hy.trans hy'.symm)
    exact Set.disjoint_left.mp (hd hij)
      (show (x₁,y₁) ∈ A i ×ˢ B i from ⟨hx₁,hy₁⟩)
      (by simpa only [mem_prod,hxx,hyy] using And.intro hx₂ hy₂)
  · ext z
    simp only [mem_image,mem_iUnion,mem_prod,pairHomeomorph_apply]
    constructor
    · rintro ⟨⟨x,y⟩,⟨i,hx,hy⟩,heq⟩
      exact ⟨i,⟨x,hx,congrArg Prod.fst heq⟩,⟨y,hy,congrArg Prod.snd heq⟩⟩
    · rintro ⟨i,⟨x,hx,hx'⟩,⟨y,hy,hy'⟩⟩
      exact ⟨(x,y),⟨i,hx,hy⟩,Prod.ext hx' hy'⟩

theorem scaledIsometry_distanceSet {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (E : Set (Space d)) :
    distanceSet (scaledIsometry e a ha '' E) = (fun r : ℝ => a*r) '' distanceSet E := by
  ext r
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,hr⟩
    exact ⟨dist x y,⟨x,hx,y,hy,rfl⟩,(scaledIsometry_dist e a ha x y).symm.trans hr⟩
  · rintro ⟨_,⟨x,hx,y,hy,rfl⟩,rfl⟩
    exact ⟨_,mem_image_of_mem _ hx,_,mem_image_of_mem _ hy,scaledIsometry_dist e a ha x y⟩

theorem positive_distance_of_scaledIsometry {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (E : Set (Space d))
    (h : 0 < volume (distanceSet (scaledIsometry e a ha '' E))) :
    0 < volume (distanceSet E) := by
  rw [scaledIsometry_distanceSet] at h
  have he : (fun r : ℝ => a*r) '' distanceSet E =
      (fun r : ℝ => a⁻¹*r) ⁻¹' distanceSet E := by
    ext r
    constructor
    · rintro ⟨t,ht,rfl⟩
      simpa only [mem_preimage,inv_mul_cancel_left₀ ha.ne'] using ht
    · intro hr
      exact ⟨a⁻¹*r,hr,mul_inv_cancel_left₀ ha.ne' r⟩
  rw [he,Real.volume_preimage_mul_left (inv_ne_zero ha.ne')] at h
  exact (ENNReal.mul_pos_iff.mp h).2

end Falconer

end OAI
