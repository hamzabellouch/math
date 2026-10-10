import OAI.Geometry.TranslativeCovering.PoissonRealization

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace RandomBody
open Set MeasureTheory Metric SphericalLaw
open scoped ENNReal NNReal

def body {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) : Set (Space n) :=
  closedBall 0 b ∩ ⋂ i, {x | |inner ℝ (U.2.val i).val x| ≤ t}

lemma body_closed {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    IsClosed (body b t U) := by
  apply isClosed_closedBall.inter
  exact isClosed_iInter fun i => isClosed_le ((continuous_const.inner continuous_id).abs) continuous_const

lemma body_compact {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    IsCompact (body b t U) :=
  (isCompact_closedBall (0 : Space n) b).of_isClosed_subset (body_closed b t U) inter_subset_left

lemma convex_slab {n : ℕ} (u : Space n) (t : ℝ) :
    Convex ℝ {x | |inner ℝ u x| ≤ t} := by
  intro x hx y hy a b ha hb hab
  change |inner ℝ u (a • x+b • y)| ≤ t
  rw [inner_add_right,inner_smul_right,inner_smul_right]
  have hx' : |inner ℝ u x| ≤ t := hx
  have hy' : |inner ℝ u y| ≤ t := hy
  calc
    _ ≤ |a*inner ℝ u x|+|b*inner ℝ u y| := abs_add_le _ _
    _ = a*|inner ℝ u x|+b*|inner ℝ u y| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*t+b*t := add_le_add (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hb)
    _ = t := by rw [← add_mul,hab,one_mul]

lemma body_convex {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    Convex ℝ (body b t U) :=
  (convex_closedBall (0 : Space n) b).inter (convex_iInter fun i => convex_slab (U.2.val i).val t)

lemma ball_subset {n : ℕ} (b t r : ℝ) (U : PoissonConfig.Config (Sphere n))
    (hrb : r ≤ b) (hrt : r ≤ t) : closedBall 0 r ⊆ body b t U := by
  intro x hx
  refine ⟨closedBall_subset_closedBall hrb hx,mem_iInter.mpr fun i => ?_⟩
  have hnx : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
  have hu : ‖(U.2.val i).val‖ = 1 := mem_sphere_zero_iff_norm.mp (U.2.val i).property
  exact (abs_real_inner_le_norm _ _).trans (by rw [hu,one_mul]; exact hnx.trans hrt)

lemma body_symm {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    TranslativeCovering.CentrallySymmetric (body b t U) := by
  refine ⟨0,?_⟩
  intro x
  simp only [smul_zero,zero_sub,body,mem_inter_iff,mem_iInter,mem_ofPred_eq,
    mem_closedBall_zero_iff,norm_neg,inner_neg_right,abs_neg]

lemma body_isBody {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n))
    (hb : 0 < b) (ht : 0 < t) : TranslativeCovering.ConvexBody (body b t U) := by
  refine ⟨body_compact b t U,body_convex b t U,?_⟩
  have hr : 0 < min b t := lt_min hb ht
  have hsub : ball (0 : Space n) (min b t) ⊆ body b t U :=
    ball_subset_closedBall.trans (ball_subset b t (min b t) U (min_le_left _ _) (min_le_right _ _))
  exact ⟨0, (isOpen_ball.subset_interior_iff.mpr hsub) (mem_ball_self hr)⟩

lemma body_measurable {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    MeasurableSet (body b t U) := (body_closed b t U).measurableSet

lemma embedding_sigmaMk {β : ℕ → Type u_1} [∀ k,MeasurableSpace (β k)] (k : ℕ) :
    MeasurableEmbedding (@Sigma.mk ℕ β k) := by
  refine ⟨fun x y h => eq_of_heq (Sigma.mk.inj h).2,PoissonSample.measurable_sigmaMk k,?_⟩
  intro S hS
  apply PoissonConfig.measurableSet_sigma
  intro j
  by_cases hj : j = k
  · subst j
    rwa [Set.preimage_image_eq _ (fun x y h => eq_of_heq (Sigma.mk.inj h).2)]
  · have he : Sigma.mk j ⁻¹' (Sigma.mk k '' S) = ∅ := by
      ext x
      simp only [mem_preimage,mem_image,mem_empty_iff_false,iff_false,not_exists,not_and]
      intro y hy he
      exact hj (Sigma.mk.inj_iff.mp he.symm).1
    rw [he]
    exact MeasurableSet.empty

lemma measurableSet_sigma_prod {β : ℕ → Type u_2} {X : Type u_3}
    [∀ k,MeasurableSpace (β k)] [MeasurableSpace X]
    {S : Set ((Σ k,β k) × X)}
    (hS : ∀ k,MeasurableSet ((Prod.map (Sigma.mk k) id) ⁻¹' S)) : MeasurableSet S := by
  have he : S = ⋃ k,(Prod.map (Sigma.mk k) id) '' ((Prod.map (Sigma.mk k) id) ⁻¹' S) := by
    ext ⟨⟨k,y⟩,x⟩
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨k,⟨(y,x),hx,rfl⟩⟩
    · rintro hx
      obtain ⟨j,z,hz,he⟩ := mem_iUnion.mp hx
      rw [← he]
      exact hz
  rw [he]
  apply MeasurableSet.iUnion
  intro k
  exact ((embedding_sigmaMk k).prodMap MeasurableEmbedding.id).measurableSet_image.mpr (hS k)

lemma measurable_bodyRelation {n : ℕ} (b t : ℝ) :
    MeasurableSet {z : PoissonConfig.Config (Sphere n) × Space n | z.2 ∈ body b t z.1} := by
  apply measurableSet_sigma_prod
  intro k
  have hm : MeasurableSet ({z : {f : Fin k → Sphere n // Function.Injective f} × Space n |
      z.2 ∈ closedBall (0 : Space n) b} ∩
      ⋂ i : Fin k,{z | |inner ℝ (z.1.val i).val z.2| ≤ t}) := by
    apply ((isClosed_closedBall : IsClosed (closedBall (0 : Space n) b)).measurableSet.preimage measurable_snd).inter
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    exact (((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_fst)).subtype_val.inner measurable_snd).abs
  convert hm using 1
  ext z
  simp [body]

lemma measurable_bodyVolume {n : ℕ} (b t : ℝ) :
    Measurable (fun U : PoissonConfig.Config (Sphere n) => volume (body b t U)) :=
  measurable_measure_prodMk_left (measurable_bodyRelation b t)

end RandomBody

end OAI
