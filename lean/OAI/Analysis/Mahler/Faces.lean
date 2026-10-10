import OAI.Analysis.Mahler.EqualityMedians

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Metric
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsFace (K F : Set E) : Prop := Convex ℝ F ∧ IsExtreme ℝ K F

namespace IsFace
variable {K F G : Set E}
lemma subset (h : IsFace K F) : F ⊆ K := h.2.subset
lemma trans (h : IsFace K F) (h' : IsFace F G) : IsFace K G :=
  ⟨h'.1, h.2.trans h'.2⟩
lemma inter (h : IsFace K F) (h' : IsFace K G) : IsFace K (F ∩ G) :=
  ⟨h.1.inter h'.1, h.2.inter h'.2⟩
lemma mono (h : IsFace K G) (hFK : F ⊆ K) (hGF : G ⊆ F) : IsFace F G :=
  ⟨h.1, h.2.mono hFK hGF⟩
lemma refl (h : Convex ℝ K) : IsFace K K := ⟨h, .rfl⟩
lemma empty (K : Set E) : IsFace K ∅ :=
  ⟨convex_empty, ⟨empty_subset _, fun _ _ _ _ _ h => h.elim⟩⟩

lemma eq_convexHull_inter {A : Set E} (h : IsFace (convexHull ℝ A) F) :
    F = convexHull ℝ (A ∩ F) := by
  apply subset_antisymm
  · let T : Set E := {x | x ∈ convexHull ℝ A ∧
        (x ∈ F → x ∈ convexHull ℝ (A ∩ F))}
    have hT : Convex ℝ T := by
      apply convex_iff_openSegment_subset.mpr
      intro x hx y hy z hz
      refine ⟨(convex_convexHull ℝ A).openSegment_subset hx.1 hy.1 hz, ?_⟩
      intro hzF
      exact (convex_convexHull ℝ (A ∩ F)).openSegment_subset
        (hx.2 (h.2.left_mem_of_mem_openSegment hx.1 hy.1 hzF hz))
        (hy.2 (h.2.right_mem_of_mem_openSegment hx.1 hy.1 hzF hz)) hz
    have hAT : A ⊆ T := fun x hx =>
      ⟨subset_convexHull ℝ A hx, fun hxF => subset_convexHull ℝ (A ∩ F) ⟨hx,hxF⟩⟩
    intro x hx
    exact (convexHull_min hAT hT (h.subset hx)).2 hx
  · exact convexHull_min inter_subset_right h.1

lemma isCompact_of_finite_hull {A : Set E} (hA : A.Finite)
    (h : IsFace (convexHull ℝ A) F) : IsCompact F := by
  rw [h.eq_convexHull_inter]
  exact (hA.inter_of_left F).isCompact_convexHull ℝ

lemma eq_of_inter_eq {A : Set E} (h : IsFace (convexHull ℝ A) F)
    (h' : IsFace (convexHull ℝ A) G) (he : A ∩ F = A ∩ G) : F = G := by
  rw [h.eq_convexHull_inter, h'.eq_convexHull_inter, he]
end IsFace

def faceHull (K A : Set E) : Set E := ⋂₀ {F | IsFace K F ∧ A ⊆ F}

lemma subset_faceHull {K A : Set E} : A ⊆ faceHull K A :=
  fun _ hx => mem_sInter.mpr fun _ hF => hF.2 hx

lemma faceHull_min {K A F : Set E} (hF : IsFace K F) (hAF : A ⊆ F) :
    faceHull K A ⊆ F := sInter_subset_of_mem ⟨hF,hAF⟩

lemma isFace_faceHull {K A : Set E} (hK : Convex ℝ K) (hAK : A ⊆ K) :
    IsFace K (faceHull K A) := by
  refine ⟨convex_sInter (fun F hF => hF.1.1), ?_⟩
  exact isExtreme_sInter ⟨K,IsFace.refl hK,hAK⟩ (fun F hF => hF.1.2)

lemma faceHull_mono {K A B : Set E} (hAB : A ⊆ B) :
    faceHull K A ⊆ faceHull K B := by
  intro x hx
  exact mem_sInter.mpr fun F hF => mem_sInter.mp hx F ⟨hF.1,hAB.trans hF.2⟩

lemma faceHull_eq {K F : Set E} (hF : IsFace K F) : faceHull K F = F :=
  subset_antisymm (faceHull_min hF Subset.rfl) subset_faceHull

lemma finite_faces_of_finite_hull {A : Set E} (hA : A.Finite) :
    {F : Set E | IsFace (convexHull ℝ A) F}.Finite := by
  classical
  apply Set.Finite.of_finite_image (f := fun F : Set E => A ∩ F)
  · exact hA.finite_subsets.subset (by
      rintro _ ⟨F,-,rfl⟩
      exact inter_subset_left)
  · intro F hF G hG he
    exact hF.eq_of_inter_eq hG he

lemma finite_unit_faces_of_medians [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) :
    {F : Set E | IsFace (closedBall (0:E) 1) F}.Finite := by
  obtain ⟨V,hV,hB⟩ := unitBall_eq_finite_convexHull_of_medians hmed
  rw [hB]
  exact finite_faces_of_finite_hull hV

end

open Set Metric
open scoped Pointwise
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extreme_set_eq_ball_of_zero {F : Set E}
    (hF : IsExtreme ℝ (closedBall (0:E) 1) F) (h0 : (0:E) ∈ F) :
    F = closedBall (0:E) 1 := by
  apply subset_antisymm hF.subset
  intro x hx
  apply hF.left_mem_of_mem_openSegment hx (show -x ∈ closedBall (0:E) 1 by simpa using hx) h0
  refine ⟨(1:ℝ)/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
  simp

lemma norm_eq_one_of_mem_proper_face {F : Set E}
    (hF : IsExtreme ℝ (closedBall (0:E) 1) F) (hproper : F ≠ closedBall (0:E) 1)
    {x : E} (hx : x ∈ F) : ‖x‖ = 1 := by
  have hle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hF.subset hx)
  by_contra hne
  have hlt := lt_of_le_of_ne hle hne
  have h0 : (0:E) ∈ F := by
    by_cases hx0 : x = 0
    · simpa only [hx0] using hx
    have hpos := norm_pos_iff.mpr hx0
    have hxu : ‖x‖⁻¹ • x ∈ closedBall (0:E) 1 := by
      simp only [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos),inv_mul_cancel₀ hpos.ne',le_refl]
    apply hF.left_mem_of_mem_openSegment (show (0:E) ∈ closedBall (0:E) 1 by simp) hxu hx
    refine ⟨1-‖x‖,‖x‖,by linarith,hpos,by ring,?_⟩
    simp only [smul_zero,zero_add,smul_smul,mul_inv_cancel₀ hpos.ne',one_smul]
  exact hproper (extreme_set_eq_ball_of_zero hF h0)

lemma normalized_summand_mem_face {F : Set E}
    (hF : IsExtreme ℝ (closedBall (0:E) 1) F) {x m : E}
    (hx : x ∈ F) (hnx : ‖x‖ = 1) (hm : m ≠ 0)
    (hadd : ‖m‖+‖x-m‖ = 1) : ‖m‖⁻¹ • m ∈ F := by
  have hmp := norm_pos_iff.mpr hm
  by_cases hxm : x = m
  · simpa [← hxm,hnx] using hx
  have hxp : 0 < ‖x-m‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxm)
  apply hF.left_mem_of_mem_openSegment (show ‖m‖⁻¹ • m ∈ closedBall (0:E) 1 by
    simp [norm_smul,hmp.ne'])
    (show ‖x-m‖⁻¹ • (x-m) ∈ closedBall (0:E) 1 by
      simp [norm_smul,hxp.ne']) hx
  refine ⟨‖m‖,‖x-m‖,hmp,hxp,hadd,?_⟩
  simp only [smul_smul,mul_inv_cancel₀ hmp.ne',mul_inv_cancel₀ hxp.ne',one_smul]
  abel

theorem disjoint_faces_distance_two (hmed : HasMetricMedians E)
    {F G : Set E} (hF : IsExtreme ℝ (closedBall (0:E) 1) F)
    (hG : IsExtreme ℝ (closedBall (0:E) 1) G)
    (hdis : Disjoint F G) {x y : E} (hx : x ∈ F) (hy : y ∈ G) :
    dist x y = 2 := by
  have hFp : F ≠ closedBall (0:E) 1 := by
    intro he; exact Set.disjoint_left.mp hdis (he ▸ hG.subset hy) hy
  have hGp : G ≠ closedBall (0:E) 1 := by
    intro he; exact Set.disjoint_left.mp hdis hx (he ▸ hF.subset hx)
  have hnx := norm_eq_one_of_mem_proper_face hF hFp hx
  have hny := norm_eq_one_of_mem_proper_face hG hGp hy
  obtain ⟨m,hm⟩ := hmed ![0,x,y]
  have hmx : ‖m‖+‖x-m‖ = 1 := by
    have hh := hm 0 1 (by decide)
    simpa [dist_eq_norm,norm_sub_rev,hnx] using hh.symm
  have hmy : ‖m‖+‖y-m‖ = 1 := by
    have hh := hm 0 2 (by decide)
    simpa [dist_eq_norm,norm_sub_rev,hny] using hh.symm
  have hm0 : m = 0 := by
    by_contra hh
    exact Set.disjoint_left.mp hdis (normalized_summand_mem_face hF hx hnx hh hmx)
      (normalized_summand_mem_face hG hy hny hh hmy)
  have hh := hm 1 2 (by decide)
  simpa [hm0,dist_zero_left,dist_zero_right,hnx,hny,show (1:ℝ)+1=2 by norm_num] using hh

theorem disjoint_faces_opposite_support [FiniteDimensional ℝ E]
    (hmed : HasMetricMedians E) {F G : Set E}
    (hF : IsExtreme ℝ (closedBall (0:E) 1) F)
    (hG : IsExtreme ℝ (closedBall (0:E) 1) G)
    (hFc : Convex ℝ F) (hGc : Convex ℝ G)
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hdis : Disjoint F G) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ = 1 ∧ (∀ x ∈ F, f x = 1) ∧ ∀ y ∈ G, f y = -1 := by
  have hsep : Disjoint (ball (0:E) 2) (F-G) := by
    rw [Set.disjoint_left]
    intro z hz hzg
    obtain ⟨x,hx,y,hy,rfl⟩ := Set.mem_sub.mp hzg
    have hn : ‖x-y‖ = 2 := by rw [← dist_eq_norm]; exact disjoint_faces_distance_two hmed hF hG hdis hx hy
    simp [hn] at hz
  obtain ⟨f,u,hlo,hhi⟩ := geometric_hahn_banach_open (convex_ball (0:E) 2) isOpen_ball
    (hFc.sub hGc) hsep
  have hclosed : ∀ z ∈ closedBall (0:E) 2, f z ≤ u := by
    have hc : closure (ball (0:E) 2) ⊆ f ⁻¹' Iic u :=
      closure_minimal (fun z hz => (hlo z hz).le) (isClosed_Iic.preimage f.continuous)
    rwa [closure_ball 0 (by norm_num : (2:ℝ) ≠ 0)] at hc
  have hu : 0 < u := by simpa using hlo 0 (by simp : (0:E) ∈ ball 0 2)
  obtain ⟨v,hv,hfv⟩ := exists_unitBall_dual_maximizer f
  have hnu : 2*‖f‖ ≤ u := by
    have hh := hclosed ((2:ℝ) • v) (by
      rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith)
    simpa [hfv] using hh
  have hxy (x : E) (hx : x ∈ F) (y : E) (hy : y ∈ G) :
      f x - f y = 2*‖f‖ := by
    have ha := hhi (x-y) (Set.sub_mem_sub hx hy)
    have hb := f.le_opNorm (x-y)
    have hn : ‖x-y‖ = 2 := by rw [← dist_eq_norm]; exact disjoint_faces_distance_two hmed hF hG hdis hx hy
    rw [map_sub] at ha hb
    rw [hn,Real.norm_eq_abs] at hb
    have hab := le_abs_self (f x-f y)
    linarith
  obtain ⟨x0,hx0⟩ := hFn
  obtain ⟨y0,hy0⟩ := hGn
  have hfp : 0 < ‖f‖ := by
    have hu' := hhi (x0-y0) (Set.sub_mem_sub hx0 hy0)
    rw [map_sub,hxy x0 hx0 y0 hy0] at hu'
    linarith
  have hfup (z : E) (hz : z ∈ closedBall (0:E) 1) : |f z| ≤ ‖f‖ :=
    (f.le_opNorm z).trans (by nlinarith [norm_nonneg f,mem_closedBall_zero_iff.mp hz])
  refine ⟨‖f‖⁻¹ • f,?_,?_,?_⟩
  · simp [norm_smul,hfp.ne']
  · intro x hx
    have hfx : f x = ‖f‖ := by
      have ha := hxy x hx y0 hy0
      have hb := (abs_le.mp (hfup x (hF.subset hx))).2
      have hc := (abs_le.mp (hfup y0 (hG.subset hy0))).1
      linarith
    simp [hfx,hfp.ne']
  · intro y hy
    have hfy : f y = -‖f‖ := by
      have ha := hxy x0 hx0 y hy
      have hb := (abs_le.mp (hfup y (hG.subset hy))).1
      have hc := (abs_le.mp (hfup x0 (hF.subset hx0))).2
      linarith
    simp [hfy,hfp.ne']

end

open Set Metric

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bidual_functional_representation [FiniteDimensional ℝ E]
    (L : (E →L[ℝ] ℝ) →L[ℝ] ℝ) : ∃ x : E, ∀ f : E →L[ℝ] ℝ, L f = f x := by
  let L' : Module.Dual ℝ (Module.Dual ℝ E) :=
    L.toLinearMap.comp (LinearMap.toContinuousLinearMap : Module.Dual ℝ E ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap
  let x := (Module.evalEquiv ℝ E).symm L'
  refine ⟨x,?_⟩
  intro f
  have hh := Module.apply_evalEquiv_symm_apply ℝ E f.toLinearMap L'
  exact hh.symm

theorem dual_ball_eq_convexHull_opposite_faces [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) {e : E}
    (he : e ∈ (closedBall (0:E) 1).extremePoints ℝ) :
    closedBall (0 : E →L[ℝ] ℝ) 1 =
      convexHull ℝ {f : E →L[ℝ] ℝ | ‖f‖ ≤ 1 ∧ (f e = 1 ∨ f e = -1)} := by
  let S := {f : E →L[ℝ] ℝ | ‖f‖ ≤ 1 ∧ (f e = 1 ∨ f e = -1)}
  have hSc : IsCompact S := by
    have hclosed : IsClosed {f : E →L[ℝ] ℝ | f e = 1 ∨ f e = -1} :=
      (isClosed_eq (by fun_prop) continuous_const).union
        (isClosed_eq (by fun_prop) continuous_const)
    have hs_eq : S = closedBall (0 : E →L[ℝ] ℝ) 1 ∩ {f | f e = 1 ∨ f e = -1} := by
      ext f
      simp only [S, Set.mem_ofPred, mem_inter_iff, mem_closedBall_zero_iff]
    rw [hs_eq]
    exact (isCompact_closedBall (0 : E →L[ℝ] ℝ) 1).inter_right hclosed
  have hsub : convexHull ℝ S ⊆ closedBall (0 : E →L[ℝ] ℝ) 1 :=
    convexHull_min (fun f hf => mem_closedBall_zero_iff.mpr hf.1) (convex_closedBall _ _)
  apply subset_antisymm _ hsub
  intro f hf
  by_contra hnot
  obtain ⟨L,u,hlo,hhi⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ S)
    (isCompact_convexHull_of_isCompact hSc).isClosed hnot
  obtain ⟨x,hx⟩ := bidual_functional_representation L
  obtain ⟨g,hgn,hgx,hge⟩ := extreme_unit_dual_face_norming hmed he x
  have hless := hlo g (subset_convexHull ℝ S ⟨hgn,hge⟩)
  rw [hx,hgx] at hless
  rw [hx] at hhi
  have hle := dual_eval_le_unit_norm f (mem_closedBall_zero_iff.mp hf) x
  linarith

theorem extreme_dual_eval_eq_one_or_neg_one [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) {e : E} {f : E →L[ℝ] ℝ}
    (he : e ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hf : f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ) :
    f e = 1 ∨ f e = -1 := by
  rw [dual_ball_eq_convexHull_opposite_faces hmed he] at hf
  exact (extremePoints_convexHull_subset hf).2

lemma dual_eval_bounds {f : E →L[ℝ] ℝ} (hf : ‖f‖ ≤ 1) {x : E}
    (hx : x ∈ closedBall (0:E) 1) : -1 ≤ f x ∧ f x ≤ 1 := by
  have hn := mem_closedBall_zero_iff.mp hx
  have hp := dual_eval_le_unit_norm f hf x
  have hm := dual_eval_le_unit_norm f hf (-x)
  simp only [map_neg,norm_neg] at hm
  constructor <;> linarith

lemma norm_le_of_dual_extreme_le [FiniteDimensional ℝ E] {x : E} {r : ℝ}
    (h : ∀ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ, f x ≤ r) :
    ‖x‖ ≤ r := by
  let S : Set (E →L[ℝ] ℝ) := {f | f x ≤ r}
  have hS : Convex ℝ S := by
    intro f hf g hg a b ha hb hab
    change a * f x + b * g x ≤ r
    change f x ≤ r at hf
    change g x ≤ r at hg
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hf),
      mul_nonneg hb (sub_nonneg.mpr hg),
      congrArg (fun t : ℝ => t*r) hab]
  have hcl : IsClosed S := isClosed_le (by fun_prop) continuous_const
  have hs : closedBall (0 : E →L[ℝ] ℝ) 1 ⊆ S := by
    rw [← closure_convexHull_extremePoints (isCompact_closedBall _ _) (convex_closedBall _ _)]
    exact closure_minimal (convexHull_min h hS) hcl
  obtain ⟨f,hf,he⟩ := exists_dual_vector'' ℝ x
  have hh := hs (mem_closedBall_zero_iff.mpr hf)
  change f x ≤ r at hh
  rwa [he] at hh

lemma eq_of_dual_extreme_eq [FiniteDimensional ℝ E] {x y : E}
    (h : ∀ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ, f x = f y) : x = y := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply norm_le_of_dual_extreme_le
  intro f hf
  simp [h f hf]

lemma extreme_of_dual_levels [FiniteDimensional ℝ E] {x : E}
    (hx : x ∈ closedBall (0:E) 1)
    (h : ∀ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ, f x = 1 ∨ f x = -1) :
    x ∈ (closedBall (0:E) 1).extremePoints ℝ := by
  refine ⟨hx, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  apply eq_of_dual_extreme_eq
  intro f hf
  have hfy := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hy
  have hfz := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hz
  have hev := congrArg f he
  simp only [map_add,map_smul,smul_eq_mul] at hev
  rcases h f hf with hh | hh
  · rw [hh] at hev ⊢
    have hprod : a * (1 - f y) = 0 := by
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hfy.2),
        mul_nonneg hb.le (sub_nonneg.mpr hfz.2)]
    have := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
    linarith
  · rw [hh] at hev ⊢
    have hprod : a * (f y + 1) = 0 := by
      nlinarith [mul_nonneg ha.le (show 0 ≤ f y+1 by linarith),
        mul_nonneg hb.le (show 0 ≤ f z+1 by linarith)]
    have := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
    linarith

lemma isFace_support {f : E →L[ℝ] ℝ} (hf : ‖f‖ ≤ 1) :
    IsFace (closedBall (0:E) 1) {x ∈ closedBall (0:E) 1 | f x = 1} := by
  constructor
  · intro x hx y hy a b ha hb hab
    refine ⟨(convex_closedBall _ _) hx.1 hy.1 ha hb hab, ?_⟩
    simp [hx.2,hy.2,hab]
  · refine ⟨fun x hx => hx.1, ?_⟩
    intro x hx y hy z hz hseg
    obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
    refine ⟨hx, ?_⟩
    have hfx := (dual_eval_bounds hf hx).2
    have hfy := (dual_eval_bounds hf hy).2
    have hev := congrArg f he
    simp only [map_add,map_smul,smul_eq_mul,hz.2] at hev
    nlinarith

def exchangeFace (x y : E) : Set E :=
  {u ∈ closedBall (0:E) 1 | x+u-y ∈ closedBall (0:E) 1}

lemma isFace_exchangeFace [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) {x y : E}
    (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hy : y ∈ (closedBall (0:E) 1).extremePoints ℝ) :
    IsFace (closedBall (0:E) 1) (exchangeFace x y) := by
  constructor
  · intro u hu v hv a b ha hb hab
    refine ⟨(convex_closedBall _ _) hu.1 hv.1 ha hb hab, ?_⟩
    have he : x+(a • u+b • v)-y = a • (x+u-y)+b • (x+v-y) := by
      calc
        _ = (a+b) • x+(a • u+b • v)-(a+b) • y := by rw [hab]; simp
        _ = _ := by module
    rw [he]
    exact (convex_closedBall _ _) hu.2 hv.2 ha hb hab
  · refine ⟨fun u hu => hu.1, ?_⟩
    intro u hu v hv z hz hseg
    obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
    refine ⟨hu, mem_closedBall_zero_iff.mpr ?_⟩
    apply norm_le_of_dual_extreme_le
    intro f hf
    have hfu := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hu
    have hfv := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hv
    have hfz := (dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hz.2).2
    have hev := congrArg f he
    simp only [map_add,map_smul,smul_eq_mul] at hev
    simp only [map_add,map_sub] at hfz ⊢
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hx hf with hfx | hfx <;>
      rcases extreme_dual_eval_eq_one_or_neg_one hmed hy hf with hfy | hfy <;>
      rw [hfx,hfy] at hfz ⊢ <;> nlinarith

lemma exchange_vertex [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) {x y u : E}
    (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hy : y ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hu : u ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hex : u ∈ exchangeFace x y) :
    x+u-y ∈ (closedBall (0:E) 1).extremePoints ℝ := by
  apply extreme_of_dual_levels hex.2
  intro f hf
  have hb := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hex.2
  simp only [map_sub,map_add] at hb ⊢
  rcases extreme_dual_eval_eq_one_or_neg_one hmed hx hf with hfx | hfx <;>
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hy hf with hfy | hfy <;>
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hu hf with hfu | hfu <;>
    simp_all <;> linarith

theorem face_vertex_exchange [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) {x y : E} {F : Set E}
    (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hy : y ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hF : IsFace (closedBall (0:E) 1) F) (hFn : F.Nonempty)
    (hyF : y ∈ faceHull (closedBall (0:E) 1) ({x} ∪ F)) :
    ∃ u ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ v ∈ (closedBall (0:E) 1).extremePoints ℝ, x+u = y+v := by
  let C := exchangeFace x y
  have hC : IsFace (closedBall (0:E) 1) C := isFace_exchangeFace hmed hx hy
  have hyC : y ∈ C := ⟨hy.1, by simpa using hx.1⟩
  have hnxC : -x ∈ C := ⟨by simpa using hx.1, by simpa using hy.1⟩
  have hinter : (F ∩ C).Nonempty := by
    by_contra hh
    have hdis : Disjoint F C := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hh)
    obtain ⟨f,hfn,hfF,hfC⟩ := disjoint_faces_opposite_support hmed hF.2 hC.2
      hF.1 hC.1 hFn ⟨y,hyC⟩ hdis
    have hfx : f x = 1 := by have ht := hfC _ hnxC; simpa using ht
    have hfy := hfC y hyC
    have hsub : {x} ∪ F ⊆ {z ∈ closedBall (0:E) 1 | f z = 1} := by
      rintro z (rfl | hz)
      · exact ⟨hx.1,hfx⟩
      · exact ⟨hF.subset hz,hfF z hz⟩
    have hh' := (faceHull_min (isFace_support hfn.le) hsub hyF).2
    linarith
  obtain ⟨V,hV,hball⟩ := unitBall_eq_finite_convexHull_of_medians hmed
  have hFC := hF.inter hC
  have hcompact : IsCompact (F ∩ C) := by
    apply IsFace.isCompact_of_finite_hull hV
    rwa [← hball]
  obtain ⟨u,hu⟩ := hcompact.extremePoints_nonempty hinter
  have hub := hFC.2.extremePoints_subset_extremePoints hu
  exact ⟨u,⟨hu.1.1,hub⟩,x+u-y,exchange_vertex hmed hx hy hub hu.1.2,by abel⟩

lemma IsFace.singleton {K : Set E} {x : E} (hx : x ∈ K.extremePoints ℝ) :
    IsFace K {x} := ⟨convex_singleton _, isExtreme_singleton.mpr hx⟩

lemma IsFace.extremePoints_eq {K F : Set E} (hF : IsFace K F) :
    F.extremePoints ℝ = K.extremePoints ℝ ∩ F := by
  apply subset_antisymm
  · exact fun x hx => ⟨hF.2.extremePoints_subset_extremePoints hx,hx.1⟩
  · intro x hx
    exact ⟨hx.2,fun y hy z hz hs => hx.1.2 (hF.subset hy) (hF.subset hz) hs⟩

variable [inst472 : FiniteDimensional ℝ E] [inst473 : Nontrivial E]

lemma unitBall_eq_convexHull_extreme (hmed : HasMetricMedians E) :
    closedBall (0:E) 1 = convexHull ℝ ((closedBall (0:E) 1).extremePoints ℝ) := by
  have h := closure_convexHull_extremePoints (isCompact_closedBall (0:E) 1)
    (convex_closedBall (0:E) 1)
  rw [((finite_extreme_unit_of_medians hmed).isClosed_convexHull ℝ).closure_eq] at h
  exact h.symm

lemma IsFace.isCompact_unit (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) : IsCompact F := by
  apply IsFace.isCompact_of_finite_hull (finite_extreme_unit_of_medians hmed)
  rwa [← unitBall_eq_convexHull_extreme hmed]

lemma IsFace.eq_convexHull_vertices (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) :
    F = convexHull ℝ ((closedBall (0:E) 1).extremePoints ℝ ∩ F) := by
  apply IsFace.eq_convexHull_inter
  rwa [← unitBall_eq_convexHull_extreme hmed]

lemma IsFace.exists_vertex (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hn : F.Nonempty) :
    ∃ x ∈ (closedBall (0:E) 1).extremePoints ℝ, x ∈ F := by
  obtain ⟨x,hx⟩ := (hF.isCompact_unit hmed).extremePoints_nonempty hn
  exact ⟨x,hF.2.extremePoints_subset_extremePoints hx,hx.1⟩

lemma IsFace.subset_of_vertices (hmed : HasMetricMedians E) {F G : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hG : Convex ℝ G)
    (h : (closedBall (0:E) 1).extremePoints ℝ ∩ F ⊆ G) : F ⊆ G := by
  rw [hF.eq_convexHull_vertices hmed]
  exact convexHull_min h hG

lemma IsFace.exists_vertex_outside (hmed : HasMetricMedians E) {F K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hF : Convex ℝ F) (hn : ¬ K ⊆ F) :
    ∃ x ∈ (closedBall (0:E) 1).extremePoints ℝ, x ∈ K ∧ x ∉ F := by
  classical
  by_contra! h
  apply hn
  exact hK.subset_of_vertices hmed hF (fun x hx => h x hx.1 hx.2)

omit inst472 inst473 in
lemma isFace_dual_common [FiniteDimensional ℝ E] [Nontrivial E] {A : Set E} (hA : A ⊆ closedBall (0:E) 1) :
    IsFace (closedBall (0 : E →L[ℝ] ℝ) 1)
      {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | ∀ x ∈ A, f x = 1} := by
  constructor
  · intro f hf g hg a b ha hb hab
    refine ⟨(convex_closedBall _ _) hf.1 hg.1 ha hb hab, ?_⟩
    intro x hx
    simp [hf.2 x hx,hg.2 x hx,hab]
  · refine ⟨fun f hf => hf.1, ?_⟩
    intro f hf g hg k hk hs
    obtain ⟨a,b,ha,hb,hab,he⟩ := hs
    refine ⟨hf, fun x hx => ?_⟩
    have hfx := (dual_eval_bounds (mem_closedBall_zero_iff.mp hf) (hA hx)).2
    have hgx := (dual_eval_bounds (mem_closedBall_zero_iff.mp hg) (hA hx)).2
    have hev := congrArg (fun q : E →L[ℝ] ℝ => q x) he
    simp only [add_apply, smul_apply,
      smul_eq_mul, hk.2 x hx] at hev
    nlinarith

omit inst473 in
lemma isCompact_dual_common [Nontrivial E] (A : Set E) :
    IsCompact {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | ∀ x ∈ A, f x = 1} := by
  apply (isCompact_closedBall _ _).inter_right
  change IsClosed {f : E →L[ℝ] ℝ | ∀ x ∈ A, f x = 1}
  have he : {f : E →L[ℝ] ℝ | ∀ x ∈ A, f x = 1} =
      ⋂ x ∈ A, {f : E →L[ℝ] ℝ | f x = 1} := by ext f; simp
  rw [he]
  exact isClosed_biInter (fun x _ => isClosed_eq (by fun_prop) continuous_const)

lemma face_vertex_dual_separation (hmed : HasMetricMedians E) {F : Set E} {x : E}
    (hF : IsFace (closedBall (0:E) 1) F) (hn : F.Nonempty)
    (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ) (hxn : x ∉ F) :
    ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      (∀ y ∈ F, f y = 1) ∧ f x = -1 := by
  have hd : Disjoint F {x} := by simpa using hxn
  obtain ⟨g,hg,hgF,hgx⟩ := disjoint_faces_opposite_support hmed hF.2
    (IsFace.singleton hx).2 hF.1 (convex_singleton x) hn (singleton_nonempty x) hd
  let A := F ∪ {-x}
  have hA : A ⊆ closedBall (0:E) 1 := by
    rintro y (hy | rfl)
    · exact hF.subset hy
    · simpa using hx.1
  have hnD : {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | ∀ y ∈ A, f y = 1}.Nonempty := by
    refine ⟨g,mem_closedBall_zero_iff.mpr hg.le,?_⟩
    rintro y (hy | rfl)
    · exact hgF y hy
    · simp [hgx x (mem_singleton x)]
  obtain ⟨f,hf⟩ := (isCompact_dual_common A).extremePoints_nonempty hnD
  refine ⟨f,(isFace_dual_common hA).2.extremePoints_subset_extremePoints hf,
    fun y hy => hf.1.2 y (Or.inl hy), ?_⟩
  have hh := hf.1.2 (-x) (Or.inr (mem_singleton _))
  simp only [map_neg] at hh
  linarith

def IsParallelPair (K F G : Set E) : Prop :=
  IsFace K F ∧ IsFace K G ∧ Disjoint F G ∧ K = convexHull ℝ (F ∪ G)

def IsParallelFace (K F : Set E) : Prop := ∃ G, IsParallelPair K F G

namespace IsParallelPair
variable {K F G : Set E}
omit inst472 inst473 in
lemma symm [FiniteDimensional ℝ E] [Nontrivial E] (h : IsParallelPair K F G) : IsParallelPair K G F :=
  ⟨h.2.1,h.1,h.2.2.1.symm,by simpa [union_comm] using h.2.2.2⟩
omit inst472 inst473 in
lemma vertex_mem [FiniteDimensional ℝ E] [Nontrivial E] (h : IsParallelPair K F G) {x : E} (hx : x ∈ K.extremePoints ℝ) :
    x ∈ F ∨ x ∈ G := by
  rw [h.2.2.2] at hx
  exact (show x ∈ F ∪ G from extremePoints_convexHull_subset hx)
lemma not_mem_iff (h : IsParallelPair K F G) {x : E} (hx : x ∈ K.extremePoints ℝ) :
    x ∉ F ↔ x ∈ G := by
  constructor
  · intro hn
    exact (h.vertex_mem hx).resolve_left hn
  · exact fun hg hf => Set.disjoint_left.mp h.2.2.1 hf hg
end IsParallelPair

lemma parallelPair_of_dual_vertex (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) {f : E →L[ℝ] ℝ}
    (hf : f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ) :
    IsParallelPair K {x ∈ K | f x = 1} {x ∈ K | f x = -1} := by
  have heF : K ∩ {x ∈ closedBall (0:E) 1 | f x = 1} = {x ∈ K | f x = 1} := by
    ext x
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hK.subset h.1,h.2⟩⟩
  have hF : IsFace (closedBall (0:E) 1) {x ∈ K | f x = 1} := by
    rw [← heF]
    exact hK.inter (isFace_support (mem_closedBall_zero_iff.mp hf.1))
  have hG : IsFace (closedBall (0:E) 1) {x ∈ K | f x = -1} := by
    have hh := hK.inter (isFace_support (f := -f) (by simpa using mem_closedBall_zero_iff.mp hf.1))
    have he : K ∩ {x ∈ closedBall (0:E) 1 | (-f) x = 1} = {x ∈ K | f x = -1} := by
      ext x
      constructor
      · rintro ⟨hx,hxb,hfx⟩
        refine ⟨hx,?_⟩
        change -f x = 1 at hfx
        linarith
      · rintro ⟨hx,hfx⟩
        exact ⟨hx,hK.subset hx,by simp [hfx]⟩
    rwa [he] at hh
  refine ⟨hF.mono hK.subset (fun _ h => h.1),hG.mono hK.subset (fun _ h => h.1),?_,?_⟩
  · exact disjoint_left.mpr (fun x hx hy => by linarith [hx.2,hy.2])
  · apply subset_antisymm
    · apply hK.subset_of_vertices hmed (convex_convexHull _ _)
      intro x hx
      apply subset_convexHull
      rcases extreme_dual_eval_eq_one_or_neg_one hmed hx.1 hf with h | h
      · exact Or.inl ⟨hx.2,h⟩
      · exact Or.inr ⟨hx.2,h⟩
    · exact convexHull_min (union_subset (fun _ h => h.1) (fun _ h => h.1)) hK.1

theorem maximal_avoiding_vertex_parallel (hmed : HasMetricMedians E) {K F : Set E} {x : E}
    (hK : IsFace (closedBall (0:E) 1) K) (hF : IsFace K F) (hn : F.Nonempty)
    (hx : x ∈ K.extremePoints ℝ) (hxn : x ∉ F)
    (hmax : ∀ G, IsFace K G → F ⊆ G → x ∉ G → G ⊆ F) :
    IsParallelFace K F := by
  obtain ⟨f,hf,hfF,hfx⟩ := face_vertex_dual_separation hmed (hK.trans hF) hn
    (hK.2.extremePoints_subset_extremePoints hx) hxn
  have hp := parallelPair_of_dual_vertex hmed hK hf
  have he : {z ∈ K | f z = 1} = F := subset_antisymm
    (hmax _ hp.1 (fun z hz => ⟨hF.subset hz,hfF z hz⟩) (by intro hh; linarith [hh.2]))
    (fun z hz => ⟨hF.subset hz,hfF z hz⟩)
  exact ⟨_,he ▸ hp⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst476 : FiniteDimensional ℝ E] [inst477 : Nontrivial E]

omit inst476 inst477 in
lemma face_mem_of_parallelogram [FiniteDimensional ℝ E] [Nontrivial E] {K F : Set E} (hF : IsFace K F)
    {x u y v : E} (hx : x ∈ F) (hu : u ∈ F) (hy : y ∈ K) (hv : v ∈ K)
    (he : x+u = y+v) : y ∈ F ∧ v ∈ F := by
  have hm : (1/2:ℝ) • x+(1/2:ℝ) • u ∈ F :=
    hF.1 hx hu (by norm_num) (by norm_num) (by norm_num)
  have hs : (1/2:ℝ) • x+(1/2:ℝ) • u ∈ openSegment ℝ y v := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    simpa only [smul_add] using congrArg (fun z : E => (1/2:ℝ) • z) he.symm
  exact ⟨hF.2.left_mem_of_mem_openSegment hy hv hm hs,
    hF.2.right_mem_of_mem_openSegment hy hv hm hs⟩

lemma proper_face_support (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hn : K.Nonempty)
    (hp : K ≠ closedBall (0:E) 1) :
    ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ, ∀ x ∈ K, f x = 1 := by
  obtain ⟨x,hx,-,hxn⟩ := (IsFace.refl (convex_closedBall (0:E) 1)).exists_vertex_outside
    hmed hK.1 (by intro hh; exact hp (subset_antisymm hK.subset hh))
  obtain ⟨f,hf,hfK,-⟩ := face_vertex_dual_separation hmed hK hn hx hxn
  exact ⟨f,hf,hfK⟩

lemma vertex_not_mem_span_face (hmed : HasMetricMedians E) {K F : Set E} {x : E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hx : x ∈ K.extremePoints ℝ) (hxn : x ∉ F) :
    x ∉ Submodule.span ℝ F := by
  by_cases hn : F.Nonempty
  · obtain ⟨f,hf,hfF,hfx⟩ := face_vertex_dual_separation hmed (hK.trans hF) hn
      (hK.2.extremePoints_subset_extremePoints hx) hxn
    obtain ⟨g,hg,hgK⟩ := proper_face_support hmed hK ⟨x,hx.1⟩ hp
    have hs : Submodule.span ℝ F ≤ (f-g).toLinearMap.ker := by
      apply Submodule.span_le.mpr
      intro y hy
      change f y-g y = 0
      rw [hfF y hy,hgK y (hF.subset hy)]
      ring
    intro hh
    have hz := hs hh
    change f x-g x = 0 at hz
    rw [hfx,hgK x hx.1] at hz
    norm_num at hz
  · rw [not_nonempty_iff_eq_empty.mp hn,Submodule.span_empty]
    intro hx0
    have he : x = 0 := hx0
    have hh := norm_eq_one_of_mem_proper_face hK.2 hp hx.1
    simp [he] at hh

def faceRank (F : Set E) : ℕ := Module.finrank ℝ (Submodule.span ℝ F)

lemma faceRank_lt (hmed : HasMetricMedians E) {F K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hne : F ≠ K) : faceRank F < faceRank K := by
  obtain ⟨x,hx,hxK,hxn⟩ := hK.exists_vertex_outside hmed hF.1
    (by intro hh; exact hne (subset_antisymm hF.subset hh))
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (Submodule.span_mono hF.subset) ?_
  intro he
  apply vertex_not_mem_span_face hmed hK hp hF
    (by rw [hK.extremePoints_eq]; exact ⟨hx,hxK⟩) hxn
  rw [he]
  exact Submodule.subset_span hxK

omit inst476 inst477 in
lemma faceHull_subset_face [FiniteDimensional ℝ E] [Nontrivial E] {K A : Set E} (hK : IsFace (closedBall (0:E) 1) K)
    (hA : A ⊆ K) : faceHull (closedBall (0:E) 1) A ⊆ K := faceHull_min hK hA

lemma parallel_face_vertex_exchange (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hpair : IsParallelPair K F G)
    (hFn : F.Nonempty) {x y : E} (hx : x ∈ K.extremePoints ℝ) (_ : x ∈ G)
    (hy : y ∈ K.extremePoints ℝ) (hyG : y ∈ G)
    (hyH : y ∈ faceHull (closedBall (0:E) 1) ({x} ∪ F)) :
    ∃ u ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ v ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ, x+u = y+v := by
  obtain ⟨u,hu,v,hv,he⟩ := face_vertex_exchange hmed
    (hK.2.extremePoints_subset_extremePoints hx) (hK.2.extremePoints_subset_extremePoints hy)
    (hK.trans hpair.1) hFn hyH
  have hvK := (face_mem_of_parallelogram hK hx.1 (hpair.1.subset hu.1) (hK.subset hy.1) hv.1 he).2
  have hvKex : v ∈ K.extremePoints ℝ := by rw [hK.extremePoints_eq]; exact ⟨hv,hvK⟩
  have hvF : v ∈ F := by
    rcases hpair.vertex_mem hvKex with hh | hh
    · exact hh
    · have huG := (face_mem_of_parallelogram hpair.2.1 hyG hh hx.1
        (hpair.1.subset hu.1) he.symm).2
      exact False.elim (disjoint_left.mp hpair.2.2.1 hu.1 huG)
  exact ⟨u,hu,v,⟨hvF,hv⟩,he⟩

theorem parallel_faceHull_rank (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair K F G) (hFn : F.Nonempty) {x : E}
    (hx : x ∈ K.extremePoints ℝ) (hxG : x ∈ G) :
    faceRank (faceHull (closedBall (0:E) 1) ({x} ∪ F)) = faceRank F + 1 := by
  let H := faceHull (closedBall (0:E) 1) ({x} ∪ F)
  have hsub : {x} ∪ F ⊆ K := union_subset (singleton_subset_iff.mpr hx.1) hpair.1.subset
  have hH : IsFace (closedBall (0:E) 1) H :=
    isFace_faceHull (convex_closedBall _ _) (hsub.trans hK.subset)
  have hHK : H ⊆ K := faceHull_min hK hsub
  have hs : Submodule.span ℝ H = Submodule.span ℝ ({x} ∪ F) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      apply hH.subset_of_vertices hmed (Submodule.convex _)
      intro y hy
      have hyK : y ∈ K.extremePoints ℝ := by rw [hK.extremePoints_eq]; exact ⟨hy.1,hHK hy.2⟩
      rcases hpair.vertex_mem hyK with hyF | hyG
      · exact Submodule.subset_span (Or.inr hyF)
      · obtain ⟨u,hu,v,hv,he⟩ := parallel_face_vertex_exchange hmed hK hpair hFn hx hxG hyK hyG hy.2
        have hey : y = x+u-v := by rw [he]; abel
        rw [hey]
        exact (Submodule.span ℝ ({x} ∪ F)).sub_mem
          ((Submodule.span ℝ ({x} ∪ F)).add_mem
            (Submodule.subset_span (Or.inl (mem_singleton x)))
            (Submodule.subset_span (Or.inr hu.1)))
          (Submodule.subset_span (Or.inr hv.1))
    · exact Submodule.span_mono subset_faceHull
  unfold faceRank
  rw [hs,Submodule.span_union,sup_comm]
  exact Submodule.finrank_sup_span_singleton
    (vertex_not_mem_span_face hmed hK hp hpair.1 hx ((hpair.not_mem_iff hx).mpr hxG))

def IsMaximalProperFace (K F : Set E) : Prop :=
  IsFace K F ∧ F ≠ K ∧ ∀ G, IsFace K G → F ⊆ G → G ≠ K → G = F

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

lemma parallelogram_not_parallel {K F : Set E}
    {x y u v : E} (hxF : x ∈ F) (hxK : x ∈ K)
    (hyK : y ∈ K) (hu : u ∈ K.extremePoints ℝ) (hv : v ∈ K.extremePoints ℝ)
    (huF : u ∉ F) (hvF : v ∉ F) (he : x+y = u+v) :
    ¬ IsParallelFace K F := by
  rintro ⟨G,hpair⟩
  have huG := (hpair.not_mem_iff hu).mp huF
  have hvG := (hpair.not_mem_iff hv).mp hvF
  have hxG := (face_mem_of_parallelogram hpair.2.1 huG hvG hxK hyK he.symm).1
  exact disjoint_left.mp hpair.2.2.1 hxF hxG

theorem nonparallel_vertex_parallelogram (hmed : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hF : IsFace K F)
    (_ : F.Nonempty) (hp : F ≠ K) (hnp : ¬ IsParallelFace K F) :
    ∃ x ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ y ∈ (K \ F) ∩ (closedBall (0:E) 1).extremePoints ℝ,
        ∃ u ∈ (K \ F) ∩ (closedBall (0:E) 1).extremePoints ℝ,
          ∃ v ∈ (K \ F) ∩ (closedBall (0:E) 1).extremePoints ℝ, x+y = u+v := by
  classical
  obtain ⟨z,hz,hzK,hzF⟩ := hK.exists_vertex_outside hmed hF.1
    (by intro hh; exact hp (subset_antisymm hF.subset hh))
  let D : Set (Set E) := {S | IsFace (closedBall (0:E) 1) S ∧ S ⊆ K ∧
    Disjoint F S ∧ z ∈ S}
  have hDf : D.Finite := (finite_unit_faces_of_medians hmed).subset (fun _ h => h.1)
  have hDn : D.Nonempty := by
    refine ⟨{z},IsFace.singleton hz,singleton_subset_iff.mpr hzK,?_,mem_singleton z⟩
    simpa using hzF
  obtain ⟨S,hSmax⟩ := hDf.exists_maximal hDn
  have hSD : S ∈ D := hSmax.1
  obtain ⟨hS,hSK,hFS,hzS⟩ := hSD
  have hSc : IsFace K S := hS.mono hK.subset hSK
  have hnot : ¬ K ⊆ convexHull ℝ (F ∪ S) := by
    intro hh
    apply hnp
    refine ⟨S,hF,hSc,hFS,subset_antisymm hh ?_⟩
    exact convexHull_min (union_subset hF.subset hSK) hK.1
  obtain ⟨u,hu,huK,huN⟩ := hK.exists_vertex_outside hmed (convex_convexHull ℝ (F ∪ S)) hnot
  have huF : u ∉ F := fun hh => huN (subset_convexHull ℝ _ (Or.inl hh))
  have huS : u ∉ S := fun hh => huN (subset_convexHull ℝ _ (Or.inr hh))
  let H := faceHull (closedBall (0:E) 1) ({u} ∪ S)
  have hbase : {u} ∪ S ⊆ K := union_subset (singleton_subset_iff.mpr huK) hSK
  have hH : IsFace (closedBall (0:E) 1) H :=
    isFace_faceHull (convex_closedBall _ _) (hbase.trans hK.subset)
  have hHK : H ⊆ K := faceHull_min hK hbase
  have hSH : S ⊆ H := fun x hx => subset_faceHull (Or.inr hx)
  have huH : u ∈ H := subset_faceHull (Or.inl (mem_singleton u))
  have hI : (F ∩ H).Nonempty := by
    by_contra hni
    have hdis : Disjoint F H := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hni)
    have hHD : H ∈ D := ⟨hH,hHK,hdis,hSH hzS⟩
    exact huS (hSmax.2 hHD hSH huH)
  have hIF : IsFace (closedBall (0:E) 1) (F ∩ H) := (hK.trans hF).inter hH
  obtain ⟨x,hx,hxFH⟩ := hIF.exists_vertex hmed hI
  obtain ⟨v,hv,y,hy,he⟩ := face_vertex_exchange hmed hu hx hS ⟨z,hzS⟩ hxFH.2
  have hyK := (face_mem_of_parallelogram hK huK (hSK hv.1) (hK.subset (hF.subset hxFH.1)) hy.1 he).2
  have hyF : y ∉ F := by
    intro hyF
    have huF' := (face_mem_of_parallelogram hF hxFH.1 hyF huK (hSK hv.1) he.symm).1
    exact huF huF'
  exact ⟨x,⟨hxFH.1,hx⟩,y,⟨⟨hyK,hyF⟩,hy⟩,u,⟨⟨huK,huF⟩,hu⟩,
    v,⟨⟨hSK hv.1,fun hh => disjoint_left.mp hFS hh hv.1⟩,hv.2⟩,he.symm⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [inst485 : Nontrivial E]

omit inst485 in
lemma faceRank_mono [Nontrivial E] {F G : Set E} (h : F ⊆ G) : faceRank F ≤ faceRank G :=
  Submodule.finrank_mono (Submodule.span_mono h)

omit inst485 in
lemma faceRank_le_dim [Nontrivial E] (F : Set E) : faceRank F ≤ Module.finrank ℝ E :=
  Submodule.finrank_le _

lemma rank_succ_maximal (hmed : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hne : F ≠ K) (hr : faceRank K = faceRank F + 1) :
    IsMaximalProperFace K F := by
  refine ⟨hF,hne,?_⟩
  intro G hG hFG hGp
  by_contra hGF
  have h1 := faceRank_lt hmed hK hp hG hGp
  have hGproper : G ≠ closedBall (0:E) 1 := by
    intro hh
    exact hp (subset_antisymm hK.subset (hh ▸ hG.subset))
  have h2 := faceRank_lt hmed (hK.trans hG) hGproper
    (hF.mono hG.subset hFG) (Ne.symm hGF)
  omega

lemma parallel_faceHull_maximal (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair K F G) (hFn : F.Nonempty) {x : E}
    (hx : x ∈ K.extremePoints ℝ) (hxG : x ∈ G) :
    IsMaximalProperFace (faceHull (closedBall (0:E) 1) ({x} ∪ F)) F := by
  let H := faceHull (closedBall (0:E) 1) ({x} ∪ F)
  have hbase : {x} ∪ F ⊆ K := union_subset (singleton_subset_iff.mpr hx.1) hpair.1.subset
  have hH : IsFace (closedBall (0:E) 1) H :=
    isFace_faceHull (convex_closedBall _ _) (hbase.trans hK.subset)
  have hHK : H ⊆ K := faceHull_min hK hbase
  have hFH : F ⊆ H := fun _ hy => subset_faceHull (Or.inr hy)
  have hxH : x ∈ H := subset_faceHull (Or.inl (mem_singleton x))
  apply rank_succ_maximal hmed hH
    (by intro he; exact hp (subset_antisymm hK.subset (he ▸ hHK)))
    ((hK.trans hpair.1).mono hH.subset hFH)
  · intro he
    exact disjoint_left.mp hpair.2.2.1 (he.symm ▸ hxH) hxG
  · exact parallel_faceHull_rank hmed hK hp hpair hFn hx hxG

theorem maximal_avoiding_vertex_rank (hmed : HasMetricMedians E) {K F : Set E} {x : E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hFn : F.Nonempty)
    (hx : x ∈ K.extremePoints ℝ) (hxn : x ∉ F)
    (hmax : ∀ G, IsFace K G → F ⊆ G → x ∉ G → G ⊆ F) :
    faceRank K = faceRank F + 1 ∧ IsMaximalProperFace K F := by
  obtain ⟨G,hpair⟩ := maximal_avoiding_vertex_parallel hmed hK hF hFn hx hxn hmax
  have hxG := (hpair.not_mem_iff hx).mp hxn
  have hspan : Submodule.span ℝ K = Submodule.span ℝ ({x} ∪ F) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      apply hK.subset_of_vertices hmed (Submodule.convex _)
      intro y hy
      have hyK : y ∈ K.extremePoints ℝ := by rw [hK.extremePoints_eq]; exact hy
      rcases hpair.vertex_mem hyK with hyF | hyG
      · exact Submodule.subset_span (Or.inr hyF)
      · let H := faceHull (closedBall (0:E) 1) ({y} ∪ F)
        have hbase : {y} ∪ F ⊆ K := union_subset (singleton_subset_iff.mpr hy.2) hF.subset
        have hH : IsFace (closedBall (0:E) 1) H :=
          isFace_faceHull (convex_closedBall _ _) (hbase.trans hK.subset)
        have hHK : H ⊆ K := faceHull_min hK hbase
        have hFH : F ⊆ H := fun _ hz => subset_faceHull (Or.inr hz)
        have hxH : x ∈ H := by
          by_contra hn
          exact disjoint_left.mp hpair.2.2.1
            (hmax H (hH.mono hK.subset hHK) hFH hn
              (subset_faceHull (Or.inl (mem_singleton y)))) hyG
        obtain ⟨u,hu,v,hv,he⟩ := parallel_face_vertex_exchange hmed hK hpair hFn hyK hyG hx hxG hxH
        have hey : y = x+v-u := by rw [← he]; abel
        rw [hey]
        exact (Submodule.span ℝ ({x} ∪ F)).sub_mem
          ((Submodule.span ℝ ({x} ∪ F)).add_mem
            (Submodule.subset_span (Or.inl (mem_singleton x)))
            (Submodule.subset_span (Or.inr hv.1)))
          (Submodule.subset_span (Or.inr hu.1))
    · exact Submodule.span_mono (union_subset (singleton_subset_iff.mpr hx.1) hF.subset)
  have hr : faceRank K = faceRank F + 1 := by
    unfold faceRank
    rw [hspan,Submodule.span_union,sup_comm]
    exact Submodule.finrank_sup_span_singleton (vertex_not_mem_span_face hmed hK hp hF hx hxn)
  exact ⟨hr,rank_succ_maximal hmed hK hp hF (by intro hh; exact hxn (hh.symm ▸ hx.1)) hr⟩

lemma extend_face_avoiding_vertex (hmed : HasMetricMedians E) {K F : Set E} {x : E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hFn : F.Nonempty) (hx : x ∈ K.extremePoints ℝ) (hxn : x ∉ F) :
    ∃ G, IsMaximalProperFace K G ∧ F ⊆ G ∧ x ∉ G := by
  classical
  let D : Set (Set E) := {G | IsFace K G ∧ F ⊆ G ∧ x ∉ G}
  have hDf : D.Finite := (finite_unit_faces_of_medians hmed).subset
    (fun G hG => hK.trans hG.1)
  obtain ⟨G,hGmax⟩ := hDf.exists_maximal ⟨F,hF,Subset.rfl,hxn⟩
  have hG : G ∈ D := hGmax.1
  have hm := maximal_avoiding_vertex_rank hmed hK hp hG.1
    (hFn.mono hG.2.1) hx hG.2.2
    (fun H hH hGH hxnH => hGmax.2 ⟨hH,hG.2.1.trans hGH,hxnH⟩ hGH)
  exact ⟨G,hm.2,hG.2.1,hG.2.2⟩

lemma maximal_proper_parallel (hmed : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hF : IsMaximalProperFace K F)
    (hn : F.Nonempty) : IsParallelFace K F := by
  obtain ⟨x,hx,hxK,hxn⟩ := hK.exists_vertex_outside hmed hF.1.1
    (by intro hh; exact hF.2.1 (subset_antisymm hF.1.subset hh))
  apply maximal_avoiding_vertex_parallel hmed hK hF.1 hn
    (by rw [hK.extremePoints_eq]; exact ⟨hx,hxK⟩) hxn
  intro G hG hFG hxG
  exact (hF.2.2 G hG hFG (by intro hh; exact hxG (hh.symm ▸ hxK))).le

lemma maximal_proper_rank (hmed : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsMaximalProperFace K F) (hn : F.Nonempty) :
    faceRank K = faceRank F + 1 := by
  obtain ⟨x,hx,hxK,hxn⟩ := hK.exists_vertex_outside hmed hF.1.1
    (by intro hh; exact hF.2.1 (subset_antisymm hF.1.subset hh))
  apply (maximal_avoiding_vertex_rank hmed hK hp hF.1 hn
    (by rw [hK.extremePoints_eq]; exact ⟨hx,hxK⟩) hxn ?_).1
  intro G hG hFG hxG
  exact (hF.2.2 G hG hFG (by intro hh; exact hxG (hh.symm ▸ hxK))).le

lemma span_support_dual_vertex (hmed : HasMetricMedians E) {f : E →L[ℝ] ℝ}
    (hf : f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ) :
    Submodule.span ℝ {x ∈ closedBall (0:E) 1 | f x = 1} = ⊤ := by
  let S := Submodule.span ℝ {x ∈ closedBall (0:E) 1 | f x = 1}
  have hBS : closedBall (0:E) 1 ⊆ S := by
    rw [unitBall_eq_convexHull_extreme hmed]
    apply convexHull_min _ (Submodule.convex _)
    intro x hx
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hx hf with h | h
    · exact Submodule.subset_span ⟨hx.1,h⟩
    · have hn : -x ∈ S := Submodule.subset_span ⟨by simpa using hx.1,by simp [h]⟩
      simpa using S.neg_mem hn
  apply top_unique
  intro x _
  by_cases hx : x = 0
  · simp [hx]
  have hn := norm_pos_iff.mpr hx
  have hxu : ‖x‖⁻¹ • x ∈ S := hBS (by simp [norm_smul,hn.ne'])
  change x ∈ S
  simpa [smul_smul,hn.ne'] using S.smul_mem ‖x‖ hxu

lemma full_rank_maximal_proper (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hp : F ≠ closedBall (0:E) 1)
    (hr : faceRank F = Module.finrank ℝ E) :
    IsMaximalProperFace (closedBall (0:E) 1) F := by
  refine ⟨hF,hp,?_⟩
  intro G hG hFG hGp
  by_contra hne
  have hh := faceRank_lt hmed hG hGp (hF.mono hG.subset hFG) (Ne.symm hne)
  have := faceRank_le_dim G
  omega

lemma maximal_unit_face_rank (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsMaximalProperFace (closedBall (0:E) 1) F) (hn : F.Nonempty) :
    faceRank F = Module.finrank ℝ E := by
  obtain ⟨f,hf,hfF⟩ := proper_face_support hmed hF.1 hn hF.2.1
  have hs : IsFace (closedBall (0:E) 1) {x ∈ closedBall (0:E) 1 | f x = 1} :=
    isFace_support (mem_closedBall_zero_iff.mp hf.1)
  have hp : {x ∈ closedBall (0:E) 1 | f x = 1} ≠ closedBall (0:E) 1 := by
    intro hh
    have h0 : (0:E) ∈ {x ∈ closedBall (0:E) 1 | f x = 1} := hh.symm ▸ (by simp)
    simpa using h0.2
  have he := hF.2.2 _ hs (fun x hx => ⟨hF.1.subset hx,hfF x hx⟩) hp
  unfold faceRank
  rw [← he,span_support_dual_vertex hmed hf,finrank_top]

def HasMFaceStructure (F : Set E) : Prop :=
  ∃ G H, IsMaximalProperFace F G ∧ IsMaximalProperFace F H ∧
    G.Nonempty ∧ H.Nonempty ∧ Disjoint G H

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst488 : FiniteDimensional ℝ E] [inst489 : Nontrivial E]

omit inst488 inst489 in
lemma IsFace.extreme_mem [FiniteDimensional ℝ E] [Nontrivial E] {K F : Set E} (hF : IsFace K F) {x : E}
    (hx : x ∈ K.extremePoints ℝ) (hxF : x ∈ F) : x ∈ F.extremePoints ℝ := by
  rw [hF.extremePoints_eq]; exact ⟨hx,hxF⟩

lemma IsParallelPair.restrict (hmed : HasMetricMedians E) {K F G L : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    (hL : IsFace K L) : IsParallelPair L (L ∩ F) (L ∩ G) := by
  have hLF := hL.inter h.1
  have hLG := hL.inter h.2.1
  refine ⟨hLF.mono hL.subset inter_subset_left,hLG.mono hL.subset inter_subset_left,
    h.2.2.1.mono inter_subset_right inter_subset_right,?_⟩
  apply subset_antisymm
  · apply (hK.trans hL).subset_of_vertices hmed (convex_convexHull _ _)
    intro x hx
    apply subset_convexHull
    rcases h.vertex_mem (hK.extreme_mem hx.1 (hL.subset hx.2)) with hh | hh
    · exact Or.inl ⟨hx.2,hh⟩
    · exact Or.inr ⟨hx.2,hh⟩
  · exact convexHull_min (union_subset inter_subset_left inter_subset_left) hL.1

lemma IsParallelPair.complement_anti (hmed : HasMetricMedians E) {K F G A B : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    (h' : IsParallelPair K A B) (hFA : F ⊆ A) : B ⊆ G := by
  apply (hK.trans h'.2.1).subset_of_vertices hmed h.2.1.1
  intro x hx
  apply (h.not_mem_iff (hK.extreme_mem hx.1 (h'.2.1.subset hx.2))).mp
  exact fun hf => disjoint_left.mp h'.2.2.1 (hFA hf) hx.2

lemma IsParallelPair.complement_unique (hmed : HasMetricMedians E) {K F G A : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    (h' : IsParallelPair K F A) : G = A :=
  subset_antisymm (h'.complement_anti hmed hK h Subset.rfl)
    (h.complement_anti hmed hK h' Subset.rfl)

lemma IsParallelPair.subset_of_disjoint (hmed : HasMetricMedians E) {K F G A : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    (hA : IsFace K A) (hAF : Disjoint A F) : A ⊆ G := by
  apply (hK.trans hA).subset_of_vertices hmed h.2.1.1
  intro x hx
  exact (h.not_mem_iff (hK.extreme_mem hx.1 (hA.subset hx.2))).mp
    (fun hh => disjoint_left.mp hAF hx.2 hh)

omit inst488 inst489 in
lemma IsParallelPair.nonempty_right [FiniteDimensional ℝ E] [Nontrivial E] {K F G : Set E} (h : IsParallelPair K F G)
    (hne : F ≠ K) : G.Nonempty := by
  by_contra hn
  have he := h.2.2.2
  rw [not_nonempty_iff_eq_empty.mp hn,union_empty,h.1.1.convexHull_eq] at he
  exact hne he.symm

omit inst488 inst489 in
lemma IsParallelPair.left_ne [FiniteDimensional ℝ E] [Nontrivial E] {K F G : Set E} (h : IsParallelPair K F G)
    (hn : G.Nonempty) : F ≠ K := by
  intro he
  obtain ⟨x,hx⟩ := hn
  exact disjoint_left.mp h.2.2.1 (he.symm ▸ h.2.1.subset hx) hx

omit inst488 inst489 in
lemma IsMaximalProperFace.faceHull_vertex [FiniteDimensional ℝ E] [Nontrivial E] (_ : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsMaximalProperFace K F)
    {x : E} (hx : x ∈ K) (hxn : x ∉ F) :
    faceHull (closedBall (0:E) 1) ({x} ∪ F) = K := by
  let H := faceHull (closedBall (0:E) 1) ({x} ∪ F)
  have hbase : {x} ∪ F ⊆ K := union_subset (singleton_subset_iff.mpr hx) h.1.subset
  have hH := isFace_faceHull (convex_closedBall (0:E) 1) (hbase.trans hK.subset)
  have hHK : H ⊆ K := faceHull_min hK hbase
  have hFH : F ⊆ H := fun _ hx => subset_faceHull (Or.inr hx)
  by_contra hp
  have he := h.2.2 H (hH.mono hK.subset hHK) hFH hp
  exact hxn (he ▸ subset_faceHull (Or.inl (mem_singleton x)))

lemma IsMaximalProperFace.exchange (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsMaximalProperFace K F)
    (hpair : IsParallelPair K F G) (hn : F.Nonempty) {x y : E}
    (hx : x ∈ K.extremePoints ℝ) (hxG : x ∈ G)
    (hy : y ∈ K.extremePoints ℝ) (hyG : y ∈ G) :
    ∃ u ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ v ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ, x+u=y+v := by
  apply parallel_face_vertex_exchange hmed hK hpair hn hx hxG hy hyG
  rw [h.faceHull_vertex hmed hK hx.1 ((hpair.not_mem_iff hx).mpr hxG)]
  exact hy.1

lemma maximal_pair_of_disjoint (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K)
    (hF : IsMaximalProperFace K F) (hG : IsMaximalProperFace K G)
    (hFn : F.Nonempty) (_ : G.Nonempty) (hd : Disjoint F G) :
    IsParallelPair K F G := by
  obtain ⟨A,hA⟩ := maximal_proper_parallel hmed hK hF hFn
  have hGA : G ⊆ A := hA.subset_of_disjoint hmed hK hG.1 hd.symm
  have hAp : A ≠ K := hA.symm.left_ne hFn
  have he := hG.2.2 A hA.2.1 hGA hAp
  exact he ▸ hA

omit inst488 inst489 in
lemma proper_unit_face_subface_ne [FiniteDimensional ℝ E] [Nontrivial E] {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hFK : F ⊆ K) : F ≠ closedBall (0:E) 1 := by
  intro he
  exact hp (subset_antisymm hK.subset (he ▸ hFK))

lemma IsFace.rank_pos (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hp : F ≠ closedBall (0:E) 1)
    (hn : F.Nonempty) : 0 < faceRank F := by
  have hh := faceRank_lt hmed hF hp
    (show IsFace F ∅ from ⟨convex_empty,⟨empty_subset _,by simp⟩⟩) (Ne.symm hn.ne_empty)
  change Module.finrank ℝ (Submodule.span ℝ (∅ : Set E)) < faceRank F at hh
  rw [Submodule.span_empty] at hh
  simpa using hh

end

open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma IsFace.of_support_le {K : Set E} (hK : Convex ℝ K)
    (f : E →ₗ[ℝ] ℝ) (c : ℝ) (hb : ∀ x ∈ K, f x ≤ c) :
    IsFace K {x ∈ K | f x = c} := by
  constructor
  · intro x hx y hy a b ha hb' hab
    refine ⟨hK hx.1 hy.1 ha hb' hab,?_⟩
    simp only [map_add,map_smul,smul_eq_mul,hx.2,hy.2]
    rw [← add_mul, hab, one_mul]
  · refine ⟨fun _ h => h.1,?_⟩
    intro x hx y hy z hz hs
    obtain ⟨a,b,ha,hb',hab,he⟩ := hs
    refine ⟨hx,?_⟩
    have hh := congrArg f he
    simp only [map_add,map_smul,smul_eq_mul,hz.2] at hh
    have hfx := hb x hx
    have hfy := hb y hy
    apply le_antisymm hfx
    by_contra hn
    have hlt : f x < c := lt_of_not_ge hn
    have hpos := mul_pos ha (sub_pos.mpr hlt)
    have hnon := mul_nonneg hb'.le (sub_nonneg.mpr hfy)
    have hc := congrArg (fun t : ℝ => t*c) hab
    nlinarith

variable [FiniteDimensional ℝ E] [Nontrivial E]

lemma disjoint_faces_dual_vertex (hmed : HasMetricMedians E) {F G : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hG : IsFace (closedBall (0:E) 1) G)
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hd : Disjoint F G) :
    ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      (∀ x ∈ F, f x = 1) ∧ ∀ x ∈ G, f x = -1 := by
  obtain ⟨g,hg,hgF,hgG⟩ := disjoint_faces_opposite_support hmed hF.2 hG.2
    hF.1 hG.1 hFn hGn hd
  let A := F ∪ -G
  have hA : A ⊆ closedBall (0:E) 1 := by
    rintro x (hx | hx)
    · exact hF.subset hx
    · have hneg : -x ∈ G := hx
      have hh := hG.subset hneg
      simpa using hh
  have hD : {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | ∀ x ∈ A, f x = 1}.Nonempty := by
    refine ⟨g,mem_closedBall_zero_iff.mpr hg.le,?_⟩
    rintro x (hx | hx)
    · exact hgF x hx
    · have hh := hgG (-x) hx
      simp only [map_neg] at hh
      linarith
  obtain ⟨f,hf⟩ := (isCompact_dual_common A).extremePoints_nonempty hD
  refine ⟨f,(isFace_dual_common hA).2.extremePoints_subset_extremePoints hf,
    fun x hx => hf.1.2 x (Or.inl hx),?_⟩
  intro x hx
  have hh := hf.1.2 (-x) (Or.inr (by simpa using hx))
  simp only [map_neg] at hh
  linarith

lemma IsParallelPair.support_dual_vertex (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    (hFn : F.Nonempty) (hGn : G.Nonempty) :
    ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      F = {x ∈ K | f x = 1} ∧ G = {x ∈ K | f x = -1} := by
  obtain ⟨f,hf,hfF,hfG⟩ := disjoint_faces_dual_vertex hmed (hK.trans h.1)
    (hK.trans h.2.1) hFn hGn h.2.2.1
  have hp := parallelPair_of_dual_vertex hmed hK hf
  have hFsub : F ⊆ {x ∈ K | f x = 1} := fun x hx => ⟨h.1.subset hx,hfF x hx⟩
  have hGsub : G ⊆ {x ∈ K | f x = -1} := fun x hx => ⟨h.2.1.subset hx,hfG x hx⟩
  exact ⟨f,hf,subset_antisymm hFsub (h.symm.complement_anti hmed hK hp.symm hGsub),
    subset_antisymm hGsub (h.complement_anti hmed hK hp hFsub)⟩

lemma parallel_disjoint_union_face (hmed : HasMetricMedians E) {K F F' G G' : Set E}
    (hK : IsFace (closedBall (0:E) 1) K)
    (hF : IsParallelPair K F F') (hG : IsParallelPair K G G')
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hd : Disjoint F G) :
    IsFace K (convexHull ℝ (F ∪ G)) := by
  have hFG' := hG.subset_of_disjoint hmed hK hF.1 hd
  have hGF' := hF.subset_of_disjoint hmed hK hG.1 hd.symm
  obtain ⟨f,hf,heF,heF'⟩ := hF.support_dual_vertex hmed hK hFn (hGn.mono hGF')
  obtain ⟨g,hg,heG,heG'⟩ := hG.support_dual_vertex hmed hK hGn (hFn.mono hFG')
  have hb : ∀ x ∈ K, (f+g) x ≤ 0 := by
    have hs : K ⊆ {x | (f+g) x ≤ (0:ℝ)} := by
      apply hK.subset_of_vertices hmed
        (convex_halfSpace_le (f+g).toLinearMap.isLinear 0)
      intro x hx
      have hv := hK.extreme_mem hx.1 hx.2
      rcases hF.vertex_mem hv with hxF | hxF'
      · have hhF := (heF ▸ hxF).2
        have hhG := (heG' ▸ hFG' hxF).2
        change f x+g x ≤ 0
        linarith
      · have hhF := (heF' ▸ hxF').2
        have hhG := (dual_eval_bounds (mem_closedBall_zero_iff.mp hg.1) hx.1.1).2
        change f x+g x ≤ 0
        linarith
    exact fun x hx => hs hx
  have hC := IsFace.of_support_le hK.1 (f+g).toLinearMap 0 hb
  have he : convexHull ℝ (F ∪ G) = {x ∈ K | (f+g) x = 0} := by
    apply subset_antisymm
    · apply convexHull_min _ hC.1
      rintro x (hx | hx)
      · refine ⟨hF.1.subset hx,?_⟩
        have h1 := (heF ▸ hx).2
        have h2 := (heG' ▸ hFG' hx).2
        change f x+g x = 0
        linarith
      · refine ⟨hG.1.subset hx,?_⟩
        have h1 := (heG ▸ hx).2
        have h2 := (heF' ▸ hGF' hx).2
        change f x+g x = 0
        linarith
    · apply (hK.trans hC).subset_of_vertices hmed (convex_convexHull _ _)
      intro x hx
      apply subset_convexHull
      have hv := hK.extreme_mem hx.1 hx.2.1
      rcases hF.vertex_mem hv with hh | hh
      · exact Or.inl hh
      · right
        rcases hG.vertex_mem hv with hhG | hhG
        · exact hhG
        · have h1 := (heF' ▸ hh).2
          have h2 := (heG' ▸ hhG).2
          have h3 := hx.2.2
          change f x+g x = 0 at h3
          linarith
  exact he.symm ▸ hC

end SymmetricMahler

end

end OAI
