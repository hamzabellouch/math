import OAI.Geometry.RuledCovering.TipCylinders

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- The shape predicate denotes a genuinely compact convex base, not merely
four distinguished points or an unbounded affine plane. -/
lemma IsParallelogram.convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsParallelogram P) : Convex ℝ P := by
  obtain ⟨c,u,v,_,rfl⟩ := hP
  intro x hx y hy a b ha hb hab
  obtain ⟨s,hs,t,ht,rfl⟩ := hx
  obtain ⟨s',hs',t',ht',rfl⟩ := hy
  refine ⟨a*s+b*s',⟨add_nonneg (mul_nonneg ha hs.1) (mul_nonneg hb hs'.1),?_⟩,
    a*t+b*t',⟨add_nonneg (mul_nonneg ha ht.1) (mul_nonneg hb ht'.1),?_⟩,?_⟩
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hs.2),mul_nonneg hb (sub_nonneg.mpr hs'.2)]
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr ht.2),mul_nonneg hb (sub_nonneg.mpr ht'.2)]
  · calc
      _ = (a+b) • c+(a*s+b*s') • u+(a*t+b*t') • v := by module
      _ = _ := by rw [hab,one_smul]

lemma IsTriangle.isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsTriangle P) : IsCompact P := by
  obtain ⟨c,u,v,_,rfl⟩ := hP
  let S : Set (ℝ × ℝ) := (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ∩ {z | z.1+z.2 ≤ 1}
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le (by fun_prop) continuous_const)
  have hc := hS.image (show Continuous (fun z : ℝ × ℝ => c+z.1 • u+z.2 • v) by fun_prop)
  convert hc using 1
  ext x
  constructor
  · rintro ⟨s,t,hs,ht,hst,rfl⟩
    exact ⟨(s,t),⟨⟨⟨hs,by linarith⟩,⟨ht,by linarith⟩⟩,hst⟩,rfl⟩
  · rintro ⟨⟨s,t⟩,⟨⟨hs,ht⟩,hst⟩,rfl⟩
    exact ⟨s,t,hs.1,ht.1,hst,rfl⟩

lemma IsTriangle.convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsTriangle P) : Convex ℝ P := by
  obtain ⟨c,u,v,_,rfl⟩ := hP
  intro x hx y hy a b ha hb hab
  obtain ⟨s,t,hs,ht,hst,rfl⟩ := hx
  obtain ⟨s',t',hs',ht',hst',rfl⟩ := hy
  refine ⟨a*s+b*s',a*t+b*t',by positivity,by positivity,?_,?_⟩
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hst),mul_nonneg hb (sub_nonneg.mpr hst')]
  · calc
      _ = (a+b) • c+(a*s+b*s') • u+(a*t+b*t') • v := by module
      _ = _ := by rw [hab,one_smul]

lemma Cylinder.parallelogram_compact_convex {C : Cylinder} (hC : C.parallelogram) :
    IsCompact C.base ∧ Convex ℝ C.base := ⟨hC.isCompact,hC.convex⟩

lemma Cylinder.triangle_compact_convex {C : Cylinder} (hC : C.triangle) :
    IsCompact C.base ∧ Convex ℝ C.base := ⟨hC.isCompact,hC.convex⟩

lemma IsSquareTile.compact_convex {T : Set Plane} (hT : IsSquareTile T) :
    IsCompact T ∧ Convex ℝ T := ⟨hT.parallelogram.isCompact,hT.parallelogram.convex⟩

end RuledApproximation

end

end OAI
