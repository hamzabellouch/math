import OAI.Geometry.CylinderCovering.Beams.ShapeCompact
import OAI.Geometry.TriangularCovering.Main

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace

namespace ShortenedBeam

private theorem affineIndependent_triple_iff {E : Type*}
    [AddCommGroup E] [Module ℝ E] (a b c : E) :
    AffineIndependent ℝ (![a,b,c] : Fin 3 → E) ↔
      LinearIndependent ℝ (![b-a,c-a] : Fin 2 → E) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0,
    ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
  apply Iff.of_eq
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem isTriangle_iff_vertices {E : Type*}
    [AddCommGroup E] [Module ℝ E] (B : Set E) :
    RuledApproximation.IsTriangle B ↔
      ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧ B = convexHull ℝ (range v) := by
  constructor
  · rintro ⟨c,u,v,huv,hB⟩
    refine ⟨![c,c+u,c+v],?_,?_⟩
    · rw [affineIndependent_triple_iff]
      simpa only [add_sub_cancel_left] using huv
    · rw [hB]
      change _ = TriangularCovering.triangle c (c+u) (c+v)
      ext x
      simp only [TriangularCovering.mem_triangle_iff, add_sub_cancel_left, mem_ofPred_eq]
  · rintro ⟨v,hv,rfl⟩
    have heq : v = ![v 0,v 1,v 2] := by
      funext i
      fin_cases i <;> rfl
    have hind : LinearIndependent ℝ (![v 1-v 0,v 2-v 0] : Fin 2 → E) := by
      apply (affineIndependent_triple_iff _ _ _).mp
      simpa only [← heq] using hv
    refine ⟨v 0,v 1-v 0,v 2-v 0,hind,?_⟩
    rw [heq]
    change TriangularCovering.triangle (v 0) (v 1) (v 2) = _
    ext x
    exact TriangularCovering.mem_triangle_iff _ _ _ _

theorem hasTriangularBase_iff_triangle (C : RuledApproximation.Cylinder) :
    HasTriangularBase C ↔ C.triangle := by
  let P := (Submodule.span ℝ ({C.axis} : Set Space))ᗮ
  constructor
  · rintro ⟨v,hv,hB⟩
    have hmem (i : Fin 3) : v i ∈ (Subtype.val : P → Space) '' C.base := by
      rw [hB]
      exact subset_convexHull ℝ _ (mem_range_self i)
    choose w hw hweq using hmem
    have hfun : (P.subtype.toAffineMap ∘ w) = v := funext hweq
    have hwi : AffineIndependent ℝ w := by
      apply AffineIndependent.of_comp P.subtype.toAffineMap
      rw [hfun]
      exact hv
    apply (isTriangle_iff_vertices C.base).mpr
    refine ⟨w,hwi,?_⟩
    apply (Set.image_injective.mpr Subtype.val_injective)
    change P.subtype '' C.base = P.subtype '' convexHull ℝ (range w)
    rw [P.subtype.image_convexHull, ← range_comp]
    exact hB.trans (congrArg (fun f : Fin 3 → Space => convexHull ℝ (range f)) hfun.symm)
  · intro hC
    obtain ⟨w,hw,hB⟩ := (isTriangle_iff_vertices C.base).mp hC
    refine ⟨P.subtype.toAffineMap ∘ w,hw.map' P.subtype.toAffineMap Subtype.val_injective,?_⟩
    change P.subtype '' C.base = _
    rw [hB,P.subtype.image_convexHull,← range_comp]
    rfl

theorem hasRectangularBase_iff_intrinsic (C : RuledApproximation.Cylinder) :
    CylinderCovering.BeamStrip.HasRectangularBase C ↔
    ∃ c u v : ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ),
      inner ℝ u v = 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      C.base = {z | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1,
        z = c+s • u+t • v} := by
  let P := (Submodule.span ℝ ({C.axis} : Set Space))ᗮ
  constructor
  · rintro ⟨c,u,v,huv,hu,hv,hB⟩
    have hplane : ∀ z ∈ (Subtype.val : P → Space) '' C.base, z ∈ P := by
      rintro z ⟨p,hp,rfl⟩
      exact p.property
    have hc : c ∈ P := by
      apply hplane
      rw [hB]
      exact ⟨0,by norm_num,0,by norm_num,by simp⟩
    have hcu : c+u ∈ P := by
      apply hplane
      rw [hB]
      exact ⟨1,by norm_num,0,by norm_num,by simp⟩
    have hcv : c+v ∈ P := by
      apply hplane
      rw [hB]
      exact ⟨0,by norm_num,1,by norm_num,by simp⟩
    have huP : u ∈ P := by simpa only [add_sub_cancel_left] using P.sub_mem hcu hc
    have hvP : v ∈ P := by simpa only [add_sub_cancel_left] using P.sub_mem hcv hc
    refine ⟨⟨c,hc⟩,⟨u,huP⟩,⟨v,hvP⟩,huv,?_,?_,?_⟩
    · intro h
      exact hu (congrArg Subtype.val h)
    · intro h
      exact hv (congrArg Subtype.val h)
    · ext z
      constructor
      · intro hz
        have hz' : (z:Space) ∈ (Subtype.val : P → Space) '' C.base := ⟨z,hz,rfl⟩
        rw [hB] at hz'
        obtain ⟨s,hs,t,ht,he⟩ := hz'
        exact ⟨s,hs,t,ht,Subtype.ext he⟩
      · rintro ⟨s,hs,t,ht,he⟩
        have hz' : (z:Space) ∈ (Subtype.val : P → Space) '' C.base := by
          rw [hB]
          exact ⟨s,hs,t,ht,congrArg Subtype.val he⟩
        obtain ⟨q,hq,hqz⟩ := hz'
        exact (Subtype.val_injective hqz) ▸ hq
  · rintro ⟨c,u,v,huv,hu,hv,hB⟩
    refine ⟨(c:Space),(u:Space),(v:Space),huv,?_,?_,?_⟩
    · intro h
      exact hu (Subtype.ext h)
    · intro h
      exact hv (Subtype.ext h)
    · ext z
      constructor
      · rintro ⟨q,hq,rfl⟩
        rw [hB] at hq
        obtain ⟨s,hs,t,ht,he⟩ := hq
        exact ⟨s,hs,t,ht,congrArg Subtype.val he⟩
      · rintro ⟨s,hs,t,ht,rfl⟩
        refine ⟨c+s • u+t • v,?_,rfl⟩
        rw [hB]
        exact ⟨s,hs,t,ht,rfl⟩

theorem hasMixedBase_iff_intrinsic_compact (C : RuledApproximation.Cylinder) :
    HasMixedBase C ↔
      (C.triangle ∨ ∃ c u v : ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ),
        inner ℝ u v = 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
        C.base = {z | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1,
          z = c+s • u+t • v}) ∧ IsCompact C.base := by
  have he := or_congr (hasTriangularBase_iff_triangle C)
    (hasRectangularBase_iff_intrinsic C)
  constructor
  · intro h
    exact ⟨he.mp h,h.isCompact⟩
  · intro h
    exact he.mpr h.1

end ShortenedBeam

end

end OAI
