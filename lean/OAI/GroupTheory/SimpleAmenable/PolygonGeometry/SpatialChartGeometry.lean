import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ChartQuadrants

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SpatialChartGeometry

theorem translated_clippedSlope_lift {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (u : CutRing × CutRing)
    (p : GenericSquare a) (t : ℝ × ℝ)
    (ht : p.val = (Int.fract t.1,Int.fract t.2))
    (hp : (-ordinary r < t.1-ordinary u.1 ∧ t.1-ordinary u.1 < ordinary r) ∧
      (-ordinary r < t.2-ordinary u.2 ∧ t.2-ordinary u.2 < ordinary r)) :
    p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ↔
      ordinary (integralCutForm a j u) ≤ cutForm a j t := by
  change translate a (-u) p ∈ (clippedSlopePrimitive a r j).val ↔ _
  rw [mem_clippedSlope_lift r j hr (translate a (-u) p)
    (t-(ordinary u.1,ordinary u.2)) hp ?_]
  · rw [cutForm_sub,cutForm_ordinary]
    exact sub_nonneg
  · have hfract (x y : ℝ) : Int.fract (Int.fract x+y) = Int.fract (x+y) := by
      change Int.fract (x-(⌊x⌋:ℝ)+y) = _
      rw [sub_add_eq_add_sub,Int.fract_sub_intCast]
    simp [ht,hfract,sub_eq_add_neg]

theorem clippedSlope_agree_on_rectangle {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (u v : CutRing × CutRing) (l h : Fin 2 → CutRing)
    (hlh : ∀ k, ordinary (l k) ≤ ordinary (h k))
    (hlen : ∀ k, ordinary (h k)-ordinary (l k) < 1)
    (hu : ∀ k, -ordinary r < ordinary (l k)-ordinary (if k=0 then u.1 else u.2) ∧
      ordinary (h k)-ordinary (if k=0 then u.1 else u.2) < ordinary r)
    (hv : ∀ k, -ordinary r < ordinary (l k)-ordinary (if k=0 then v.1 else v.2) ∧
      ordinary (h k)-ordinary (if k=0 then v.1 else v.2) < ordinary r)
    (hline : integralCutForm a j u = integralCutForm a j v) :
    spatialTranslate u (clippedSlopePrimitive a r j) ⊓ coordinateRectangle a l h =
      spatialTranslate v (clippedSlopePrimitive a r j) ⊓ coordinateRectangle a l h := by
  apply Subtype.ext
  ext p
  change (p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ∧
    p ∈ (coordinateRectangle a l h).val) ↔
    (p ∈ (spatialTranslate v (clippedSlopePrimitive a r j)).val ∧
    p ∈ (coordinateRectangle a l h).val)
  by_cases hp : p ∈ (coordinateRectangle a l h).val
  · obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_lift l h hlh hlen p hp
    have hbox (w : CutRing × CutRing)
        (hw : ∀ k : Fin 2, -ordinary r < ordinary (l k)-ordinary (if k=0 then w.1 else w.2) ∧
          ordinary (h k)-ordinary (if k=0 then w.1 else w.2) < ordinary r) :
        (-ordinary r < t.1-ordinary w.1 ∧ t.1-ordinary w.1 < ordinary r) ∧
          (-ordinary r < t.2-ordinary w.2 ∧ t.2-ordinary w.2 < ordinary r) := by
      have hw0 := hw 0
      have hw1 := hw 1
      simp only [ite_true,Fin.isValue,show (1:Fin 2) ≠ 0 by decide,ite_false] at hw0 hw1
      constructor <;> constructor <;> linarith
    rw [translated_clippedSlope_lift r j hr u p t ht (hbox u hu),
      translated_clippedSlope_lift r j hr v p t ht (hbox v hv),hline]
  · simp only [hp,and_false]

theorem integralCutForm_tangent (a : ℕ) (d : CutRing) :
    integralCutForm a 2 (d,cutTau^a*d) = 0 := by
  simp [integralCutForm]

theorem integralCutForm_tangent_swapped (a : ℕ) (d : CutRing) :
    integralCutForm a 3 (cutTau^a*d,d) = 0 := by
  simp [integralCutForm]

end SpatialChartGeometry

section ChartTransforms

@[simp] theorem spatialTranslate_inter {a : ℕ} (z : CutRing × CutRing)
    (U V : polygonAlgebra a) : spatialTranslate z (U ⊓ V) =
      spatialTranslate z U ⊓ spatialTranslate z V := rfl

@[simp] theorem spatialTranslate_compl {a : ℕ} (z : CutRing × CutRing)
    (U : polygonAlgebra a) : spatialTranslate z Uᶜ = (spatialTranslate z U)ᶜ := rfl

theorem spatialTranslate_mono {a : ℕ} (z : CutRing × CutRing)
    {U V : polygonAlgebra a} (h : U ≤ V) : spatialTranslate z U ≤ spatialTranslate z V :=
  fun _ hp => h hp

theorem spatialTranslate_resolved {a : ℕ} {ι : Type*}
    (U : ι → polygonAlgebra a) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (U i).val) V.val) (z : CutRing × CutRing) :
    ResolvedBy (fun i => (spatialTranslate z (U i)).val) (spatialTranslate z V).val := by
  intro x y he
  exact hV (translate a (-z) x) (translate a (-z) y) he

theorem spatialTranslate_coordinateInterval {a : ℕ} (z : CutRing × CutRing)
    (j : Fin 2) (u v : CutRing) :
    spatialTranslate z (coordinateInterval a j u v) =
      coordinateInterval a j (u+(if j=0 then z.1 else z.2))
        (v+(if j=0 then z.1 else z.2)) := by
  apply Subtype.ext
  ext p
  have hfract (x y : ℝ) : Int.fract (Int.fract x+y) = Int.fract (x+y) := by
    change Int.fract (x-(⌊x⌋:ℝ)+y) = _
    rw [sub_add_eq_add_sub,Int.fract_sub_intCast]
  have hsub (x y : CutRing) : v+x-(u+y) = v-u+(x-y) := by ring
  fin_cases j <;>
    simp [spatialTranslate,coordinateInterval,coordinateBetween,coordinateArc,
      coordinate,coordinateShift,translate_val,hfract,hsub,sub_eq_add_neg,add_assoc]

theorem spatialTranslate_coordinateRectangle {a : ℕ} (z : CutRing × CutRing)
    (u v : Fin 2 → CutRing) :
    spatialTranslate z (coordinateRectangle a u v) =
      coordinateRectangle a (fun j => u j+(if j=0 then z.1 else z.2))
        (fun j => v j+(if j=0 then z.1 else z.2)) := by
  simp [coordinateRectangle,spatialTranslate_coordinateInterval]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_shared_primitive (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (i : ι) (j : κ) (he : P i = Q j)
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun _ : Unit => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    B.fullGeometricSector hlarge P h V = B.fullGeometricSector hlarge Q g V := by
  let S : Unit → Fin 5 × (CutRing × CutRing) := fun _ => P i
  have hS : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb S :=
    fun I hI b hb => PrimitiveFamilyLaw.reindex B I b hb P (h I hI b hb) (fun _ => i)
  rw [← B.fullGeometricSector_subfamily hlarge P S (fun _ => i) rfl h hS V hV]
  apply B.fullGeometricSector_subfamily hlarge Q S (fun _ => j) _ g hS V hV
  exact funext (fun _ => he.symm)

end InitialCoverSystem
end ChartTransforms

end SimpleAmenable
end
end

end OAI
