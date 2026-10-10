import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteArrangementGerms
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SupportedCellPatching

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section InwardPlanarGerms

theorem finite_arrangement_germ_inward {ι : Type*} [Finite ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → ℝ) (z y : ℝ × ℝ) (σ : ι → Bool)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (hzero : ∀ k, realCoordinate z k=0 → 0<realCoordinate y k)
    (hone : ∀ k, realCoordinate z k=1 → realCoordinate y k<1)
    (hactive : ∀ i, cutForm a (j i) z=c i →
      if σ i then cutForm a (j i) y < c i else c i < cutForm a (j i) y)
    (hinactive : ∀ i, cutForm a (j i) z≠c i →
      if σ i then cutForm a (j i) z < c i else c i < cutForm a (j i) z)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ p : GenericSquare a, p.val ∈ N ∧ p.val ∈ strictLineCell a j c σ := by
  classical
  let J : Sum ι (Fin 2 × Bool) → Fin 4 := Sum.elim j (fun d => Fin.castLE (by omega) d.1)
  let C : Sum ι (Fin 2 × Bool) → ℝ := Sum.elim c (fun d => if d.2 then 1 else 0)
  let S : Sum ι (Fin 2 × Bool) → Bool := Sum.elim σ Prod.snd
  have ha : ∀ i, cutForm a (J i) z=C i →
      if S i then cutForm a (J i) y < C i else C i < cutForm a (J i) y := by
    intro i hi
    cases i with
    | inl i => exact hactive i hi
    | inr d =>
      rcases d with ⟨d,b⟩
      fin_cases d <;> cases b
      · exact hzero 0 hi
      · exact hone 0 hi
      · exact hzero 1 hi
      · exact hone 1 hi
  have hn : ∀ i, cutForm a (J i) z≠C i →
      if S i then cutForm a (J i) z < C i else C i < cutForm a (J i) z := by
    intro i hi
    cases i with
    | inl i => exact hinactive i hi
    | inr d =>
      rcases d with ⟨d,b⟩
      fin_cases d <;> cases b <;>
        simp [J,C,S,cutForm] at hi ⊢
      · exact lt_of_le_of_ne hz₁.1 (Ne.symm hi)
      · exact lt_of_le_of_ne hz₁.2 hi
      · exact lt_of_le_of_ne hz₂.1 (Ne.symm hi)
      · exact lt_of_le_of_ne hz₂.2 hi
  obtain ⟨p,hp,hcell,hgeneric⟩ := finite_arrangement_germ a J C z y S ha hn N hN hz
  have hp₁ : p.1 ∈ Set.Ioo (0:ℝ) 1 := ⟨hcell (.inr (0,false)),hcell (.inr (0,true))⟩
  have hp₂ : p.2 ∈ Set.Ioo (0:ℝ) 1 := ⟨hcell (.inr (1,false)),hcell (.inr (1,true))⟩
  exact ⟨⟨p,⟨hp₁.1.le,hp₁.2⟩,⟨hp₂.1.le,hp₂.2⟩,hgeneric⟩,hp,fun i => hcell (.inl i)⟩

end InwardPlanarGerms

section ConcurrentPositiveDecisions
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

noncomputable def positiveDecision (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (j : Fin 4) : polygonAlgebra a :=
  spatialTranslate (u+C.anchors t j) (initialTest a r ⟨j.val+1,by omega⟩)

noncomputable def marginPolygon (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) : polygonAlgebra a :=
  spatialTranslate u (coordinateRectangle a (C.margins t).lower (C.margins t).upper)

theorem positiveDecision_planar (hr : 0<ordinary r ∧ ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) (j : Fin 4)
    (hnear : ∀ z : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate z k ∧
        realCoordinate z k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate z k-ordinary (pointCoordinate (u+C.anchors t j) k)|<3*C.epsilon)
    (p : GenericSquare a) (y : ℝ × ℝ) (hy : p.val=(Int.fract y.1,Int.fract y.2))
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate y k ∧
      realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (C.positiveDecision t u j).val ↔
      ordinary (integralCutForm a j (u+C.anchors t j))≤cutForm a j y := by
  have hs : |y.1-ordinary (u+C.anchors t j).1|<ordinary r ∧
      |y.2-ordinary (u+C.anchors t j).2|<ordinary r := by
    have h₀ := hnear y hcell 0
    have h₁ := hnear y hcell 1
    have hr' := C.radius
    have hε := C.positive
    change |y.1-ordinary (u+C.anchors t j).1|<3*C.epsilon at h₀
    change |y.2-ordinary (u+C.anchors t j).2|<3*C.epsilon at h₁
    constructor <;> linarith
  fin_cases j
  · exact C.axis_on_margin 0 u (u+C.anchors t 0) t hnear p y hy hcell
  · exact C.axis_on_margin 1 u (u+C.anchors t 1) t hnear p y hy hcell
  · exact translated_clippedSlope_planar r 2 hr (u+C.anchors t 2) p y hy hs
  · exact translated_clippedSlope_planar r 3 hr (u+C.anchors t 3) p y hy hs

theorem marginPolygon_lift (hr : ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (p : GenericSquare a) (hp : p ∈ (C.marginPolygon t u).val) :
    ∃ y : ℝ × ℝ, p.val=(Int.fract y.1,Int.fract y.2) ∧ AvoidsCuts a y ∧
      ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)<realCoordinate y k ∧
        realCoordinate y k<ordinary ((C.margins t).upper k+pointCoordinate u k) := by
  have hw (k) := (C.margins t).width C.positive k
  have hrad := C.radius
  have hlen (k) : ordinary ((C.margins t).upper k+pointCoordinate u k)-
      ordinary ((C.margins t).lower k+pointCoordinate u k)<1 := by
    simp only [map_add]
    linarith [hw k]
  have hle (k) : ordinary ((C.margins t).lower k+pointCoordinate u k) ≤
      ordinary ((C.margins t).upper k+pointCoordinate u k) := by
    simp only [map_add]
    linarith [hw k,C.positive]
  have hp' : p ∈ (coordinateRectangle a
      (fun k => (C.margins t).lower k+pointCoordinate u k)
      (fun k => (C.margins t).upper k+pointCoordinate u k)).val := by
    simpa only [marginPolygon,spatialTranslate_coordinateRectangle,pointCoordinate] using hp
  obtain ⟨y,hy,hy₀,hy₁⟩ := coordinateRectangle_strict_lift _ _ hle hlen p hp'
  refine ⟨y,hy,planar_lift_avoidsCuts p y hy,?_⟩
  intro k
  fin_cases k
  · exact hy₀
  · exact hy₁

end ConcurrentGeometry
end ConcurrentPositiveDecisions

end SimpleAmenable
end
end

end OAI
