import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.VaryingCellClassification
import OAI.GroupTheory.SimpleAmenable.CentralCovers.LocalArrangementAssignments
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InwardPlanarGerms
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CompactFineGrid

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConcurrentInwardModel
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

noncomputable def inwardGate (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (k : Fin 2) : polygonAlgebra a :=
  if realCoordinate z k=0 then C.positiveDecision t u (axisDirection k)
  else if realCoordinate z k=1 then (C.positiveDecision t u (axisDirection k))ᶜ
  else wholePolygon a

noncomputable def inwardMargin (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) : polygonAlgebra a :=
  C.marginPolygon t u ⊓ C.inwardGate t u z 0 ⊓ C.inwardGate t u z 1

noncomputable def localDecision (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (j : Fin 4) (c : CutRing) : polygonAlgebra a :=
  if cutForm a j z=ordinary c then (C.positiveDecision t u j)ᶜ
  else if cutForm a j z<ordinary c then ⊤ else ⊥

theorem localDecision_assignment_realized {ι : Type*} [Finite ι]
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (hline : ∀ i, cutForm a (j i) z=ordinary (c i) →
      integralCutForm a (j i) (u+C.anchors t (j i))=c i)
    (hboundary : ∀ k, realCoordinate z k=0 ∨ realCoordinate z k=1 →
      ordinary (pointCoordinate (u+C.anchors t (axisDirection k)) k)=realCoordinate z k)
    (hnear : ∀ i, cutForm a (j i) z=ordinary (c i) → ∀ y : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate y k ∧
        realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (j i)) k)|<3*C.epsilon)
    (hnearB : ∀ d, realCoordinate z d=0 ∨ realCoordinate z d=1 → ∀ y : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate y k ∧
        realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (axisDirection d)) k)|<3*C.epsilon)
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin t u z).val)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ q : GenericSquare a, q.val ∈ N ∧
      polygonAssignment (fun i => cutPolygon a (j i) (c i)) q=
        polygonAssignment (fun i => C.localDecision t u z (j i) (c i)) p := by
  classical
  have hpM : p ∈ (C.marginPolygon t u).val := hp.1.1
  have hpG (k : Fin 2) : p ∈ (C.inwardGate t u z k).val := by
    fin_cases k
    · exact hp.1.2
    · exact hp.2
  obtain ⟨y,hy,ha,hcell⟩ := C.marginPolygon_lift hr.2 t u p hpM
  have hzero : ∀ k, realCoordinate z k=0 → 0<realCoordinate y k := by
    intro k hk
    have h := hpG k
    simp only [inwardGate,hk,ite_eq_left] at h
    have hd := (C.positiveDecision_planar hr t u (axisDirection k) (hnearB k (Or.inl hk)) p y hy
      (fun k => ⟨(hcell k).1.le,(hcell k).2.le⟩)).mp h
    rw [integralCutForm_axis,hboundary k (Or.inl hk),hk] at hd
    have haxis : cutForm a (axisDirection k) y=realCoordinate y k := by fin_cases k <;> rfl
    rw [haxis] at hd
    apply lt_of_le_of_ne hd
    intro he
    have hn := ha (axisDirection k) 0
    simp only [map_zero,haxis] at hn
    exact hn he.symm
  have hone : ∀ k, realCoordinate z k=1 → realCoordinate y k<1 := by
    intro k hk
    have h := hpG k
    have hn : realCoordinate z k≠0 := by rw [hk]; norm_num
    simp only [inwardGate,ite_eq_right hn,ite_eq_left hk] at h
    have hd := (not_congr (C.positiveDecision_planar hr t u (axisDirection k) (hnearB k (Or.inr hk)) p y hy
      (fun k => ⟨(hcell k).1.le,(hcell k).2.le⟩))).mp h
    rw [integralCutForm_axis,hboundary k (Or.inr hk),hk] at hd
    have haxis : cutForm a (axisDirection k) y=realCoordinate y k := by fin_cases k <;> rfl
    rw [haxis] at hd
    exact lt_of_not_ge hd
  let σ := polygonAssignment (fun i => C.localDecision t u z (j i) (c i)) p
  have hactive : ∀ i, cutForm a (j i) z=ordinary (c i) →
      if σ i then cutForm a (j i) y<ordinary (c i)
      else ordinary (c i)<cutForm a (j i) y := by
    intro i hi
    have hd := C.positiveDecision_planar hr t u (j i) (hnear i hi) p y hy
      (fun k => ⟨(hcell k).1.le,(hcell k).2.le⟩)
    rw [hline i hi] at hd
    have hσ : σ i=decide (¬ordinary (c i)≤cutForm a (j i) y) := by
      apply decide_eq_decide.mpr
      change (p ∈ (C.localDecision t u z (j i) (c i)).val) ↔ _
      simp only [localDecision,ite_eq_left hi]
      exact not_congr hd
    rw [hσ]
    split_ifs with h
    · exact lt_of_not_ge (of_decide_eq_true h)
    · have hh := of_decide_eq_false (Bool.eq_false_iff.mpr h)
      exact lt_of_le_of_ne (not_not.mp hh) (ha (j i) (c i)).symm
  have hinactive : ∀ i, cutForm a (j i) z≠ordinary (c i) →
      if σ i then cutForm a (j i) z<ordinary (c i)
      else ordinary (c i)<cutForm a (j i) z := by
    intro i hi
    by_cases hlt : cutForm a (j i) z<ordinary (c i)
    · simp [σ,polygonAssignment,localDecision,hi,hlt]
    · simp only [σ,polygonAssignment,localDecision,ite_eq_right hi,ite_eq_right hlt]
      simpa using lt_of_le_of_ne (le_of_not_gt hlt) hi.symm
  obtain ⟨q,hq,hassign⟩ := finite_arrangement_germ_inward a j (fun i => ordinary (c i))
    z y σ hz₁ hz₂ hzero hone hactive hinactive N hN hz
  refine ⟨q,hq,?_⟩
  funext i
  change decide (cutForm a (j i) q.val<ordinary (c i))=σ i
  have hi := hassign i
  cases he : σ i
  · simp only [he,Bool.false_eq_true,↓reduceIte] at hi
    exact decide_eq_false (not_lt_of_gt hi)
  · simp only [he,↓reduceIte] at hi
    exact decide_eq_true hi

theorem exists_inward_assignment_model {ι : Type*} [Finite ι]
    (ha : 0<a) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      (∀ y : ℝ × ℝ, dist y z<C.epsilon/2 → ∀ k,
        ordinary ((C.margins t).lower k+pointCoordinate u k)<realCoordinate y k ∧
        realCoordinate y k<ordinary ((C.margins t).upper k+pointCoordinate u k)) ∧
      ∀ p : GenericSquare a, p ∈ (C.inwardMargin t u z).val →
        ∀ N : Set (ℝ × ℝ), IsOpen N → z ∈ N →
        ∃ q : GenericSquare a, q.val ∈ N ∧
          polygonAssignment (fun i => cutPolygon a (j i) (c i)) q=
            polygonAssignment (fun i => C.localDecision t u z (j i) (c i)) p := by
  classical
  let J : Sum ι (Fin 2 × Bool) → Fin 4 := Sum.elim j (fun d => axisDirection d.1)
  let K : Sum ι (Fin 2 × Bool) → CutRing := Sum.elim c (fun d => if d.2 then 1 else 0)
  obtain ⟨t,u,hcell,hactive⟩ := C.simultaneous_active_neighborhood ha J K z
  have hb (k : Fin 2) (hk : realCoordinate z k=0 ∨ realCoordinate z k=1) :
      ∃ b : Bool, cutForm a (J (.inr (k,b))) z=ordinary (K (.inr (k,b))) := by
    have haxis : cutForm a (axisDirection k) z=realCoordinate z k := by fin_cases k <;> rfl
    rcases hk with hk | hk
    · exact ⟨false,by simpa only [J,K,Sum.elim_inr,Bool.false_eq_true,↓reduceIte,map_zero,haxis] using hk⟩
    · exact ⟨true,by simpa only [J,K,Sum.elim_inr,↓reduceIte,map_one,haxis] using hk⟩
  refine ⟨t,u,hcell,fun p hp N hN hz =>
    C.localDecision_assignment_realized hr t u j c z hz₁ hz₂
      (fun i hi => (hactive (.inl i) hi).1) ?_
      (fun i hi => (hactive (.inl i) hi).2) ?_ p hp N hN hz⟩
  · intro k hk
    obtain ⟨b,hb⟩ := hb k hk
    have he := congrArg ordinary (hactive (.inr (k,b)) hb).1
    have haxis : cutForm a (axisDirection k) z=realCoordinate z k := by fin_cases k <;> rfl
    change ordinary (integralCutForm a (axisDirection k) (u+C.anchors t (axisDirection k)))=_ at he
    rw [integralCutForm_axis] at he
    exact he.trans (by simpa only [J,Sum.elim_inr,haxis] using hb.symm)
  · intro k hk
    obtain ⟨b,hb⟩ := hb k hk
    exact (hactive (.inr (k,b)) hb).2

end ConcurrentGeometry
end ConcurrentInwardModel

end SimpleAmenable
end
end

end OAI
