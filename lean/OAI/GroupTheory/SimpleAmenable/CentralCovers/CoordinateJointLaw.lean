import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GrowthAxisUniform
import OAI.GroupTheory.SimpleAmenable.CentralCovers.StarProjection
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CoordinateProductPatterns

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CoordinateJointLaw
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem coordinate_pair_law {n k : ℕ} (hn : 2 ≤ n)
    (g : B.CoordinateWindowLaw n) (q : Fin 2 → ℤ)
    (haxis : ∀ d p I b hb, B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives d k p))
    (i j : Fin 2 × Fin (k-1)) (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) :
    B.PrimitiveFamilyLaw I b hb (primitivePair (coordinateWindowPrimitives k q) i j) := by
  classical
  by_cases hij : i.1 = j.1
  · have h := PrimitiveFamilyLaw.reindex B I b hb (axisWindowPrimitives i.1 k (q i.1))
      (haxis i.1 (q i.1) I b hb) (fun t : Bool => if t then j.2 else i.2)
    convert h using 1
    funext t
    cases t <;> simp [primitivePair,axisWindowPrimitives,coordinateWindowPrimitives,hij]
  · let p : Fin 2 → ℤ := fun d => if d=i.1 then q i.1+(i.2.val:ℤ) else q j.1+(j.2.val:ℤ)
    let v : Bool → Fin 2 × Fin (n-1) := fun t => (if t then j.1 else i.1,⟨0,by omega⟩)
    have h := PrimitiveFamilyLaw.reindex B I b hb (coordinateWindowPrimitives n p) (g I b hb p) v
    convert h using 1
    funext t
    cases t <;> simp [primitivePair,coordinateWindowPrimitives,p,v,Ne.symm hij]

omit B in
theorem coordinateWindowPatterns {k : ℕ} (q : Fin 2 → ℤ)
    (σ : Fin 2 × Fin (k-1) → Bool)
    (hσ : ∀ d : Fin 2, (fun i => σ (d,i)) ∈
      Set.range (polygonAssignment (primitiveTests (a := a) (r := r) (axisWindowPrimitives d k (q d))))) :
    σ ∈ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) (coordinateWindowPrimitives k q))) := by
  apply coordinate_patterns_product _ _ σ hσ
  intro d i p p' hp
  simp only [primitiveTests,primitiveFamilyTests,coordinateWindowPrimitives,initialTest_coordinate]
  fin_cases d <;>
    simp_all [spatialTranslate,coordinatePrimitive,coordinateShift,halfPlane,cutForm,translate_val,coordinate]

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem coordinate_joint_law (h20 : 20 ≤ m+1) {n k : ℕ} (hn : 2 ≤ n)
    (g : B.CoordinateWindowLaw n)
    (haxis : ∀ d p I b hb, B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives d k p)) :
    B.CoordinateWindowLaw k := by
  classical
  intro I b hb q
  apply B.pair_actual_law (by omega) (coordinateWindowPrimitives k q)
    (fun i j I _ b hb => B.coordinate_pair_law hn g q haxis i j I b hb) h20
    (fun d : Fin 2 => fun i : Fin (k-1) => (d,i)) _ _ I b hb
  · intro d I _ b hb
    exact haxis d (q d) I b hb
  · intro σ hσ
    by_contra! h
    apply hσ
    apply coordinateWindowPatterns q σ
    exact h

end InitialCoverSystem
end CoordinateJointLaw

section CoordinatePropagation
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem coordinate_growth (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hwz : w*z=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
    {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ N : ℕ, 1005 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
      ∀ n : ℕ, N ≤ n → B.CoordinateWindowLaw n → B.CoordinateWindowLaw (growthNewLength n) := by
  obtain ⟨N,hN,h⟩ := growth_axis_law (hm := hm) hlarge hr s w z hs hsr hwz hshort hC hSlope hconj
  refine ⟨N,hN,?_⟩
  intro M B hB n hn g
  exact B.coordinate_joint_law hlarge (by omega) g (h M B hB n hn g)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in

theorem coordinate_iteration {M : ℕ} (B : InitialCoverSystem a r m hm M)
    (N : ℕ) (hN : 5 ≤ N) (hbase : B.CoordinateWindowLaw N)
    (hstep : ∀ n, N ≤ n → B.CoordinateWindowLaw n → B.CoordinateWindowLaw (growthNewLength n)) :
    ∀ n, B.CoordinateWindowLaw n := by
  have hge : ∀ n, N ≤ n → B.CoordinateWindowLaw n := by
    apply Nat.le_induction
    · exact hbase
    · intro n hn g
      apply (hstep n hn g).mono B
      simp only [growthNewLength]
      omega
  intro n
  rcases le_total n N with hn|hn
  · exact hbase.mono B hn
  · exact hge n hn

end InitialCoverSystem
end CoordinatePropagation

end SimpleAmenable
end
end

end OAI
