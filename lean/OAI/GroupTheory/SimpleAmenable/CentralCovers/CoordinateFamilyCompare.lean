import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SectorOffsetCoherence

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CoordinateFamilyCompare

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_compare (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (v : κ → ι)
    (hj : ∀ i, (P (v i)).1 = (Q i).1)
    (hp : ∀ i, spatialTranslate (P (v i)).2 (initialTest a r (P (v i)).1) =
      spatialTranslate (Q i).2 (initialTest a r (Q i).1))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val) :
    B.fullGeometricSector hlarge Q g V = B.fullGeometricSector hlarge P h V := by
  let R := P ∘ v
  have hR : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb R :=
    fun I hI b hb => PrimitiveFamilyLaw.reindex B I b hb P (h I hI b hb) v
  have hVR : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) R i).val) V.val := by
    intro x y he
    apply hV x y
    intro i
    have hh := he i
    change x ∈ (spatialTranslate (P (v i)).2 (initialTest a r (P (v i)).1)).val ↔
      y ∈ (spatialTranslate (P (v i)).2 (initialTest a r (P (v i)).1)).val at hh
    rw [hp i] at hh
    exact hh
  rw [← B.fullGeometricSector_congr_offsets hlarge R Q hj hp hR g V hVR]
  exact B.fullGeometricSector_subfamily hlarge P R v rfl h hR V hVR

omit [Finite ι] [Finite κ] [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in

theorem coordinateFamily_window_reindex (n : ℕ) (q : Fin 2 → ℤ)
    (j : ι → Fin 2) (u : ι → CutRing × CutRing)
    (hs : ∀ i, q (j i) ≤ endpointLabel (if j i = 0 then (u i).1 else (u i).2))
    (he : ∀ i, endpointLabel (if j i = 0 then (u i).1 else (u i).2) < q (j i)+(n-1:ℕ)) :
    ∃ v : ι → Fin 2 × Fin (n-1),
      (∀ i, (coordinateWindowPrimitives n q (v i)).1 = coordinateTestIndex (j i)) ∧
      ∀ i, spatialTranslate (coordinateWindowPrimitives n q (v i)).2
          (initialTest a r (coordinateWindowPrimitives n q (v i)).1) =
        spatialTranslate (u i) (initialTest a r (coordinateTestIndex (j i))) := by
  let k (i : ι) := (endpointLabel (if j i = 0 then (u i).1 else (u i).2)-q (j i)).toNat
  have hk (i : ι) : (k i:ℤ) = endpointLabel (if j i = 0 then (u i).1 else (u i).2)-q (j i) :=
    Int.toNat_of_nonneg (by have hh := hs i; omega)
  have hk' (i : ι) : k i < n-1 := by have hh := he i; have hh' := hk i; omega
  refine ⟨fun i => (j i,⟨k i,hk' i⟩),fun _ => rfl,?_⟩
  intro i
  simp only [coordinateWindowPrimitives,initialTest_coordinate]
  apply coordinatePrimitive_translate_label_eq
  have hz : endpointLabel (((q (j i)+(k i:ℤ)):CutRing)*cutTau) =
      endpointLabel (if j i = 0 then (u i).1 else (u i).2) := by
    simp [endpointLabel,cutTau]
    have hh := hk i
    change (k i:ℤ) = (if j i = 0 then (u i).1 else (u i).2).im-q (j i) at hh
    omega
  by_cases hji : j i = 0 <;> simpa [coordinateShift,hji] using hz

omit [Finite ι] [Finite κ] [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem coordinateFamilyLaw_of_window (n : ℕ) (h : B.CoordinateWindowLaw n)
    (q : Fin 2 → ℤ) (j : ι → Fin 2) (u : ι → CutRing × CutRing)
    (hs : ∀ i, q (j i) ≤ endpointLabel (if j i = 0 then (u i).1 else (u i).2))
    (he : ∀ i, endpointLabel (if j i = 0 then (u i).1 else (u i).2) < q (j i)+(n-1:ℕ))
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) :
    B.PrimitiveFamilyLaw I b hb (fun i => (coordinateTestIndex (j i),u i)) := by
  obtain ⟨v,hj,hp⟩ := coordinateFamily_window_reindex (a := a) (r := r) n q j u hs he
  exact PrimitiveFamilyLaw.congr_offsets B I b hb
    (coordinateWindowPrimitives n q ∘ v) _ hj hp
    (PrimitiveFamilyLaw.reindex B I b hb _ (h I b hb q) v)

omit [Finite κ] in
theorem coordinateFamilySector_eq_window (hlarge : 15 < m+1)
    (n : ℕ) (h : B.CoordinateWindowLaw n) (q : Fin 2 → ℤ)
    (j : ι → Fin 2) (u : ι → CutRing × CutRing)
    (hs : ∀ i, q (j i) ≤ endpointLabel (if j i = 0 then (u i).1 else (u i).2))
    (he : ∀ i, endpointLabel (if j i = 0 then (u i).1 else (u i).2) < q (j i)+(n-1:ℕ))
    (g : ∀ I, I.card ≤ 15 → ∀ b hb,
      B.PrimitiveFamilyLaw I b hb (fun i => (coordinateTestIndex (j i),u i)))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (spatialTranslate (u i) (coordinatePrimitive a (j i))).val) V.val) :
    B.fullGeometricSector hlarge (fun i => (coordinateTestIndex (j i),u i)) g V =
      B.windowSector hlarge n h q V := by
  obtain ⟨v,hj,hp⟩ := coordinateFamily_window_reindex (a := a) (r := r) n q j u hs he
  apply B.fullGeometricSector_compare hlarge _ _ v hj hp _ g V
  simpa only [primitiveTests,primitiveFamilyTests,initialTest_coordinate] using hV

end InitialCoverSystem
end CoordinateFamilyCompare

end SimpleAmenable
end
end

end OAI
