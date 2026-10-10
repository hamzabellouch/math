import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TupleChartDomain

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonFullGroup
attribute [local instance] Classical.propDecidable

private noncomputable def trackTranslationChart {a m : ℕ}
    (d : Fin m → CutRing × CutRing) (i : Fin m) : TableChart a m :=
  ⟨i,i,d i,⟨Set.univ,BooleanSubalgebra.top_mem⟩⟩

theorem trackTranslation_hasTable {a m : ℕ} (d : Fin m → CutRing × CutRing) :
    HasTranslationTable (trackTranslationPerm (a := a) d) := by
  classical
  refine ⟨Finset.univ.image (trackTranslationChart d), ?_, ?_⟩
  · intro c hc
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
    intro x _
    rfl
  · intro p
    exact ⟨trackTranslationChart d p.1,
      Finset.mem_image.mpr ⟨p.1,Finset.mem_univ _,rfl⟩,rfl,Set.mem_univ _⟩

noncomputable def trackTranslation {a m : ℕ} (d : Fin m → CutRing × CutRing) :
    polygonFullGroup a m := ⟨trackTranslationPerm d,trackTranslation_hasTable d⟩

@[simp] theorem trackTranslation_apply {a m : ℕ} (d : Fin m → CutRing × CutRing)
    (p : TrackPoint a m) :
    (trackTranslation d).val p = (p.1,translate a (d p.1) p.2) := rfl

@[simp] theorem trackTranslation_zero {a m : ℕ} :
    trackTranslation (a := a) (m := m) 0 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  simp

@[simp] theorem trackTranslation_add {a m : ℕ} (d e : Fin m → CutRing × CutRing) :
    trackTranslation (a := a) (d+e) = trackTranslation d * trackTranslation e := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change (p.1,translate a (d p.1 + e p.1) p.2) =
    (p.1,translate a (d p.1) (translate a (e p.1) p.2))
  rw [translate_add]

@[simp] theorem trackTranslation_neg {a m : ℕ} (d : Fin m → CutRing × CutRing) :
    trackTranslation (a := a) (-d) = (trackTranslation d)⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rfl

@[simp] theorem trackTranslation_sub {a m : ℕ} (d e : Fin m → CutRing × CutRing) :
    trackTranslation (a := a) (d-e) = trackTranslation d * (trackTranslation e)⁻¹ := by
  rw [sub_eq_add_neg,trackTranslation_add,trackTranslation_neg]

noncomputable def wholePolygon (a : ℕ) : polygonAlgebra a :=
  ⟨Set.univ,BooleanSubalgebra.top_mem⟩

theorem constant_conjugate_translation {a m : ℕ} (ρ : Equiv.Perm (Fin m))
    (d : Fin m → CutRing × CutRing) :
    conditionalHom (wholePolygon a) ρ * trackTranslation d *
        (conditionalHom (wholePolygon a) ρ)⁻¹ =
      trackTranslation (fun i => d (ρ.symm i)) := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm (wholePolygon a) ρ
    (trackTranslationPerm d ((conditionalPerm (wholePolygon a) ρ).symm p)) = _
  simp [conditionalPerm,wholePolygon,trackTranslationPerm,trackTranslation]

theorem constant_conjugate_point_translation {a m : ℕ} (ρ : Equiv.Perm (Fin m))
    (i : Fin m) (v : CutRing × CutRing) :
    conditionalHom (wholePolygon a) ρ * trackTranslation (Pi.single i v) *
        (conditionalHom (wholePolygon a) ρ)⁻¹ =
      trackTranslation (Pi.single (ρ i) v) := by
  rw [constant_conjugate_translation]
  congr 1
  funext j
  simp only [Pi.single_apply]
  congr 1
  exact propext (Equiv.symm_apply_eq ρ)

theorem trackTranslation_difference_mem {a m : ℕ} (hm : 3 ≤ m)
    (i j : Fin m) (v : CutRing × CutRing) :
    trackTranslation (a := a) (Pi.single j v - Pi.single i v) ∈ polygonAlternatingGroup a m := by
  classical
  by_cases hij : i = j
  · subst j
    simp
  obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  let ι : Fin 3 ↪ Fin m := ⟨![i,j,k], by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp_all⟩
  let c := conditionalHom (wholePolygon a) (trackCycle ι)
  let t := trackTranslation (a := a) (Pi.single i v)
  have hc : c ∈ polygonAlternatingGroup a m := conditional_cycle_mem _ _
  have hnormal := polygonAlternatingGroup_normal a m
  have ht : c * t * c⁻¹ * t⁻¹ ∈ polygonAlternatingGroup a m := by
    have hconj := hnormal.conj_mem c⁻¹ ((polygonAlternatingGroup a m).inv_mem hc) t
    simpa only [mul_assoc] using (polygonAlternatingGroup a m).mul_mem hc hconj
  have he : (trackCycle ι) i = j := trackCycle_apply ι 0
  have heq : c * t * c⁻¹ = trackTranslation (a := a) (Pi.single j v) := by
    change conditionalHom (wholePolygon a) (trackCycle ι) * trackTranslation (Pi.single i v) *
      (conditionalHom (wholePolygon a) (trackCycle ι))⁻¹ = _
    rw [constant_conjugate_point_translation,he]
  rw [heq] at ht
  simpa only [trackTranslation_sub,t] using ht

noncomputable def coordinatePrimitive (a : ℕ) (j : Fin 2) : polygonAlgebra a :=
  ⟨halfPlane a (Fin.castLE (by omega) j) (cutTau-1) ∩
      (halfPlane a (Fin.castLE (by omega) j) 0)ᶜ,
    BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem
      (halfPlane_mem _ _ _))⟩

noncomputable def circularBoxPiece (a : ℕ) (r : CutRing) (k : Fin 2 × Fin 2) :
    polygonAlgebra a :=
  ⟨(halfPlane a 0 (r + (k.1.val : CutRing)) ∩
      (halfPlane a 0 (-r + (k.1.val : CutRing)))ᶜ) ∩
    (halfPlane a 1 (r + (k.2.val : CutRing)) ∩
      (halfPlane a 1 (-r + (k.2.val : CutRing)))ᶜ), by
    apply BooleanSubalgebra.inf_mem <;> apply BooleanSubalgebra.inf_mem
    · exact halfPlane_mem _ _ _
    · exact BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)
    · exact halfPlane_mem _ _ _
    · exact BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)⟩

noncomputable def clippedSlopePrimitive (a : ℕ) (r : CutRing) (j : Fin 4) :
    polygonAlgebra a :=
  ⟨⋃ k : Fin 2 × Fin 2, (circularBoxPiece a r k).val ∩
      (halfPlane a j (integralCutForm a j (k.1.val,k.2.val)))ᶜ, by
    apply BooleanSubalgebra.iSup_mem
    intro k
    exact BooleanSubalgebra.inf_mem (circularBoxPiece a r k).property
      (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _))⟩

noncomputable def initialTest (a : ℕ) (r : CutRing) : Fin 5 → polygonAlgebra a :=
  ![wholePolygon a,coordinatePrimitive a 0,coordinatePrimitive a 1,
    clippedSlopePrimitive a r 2,clippedSlopePrimitive a r 3]

def SourceGeneratorLabel (m : ℕ) :=
  (Fin 5 × {σ : Equiv.Perm (Fin (m+1)) //
    σ ∈ alternatingGroup (Fin (m+1)) ∧ σ.support.card ≤ 5}) ⊕ (Fin m × Fin 2)

instance (m : ℕ) : Finite (SourceGeneratorLabel m) := by
  unfold SourceGeneratorLabel
  infer_instance

noncomputable def sourceGenerator (a : ℕ) (r : CutRing) (m : ℕ) :
    SourceGeneratorLabel m → polygonFullGroup a (m+1)
  | Sum.inl (j,σ) => conditionalHom (initialTest a r j) σ.val
  | Sum.inr (i,j) => trackTranslation
      (Pi.single i.castSucc (if j = 0 then (cutTau,0) else (0,cutTau)) -
       Pi.single (Fin.last m) (if j = 0 then (cutTau,0) else (0,cutTau)))

theorem sourceGenerator_mem (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (s : SourceGeneratorLabel m) : sourceGenerator a r m s ∈ polygonAlternatingGroup a (m+1) := by
  cases s with
  | inl s => exact conditionalHom_alternating_mem _ s.2.property.1
  | inr s => exact trackTranslation_difference_mem (by omega) _ _ _

noncomputable def alternatingGenerator (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) :
    SourceGeneratorLabel m → polygonAlternatingGroup a (m+1) :=
  fun s => ⟨sourceGenerator a r m s,sourceGenerator_mem a r m hm s⟩

end PolygonFullGroup

end SimpleAmenable
end
end

end OAI
