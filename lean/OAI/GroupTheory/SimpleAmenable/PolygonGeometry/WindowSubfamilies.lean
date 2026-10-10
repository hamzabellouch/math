import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowIntervals

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WindowSubfamilies

def coordinateWindowEmbedding (n k : ℕ) (q p : Fin 2 → ℤ)
    (hstart : ∀ j, q j ≤ p j) (hend : ∀ j, p j+(k:ℤ) ≤ q j+n) :
    Fin 2 × Fin (k-1) → Fin 2 × Fin (n-1) := fun i =>
  (i.1,⟨(p i.1-q i.1).toNat+i.2.val,by
    have hi := i.2.isLt
    have he : ((p i.1-q i.1).toNat:ℤ) = p i.1-q i.1 := Int.toNat_of_nonneg (by linarith [hstart i.1])
    have hn := hend i.1
    omega⟩)

theorem coordinateWindowEmbedding_spec (n k : ℕ) (q p : Fin 2 → ℤ)
    (hs : ∀ j, q j ≤ p j) (he : ∀ j, p j+(k:ℤ) ≤ q j+n) :
    coordinateWindowPrimitives n q ∘ coordinateWindowEmbedding n k q p hs he =
      coordinateWindowPrimitives k p := by
  funext i
  apply Prod.ext
  · rfl
  · change coordinateShift i.1 (((q i.1+(((p i.1-q i.1).toNat+i.2.val:ℕ):ℤ)):CutRing)*cutTau) = _
    have ht : ((p i.1-q i.1).toNat:ℤ) = p i.1-q i.1 := Int.toNat_of_nonneg (by linarith [hs i.1])
    simp only [Nat.cast_add,ht]
    congr 2
    push_cast
    ring

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem geometricSector_subfamily {ι κ : Type*} [Finite ι] [Finite κ]
    (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (v : κ → ι) (hv : P ∘ v = Q)
    (h : B.PrimitiveFamilyLaw I b hb P) (g : B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val) :
    B.geometricSector I b hb Q g V = B.geometricSector I b hb P h V := by
  subst Q
  exact B.geometricSector_reindex I b hb P v h g V hV

theorem geometricSector_window_inclusion
    (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (n k : ℕ) (q p : Fin 2 → ℤ)
    (hs : ∀ j, q j ≤ p j) (he : ∀ j, p j+(k:ℤ) ≤ q j+n)
    (h : B.PrimitiveFamilyLaw I b hb (coordinateWindowPrimitives n q))
    (g : B.PrimitiveFamilyLaw I b hb (coordinateWindowPrimitives k p))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives k p) i).val) V.val) :
    B.geometricSector I b hb (coordinateWindowPrimitives k p) g V =
      B.geometricSector I b hb (coordinateWindowPrimitives n q) h V :=
  B.geometricSector_subfamily I b hb _ _ (coordinateWindowEmbedding n k q p hs he)
    (coordinateWindowEmbedding_spec n k q p hs he) h g V hV

end InitialCoverSystem
end WindowSubfamilies

section CircularIntervals

theorem coordinateArc_mem (a : ℕ) (j : Fin 2) (z : CutRing) :
    coordinateArc a j z ∈ polygonAlgebra a := by
  have he : coordinateArc a j z = halfPlane a (Fin.castLE (by omega) j)
      (z-(⌊ordinary z⌋:ℤ)) := by
    ext p
    have hc : cutForm a (Fin.castLE (by omega) j) p.val = coordinate j p := by
      fin_cases j <;> rfl
    simp only [coordinateArc,halfPlane,Set.mem_ofPred_eq,hc,map_sub,map_intCast]
    rfl
  rw [he]
  exact halfPlane_mem _ _ _

theorem coordinateBetween_mem (a : ℕ) (j : Fin 2) (u v : CutRing) :
    coordinateBetween a j u v ∈ polygonAlgebra a :=
  polygon_preimage_translate (-coordinateShift j u) (coordinateArc_mem a j (v-u))

noncomputable def coordinateInterval (a : ℕ) (j : Fin 2) (u v : CutRing) : polygonAlgebra a :=
  ⟨coordinateBetween a j u v,coordinateBetween_mem a j u v⟩

theorem mem_coordinateBetween_iff {a : ℕ} (j : Fin 2) (u v : CutRing)
    (h₀ : ordinary u ≤ ordinary v) (h₁ : ordinary v-ordinary u < 1)
    (p : GenericSquare a) :
    p ∈ coordinateBetween a j u v ↔
      ∃ k : ℤ, ordinary u ≤ coordinate j p+(k:ℝ) ∧ coordinate j p+(k:ℝ) < ordinary v := by
  change coordinate j (translate a (-coordinateShift j u) p) < Int.fract (ordinary (v-u)) ↔ _
  rw [← coordinateShift_neg,coordinate_translate,map_neg,map_sub,
    Int.fract_eq_self.mpr ⟨sub_nonneg.mpr h₀,h₁⟩]
  change Int.fract (coordinate j p-ordinary u) < ordinary v-ordinary u ↔ _
  constructor
  · intro h
    refine ⟨-⌊coordinate j p-ordinary u⌋,?_,?_⟩
    · have hn := Int.fract_nonneg (coordinate j p-ordinary u)
      simp only [Int.fract,Int.cast_neg] at *
      linarith
    · simp only [Int.fract,Int.cast_neg] at *
      linarith
  · rintro ⟨k,hk₀,hk₁⟩
    have he : Int.fract (coordinate j p-ordinary u+(k:ℝ)) =
        coordinate j p-ordinary u+(k:ℝ) :=
      Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩
    rw [Int.fract_add_intCast] at he
    rw [he]
    linarith

theorem coordinateInterval_mono {a : ℕ} (j : Fin 2) (u v u' v' : CutRing)
    (hu : ordinary u' ≤ ordinary u) (huv : ordinary u ≤ ordinary v)
    (hv : ordinary v ≤ ordinary v') (hlen : ordinary v'-ordinary u' < 1) :
    coordinateInterval a j u v ≤ coordinateInterval a j u' v' := by
  intro p hp
  obtain ⟨k,hk⟩ := (mem_coordinateBetween_iff j u v huv (by linarith) p).mp hp
  exact (mem_coordinateBetween_iff j u' v' (by linarith) hlen p).mpr
    ⟨k,hu.trans hk.1,hk.2.trans_le hv⟩

theorem coordinateInterval_disjoint {a : ℕ} (j : Fin 2) (u v w z : CutRing)
    (huv : ordinary u ≤ ordinary v) (hvw : ordinary v ≤ ordinary w)
    (hwz : ordinary w ≤ ordinary z) (hlen : ordinary z-ordinary u < 1) :
    Disjoint (coordinateInterval a j u v).val (coordinateInterval a j w z).val := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  obtain ⟨k,hk₀,hk₁⟩ := (mem_coordinateBetween_iff j u v huv (by linarith) p).mp hp
  obtain ⟨l,hl₀,hl₁⟩ := (mem_coordinateBetween_iff j w z hwz (by linarith) p).mp hq
  have hk : (k:ℝ)-(l:ℝ) < 1 := by linarith
  have hl : (l:ℝ)-(k:ℝ) < 1 := by linarith
  have hk' : k-l < (1:ℤ) := by exact_mod_cast hk
  have hl' : l-k < (1:ℤ) := by exact_mod_cast hl
  have he : k = l := by omega
  subst l
  linarith

theorem coordinateInterval_window {a : ℕ} {r : CutRing}
    (n : ℕ) (q : Fin 2 → ℤ) (j : Fin 2) (u v : CutRing)
    (hu : q j ≤ endpointLabel u ∧ endpointLabel u < q j+n)
    (hv : q j ≤ endpointLabel v ∧ endpointLabel v < q j+n) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (coordinateInterval a j u v).val :=
  coordinateLabelWindow_resolved n q j u v hu hv

end CircularIntervals

end SimpleAmenable
end
end

end OAI
