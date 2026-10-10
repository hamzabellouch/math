import Mathlib
import OAI.Geometry.Cannon.CirclePacking.StrictCutsGiveAngles
import OAI.Geometry.Cannon.PlanarGraphs.TriangularCounts
import OAI.Geometry.Cannon.PlaneTopology.MetricStarFlat
import OAI.Geometry.Cannon.CirclePacking.Demand

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem triangular_graph_radii (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (htri : ∀ d : Faces F,∃ i j k : ι,i≠j ∧ j≠k ∧ k≠i ∧
      closure (face F d)=face F d∪(range (F i)∪range (F j)∪range (F k)))
    (out : Faces F) :
    let _ : Finite (Faces F) := faces_finite F hF Q hQ
    let _ := Fintype.ofFinite (Faces F)
    let _ := Classical.decEq (Faces F)
    let V := vertices F Finset.univ
    let A := {d : Faces F // d≠out}
    ∃ vertex : A × Fin 3 → V,
      (∀ f,Function.Injective (fun k=>vertex (f,k))) ∧
      (∀ f,range (fun k=>(vertex (f,k)).val)=(faceVertices F f.val : Set ℂ)) ∧
      ∃ θ : A × Fin 3 → ℝ, ∃ r : V → ℝ,∃ q : A → ℝ,
        (∀ i,θ i∈Ioo (0:ℝ) Real.pi) ∧
        (∀ f,∑ k:Fin 3,θ (f,k)=Real.pi) ∧
        (∀ v,(∑ i : A×Fin 3,if vertex i=v then θ i else 0)=
          if v.val∈faceVertices F out then Real.pi/3 else 2*Real.pi) ∧
        (∀ v,0<r v) ∧ (∀ f,0<q f) ∧
        ∀ i,Real.tan (θ i/2)=q i.1/r (vertex i) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ := Fintype.ofFinite (Faces F)
  dsimp only
  let V := vertices F Finset.univ
  let A := {d : Faces F // d≠out}
  let corners : Faces F → Finset V := fun d=>Finset.univ.filter (fun v=>v.val∈faceVertices F d)
  have himage (d : Faces F) : (corners d).image (fun v:V=>v.val)=faceVertices F d := by
    ext z
    simp only [Finset.mem_image,corners,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hz
      have hv : z∈V := by
        obtain ⟨i,hi⟩ := ((mem_faceVertices F d z).mp hz).1
        exact (mem_vertices F Finset.univ z).mpr ⟨i,Finset.mem_univ _,hi⟩
      exact ⟨⟨z,hv⟩,hz,rfl⟩
  obtain ⟨hcorner,hEuler,_⟩ := CannonPlanarEuler.triangular_counts F hF Q hQ hK htri
  have hthree (d : Faces F) : (corners d).card=3 := by
    rw [←hcorner d,←himage d,Finset.card_image_of_injective _ Subtype.val_injective]
  have hregion (d : Faces F) : 3≤Nat.card (regionEdges F ConnectedComponents.mk d) := by
    rw [←noncut_facial_vertices_edges F hF Q hQ hK d,hcorner d]
  have hbounds (T : Finset V) (hT : T≠Finset.univ) (hB : ∃ d,corners d⊆T) :
      (Finset.univ.filter fun d=>corners d⊆T).card+5≤2*T.card := by
    let U := T.image (fun v:V=>v.val)
    have heq (d : Faces F) : corners d⊆T ↔ faceVertices F d⊆U := by
      rw [←himage d]
      exact (Finset.image_subset_image_iff Subtype.val_injective).symm
    have hproper : ¬vertices F Finset.univ⊆U := by
      intro hh
      apply hT
      apply Finset.eq_univ_of_forall
      intro v
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (hh v.property)
      have : w=v := Subtype.ext he
      exact this ▸ hw
    have hb : ∃ d,faceVertices F d⊆U := by
      obtain ⟨d,hd⟩ := hB
      exact ⟨d,(heq d).mp hd⟩
    have hp := proper_facial_bound F hF Q hQ hregion U hproper hb
    have hn : Nat.card {d : Faces F | faceVertices F d⊆U}=
        (Finset.univ.filter fun d=>corners d⊆T).card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_of_subtype _ (fun d=>by simp only [Finset.mem_filter,Finset.mem_univ,true_and,heq,Set.mem_ofPred_eq])
    rw [hn,Finset.card_image_of_injective _ Subtype.val_injective] at hp
    exact hp
  have hE : Fintype.card (Faces F)+4=2*Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hEuler
  obtain ⟨htotal,hcut⟩ := CannonTriangleCuts.disk_demands corners out (hthree out) hE hbounds
  let en (d : Faces F) : Fin 3 ≃ corners d := (Finset.equivFinOfCardEq (hthree d)).symm
  let vertex : A×Fin 3 → V := fun i=>(en i.1.val i.2).val
  have hinj (f:A) : Function.Injective (fun k=>vertex (f,k)) :=
    Subtype.val_injective.comp (en f.val).injective
  have hmem (f:A) (v:V) : (∃ k,vertex (f,k)=v) ↔ v.val∈faceVertices F f.val := by
    constructor
    · rintro ⟨k,rfl⟩
      exact (Finset.mem_filter.mp (en f.val k).property).2
    · intro hv
      have hh : v∈corners f.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
      obtain ⟨k,hk⟩ := (en f.val).surjective ⟨v,hh⟩
      exact ⟨k,congrArg Subtype.val hk⟩
  have hcut' (S : Finset V) (hs:S.Nonempty) (hsp:S≠Finset.univ) :
      (∑ v∈S,CannonTriangleCuts.demand (corners out) v)<
      3*(CannonPackingGeometry.neighborFaces (fun v f=>∃ k,vertex (f,k)=v) S).card := by
    convert hcut S hs hsp using 2
    congr 1
    ext f
    simp only [CannonPackingGeometry.neighborFaces,Finset.mem_filter,Finset.mem_univ,true_and,hmem,corners]
  obtain ⟨θ,r,q,hθ,hθf,hθv,hr,hq,htan⟩ := CannonPackingGeometry.strict_cuts_give_radii
    vertex hinj (CannonTriangleCuts.demand (corners out))
    (CannonTriangleCuts.demand_pos _) hcut' htotal
  refine ⟨vertex,hinj,?_,θ,r,q,hθ,hθf,?_,hr,hq,htan⟩
  · intro f
    ext z
    constructor
    · rintro ⟨k,rfl⟩
      exact (hmem f _).mp ⟨k,rfl⟩
    · intro hz
      have hv : z∈V := by
        obtain ⟨i,hi⟩ := ((mem_faceVertices F f.val z).mp hz).1
        exact (mem_vertices F Finset.univ z).mpr ⟨i,Finset.mem_univ _,hi⟩
      obtain ⟨k,hk⟩ := (hmem f ⟨z,hv⟩).mpr hz
      exact ⟨k,congrArg Subtype.val hk⟩
  · intro v
    rw [hθv]
    simp only [CannonTriangleCuts.demand,corners,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> norm_num
    ring
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HasIntrinsicCircleData (F : ι → Arc ℂ) [Fintype (Faces F)] (out : Faces F) : Prop := by
  classical
  exact
   let V := vertices F Finset.univ
   let A := {d : Faces F // d≠out}
   ∃ vertex : A×Fin 3 → V,
    (∀ f,Function.Injective (fun k=>vertex (f,k))) ∧
    (∀ f,range (fun k=>(vertex (f,k)).val)=(faceVertices F f.val : Set ℂ)) ∧
    ∃ θ : A×Fin 3 → ℝ,∃ r : V → ℝ,∃ q : A → ℝ,
      (∀ i,θ i∈Ioo (0:ℝ) Real.pi) ∧
      (∀ f,∑ k:Fin 3,θ (f,k)=Real.pi) ∧
      (∀ v,(∑ i : A×Fin 3,if vertex i=v then θ i else 0)=
        if v.val∈faceVertices F out then Real.pi/3 else 2*Real.pi) ∧
      (∀ v,0<r v) ∧ (∀ f,0<q f) ∧
      ∀ i,Real.tan (θ i/2)=q i.1/r (vertex i)
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
