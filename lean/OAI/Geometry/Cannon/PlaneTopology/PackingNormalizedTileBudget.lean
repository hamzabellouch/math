import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.FaceHullCompact
import OAI.Geometry.Cannon.Modulus.LocalSubdisk

namespace OAI

section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding CannonTileTopology
open scoped OnePoint BigOperators

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)]

theorem packing_normalized_tile_budget [DecidableEq ι] [Nonempty ι]
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hsep : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → ρ u+ρ v≤dist (z u) (z v))
    (hcycles : ∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c))
    (out : Faces F)
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out)
    (pole : ℂ) (hpv : Vertex F pole)
    (N : OnePoint ℂ ≃ₜ OnePoint ℂ) (hN : N∈CannonMobius.biholomorphic) (hpole : N (z pole)=∞)
    (D : ℕ) (hdeg : ∀ v : ℂ,Nat.card {i : ι | v∈range (F i)}≤D) :
    let T : Faces F → Set ℂ:=fun d=>((↑) : ℂ → OnePoint ℂ) ⁻¹' (N '' sphereTile F z out d)
    ∃ c : Faces F → ℂ,∃ r : Faces F → ℝ,∃ s : Faces F → ℂ,
      (∀ d,s d∈faceVertices F d) ∧ (∀ d,0≤r d) ∧
      (∀ d,pole∉faceVertices F d → T d⊆closedBall (c d) (3*r d)) ∧
      (∀ p : ℂ,∀ R : ℝ,0≤R →
        (∑ d,if pole∉faceVertices F d ∧ (T d∩closedBall p R).Nonempty then (min (r d) R)^2 else 0)
          ≤(25*(D:ℝ)+1)*R^2) ∧
      (Finset.univ.filter (fun d=>¬pole∉faceVertices F d)).card≤D := by
  classical
  let ν:=GraphVertices F
  let _ : Fintype ν:=Fintype.ofFinite ν
  let V : Faces F → Finset ν:=fun d=>Finset.univ.filter (fun j=>j.val∈faceVertices F d)
  have hmem (d : Faces F) (j : ν) : j∈V d ↔ j.val∈faceVertices F d:=by simp [V]
  have hV (d : Faces F) : (V d).Nonempty := by
    obtain ⟨C,_⟩:=hcycles d
    have hC : C.a∈faceVertices F d:=by rw [C.vertices]; simp
    exact ⟨⟨C.a,((mem_faceVertices F d C.a).mp hC).1⟩,(hmem _ _).mpr hC⟩
  have hf (d : Faces F) : frontier (sphereTile F z out d)⊆
      ⋃ j∈V d,((↑) '' closedBall (z j.val) (ρ j.val) : Set (OnePoint ℂ)) := by
    intro x hx
    obtain ⟨j,hj,hxj⟩:=mem_iUnion₂.mp (sphereTile_frontier_disks z ρ hlen hcycles out d hx)
    exact mem_iUnion₂.mpr ⟨⟨j,((mem_faceVertices F d j).mp hj).1⟩,(hmem _ _).mpr hj,hxj⟩
  have hp (d : Faces F) (i : ν) (hi : i∈V d) (j : ν) (hj : j∈V d) (hij : i≠j) :
      dist (z i.val) (z j.val)=ρ i.val+ρ j.val := by
    obtain ⟨C,_⟩:=hcycles d
    obtain ⟨k,hk⟩:=C.pair_edge ((hmem _ _).mp hi) ((hmem _ _).mp hj) (Subtype.val_injective.ne hij)
    exact hk.developed_length z ρ (hlen k)
  have hpinc (d : Faces F) (hp : (z pole:OnePoint ℂ)∈sphereTile F z out d) : (⟨pole,hpv⟩ : ν)∈V d :=
    (hmem _ _).mpr (packing_center_tile_incidence hF Q hQ hK z ρ hρ hlen hsep hcycles out hI hfill hpv d hp)
  have hinc (j : ν) : (Finset.univ.filter (fun d : Faces F=>j∈V d)).card≤D := by
    simpa only [hmem] using face_incidence_card_le hF Q hQ hK D hdeg j.val
  obtain ⟨c,r,s,hs,hr,hcell,hbud,hbad⟩:=pole_chart_tile_budget V hV (⟨pole,hpv⟩ : ν)
    (sphereTile F z out) (sphereTile_closed z out)
    (sphereTile_interiors_disjoint z out hcycles hI hfill)
    (fun j=>z j.val) (fun j=>ρ j.val) (fun j=>hρ j.val)
    (fun i j hij=>hsep i.val i.property j.val j.property (Subtype.val_injective.ne hij))
    hf hp hpinc N hN hpole D hinc
  refine ⟨c,r,(fun d=>(s d).val),(fun d=>(hmem _ _).mp (hs d)),hr,?_,?_,?_⟩
  · simpa only [hmem] using hcell
  · simpa only [hmem] using hbud
  · simpa only [hmem] using hbad
end CannonEmbeddedArc.Arc

end
end

end OAI
