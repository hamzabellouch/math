import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcVerticalWeight

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M H J : ℕ} [NeZero M]

theorem atPort_cross_disjoint (A B : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M)
    (hA : A.val.height≤H) (hB : B.val.height≤H) (p q : Bool × ZMod M)
    (hpq : p.1≠q.1) (hH : A.val.word.length+B.val.word.length≤H) :
    Disjoint (atPort A hA p).vertices (atPort B hB q).vertices := by
  apply Finset.disjoint_left.mpr
  intro v hvA hvB
  have ha:=traced_layer_bound (atPort A hA p).start (atPort A hA p).word v (List.mem_toFinset.mp hvA)
  have hb:=traced_layer_bound (atPort B hB q).start (atPort B hB q).word v (List.mem_toFinset.mp hvB)
  simp only [atPort_start,atPort_word] at ha hb
  rcases p with ⟨bp,i⟩
  rcases q with ⟨bq,j⟩
  cases bp <;> cases bq <;> simp_all [vertexLayer] <;> omega

omit [NeZero M] in
private theorem disjoint_image_iff [NeZero M] (D E : Finset (Vertex M)) (f : Vertex M → Vertex M)
    (hf : Function.Injective f) : Disjoint (D.image f) (E.image f) ↔ Disjoint D E := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro v hvD hvE
    exact Finset.disjoint_left.mp h (Finset.mem_image.mpr ⟨v,hvD,rfl⟩) (Finset.mem_image.mpr ⟨v,hvE,rfl⟩)
  · intro h
    apply Finset.disjoint_left.mpr
    intro v hvD hvE
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hvD
    obtain ⟨b,hb,hba⟩:=Finset.mem_image.mp hvE
    exact Finset.disjoint_left.mp h ha (hf hba ▸ hb)

theorem atPort_disjoint_stable (A B : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M)
    (hA : A.val.height≤H) (hB : B.val.height≤H) (jA : A.val.height≤J) (jB : B.val.height≤J)
    (p q : Bool × ZMod M)
    (hH : A.val.word.length+B.val.word.length≤H) (hJ : A.val.word.length+B.val.word.length≤J) :
    Disjoint (atPort A jA p).vertices (atPort B jB q).vertices ↔
      Disjoint (atPort A hA p).vertices (atPort B hB q).vertices := by
  by_cases hp : p.1=q.1
  · rw [atPort_vertices A hA jA p,atPort_vertices B hB jB q,hp]
    exact disjoint_image_iff _ _ _ (translate_injective _ _)
  · exact ⟨fun _ => atPort_cross_disjoint A B hA hB p q hp hH,
      fun _ => atPort_cross_disjoint A B jA jB p q hp hJ⟩
end PolynomialVacuumCylinder

end OAI
