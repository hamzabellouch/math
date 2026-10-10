import OAI.Combinatorics.HoneycombCorridor.PolygonNesting

namespace OAI

namespace PolynomialVacuumBridge.Corridor

noncomputable def facePointProduct (p q : FaceIndex →₀ ℤ) : FaceIndex →₀ ℤ :=
  Finsupp.zipWith (· * ·) (by simp) p q

@[simp] theorem facePointProduct_apply (p q : FaceIndex →₀ ℤ) (f : FaceIndex) :
    facePointProduct p q f = p f * q f := Finsupp.zipWith_apply

theorem finite_face_potential_injective (p q : FaceIndex →₀ ℤ)
    (he : ∀ g : Germ, p (leftFace g) - p (rightFace g) = q (leftFace g) - q (rightFace g)) :
    p = q := by
  have hrat : toRatFinsupp p = toRatFinsupp q := by
    apply finite_gradient_injective
    funext e
    change (p (leftFace (canonicalDart e)) : ℚ) - p (rightFace (canonicalDart e)) =
      (q (leftFace (canonicalDart e)) : ℚ) - q (rightFace (canonicalDart e))
    exact_mod_cast he (canonicalDart e)
  ext f
  have h := congrArg (fun s : FaceIndex →₀ ℚ => s f) hrat
  change (p f : ℚ) = (q f : ℚ) at h
  exact_mod_cast h

namespace Polygon

theorem germ_mem_vertices (P : Polygon) : P.germ.1 ∈ P.vertices := by
  have hp : P.Traverses P.germ P.turns := P.traversal
  rw [hp.vertices]
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil hp.1
  simp [hw,traced]

 

theorem level_constant_on_boundary (P Q : Polygon) (hdis : Disjoint P.vertices Q.vertices)
    (v : Vertex) (hv : v ∈ P.vertices) :
    vertexLevel Q.potential v = vertexLevel Q.potential P.germ.1 := by
  have hp : P.Traverses P.germ P.turns := P.traversal
  have hv' : v ∈ traced P.germ P.turns := by rw [hp.vertices] at hv; exact List.mem_toFinset.mp hv
  obtain ⟨u,b,w,hu,hv''⟩ := mem_traced_split P.germ P.turns v hv'
  have hpre : ∀ a ∈ traced P.germ u, a ∉ Q.vertices := by
    intro a ha
    apply Finset.disjoint_left.mp hdis
    rw [hp.vertices,hu,traced_append,List.mem_toFinset]
    exact List.mem_append_left _ ha
  have hvQ : v ∉ Q.vertices := Finset.disjoint_left.mp hdis hv
  have h := Q.trace_level P.germ u hpre (hv'' ▸ hvQ)
  rwa [hv''] at h

theorem potential_constant_on_boundary (P Q : Polygon) (hdis : Disjoint P.vertices Q.vertices)
    (v : Vertex) (hv : v ∈ P.vertices) (k : Fin 3) :
    Q.potential (leftFace (v,k)) = vertexLevel Q.potential P.germ.1 ∧
    Q.potential (rightFace (v,k)) = vertexLevel Q.potential P.germ.1 := by
  have h := Q.off_boundary_faces v (Finset.disjoint_left.mp hdis hv) k
  rw [P.level_constant_on_boundary Q hdis v hv] at h
  exact h

 

theorem disjoint_potential_product (P Q : Polygon) (hdis : Disjoint P.vertices Q.vertices) :
    facePointProduct P.potential Q.potential =
      vertexLevel Q.potential P.germ.1 • P.potential +
      vertexLevel P.potential Q.germ.1 • Q.potential := by
  apply finite_face_potential_injective
  intro g
  simp only [facePointProduct_apply,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  by_cases hp : g.1 ∈ P.vertices
  · have h := P.potential_constant_on_boundary Q hdis g.1 hp g.2
    change Q.potential (leftFace g) = _ ∧ Q.potential (rightFace g) = _ at h
    rw [h.1,h.2]
    ring
  · by_cases hq : g.1 ∈ Q.vertices
    · have h := Q.potential_constant_on_boundary P hdis.symm g.1 hq g.2
      change P.potential (leftFace g) = _ ∧ P.potential (rightFace g) = _ at h
      rw [h.1,h.2]
      ring
    · have h := P.off_boundary_faces g.1 hp g.2
      have h' := Q.off_boundary_faces g.1 hq g.2
      change P.potential (leftFace g) = _ ∧ P.potential (rightFace g) = _ at h
      change Q.potential (leftFace g) = _ ∧ Q.potential (rightFace g) = _ at h'
      rw [h.1,h.2,h'.1,h'.2]
      ring

 
theorem disjoint_common_face_nested (P Q : Polygon) (hdis : Disjoint P.vertices Q.vertices)
    (f : FaceIndex) (hPf : f ∈ P.interiorFaces) (hQf : f ∈ Q.interiorFaces) :
    P.vertices ⊆ Q.interior ∨ Q.vertices ⊆ P.interior := by
  have hp : P.potential f ≠ 0 := Finsupp.mem_support_iff.mp hPf
  have hq : Q.potential f ≠ 0 := Finsupp.mem_support_iff.mp hQf
  have h := congrArg (fun s : FaceIndex →₀ ℤ => s f) (P.disjoint_potential_product Q hdis)
  simp only [facePointProduct_apply,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] at h
  by_cases hc : vertexLevel Q.potential P.germ.1 = 0
  · have hd : vertexLevel P.potential Q.germ.1 ≠ 0 := by
      intro hd
      rw [hc,hd,zero_mul,zero_mul,zero_add] at h
      exact mul_ne_zero hp hq h
    right
    intro v hv
    rw [P.interior_iff_level]
    exact ⟨Finset.disjoint_left.mp hdis.symm hv,by rw [Q.level_constant_on_boundary P hdis.symm v hv]; exact hd⟩
  · left
    intro v hv
    rw [Q.interior_iff_level]
    exact ⟨Finset.disjoint_left.mp hdis hv,by rw [P.level_constant_on_boundary Q hdis v hv]; exact hc⟩

end Polygon
end PolynomialVacuumBridge.Corridor

end OAI
