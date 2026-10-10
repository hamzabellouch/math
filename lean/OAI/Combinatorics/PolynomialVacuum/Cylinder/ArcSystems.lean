import OAI.Combinatorics.PolynomialVacuum.Cylinder.FiniteArcs

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ} {D : Finset (Vertex M)}
namespace ArcSystem
variable (S : ArcSystem D)

theorem vertices_subset : S.vertices⊆D := by
  intro v hv
  obtain ⟨A,hA,hv⟩:=Finset.mem_biUnion.mp hv
  exact A.vertices_subset hv

theorem on_member (A : BoundaryArc D) (hA : A∈S.val) (v : Vertex M) (hv : v∈A.vertices) (k : Fin 3) :
    orientedFlow S.current (v,k)=orientedFlow A.current (v,k) := by
  simp only [current,map_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_single A
  · intro B hB hBA
    apply B.current_zero v (A.vertices_subset hv)
    intro hvB
    exact Finset.disjoint_left.mp (S.property hA hB hBA.symm) hv hvB
  · exact fun h => (h hA).elim

theorem current_zero (v : Vertex M) (hv : v∈D) (hn : v∉S.vertices) (k : Fin 3) :
    orientedFlow S.current (v,k)=0 := by
  simp only [current,map_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro A hA
  apply A.current_zero v hv
  intro hp
  exact hn (Finset.mem_biUnion.mpr ⟨A,hA,hp⟩)

theorem domain_active : D∩activeSites S.current=S.vertices := by
  ext v
  rw [Finset.mem_inter]
  constructor
  · rintro ⟨hv,hq⟩
    by_contra hn
    obtain ⟨k,hk⟩:=(mem_activeSites S.current v).mp hq
    exact hk (S.current_zero v hv hn k)
  · intro hv
    obtain ⟨A,hA,hvA⟩:=Finset.mem_biUnion.mp hv
    have hh : v∈activeSites A.current := contour_active _ _ _ A.contour v (List.mem_toFinset.mp hvA)
    obtain ⟨k,hk⟩:=(mem_activeSites A.current v).mp hh
    refine ⟨S.vertices_subset hv,(mem_activeSites S.current v).mpr ⟨k,?_⟩⟩
    simpa only [S.on_member A hA v hvA k] using hk

theorem local_ice (v : Vertex M) (hv : v∈D) : LocalIce S.current v := by
  by_cases ha : v∈S.vertices
  · obtain ⟨A,hA,hvA⟩:=Finset.mem_biUnion.mp ha
    have hi:=A.local_ice v hv
    simpa only [LocalIce,S.on_member A hA v hvA] using hi
  · exact Or.inl (S.current_zero v hv ha)

theorem supported : SupportedAt D S.current := by
  intro g hg hr
  simp only [current,map_sum,Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun A _ => A.supported g hg hr)

theorem domain_weight : domainWeight D S.current=S.weight := by
  suffices ∀(E : Finset (BoundaryArc D)) (hE : (E : Set (BoundaryArc D)).Pairwise
      (fun A B => Disjoint A.vertices B.vertices)),
      domainWeight D (ArcSystem.current ⟨E,hE⟩)=∏A∈E,A.weight from this S.val S.property
  intro E
  induction E using Finset.induction_on with
  | empty => intro hE; simp [current,domainWeight,localCurrentWeight,
      PolynomialVacuumAlgebra.arrowVertexWeight,PolynomialVacuumAlgebra.IceTriple,
      PolynomialVacuumAlgebra.arrowTriple,PolynomialVacuumAlgebra.vertexOccupation,
      cubicTurn,columnTotal,column,zeta_eq_I]
  | @insert A E hA ih =>
    intro hE
    let R : ArcSystem D:=⟨E,hE.mono (by simp)⟩
    have hd : Disjoint A.vertices R.vertices := by
      apply Finset.disjoint_left.mpr
      intro v hvA hvR
      obtain ⟨B,hB,hvB⟩:=Finset.mem_biUnion.mp hvR
      change B∈E at hB
      have hAB : A≠B := by intro he; subst B; exact hA hB
      exact Finset.disjoint_left.mp (hE (by simp) (Finset.mem_insert_of_mem hB) hAB) hvA hvB
    have he : ArcSystem.current ⟨insert A E,hE⟩=A.current+R.current := by simp [current,R,hA]
    rw [he,domainWeight_add D A.current R.current (by rw [A.domain_active,R.domain_active]; exact hd),
      A.domain_weight,ih R.property,Finset.prod_insert hA]
end ArcSystem
end PolynomialVacuumCylinder

end OAI
