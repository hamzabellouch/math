import OAI.Combinatorics.PolynomialVacuum.Cylinder.WeightFactor

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ} {D : Finset (Vertex M)}

namespace BoundaryArc
variable (A : BoundaryArc D)
theorem length_le : A.word.length≤D.card := by
  have hc := Finset.card_le_card A.vertices_subset
  change (traced A.start A.word).toFinset.card≤D.card at hc
  simpa only [List.toFinset_card_of_nodup A.distinct,traced_length] using hc

noncomputable def finiteCode : (D × Fin 3) × ((n : Fin (D.card+1)) × List.Vector Bool n.val) :=
  ((⟨A.start.1,A.startInside⟩,A.start.2),⟨⟨A.word.length,by have h:=A.length_le; omega⟩,⟨A.word,rfl⟩⟩)

theorem finiteCode_injective : Function.Injective (finiteCode (D:=D)) := by
  intro A B h
  have hs := congrArg (fun x : (D × Fin 3) × ((n : Fin (D.card+1)) × List.Vector Bool n.val) => (x.1.1.val,x.1.2)) h
  have hw := congrArg (fun x : (D × Fin 3) × ((n : Fin (D.card+1)) × List.Vector Bool n.val) => x.2.2.val) h
  exact A.ext_data B hs hw
end BoundaryArc
instance boundaryArc_finite : Finite (BoundaryArc D) := Finite.of_injective _ BoundaryArc.finiteCode_injective
noncomputable instance : Fintype (BoundaryArc D) := Fintype.ofFinite _

abbrev ArcSystem (D : Finset (Vertex M)) :=
  {S : Finset (BoundaryArc D) // (S : Set (BoundaryArc D)).Pairwise (fun A B => Disjoint A.vertices B.vertices)}
noncomputable def ArcSystem.vertices (S : ArcSystem D) : Finset (Vertex M) := S.val.biUnion BoundaryArc.vertices
noncomputable def ArcSystem.current (S : ArcSystem D) : Edge M →₀ ℤ := ∑A∈S.val,A.current
noncomputable def ArcSystem.weight (S : ArcSystem D) : ℂ := ∏A∈S.val,A.weight

end PolynomialVacuumCylinder

end OAI
