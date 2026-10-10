import OAI.Combinatorics.PolynomialVacuum.Cylinder.SystemUniqueness

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

theorem signed_current_edge_injective (P : Polygon M) (e : Edge M) (he : e∈P.val) :
    Function.Injective (fun o : Bool => signedPolygonCurrent P o e) := by
  have hn : polygonCurrent P e≠0 := by
    apply Finsupp.mem_support_iff.mp
    rw [polygonCurrent_support]
    exact he
  intro a b hab
  cases a <;> cases b <;> simp only [signedPolygonCurrent,Bool.false_eq_true,ite_false,ite_true,Finsupp.neg_apply] at hab ⊢
  all_goals omega

theorem systemCurrent_injective_on (S : Finset (Polygon M)) (o p : Polygon M → Bool)
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices))
    (he : systemCurrent S o=systemCurrent S p) : ∀ P∈S,o P=p P := by
  intro P hP
  obtain ⟨e,heP⟩:=polygon_edges_nonempty P
  apply signed_current_edge_injective P e heP
  have hv : upEnd e∈P.vertices := edge_vertices_subset_polygon P e heP (by simp [edgeVertices,upEnd])
  have ho:=systemCurrent_at S o hS P hP (upEnd e) hv e.2
  have hp:=systemCurrent_at S p hS P hP (upEnd e) hv e.2
  rw [he,hp] at ho
  simpa only [upEnd,orientedFlow_up] using ho.symm

abbrev DisjointSystem (M : ℕ) := {S : Finset (Polygon M) //
  (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices)}
abbrev OrientedSystem (M : ℕ) := (S : DisjointSystem M) × ({P // P∈S.val} → Bool)
abbrev LegalFlow (M : ℕ) := {q : Edge M →₀ ℤ // ∀ v,LocalIce q v}

noncomputable def extendedOrientation (S : DisjointSystem M) (o : {P // P∈S.val} → Bool) : Polygon M → Bool :=
  fun P => if h : P∈S.val then o ⟨P,h⟩ else false

noncomputable def orientedSystemFlow (A : OrientedSystem M) : LegalFlow M :=
  ⟨systemCurrent A.1.val (extendedOrientation A.1 A.2),systemCurrent_localIce _ _ A.1.property⟩

theorem orientedSystemFlow_injective : Function.Injective (orientedSystemFlow (M:=M)) := by
  rintro ⟨S,o⟩ ⟨T,p⟩ he
  have hf:=congrArg Subtype.val he
  change systemCurrent S.val (extendedOrientation S o)=systemCurrent T.val (extendedOrientation T p) at hf
  have hs:=congrArg Finsupp.support hf
  rw [systemCurrent_support _ _ S.property,systemCurrent_support _ _ T.property] at hs
  have hST : S=T := Subtype.ext (polygon_system_eq_of_edge_union _ _ S.property T.property hs)
  subst T
  have hop : o=p := by
    funext P
    have hh:=systemCurrent_injective_on _ _ _ S.property hf P.val P.property
    simpa [extendedOrientation,P.property] using hh
  subst p
  rfl

theorem orientedSystemFlow_surjective : Function.Surjective (orientedSystemFlow (M:=M)) := by
  intro q
  let C:=IceNetwork.network q.val q.property
  obtain ⟨o,ho⟩:=ice_current_orientation_decomposition q.val q.property
  let S : DisjointSystem M:=⟨C.polygons,C.polygons_disjoint⟩
  let p : {P // P∈S.val} → Bool:=fun P => o P.val
  refine ⟨⟨S,p⟩,Subtype.ext ?_⟩
  change systemCurrent C.polygons (extendedOrientation S p)=q.val
  rw [ho]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [extendedOrientation,show P∈S.val from hP,dite_eq_left,p]

 

noncomputable def orientedSystemEquiv : OrientedSystem M ≃ LegalFlow M :=
  Equiv.ofBijective orientedSystemFlow ⟨orientedSystemFlow_injective,orientedSystemFlow_surjective⟩

end PolynomialVacuumCylinder

end OAI
