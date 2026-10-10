import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice23
import OAI.Combinatorics.SumProduct.Alignment.WordPlan04
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
end
 
end

section
 

 

noncomputable section
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces CubeLocalHaar MalcevCharacters
open ConstructedWordPlan.GlobalWordPlan
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {F : Factorization c Γ s K P L} {r : Fin F.period} (C : F.ResidueCover r)

def pointEvaluation (_C : F.ResidueCover r) : CubeGroup (ι:=Empty) (F:=F) →* F.state.domain.Carrier where
  toFun g:=g.val ∅
  map_one':=rfl
  map_mul' _ _:=rfl
omit [IsTopologicalGroup G] in
lemma pointEvaluation_continuous : Continuous (C.pointEvaluation):=
  (continuous_apply ∅).comp continuous_subtype_val

lemma pointEvaluation_rational (g : CubeGroup (ι:=Empty) (F:=F))
    (hg : IsRational C.pivotChart.chart g) : IsRational C.chart (C.pointEvaluation g) := by
  apply rationalHom_of_lattice C.chart C.pivotChart.chart C.pivotChart.secondKind
    C.pointEvaluation C.pointEvaluation_continuous C.pointLattice C.pivotChart.integer_lattice
    (fun h hh=>?_) g hg
  have he : h.val ∅∈C.lattice:=hh ∅
  intro i
  obtain ⟨z,hz⟩:=(C.integer_lattice _).mp he i
  exact ⟨(z:ℚ),by simpa only [Rat.cast_intCast,pointEvaluation,MonoidHom.coe_mk,OneHom.coe_mk] using hz.symm⟩

def pivotProjection : CubeGroup (ι:=Empty) (F:=F) →* G:=
  F.state.domain.embed.comp C.pointEvaluation
omit [IsTopologicalGroup G] in
lemma pivotProjection_continuous : Continuous C.pivotProjection:=
  F.state.domain.continuous.comp C.pointEvaluation_continuous
lemma pivotProjection_rational (g : CubeGroup (ι:=Empty) (F:=F))
    (hg : IsRational C.pivotChart.chart g) : IsRational c (C.pivotProjection g):=
  F.state.domain.rational_image _ ((C.rational_iff _).mp (C.pointEvaluation_rational g hg))

lemma pivotImage_mk (β : ℝ) (g : CubeGroup (ι:=Empty) (F:=F)) :
    C.pivotImage β (QuotientGroup.mk g)=
      QuotientGroup.mk (F.smoothLimit β*C.pivotProjection g*F.residue r) := by
  change F.smoothLimit β • C.pointImage (QuotientGroup.mk g)=_
  rw [pointImage,EmbeddedCubeHaar.coverImage_mk]
  change (QuotientGroup.mk (F.smoothLimit β*(C.pivotProjection g*F.residue r)) : G⧸Γ)=_
  rw [mul_assoc]

lemma pivotImage_expQuotient (β : ℝ) (z : Fin C.pivotChart.dim → ℝ) :
    C.pivotImage β (expQuotient C.pivotChart.chart C.pointLattice z)=
      QuotientGroup.mk (F.smoothLimit β*C.pivotProjection (canonicalExp C.pivotChart.chart z)*F.residue r) :=
  C.pivotImage_mk β _

end AllLevelFactorization.Factorization.ResidueCover
end
 
end

section
 

 

noncomputable section
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces CubeLocalHaar MalcevCharacters
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.RationalPivotPlan
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {k s : ℕ} {c : RealCoordinates G k} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {E : Factorization c Γ s K P L} {r : Fin E.period} (C : E.ResidueCover r)
variable {n : ℕ} (D : Pivot n)
variable {X : Type} [TopologicalSpace X]
variable {Y : Fin D.targets → Type} [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → (G⧸Γ) → Y j)
variable (A : Fin D.targets → Type) [∀ j,Group (A j)]
variable [∀ j,TopologicalSpace (A j)] [∀ j,IsTopologicalGroup (A j)]
variable (dim : Fin D.targets → ℕ) (d : ∀ j,RealCoordinates (A j) (dim j))
variable (Λ : ∀ j,Subgroup (A j)) (cover : ∀ j,CoveredLattice (d j) (Λ j))
variable (p : ∀ j,G →* A j) (hp : ∀ j,Continuous (p j))
variable (hrat : ∀ j g,IsRational c g → IsRational (d j) (p j g))
variable (read : ∀ j,(A j)⧸Λ j → Y j)
variable (hread : ∀ j g,π j (QuotientGroup.mk g)=read j (QuotientGroup.mk (p j g)))
variable (sym : (e : Fin D.pairs) → A (D.owner e) →* A (D.owner e))
variable (hsym : ∀ e,Continuous (sym e))
variable (hown : ∀ e x,read (D.owner e) (QuotientGroup.mk (sym e x))=
  unitShift D e • read (D.owner e) (QuotientGroup.mk x))

 

def projectedPhysicalData (β : ℝ)
    (hfaces : ∀ e,AffineOrbitRestriction.PreservesPhysicalFaces (Λ (D.owner e))
      ((p (D.owner e)).comp C.pivotProjection).range (p (D.owner e) (E.smoothLimit β))
      (p (D.owner e) (E.residue r))
      (LeibmanSquare.mapFiltration C.pointFiltration ((p (D.owner e)).comp C.pivotProjection).rangeRestrict)
      (sym e) s) : CoveredPhysicalData D C.pivotChart.chart C.pointFiltration C.pointLattice
        π (C.pivotImage β) s where
  A:=A
  dim:=dim
  chart:=d
  Λ:=Λ
  cover:=cover
  offset:=fun j=>p j (E.smoothLimit β)
  residue:=fun j=>p j (E.residue r)
  residue_rational:=fun j=>hrat j _ (E.residue_rational r)
  projection:=fun j=>(p j).comp C.pivotProjection
  continuous:=fun j=>(hp j).comp C.pivotProjection_continuous
  rational:=fun j g hg=>hrat j _ (C.pivotProjection_rational g hg)
  physical:=read
  physicalProjection:=by
    intro j z
    rw [C.pivotImage_expQuotient,hread]
    simp only [map_mul,MonoidHom.comp_apply]
  symmetry:=sym
  symmetryContinuous:=hsym
  preservesPhysicalFaces:=hfaces
  ownPhysical:=fun e y=>hown e _

end AllLevelFactorization.Factorization.ResidueCover
end
 
end

section
 

 

noncomputable section
namespace AffineOrbitRestriction
open CubeFaces
variable {G A : Type} [Group G] [Group A]
variable [TopologicalSpace A] [IsTopologicalGroup A]
variable (H : Filtration G) (p : G →* A) (Λ : Subgroup A) (h σ : A) (S : A →* A) (s : ℕ)

omit [TopologicalSpace A] [IsTopologicalGroup A] in
lemma physical_faces_of_projected_cubes
    (hp : ∀ k ≤ s,∀ f∈cube (ι:=Fin (k+1)) H Finset.univ 0,
      ∃ g∈cube (ι:=Fin (k+1)) H Finset.univ 0,∀ w,
        (QuotientGroup.mk (if Fin.last k∈w then S (h*p (f w)*σ) else h*p (f w)*σ) : A⧸Λ)=
          QuotientGroup.mk (h*p (g w)*σ)) :
    PreservesPhysicalFaces Λ p.range h σ (LeibmanSquare.mapFiltration H p.rangeRestrict) S s := by
  intro k hk f hf
  obtain ⟨a,ha,he⟩:=exists_cube_lift p.rangeRestrict H
    (LeibmanSquare.mapFiltration H p.rangeRestrict) (fun _=>rfl) Finset.univ 0 f hf
  obtain ⟨b,hb,hphys⟩:=hp k hk a ha
  refine ⟨vertexMap p.rangeRestrict b,?_,?_⟩
  · rw [←map_cube p.rangeRestrict H (LeibmanSquare.mapFiltration H p.rangeRestrict) (fun _=>rfl)]
    exact ⟨b,hb,rfl⟩
  · intro w
    have hw:=congrArg Subtype.val (he w)
    change p (a w)=(f w:A) at hw
    simpa only [vertexMap_apply,MonoidHom.coe_rangeRestrict,hw] using hphys w

variable {Q : Type} [Group Q] (T : Filtration Q) (e : Q →* G)

omit [TopologicalSpace A] [IsTopologicalGroup A] in
lemma physical_faces_of_filtered_cover
    (he : ∀ j,(T.level j).map e=H.level j)
    (hp : ∀ k ≤ s,∀ f∈cube (ι:=Fin (k+1)) H Finset.univ 0,
      ∃ g∈cube (ι:=Fin (k+1)) H Finset.univ 0,∀ w,
        (QuotientGroup.mk (if Fin.last k∈w then S (h*p (f w)*σ) else h*p (f w)*σ) : A⧸Λ)=
          QuotientGroup.mk (h*p (g w)*σ)) :
    PreservesPhysicalFaces Λ (p.comp e).range h σ
      (LeibmanSquare.mapFiltration T (p.comp e).rangeRestrict) S s := by
  apply physical_faces_of_projected_cubes T (p.comp e) Λ h σ S s
  intro k hk f hf
  have hmf : vertexMap e f∈cube H Finset.univ 0:=by
    rw [←map_cube e T H he]
    exact ⟨f,hf,rfl⟩
  obtain ⟨g,hg,hphys⟩:=hp k hk (vertexMap e f) hmf
  obtain ⟨b,hb,hbe⟩:=exists_cube_lift e T H he Finset.univ 0 g hg
  refine ⟨b,hb,?_⟩
  intro w
  simpa only [MonoidHom.comp_apply,vertexMap_apply,hbe] using hphys w

end AffineOrbitRestriction
end
 
end

section
 

 

noncomputable section
namespace CubeFaces
variable {G : Type*} [Group G] (H : Filtration G)

lemma empty_cube (k : ℕ) : cube (ι:=Empty) H Finset.univ k=
    (H.level k).map (face ∅) := by
  have hd : (default : Finset Empty)=∅:=Finset.eq_empty_of_isEmpty _
  simp [cube,Finset.univ_eq_empty,hd]
lemma empty_maxLevel (k : ℕ) : CubeMaxFiltration.level (ι:=Empty) H Finset.univ k=
    (H.level k).map (face ∅) := by
  have hd : (default : Finset Empty)=∅:=Finset.eq_empty_of_isEmpty _
  simp [CubeMaxFiltration.level,Finset.univ_eq_empty,hd]

def emptyEvaluation : cube (ι:=Empty) H Finset.univ 0 →* G where
  toFun g:=g.val ∅
  map_one' :=rfl
  map_mul' _ _:=rfl

lemma empty_level_iff (k : ℕ) (g : cube (ι:=Empty) H Finset.univ 0) :
    g∈(CubeMaxFiltration.filtration H Finset.univ).level k ↔
      emptyEvaluation H g∈H.level k := by
  change g.val∈CubeMaxFiltration.level H Finset.univ k ↔ _
  rw [empty_maxLevel]
  constructor
  · rintro ⟨a,ha,he⟩
    have he':=congrFun he ∅
    simpa only [face_apply,Finset.empty_subset,ite_true,emptyEvaluation,MonoidHom.coe_mk,OneHom.coe_mk] using he' ▸ ha
  · intro hg
    refine ⟨emptyEvaluation H g,hg,?_⟩
    ext w
    have hw : w=∅:=Finset.eq_empty_of_isEmpty w
    subst w
    simp [face_apply,emptyEvaluation]

def emptyConstant (h0 : H.level 0=⊤) : G →* cube (ι:=Empty) H Finset.univ 0 where
  toFun g:=⟨face ∅ g,by
    rw [empty_cube]
    exact ⟨g,by simp [h0],rfl⟩⟩
  map_one':=Subtype.ext (map_one (face ∅))
  map_mul' g h:=Subtype.ext (map_mul (face ∅) g h)

@[simp] lemma emptyEvaluation_constant (h0 : H.level 0=⊤) (g : G) :
    emptyEvaluation H (emptyConstant H h0 g)=g := by
  simp [emptyEvaluation,emptyConstant,face_apply]

lemma emptyEvaluation_levels (h0 : H.level 0=⊤) (k : ℕ) :
    ((CubeMaxFiltration.filtration H Finset.univ).level k).map (emptyEvaluation H)=H.level k := by
  ext g
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (empty_level_iff H k a).mp ha
  · intro hg
    exact ⟨emptyConstant H h0 g,(empty_level_iff H k _).mpr (by simpa using hg),
      emptyEvaluation_constant H h0 g⟩

end CubeFaces

end
end
end

end OAI
