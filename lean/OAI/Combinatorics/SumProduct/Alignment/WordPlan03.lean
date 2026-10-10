import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AffineOrbit01
import OAI.Combinatorics.SumProduct.Alignment.AllLevel12
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
end
 
end

section
 

 

noncomputable section
namespace RationalLattice
open CubeFaces MalcevCharacters CompactGroupProducts
open FilteredShears.PolynomialShears PolynomialShearPoint
variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
variable (Λ J : Subgroup A) [T2Space J]
variable {n m : ℕ} (c : RealCoordinates G n) (d : RealCoordinates J m)
variable (hsk : SecondKind c) (hdsk : SecondKind d)
variable (H : Filtration G) (K : Filtration J)
variable (w : Fin n → ℕ) (v : Fin m → ℕ)
variable (hw : ∀ i,0<w i) (hv : ∀ i,0<v i)
variable (hmono : Monotone w) (hvmono : Monotone v)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)
variable (hK : ∀ k (g : J),g∈K.level k ↔ ∀ i : Fin m,v i<k → d.coord g i=0)
variable (p : G →* J) (hp : Continuous p)
variable (honto : ∀ k,(H.level k).map p=K.level k)
variable (h σ : A) [CompactSpace (J⧸(CubeLocalHaar.conjugateLattice Λ σ).comap J.subtype)]
variable [T2Space (A⧸CubeLocalHaar.conjugateLattice Λ σ)]
variable (hΛ : IsDiscrete (CubeLocalHaar.conjugateLattice Λ σ : Set A))
variable (hdisc : IsDiscrete ((CubeLocalHaar.conjugateLattice Λ σ).comap J.subtype : Set J))
variable (hrep : ∀ j,HasCompactReps (K.level j) ((CubeLocalHaar.conjugateLattice Λ σ).comap J.subtype))
variable (S : A →* A) (hS : Continuous S)
variable (s : ℕ) (hs : K.level (s+1)=⊥)
variable (hfaces : AffineOrbitRestriction.PreservesPhysicalFaces Λ J h σ K S s)

include hsk hdsk hw hv hmono hvmono hH hK hp honto hΛ hdisc hrep hS hs hfaces in
 

theorem exists_physical_face_lift :
    ∃ B : shears (R:=ℝ) w,
      (∀ x,(QuotientGroup.mk (h*(p (canonicalExp c (pointMap B.val.toAlgHom x)):A)*σ) : A⧸Λ)=
        QuotientGroup.mk (S (h*(p (canonicalExp c x):A)*σ))) ∧
      Function.Bijective (pointMap B.val.toAlgHom) := by
  let : PathConnectedSpace J := d.coord.symm.surjective.pathConnectedSpace d.coord.symm.continuous
  have hK0 : K.level 0=⊤ := by
    ext g
    simp only [Subgroup.mem_top,iff_true]
    rw [hK]
    intro i hi
    omega
  have hK1 (a : J) : a∈K.level 1 := by
    rw [hK]
    intro i hi
    have hv':=hv i
    omega
  obtain ⟨a,φ,hφ,hphys,hpres⟩:=
    AffineOrbitRestriction.exists_affine_face_restriction Λ J h σ K S s hK0 hΛ hS hfaces
  obtain ⟨B,hB,hbij⟩:=exists_face_lift c d hsk hdsk H K w v hw hv hmono hvmono hH hK
    p hp honto _ hdisc hrep a (hK1 a) φ hφ s hs hpres
  refine ⟨B,?_,hbij⟩
  intro x
  rw [hB]
  exact (hphys (p (canonicalExp c x))).symm

end RationalLattice
end
 
end

section
 

 

noncomputable section
namespace ConstructedWordPlan.GlobalWordPlan
open AlignmentScales RationalPivotPlan PolynomialShearPoint RationalLattice MalcevCharacters
open FilteredShears.PolynomialShears
variable {n k : ℕ} (D : Pivot n)
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (c : RealCoordinates G k) (H : _root_.OAI.CubeFaces.Filtration G) (Γ : Subgroup G)
variable {X : Type} [TopologicalSpace X]
variable {Y : Fin D.targets → Type} [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → X → Y j) (q : C(G⧸Γ,X))

 

structure PhysicalMarginalFaceData (s : ℕ) where
  A : Fin D.targets → Type
  [group : ∀ j,Group (A j)]
  [topology : ∀ j,TopologicalSpace (A j)]
  [topGroup : ∀ j,IsTopologicalGroup (A j)]
  J : ∀ j,Subgroup (A j)
  [t2 : ∀ j,T2Space (J j)]
  Λ : ∀ j,Subgroup (A j)
  offset : ∀ j,A j
  residue : ∀ j,A j
  [compact : ∀ j,CompactSpace ((J j)⧸(CubeLocalHaar.conjugateLattice (Λ j) (residue j)).comap (J j).subtype)]
  [quotient_t2 : ∀ j,T2Space ((A j)⧸CubeLocalHaar.conjugateLattice (Λ j) (residue j))]
  dim : Fin D.targets → ℕ
  chart : ∀ j,RealCoordinates (J j) (dim j)
  secondKind : ∀ j,SecondKind (chart j)
  filtration : ∀ j,_root_.OAI.CubeFaces.Filtration (J j)
  weights : ∀ j,Fin (dim j) → ℕ
  positive : ∀ j i,0<weights j i
  monotone : ∀ j,Monotone (weights j)
  adapted : ∀ j l (g : J j),g∈(filtration j).level l ↔
    ∀ i : Fin (dim j),weights j i<l → (chart j).coord g i=0
  terminal : ∀ j,(filtration j).level (s+1)=⊥
  discreteAmbient : ∀ j,IsDiscrete (CubeLocalHaar.conjugateLattice (Λ j) (residue j) : Set (A j))
  discrete : ∀ j,IsDiscrete ((CubeLocalHaar.conjugateLattice (Λ j) (residue j)).comap (J j).subtype : Set (J j))
  compactReps : ∀ j l,CompactGroupProducts.HasCompactReps ((filtration j).level l)
    ((CubeLocalHaar.conjugateLattice (Λ j) (residue j)).comap (J j).subtype)
  projection : ∀ j,G →* J j
  continuous : ∀ j,Continuous (projection j)
  onto : ∀ j l,(H.level l).map (projection j)=(filtration j).level l
  physical : ∀ j,(A j)⧸Λ j → Y j
  physicalProjection : ∀ j z,π j (q (expQuotient c Γ z))=
    physical j (QuotientGroup.mk (offset j*(projection j (canonicalExp c z):A j)*residue j))
  symmetry : (e : Fin D.pairs) → A (D.owner e) →* A (D.owner e)
  symmetryContinuous : ∀ e,Continuous (symmetry e)
  preservesPhysicalFaces : ∀ e,AffineOrbitRestriction.PreservesPhysicalFaces
    (Λ (D.owner e)) (J (D.owner e)) (offset (D.owner e)) (residue (D.owner e))
    (filtration (D.owner e)) (symmetry e) s
  ownPhysical : ∀ e (y : J (D.owner e)),
    physical (D.owner e) (QuotientGroup.mk
      (symmetry e (offset (D.owner e)*(y:A (D.owner e))*residue (D.owner e))))=
    unitShift D e • physical (D.owner e) (QuotientGroup.mk
      (offset (D.owner e)*(y:A (D.owner e))*residue (D.owner e)))
attribute [instance] PhysicalMarginalFaceData.group PhysicalMarginalFaceData.topology
  PhysicalMarginalFaceData.topGroup PhysicalMarginalFaceData.t2
  PhysicalMarginalFaceData.compact PhysicalMarginalFaceData.quotient_t2

variable (hsk : SecondKind c) (w : Fin k → ℕ) (hw : ∀ i,0<w i) (hmono : Monotone w)
variable (hH : ∀ j (g : G),g∈H.level j ↔ ∀ i : Fin k,w i<j → c.coord g i=0)
include hsk hw hmono hH in
 

theorem own_lifts_from_physical_faces {s : ℕ}
    (M : PhysicalMarginalFaceData D c H Γ π q s) :
    ∃ A : Fin D.pairs → shears (R:=ℝ) w,
      ∀ j e,D.owner e=j → ∀ z,
        π j (q (expQuotient c Γ (A e • z)))=
          unitShift D e • π j (q (expQuotient c Γ z)) := by
  have hex (e : Fin D.pairs) : ∃ A : shears (R:=ℝ) w,
      ∀ z,π (D.owner e) (q (expQuotient c Γ (A • z)))=
        unitShift D e • π (D.owner e) (q (expQuotient c Γ z)) := by
    obtain ⟨B,hB,_⟩:=exists_physical_face_lift
      (M.Λ (D.owner e)) (M.J (D.owner e)) c (M.chart (D.owner e)) hsk (M.secondKind _)
      H (M.filtration _) w (M.weights _) hw (M.positive _) hmono (M.monotone _)
      hH (M.adapted _) (M.projection _) (M.continuous _) (M.onto _)
      (M.offset _) (M.residue _) (M.discreteAmbient _) (M.discrete _) (M.compactReps _)
      (M.symmetry e) (M.symmetryContinuous e) s (M.terminal _) (M.preservesPhysicalFaces e)
    refine ⟨B⁻¹,?_⟩
    intro z
    rw [M.physicalProjection,M.physicalProjection]
    change M.physical (D.owner e) (QuotientGroup.mk
      (M.offset (D.owner e)*(M.projection (D.owner e)
        (canonicalExp c (pointMap B.val.toAlgHom z)):M.A (D.owner e))*M.residue (D.owner e)))=_
    rw [hB,M.ownPhysical]
  choose A hA using hex
  refine ⟨A,?_⟩
  intro j e he z
  subst j
  exact hA e z

end ConstructedWordPlan.GlobalWordPlan
end
 
end

section
 

 

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace AllLevelFactorization.Factorization
open RationalLattice CubeFaces ResidueCover
open ConstructedWordPlan.GlobalWordPlan
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {k s : ℕ} {c : RealCoordinates G k} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (E : Factorization c Γ s K P L)
variable (C : (r : Fin E.period) → E.ResidueCover r)
variable [∀ r,MeasurableSpace ((C r).CubeSpace (ι:=Empty))]
variable [∀ r,BorelSpace ((C r).CubeSpace (ι:=Empty))]
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
variable [CompactSpace (G⧸Γ)] [SecondCountableTopology (G⧸Γ)]
variable [HasOuterApproxClosed (G⧸Γ)]
variable {n r : ℕ} (hs : 1 ≤ s) (D : ConstructedWordPlan.GlobalWordPlan.Pivot n)
variable (F B : Finset (ConstructedWordPlan.GlobalWordPlan.Scale n))
variable (q₀ : ℕ) (hq₀ : pivotModulus s r hs D F B∣q₀)
variable (b : Scale n) (hb : b∈B) (τ : ℝ)
variable (Y : Fin D.targets → Type) [∀ j,TopologicalSpace (Y j)]
variable [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → (G⧸Γ) → Y j)
variable (Read : (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ)
variable (hπ : ∀ j,Continuous (π j))
variable (hRead : ∀ j a t,Continuous (fun y=>Read j a y t))
variable (hS : ∀ j (a : Shifts D),Continuous (fun y : Y j=>a • y))
variable (M : ∀ a : Fin E.period,∀ β : ℝ,
  PhysicalMarginalFaceData D (C a).pivotChart.chart (C a).pointFiltration (C a).pointLattice
    π ((C a).pivotImage β) s)

include hπ hRead hS M hq₀ hb in
 

omit [CompactSpace (G⧸Γ)] in
theorem physical_pivot_mixture_mass :
    (((pivotOptions s r hs D F).card : ℝ≥0)⁻¹ : ℝ≥0∞) ≤
      (E.pointMixture C : Measure (G⧸Γ))
        (⋃ p∈pivotOptions s r hs D F,closedOption D π Read F τ q₀ b p) := by
  classical
  let S : Set (G⧸Γ):=⋃ p∈pivotOptions s r hs D F,closedOption D π Read F τ q₀ b p
  have hSmeas : MeasurableSet S := by
    apply MeasurableSet.biUnion (pivotOptions s r hs D F).countable_toSet
    intro p hp
    exact (closedOption_isClosed D π Read hπ hRead hS F τ q₀ b p).measurableSet
  let : Nonempty (Fin E.period):=⟨⟨0,E.period_pos⟩⟩
  apply ProbabilityMixtures.betaResidue_lower (fun a=>(C a).pointHaar)
    (fun _=>E.smoothAction) S hSmeas
  intro a
  apply Eventually.of_forall
  intro β
  let T:=(C a).pivotChart
  obtain ⟨A,hA⟩:=own_lifts_from_physical_faces D T.chart (C a).pointFiltration
    (C a).pointLattice π ((C a).pivotImage β) T.secondKind
    T.weights T.positive T.monotone T.adapted (M a β)
  have hm:=pivotOptions_mass s r hs D F B q₀ hq₀ b hb τ
    T.dim (CubeGroup (F:=E) (ι:=Empty)) T.chart T.secondKind
    (C a).pointFiltration T.weights T.positive T.bounded T.adapted
    (C a).pointLattice (G⧸Γ) Y π Read T.integer_lattice
    ((C a).haar (ι:=Empty)) ((C a).pivotImage β) A hπ hRead hS hA
  exact ((C a).pivotImage_event β S hSmeas) ▸ hm

end AllLevelFactorization.Factorization
end
 
end

end

end OAI
