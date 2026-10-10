import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel13
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open scoped Topology
open MeasureTheory Filter
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

 

structure CoveredPhysicalData (s : ℕ) where
  A : Fin D.targets → Type
  [group : ∀ j,Group (A j)]
  [topology : ∀ j,TopologicalSpace (A j)]
  [topGroup : ∀ j,IsTopologicalGroup (A j)]
  dim : Fin D.targets → ℕ
  chart : ∀ j,RealCoordinates (A j) (dim j)
  Λ : ∀ j,Subgroup (A j)
  cover : ∀ j,CoveredLattice (chart j) (Λ j)
  offset : ∀ j,A j
  residue : ∀ j,A j
  residue_rational : ∀ j,IsRational (chart j) (residue j)
  projection : ∀ j,G →* A j
  continuous : ∀ j,Continuous (projection j)
  rational : ∀ j g,IsRational c g → IsRational (chart j) (projection j g)
  physical : ∀ j,(A j)⧸Λ j → Y j
  physicalProjection : ∀ j z,π j (q (expQuotient c Γ z))=
    physical j (QuotientGroup.mk (offset j*projection j (canonicalExp c z)*residue j))
  symmetry : (e : Fin D.pairs) → A (D.owner e) →* A (D.owner e)
  symmetryContinuous : ∀ e,Continuous (symmetry e)
  preservesPhysicalFaces : ∀ e,AffineOrbitRestriction.PreservesPhysicalFaces
    (Λ (D.owner e)) (projection (D.owner e)).range (offset (D.owner e)) (residue (D.owner e))
    (LeibmanSquare.mapFiltration H (projection (D.owner e)).rangeRestrict) (symmetry e) s
  ownPhysical : ∀ e (y : (projection (D.owner e)).range),
    physical (D.owner e) (QuotientGroup.mk
      (symmetry e (offset (D.owner e)*(y:A (D.owner e))*residue (D.owner e))))=
    unitShift D e • physical (D.owner e) (QuotientGroup.mk
      (offset (D.owner e)*(y:A (D.owner e))*residue (D.owner e)))
attribute [instance] CoveredPhysicalData.group CoveredPhysicalData.topology CoveredPhysicalData.topGroup

variable (hsk : SecondKind c) (w : Fin k → ℕ) (hw : ∀ i,0<w i) (hmono : Monotone w)
variable (hH : ∀ j (g : G),g∈H.level j ↔ ∀ i : Fin k,w i<j → c.coord g i=0)
variable {s : ℕ} (hs : H.level (s+1)=⊥)
variable (M : CoveredPhysicalData D c H Γ π q s)

 

def CoveredPhysicalData.toPhysical : PhysicalMarginalFaceData D c H Γ π q s := by
  let T (j) : ImageGeometry (M.chart j) H (M.projection j):=
    Classical.choice (imageGeometry_nonempty c (M.chart j) H (M.projection j)
      hsk (M.continuous j) (M.rational j) w hw hmono hH)
  have ht2 (j) : T2Space (M.projection j).range:=(T j).chart.coord.symm.t2Space
  have hcomp (j) := ImageGeometry.covered_quotient_compactSpace (M.chart j) (M.Λ j) H (M.projection j) (T j) (M.cover j)
    (M.residue j) (M.residue_rational j)
  refine { A:=M.A, group:=M.group, topology:=M.topology, topGroup:=M.topGroup
           J:=fun j=>(M.projection j).range
           t2:=ht2, Λ:=M.Λ, offset:=M.offset, residue:=M.residue
           compact:=hcomp
           quotient_t2:=fun j=>CoveredLattice.conjugate_quotient_t2 (M.chart j) (M.Λ j) (M.cover j) (M.residue j)
           dim:=fun j=>(T j).dim, chart:=fun j=>(T j).chart
           secondKind:=fun j=>(T j).secondKind
           filtration:=fun j=>LeibmanSquare.mapFiltration H (M.projection j).rangeRestrict
           weights:=fun j=>(T j).weights, positive:=fun j=>(T j).positive
           monotone:=fun j=>(T j).monotone, adapted:=fun j=>(T j).adapted
           terminal:=?_,discreteAmbient:=?_,discrete:=?_,compactReps:=?_
           projection:=fun j=>(M.projection j).rangeRestrict
           continuous:=fun j=>(M.continuous j).subtype_mk _
           onto:=fun _ _=>rfl
           physical:=M.physical,physicalProjection:=M.physicalProjection
           symmetry:=M.symmetry,symmetryContinuous:=M.symmetryContinuous
           preservesPhysicalFaces:=M.preservesPhysicalFaces,ownPhysical:=M.ownPhysical }
  · intro j
    change (H.level (s+1)).map (M.projection j).rangeRestrict=⊥
    rw [hs,Subgroup.map_bot]
  · intro j
    exact isDiscrete_iff_discreteTopology.mpr
      (CoveredLattice.conjugate_discrete (M.chart j) (M.Λ j) (M.cover j) (M.residue j))
  · intro j
    exact isDiscrete_iff_discreteTopology.mpr
      (CoveredLattice.conjugate_induced_discrete (M.chart j) (M.Λ j) (M.cover j)
        (M.projection j).range.subtype continuous_subtype_val Subtype.val_injective (M.residue j))
  · intro j l
    exact ImageGeometry.covered_level_compact_reps (M.chart j) (M.Λ j) H (M.projection j) (T j) (M.cover j)
      (M.residue j) (M.residue_rational j) l

include hsk hw hmono hH hs M in
theorem own_lifts_from_covered_physical_faces :
    ∃ A : Fin D.pairs → shears (R:=ℝ) w,
      ∀ j e,D.owner e=j → ∀ z,
        π j (q (expQuotient c Γ (A e • z)))=
          unitShift D e • π j (q (expQuotient c Γ z)) := by
  exact own_lifts_from_physical_faces D c H Γ π q hsk w hw hmono hH
    (CoveredPhysicalData.toPhysical D c H Γ π q hsk w hw hmono hH hs M)

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
variable [HasOuterApproxClosed (G⧸Γ)] [MeasurableSingletonClass (G⧸Γ)]
variable {n r : ℕ} (hs : 1 ≤ s) (D : Pivot n)
variable (F B : Finset (Scale n))
variable (q₀ : ℕ) (hq₀ : pivotModulus s r hs D F B∣q₀)
variable (b : Scale n) (hb : b∈B) {τ : ℝ} (hτ : 0<τ)
variable (Y : Fin D.targets → Type) [∀ j,TopologicalSpace (Y j)]
variable [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → (G⧸Γ) → Y j)
variable (Read : (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ)
variable (hπ : ∀ j,Continuous (π j))
variable (hRead : ∀ j a t,Continuous (fun y=>Read j a y t))
variable (hS : ∀ j (a : Shifts D),Continuous (fun y : Y j=>a • y))
variable (M : ∀ a : Fin E.period,∀ β : ℝ,
  CoveredPhysicalData D (C a).pivotChart.chart (C a).pointFiltration (C a).pointLattice
    π ((C a).pivotImage β) s)

include hπ hRead hS M hq₀ hb hτ in
 

theorem covered_physical_pivot_empirical_success_mass (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
    (ReadN : ℕ → (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ)
    (he : ∀ᶠ N in atTop,∀ p∈pivotOptions s r hs D F,∀ i x,
      |centerReading D Y π (ReadN N) F q₀ b p i x-centerReading D Y π Read F q₀ b p i x| ≤ τ/4 ∧
      |translatedReading D Y π (ReadN N) F q₀ b p i x-translatedReading D Y π Read F q₀ b p i x| ≤ τ/4) :
    ∀ᶠ N in atTop,(((((pivotOptions s r hs D F).card : ℝ≥0)⁻¹/2) : ℝ≥0) : ℝ≥0∞) <
      (E.empiricalPointLaw N : Measure (G⧸Γ))
        (⋃ p∈pivotOptions s r hs D F,AlignmentMass.Success τ
          (centerReading D Y π (ReadN N) F q₀ b p)
          (translatedReading D Y π (ReadN N) F q₀ b p)) := by
  apply E.physical_pivot_empirical_success_mass C hs D F B q₀ hq₀ b hb hτ Y π Read hπ hRead hS
    (fun a β=>CoveredPhysicalData.toPhysical D (C a).pivotChart.chart
      (C a).pointFiltration (C a).pointLattice π ((C a).pivotImage β)
      (C a).pivotChart.secondKind (C a).pivotChart.weights (C a).pivotChart.positive
      (C a).pivotChart.monotone (C a).pivotChart.adapted
      (CubeMaxFiltration.filtration_bot E.state.domain.filtration Finset.univ E.state.domain.terminal)
      (M a β)) hL ht ReadN he

end AllLevelFactorization.Factorization
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
variable {k s : ℕ} {c : RealCoordinates G k} {Δ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (E : Factorization c Δ s K P L)
variable (C : (r : Fin E.period) → E.ResidueCover r)
variable [∀ r,MeasurableSpace ((C r).CubeSpace (ι:=Empty))]
variable [∀ r,BorelSpace ((C r).CubeSpace (ι:=Empty))]
variable [MeasurableSpace (G⧸Δ)] [BorelSpace (G⧸Δ)]
variable [CompactSpace (G⧸Δ)] [SecondCountableTopology (G⧸Δ)]
variable [HasOuterApproxClosed (G⧸Δ)] [MeasurableSingletonClass (G⧸Δ)]
variable (Γ : Subgroup G) (hle : Δ≤Γ)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)] [MeasurableSingletonClass (G⧸Γ)]
variable {n r : ℕ} (hs : 1 ≤ s) (D : Pivot n) (F B : Finset (Scale n))
variable (q₀ : ℕ) (hq₀ : pivotModulus s r hs D F B∣q₀)
variable (b : Scale n) (hb : b∈B) {τ : ℝ} (hτ : 0<τ)
variable (Y : Fin D.targets → Type) [∀ j,TopologicalSpace (Y j)]
variable [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → (G⧸Γ) → Y j)
variable (Read : (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ)
variable (hπ : ∀ j,Continuous (π j))
variable (hRead : ∀ j a t,Continuous (fun y=>Read j a y t))
variable (hS : ∀ j (a : Shifts D),Continuous (fun y : Y j=>a • y))
variable (M : ∀ a : Fin E.period,∀ β : ℝ,
  CoveredPhysicalData D (C a).pivotChart.chart (C a).pointFiltration (C a).pointLattice
    (fun j z=>π j (CosetCover.map Δ Γ hle z)) ((C a).pivotImage β) s)

include hπ hRead hS M hq₀ hb hτ in
 

omit [BorelSpace (G⧸Γ)] in
theorem actual_lattice_pivot_empirical_success_mass
    (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
    (ReadN : ℕ → (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ)
    (he : ∀ᶠ N in atTop,∀ p∈pivotOptions s r hs D F,∀ i x,
      |centerReading D Y π (ReadN N) F q₀ b p i x-centerReading D Y π Read F q₀ b p i x| ≤ τ/4 ∧
      |translatedReading D Y π (ReadN N) F q₀ b p i x-translatedReading D Y π Read F q₀ b p i x| ≤ τ/4) :
    ∀ᶠ N in atTop,(((((pivotOptions s r hs D F).card : ℝ≥0)⁻¹/2) : ℝ≥0) : ℝ≥0∞) <
      (E.coveredEmpiricalPointLaw Γ N : Measure (G⧸Γ))
        (⋃ p∈pivotOptions s r hs D F,AlignmentMass.Success τ
          (centerReading D Y π (ReadN N) F q₀ b p)
          (translatedReading D Y π (ReadN N) F q₀ b p)) := by
  let f:=CosetCover.map Δ Γ hle
  let π' (j) (z : G⧸Δ):=π j (f z)
  have he' : ∀ᶠ N in atTop,∀ p∈pivotOptions s r hs D F,∀ i x,
      |centerReading D Y π' (ReadN N) F q₀ b p i x-centerReading D Y π' Read F q₀ b p i x| ≤ τ/4 ∧
      |translatedReading D Y π' (ReadN N) F q₀ b p i x-translatedReading D Y π' Read F q₀ b p i x| ≤ τ/4:=by
    filter_upwards [he] with N hN
    intro p hp i x
    exact hN p hp i (f x)
  have H:=E.covered_physical_pivot_empirical_success_mass C hs D F B q₀ hq₀ b hb hτ Y π' Read
    (fun j=>(hπ j).comp (CosetCover.continuous_map Δ Γ hle)) hRead hS M hL ht ReadN he'
  filter_upwards [H] with N hN
  let S : Set (G⧸Γ):=⋃ p∈pivotOptions s r hs D F,AlignmentMass.Success τ
    (centerReading D Y π (ReadN N) F q₀ b p)
    (translatedReading D Y π (ReadN N) F q₀ b p)
  have heq:=ProbabilityMixtures.empirical_preimage ⌊L (E.state.subseq N)⌋₊
    (fun z=>(QuotientGroup.mk (P (E.state.subseq N) (z:ℤ)) : G⧸Δ)) f S
  change _ < (ProbabilityMixtures.empirical ⌊L (E.state.subseq N)⌋₊
    (fun z=>f (QuotientGroup.mk (P (E.state.subseq N) (z:ℤ)))) : Measure (G⧸Γ)) S
  rw [←heq]
  convert hN using 1
  congr 1
  ext z
  simp only [S,Set.mem_preimage,Set.mem_iUnion,AlignmentMass.Success,Set.mem_ofPred_eq]
  rfl

end AllLevelFactorization.Factorization

end
end
end

end OAI
