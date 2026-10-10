import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel14
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
open MeasureTheory Topology
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces PhysicalCubeMaps
variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {F : Factorization c Γ s K P L} {r : Fin F.period} (C : F.ResidueCover r)

omit [IsTopologicalGroup G] in
lemma pointEvaluation_levels (j : ℕ) :
    (C.pointFiltration.level j).map C.pointEvaluation=F.state.domain.filtration.level j :=
  emptyEvaluation_levels F.state.domain.filtration F.state.domain.zero_top j

variable [∀ k : ℕ,MeasurableSpace (C.CubeSpace (ι:=Fin (k+1)))]
variable [∀ k : ℕ,BorelSpace (C.CubeSpace (ι:=Fin (k+1)))]
variable [CompactSpace (G⧸Γ)] [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
variable [SecondCountableTopology (G⧸Γ)]
variable (Λ : Subgroup A) [MeasurableSpace (A⧸Λ)] [BorelSpace (A⧸Λ)]
variable [T2Space (A⧸Λ)]
variable [SecondCountableTopology (A⧸Λ)]
variable [∀ k : ℕ,HasOuterApproxClosed (Finset (Fin (k+1)) → A⧸Λ)]
variable (p : G →* A) (hp : Continuous p) (hpΓ : ∀ g∈Γ,p g∈Λ)
variable (S : A →* A) (hS : Continuous S) (hSΛ : ∀ g∈Λ,S g∈Λ)
variable (β : ℝ)

 

omit [IsTopologicalGroup A] [CompactSpace (G⧸Γ)]
  [∀ k : ℕ,HasOuterApproxClosed (Finset (Fin (k+1)) → A⧸Λ)] in
theorem physical_faces_of_marginal_haar
    (hinv : ∀ k ≤ s,Measure.map
      (upperFace (Fin.last k) (NonnormalCoset.map Λ Λ S hS hSΛ))
      (C.marginalCubeHaar β (vertices (ι:=Fin (k+1)) (NonnormalCoset.map Γ Λ p hp hpΓ)) :
        Measure (Finset (Fin (k+1)) → A⧸Λ))=
      (C.marginalCubeHaar β (vertices (ι:=Fin (k+1)) (NonnormalCoset.map Γ Λ p hp hpΓ)) :
        Measure (Finset (Fin (k+1)) → A⧸Λ))) :
    AffineOrbitRestriction.PreservesPhysicalFaces Λ (p.comp C.pivotProjection).range
      (p (F.smoothLimit β)) (p (F.residue r))
      (LeibmanSquare.mapFiltration C.pointFiltration (p.comp C.pivotProjection).rangeRestrict) S s := by
  apply AffineOrbitRestriction.physical_faces_of_filtered_cover F.state.domain.filtration
    (p.comp F.state.domain.embed) Λ (p (F.smoothLimit β)) (p (F.residue r)) S s
    C.pointFiltration C.pointEvaluation C.pointEvaluation_levels
  intro k hk f hf
  obtain ⟨g,hg⟩:=C.physical_cube_image_preserved β
    (vertices (ι:=Fin (k+1)) (NonnormalCoset.map Γ Λ p hp hpΓ))
    (upperFace (Fin.last k) (NonnormalCoset.map Λ Λ S hS hSΛ)) (hinv k hk) ⟨f,hf⟩
  refine ⟨g.val,g.property,?_⟩
  intro w
  have hw:=congrFun hg w
  simp only [vertices_apply,upperFace_apply] at hw
  dsimp only [NonnormalCoset.map,ContinuousMap.coe_mk,Quotient.lift_mk] at hw
  by_cases he : Fin.last k∈w
  · simpa only [he,ite_true,MonoidHom.comp_apply,map_mul] using hw
  · simpa only [he,ite_false,MonoidHom.comp_apply,map_mul] using hw

end AllLevelFactorization.Factorization.ResidueCover
end
 
end

section
 

 

noncomputable section
open MeasureTheory Topology
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces CubeLocalHaar MalcevCharacters PhysicalCubeMaps
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.RationalPivotPlan
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {k s : ℕ} {c : RealCoordinates G k} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {E : Factorization c Γ s K P L} {r : Fin E.period} (C : E.ResidueCover r)
variable [∀ k : ℕ,MeasurableSpace (C.CubeSpace (ι:=Fin (k+1)))]
variable [∀ k : ℕ,BorelSpace (C.CubeSpace (ι:=Fin (k+1)))]
variable [CompactSpace (G⧸Γ)] [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
variable [SecondCountableTopology (G⧸Γ)]
variable {n : ℕ} (D : Pivot n)
variable {Y : Fin D.targets → Type} [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → (G⧸Γ) → Y j)
variable (A : Fin D.targets → Type) [∀ j,Group (A j)]
variable [∀ j,TopologicalSpace (A j)] [∀ j,IsTopologicalGroup (A j)]
variable (dim : Fin D.targets → ℕ) (d : ∀ j,RealCoordinates (A j) (dim j))
variable (Λ : ∀ j,Subgroup (A j)) (cover : ∀ j,CoveredLattice (d j) (Λ j))
variable [∀ j,MeasurableSpace ((A j)⧸Λ j)] [∀ j,BorelSpace ((A j)⧸Λ j)]
variable [∀ j,T2Space ((A j)⧸Λ j)] [∀ j,SecondCountableTopology ((A j)⧸Λ j)]
variable [∀ j,∀ k : ℕ,HasOuterApproxClosed (Finset (Fin (k+1)) → (A j)⧸Λ j)]
variable (p : ∀ j,G →* A j) (hp : ∀ j,Continuous (p j))
variable (hpΓ : ∀ j g,g∈Γ → p j g∈Λ j)
variable (hrat : ∀ j g,IsRational c g → IsRational (d j) (p j g))
variable (read : ∀ j,(A j)⧸Λ j → Y j)
variable (hread : ∀ j g,π j (QuotientGroup.mk g)=read j (QuotientGroup.mk (p j g)))
variable (sym : (e : Fin D.pairs) → A (D.owner e) →* A (D.owner e))
variable (hsym : ∀ e,Continuous (sym e))
variable (hsymΛ : ∀ e g,g∈Λ (D.owner e) → sym e g∈Λ (D.owner e))
variable (hown : ∀ e x,read (D.owner e) (QuotientGroup.mk (sym e x))=
  unitShift D e • read (D.owner e) (QuotientGroup.mk x))

def physicalData_of_haar (β : ℝ)
    (hinv : ∀ e : Fin D.pairs,∀ k ≤ s,Measure.map
      (upperFace (Fin.last k) (NonnormalCoset.map (Λ (D.owner e)) (Λ (D.owner e))
        (sym e) (hsym e) (hsymΛ e)))
      (C.marginalCubeHaar β (vertices (ι:=Fin (k+1))
        (NonnormalCoset.map Γ (Λ (D.owner e)) (p (D.owner e)) (hp (D.owner e)) (hpΓ (D.owner e)))) :
        Measure (Finset (Fin (k+1)) → (A (D.owner e))⧸Λ (D.owner e)))=
      (C.marginalCubeHaar β (vertices (ι:=Fin (k+1))
        (NonnormalCoset.map Γ (Λ (D.owner e)) (p (D.owner e)) (hp (D.owner e)) (hpΓ (D.owner e)))) :
        Measure (Finset (Fin (k+1)) → (A (D.owner e))⧸Λ (D.owner e)))) :
    CoveredPhysicalData D C.pivotChart.chart C.pointFiltration C.pointLattice
        π (C.pivotImage β) s :=
  C.projectedPhysicalData D π A dim d Λ cover p hp hrat read hread sym hsym hown β
    (fun e=>C.physical_faces_of_marginal_haar (Λ (D.owner e)) (p (D.owner e))
      (hp (D.owner e)) (hpΓ (D.owner e)) (sym e) (hsym e) (hsymΛ e) β (hinv e))

end AllLevelFactorization.Factorization.ResidueCover
end
 
end

section
 

 

noncomputable section
namespace RationalLattice.PolynomialArrays
open CubeFaces MalcevCharacters
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k g,g∈A.level k ↔ ∀ i,w i<k → c.coord g i=0)
variable (Γ : Subgroup G)
variable {ι : Type} (ρ : (ι → ℤ) →+ (Fin q → ℤ))

@[instance_reducible]
def shiftAction : MulAction (Multiplicative (ι → ℤ))
    ((group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ) where
  smul v x:=shifted c hsk A w hA Γ (ρ v.toAdd) x
  one_smul x:=by
    change shifted c hsk A w hA Γ (ρ 0) x=x
    rw [map_zero,shifted_zero]
  mul_smul v z x:=by
    change shifted c hsk A w hA Γ (ρ (v.toAdd+z.toAdd)) x=_
    rw [map_add,shifted_add]
    rfl

lemma shiftAction_continuous (v : Multiplicative (ι → ℤ)) :
    letI := shiftAction c hsk A w hA Γ ρ
    Continuous (fun x : (group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ=>v • x) :=
  shifted_continuous c hsk A w hA Γ (ρ v.toAdd)

lemma shiftAction_mk (v : Multiplicative (ι → ℤ)) (f : group (q:=q) c hsk A w hA) :
    letI := shiftAction c hsk A w hA Γ ρ
    v • (QuotientGroup.mk f : (group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ)=
      QuotientGroup.mk (shift c hsk A w hA (fun j=>(ρ v.toAdd j:ℝ)) f) := rfl

lemma readout_shiftAction (u : Fin q → ℤ) (v : Multiplicative (ι → ℤ))
    (x : (group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ) :
    letI := shiftAction c hsk A w hA Γ ρ
    readout c hsk A w hA Γ u (v • x)=readout c hsk A w hA Γ (u+ρ v.toAdd) x :=
  readout_shifted c hsk A w hA Γ u (ρ v.toAdd) x

end RationalLattice.PolynomialArrays
end
 
end

section
 

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace AllLevelFactorization.Factorization
open RationalLattice CubeFaces ResidueCover MalcevCharacters PhysicalCubeMaps
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
variable [∀ a k,MeasurableSpace ((C a).CubeSpace (ι:=Fin (k+1)))]
variable [∀ a k,BorelSpace ((C a).CubeSpace (ι:=Fin (k+1)))]
variable (A : Fin D.targets → Type) [∀ j,Group (A j)]
variable [∀ j,TopologicalSpace (A j)] [∀ j,IsTopologicalGroup (A j)]
variable (dim : Fin D.targets → ℕ) (d : ∀ j,RealCoordinates (A j) (dim j))
variable (Λ : ∀ j,Subgroup (A j)) (cover : ∀ j,CoveredLattice (d j) (Λ j))
variable [∀ j,MeasurableSpace ((A j)⧸Λ j)] [∀ j,BorelSpace ((A j)⧸Λ j)]
variable [∀ j,T2Space ((A j)⧸Λ j)] [∀ j,SecondCountableTopology ((A j)⧸Λ j)]
variable [∀ j,∀ k : ℕ,HasOuterApproxClosed (Finset (Fin (k+1)) → (A j)⧸Λ j)]
variable (p : ∀ j,G →* A j) (hp : ∀ j,Continuous (p j))
variable (hpΓ : ∀ j g,g∈Γ → p j g∈Λ j)
variable (hrat : ∀ j g,IsRational c g → IsRational (d j) (p j g))
variable (read : ∀ j,(A j)⧸Λ j → Y j)
variable (hread : ∀ j g,π j (QuotientGroup.mk g)=read j (QuotientGroup.mk (p j g)))
variable (sym : (e : Fin D.pairs) → A (D.owner e) →* A (D.owner e))
variable (hsym : ∀ e,Continuous (sym e))
variable (hsymΛ : ∀ e g,g∈Λ (D.owner e) → sym e g∈Λ (D.owner e))
variable (hown : ∀ e x,read (D.owner e) (QuotientGroup.mk (sym e x))=
  unitShift D e • read (D.owner e) (QuotientGroup.mk x))
variable (hinv : ∀ a β (e : Fin D.pairs),∀ k ≤ s,Measure.map
  (upperFace (Fin.last k) (NonnormalCoset.map (Λ (D.owner e)) (Λ (D.owner e))
    (sym e) (hsym e) (hsymΛ e)))
  ((C a).marginalCubeHaar β (vertices (ι:=Fin (k+1))
    (NonnormalCoset.map Δ (Λ (D.owner e)) (p (D.owner e)) (hp (D.owner e))
      (fun g hg=>hpΓ (D.owner e) g (hle hg)))) :
      Measure (Finset (Fin (k+1)) → (A (D.owner e))⧸Λ (D.owner e)))=
  ((C a).marginalCubeHaar β (vertices (ι:=Fin (k+1))
    (NonnormalCoset.map Δ (Λ (D.owner e)) (p (D.owner e)) (hp (D.owner e))
      (fun g hg=>hpΓ (D.owner e) g (hle hg)))) :
      Measure (Finset (Fin (k+1)) → (A (D.owner e))⧸Λ (D.owner e))))

include hπ hRead hS hq₀ hb hτ hrat cover hinv hown hread in
 

omit [BorelSpace (G⧸Γ)]
  [∀ j,∀ k : ℕ,HasOuterApproxClosed (Finset (Fin (k+1)) → (A j)⧸Λ j)] in
theorem empirical_success_from_marginal_haar
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
  let π' (j) (z : G⧸Δ):=π j (CosetCover.map Δ Γ hle z)
  let M (a : Fin E.period) (β : ℝ) :=
    (C a).physicalData_of_haar D π' A dim d Λ cover p hp
      (fun j g hg=>hpΓ j g (hle hg)) hrat read
      (fun j g=>hread j g) sym hsym hsymΛ hown β (hinv a β)
  exact E.actual_lattice_pivot_empirical_success_mass C Γ hle hs D F B q₀ hq₀ b hb hτ
    Y π Read hπ hRead hS M hL ht ReadN he

end AllLevelFactorization.Factorization

end
end
end

end OAI
