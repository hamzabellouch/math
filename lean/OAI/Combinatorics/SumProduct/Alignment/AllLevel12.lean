import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice21
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice25
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
open MalcevCharacters MalcevWeightedCoordinates CubeFaces
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n : ℕ} (c : RealCoordinates G n) (H : Filtration G)
variable (h0 : H.level 0=⊤) (h1 : H.level 1=⊤) (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ → ℕ)
variable (hH : ∀ k (x : G),x∈H.level k ↔ ∀ i : Fin n,i.val<q k → c.coord x i=0)

include h0 h1 hs hH in
 

theorem exists_adapted_weights :
    ∃ w : Fin n → ℕ,Monotone w ∧ (∀ i,0<w i) ∧ (∀ i,w i ≤ s) ∧
      ∀ k (x : G),x∈H.level k ↔ ∀ i : Fin n,w i<k → c.coord x i=0 := by
  classical
  let w:=subspaceWeight c H s hs
  have hw (k : ℕ) (i : Fin n) : w i<k ↔ i.val<q k := by
    rw [weight_lt_iff_out c H s hs h0]
    have hh:=axis_mem_subspace_iff c (H.level k) {i : Fin n | i.val<q k} (hH k) i
    simpa only [Set.mem_ofPred_eq,not_not] using not_congr hh
  refine ⟨w,?_,?_,?_,?_⟩
  · intro i j hij
    by_contra h
    have hji : w j<w i:=Nat.lt_of_not_ge h
    have hj:= (hw (w i) j).mp hji
    have hi : i.val<q (w i):=lt_of_le_of_lt hij hj
    exact (lt_irrefl (w i)) ((hw (w i) i).mpr hi)
  · intro i
    have hn : ¬ w i<1 := by
      rw [weight_lt_iff_out c H s hs h0,h1]
      simp
    omega
  · intro i
    have ho : axis c i 1∉H.level (s+1) := by
      rw [hs,Subgroup.mem_bot]
      intro he
      have ee:=congrArg (fun g=>c.coord g i) he
      simp [axis,c.one_coord] at ee
    have hh:=(weight_lt_iff_out c H s hs h0 i (s+1)).mpr ho
    change w i<s+1 at hh
    omega
  · intro k x
    simpa only [hw] using hH k x

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
variable (c : RealCoordinates G k) (hsk : SecondKind c)
variable (H : _root_.OAI.CubeFaces.Filtration G) (w : Fin k → ℕ)
variable (hw : ∀ i,0<w i) (hmono : Monotone w)
variable (hH : ∀ j (g : G),g∈H.level j ↔ ∀ i : Fin k,w i<j → c.coord g i=0)
variable (Γ : Subgroup G)
variable {X : Type} [TopologicalSpace X]
variable {Y : Fin D.targets → Type} [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → X → Y j) (q : C(G⧸Γ,X))

 

structure MarginalFaceData (s : ℕ) where
  J : Fin D.targets → Type
  [group : ∀ j,Group (J j)]
  [topology : ∀ j,TopologicalSpace (J j)]
  [topGroup : ∀ j,IsTopologicalGroup (J j)]
  [t2 : ∀ j,T2Space (J j)]
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
  lattice : ∀ j,Subgroup (J j)
  discrete : ∀ j,IsDiscrete (lattice j : Set (J j))
  compactReps : ∀ j l,CompactGroupProducts.HasCompactReps ((filtration j).level l) (lattice j)
  projection : ∀ j,G →* J j
  continuous : ∀ j,Continuous (projection j)
  onto : ∀ j l,(H.level l).map (projection j)=(filtration j).level l
  physical : ∀ j,J j → Y j
  physicalProjection : ∀ j z,π j (q (expQuotient c Γ z))=
    physical j (projection j (canonicalExp c z))
  translate : (e : Fin D.pairs) → J (D.owner e)
  translate_mem : ∀ e,translate e∈(filtration (D.owner e)).level 1
  linearPart : (e : Fin D.pairs) → J (D.owner e) →* J (D.owner e)
  linearContinuous : ∀ e,Continuous (linearPart e)
  preservesFaces : ∀ e,RationalLattice.PreservesFaces (filtration (D.owner e))
    (lattice (D.owner e)) (translate e) (linearPart e) s
  ownPhysical : ∀ e y,physical (D.owner e) (translate e*linearPart e y)=
    unitShift D e • physical (D.owner e) y
attribute [instance] MarginalFaceData.group MarginalFaceData.topology
  MarginalFaceData.topGroup MarginalFaceData.t2

include hsk hw hmono hH in
 

theorem own_lifts_from_faces {s : ℕ} (M : MarginalFaceData D c H Γ π q s) :
    ∃ A : Fin D.pairs → shears (R:=ℝ) w,
      ∀ j e,D.owner e=j → ∀ z,
        π j (q (expQuotient c Γ (A e • z)))=
          unitShift D e • π j (q (expQuotient c Γ z)) := by
  have hex (e : Fin D.pairs) : ∃ A : shears (R:=ℝ) w,
      ∀ z,M.projection (D.owner e) (canonicalExp c (A • z))=
        M.translate e*M.linearPart e (M.projection (D.owner e) (canonicalExp c z)) := by
    obtain ⟨A,hA,_⟩:=exists_face_lift c (M.chart (D.owner e)) hsk (M.secondKind _)
      H (M.filtration _) w (M.weights _) hw (M.positive _) hmono (M.monotone _)
      hH (M.adapted _) (M.projection _) (M.continuous _) (M.onto _)
      (M.lattice _) (M.discrete _) (M.compactReps _) (M.translate e) (M.translate_mem e)
      (M.linearPart e) (M.linearContinuous e) s (M.terminal _) (M.preservesFaces e)
    refine ⟨A⁻¹,?_⟩
    intro z
    exact hA z
  choose A hA using hex
  refine ⟨A,?_⟩
  intro j e he z
  subst j
  rw [M.physicalProjection,M.physicalProjection,hA,M.ownPhysical]

end ConstructedWordPlan.GlobalWordPlan
end
 
end

section
 

 

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ProbabilityMixtures
variable {I X Y : Type*} [Fintype I] [Nonempty I]
variable [MeasurableSpace X] [MeasurableSpace Y]

lemma finiteAverage_apply (μ : I → ProbabilityMeasure X) (S : Set X) :
    (finiteAverage μ : Measure X) S =
      (Fintype.card I : ℝ≥0∞)⁻¹ * ∑ i,(μ i : Measure X) S := by
  simp [finiteAverage,Measure.finsetSum_apply]

lemma finiteAverage_lower (μ : I → ProbabilityMeasure X) (S : Set X)
    (a : ℝ≥0∞) (ha : ∀ i,a ≤ (μ i : Measure X) S) :
    a ≤ (finiteAverage μ : Measure X) S := by
  rw [finiteAverage_apply]
  calc
    a = (Fintype.card I : ℝ≥0∞)⁻¹ * ∑ _i : I,a := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [← mul_assoc,ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _),one_mul]
    _ ≤ _ := mul_le_mul_right (Finset.sum_le_sum fun i _=>ha i) _

variable [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
variable [SecondCountableTopology X]

lemma intervalPush_apply (μ : ProbabilityMeasure X) (h : C(ℝ×X,Y))
    (S : Set Y) (hS : MeasurableSet S) :
    (intervalPush μ h : Measure Y) S =
      ∫⁻ t,(μ : Measure X) {x | h (t,x)∈S} ∂unitTime := by
  change ((unitTime.prod (μ:Measure X)).map h) S=_
  rw [Measure.map_apply h.continuous.measurable hS,
    Measure.prod_apply (h.continuous.measurable hS)]
  rfl

lemma intervalPush_lower (μ : ProbabilityMeasure X) (h : C(ℝ×X,Y))
    (S : Set Y) (hS : MeasurableSet S) (a : ℝ≥0∞)
    (ha : ∀ᵐ t ∂unitTime,a ≤ (μ : Measure X) {x | h (t,x)∈S}) :
    a ≤ (intervalPush μ h : Measure Y) S := by
  rw [intervalPush_apply μ h S hS]
  simpa using (lintegral_mono_ae ha :
    (∫⁻ _t,a ∂unitTime) ≤ ∫⁻ t,(μ:Measure X) {x | h (t,x)∈S} ∂unitTime)

 

theorem betaResidue_lower (μ : I → ProbabilityMeasure X)
    (h : I → C(ℝ×X,Y)) (S : Set Y) (hS : MeasurableSet S) (a : ℝ≥0∞)
    (ha : ∀ i,∀ᵐ t ∂unitTime,a ≤ (μ i : Measure X) {x | h i (t,x)∈S}) :
    a ≤ (finiteAverage (fun i=>intervalPush (μ i) (h i)) : Measure Y) S := by
  exact finiteAverage_lower _ S a (fun i=>intervalPush_lower (μ i) (h i) S hS a (ha i))

end ProbabilityMixtures
end
 
end

section
 

noncomputable section
open MeasureTheory Filter Topology
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces CubeLocalHaar MalcevCharacters
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {F : Factorization c Γ s K P L} {r : Fin F.period} (C : F.ResidueCover r)

abbrev pointFiltration (_C : F.ResidueCover r) := CubeMaxFiltration.filtration F.state.domain.filtration
  (Finset.univ : Finset Empty)
abbrev pointLattice := cubeLattice (ι:=Empty) F.state.domain.filtration C.lattice

 

structure PivotChart where
  dim : ℕ
  chart : RealCoordinates (CubeGroup (ι:=Empty) (F:=F)) dim
  secondKind : SecondKind chart
  integer_lattice : ∀ g,g∈C.pointLattice ↔ ∀ i,∃ z : ℤ,chart.coord g i=z
  weights : Fin dim → ℕ
  monotone : Monotone weights
  positive : ∀ i,0<weights i
  bounded : ∀ i,weights i ≤ s
  adapted : ∀ j g,g∈C.pointFiltration.level j ↔
    ∀ i : Fin dim,weights i<j → chart.coord g i=0

 

omit [IsTopologicalGroup G] in
theorem exists_pivotChart [IsTopologicalGroup G] : Nonempty C.PivotChart := by
  let H:=F.state.domain.filtration
  have h01:=F.state.domain.zero_top.trans F.state.domain.one_top.symm
  obtain ⟨d,e,he,hΓ,hadapt⟩:=CubeRationalCharts.cube_chart_from_base (ι:=Empty)
    C.chart F.state.domain.cutoff H C.adapted h01 s F.state.domain.terminal
    C.lattice C.integer_lattice
  choose q hq hqH using hadapt
  obtain ⟨w,hmono,hw,hs,hH⟩:=exists_adapted_weights e
    (CubeMaxFiltration.filtration H Finset.univ)
    (CubeMaxFiltration.filtration_zero H Finset.univ)
    (CubeMaxFiltration.filtration_one H Finset.univ h01) s
    (CubeMaxFiltration.filtration_bot H Finset.univ F.state.domain.terminal) q hqH
  exact ⟨⟨d,e,he,hΓ,w,hmono,hw,hs,hH⟩⟩

def pivotChart : C.PivotChart := Classical.choice C.exists_pivotChart

 
def pivotImage (β : ℝ) : C(C.CubeSpace (ι:=Empty),G⧸Γ) :=
  ⟨fun x=>F.smoothLimit β • C.pointImage x,
    (continuous_const : Continuous (fun _ : C.CubeSpace (ι:=Empty)=>F.smoothLimit β)).smul C.pointImage_continuous⟩

variable [MeasurableSpace (C.CubeSpace (ι:=Empty))] [BorelSpace (C.CubeSpace (ι:=Empty))]
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

lemma pivotImage_event (β : ℝ) (S : Set (G⧸Γ)) (hS : MeasurableSet S) :
    ((C.haar (ι:=Empty)).map (C.pivotImage β) : Measure (G⧸Γ)) S =
      (C.pointHaar : Measure (G⧸Γ)) {x | F.smoothAction (β,x)∈S} := by
  rw [ProbabilityMeasure.toMeasure_map,Measure.map_apply (C.pivotImage β).continuous.measurable hS]
  rw [pointHaar,ProbabilityMeasure.toMeasure_map,Measure.map_apply C.pointImage_continuous.measurable]
  · rfl
  · exact ((continuous_const : Continuous (fun _ : G⧸Γ=>F.smoothLimit β)).smul continuous_id).measurable hS

end AllLevelFactorization.Factorization.ResidueCover

end
end
end

end OAI
