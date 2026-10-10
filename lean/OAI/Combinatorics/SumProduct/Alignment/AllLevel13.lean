import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice22
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice27
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
end

section
 

 

noncomputable section
namespace RationalLattice
open MalcevCharacters MalcevWeightedCoordinates
variable {G H : Type} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable {n m : ℕ} (c : RealCoordinates G n) (d : RealCoordinates H m)
variable (A : CubeFaces.Filtration G) (F : G →* H)

 

structure ImageGeometry where
  dim : ℕ
  chart : RealCoordinates F.range dim
  secondKind : SecondKind chart
  weights : Fin dim → ℕ
  positive : ∀ i,0<weights i
  monotone : Monotone weights
  adapted : ∀ l (g : F.range),g∈(A.level l).map F.rangeRestrict ↔
    ∀ i,weights i<l → chart.coord g i=0
  rational : ∀ g,IsRational chart g → IsRational d (g:H)

variable (hsk : SecondKind c) (hF : Continuous F)
variable (hrat : ∀ g,IsRational c g → IsRational d (F g))
variable (w : Fin n → ℕ) (hw : ∀ i,0<w i) (hmono : Monotone w)
variable (hA : ∀ l (g : G),g∈A.level l ↔ ∀ i,w i<l → c.coord g i=0)
include hsk hF hrat hw hmono hA in
 
theorem imageGeometry_nonempty : Nonempty (ImageGeometry d A F) := by
  obtain ⟨p,hp⟩:=exists_log_matrix c d hsk F hF hrat
  obtain ⟨E⟩:=RationalEchelon.chart_exists (LinearMap.ker p)
  exact ⟨{ dim:=E.freeSet.card
           chart:=QuotientLogImage.imageSecondChart c d hsk F hF p hp E A w hw hmono hA
           secondKind:=QuotientLogImage.imageSecondChart_secondKind c d hsk F hF p hp E A w hw hmono hA
           weights:=fun i=>w (E.free i)
           positive:=fun i=>hw (E.free i)
           monotone:=hmono.comp E.free.monotone
           adapted:=QuotientLogImage.imageSecondChart_adapted c d hsk F hF p hp E A w hw hmono hA
           rational:=QuotientLogImage.imageEmbedding_rational c d hsk F hF p hp E A w hw hmono hA }⟩

namespace ImageGeometry
variable (T : ImageGeometry d A F)
variable (Γ : Subgroup H) (hΓ : ∀ g : H,g∈Γ ↔ ∀ i,∃ z : ℤ,d.coord g i=z)
variable (σ : H) (hσ : IsRational d σ)

include T hΓ hσ in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma level_compact_reps (l : ℕ) :
    CompactGroupProducts.HasCompactReps ((A.level l).map F.rangeRestrict)
      ((CubeLocalHaar.conjugateLattice Γ σ).comap F.range.subtype) :=
  rationalConjugate_compact_reps d T.chart T.secondKind F.range.subtype
    continuous_subtype_val Subtype.val_injective T.rational Γ hΓ σ hσ _
    T.weights T.monotone l (T.adapted l)

include T hΓ hσ in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma quotient_compactSpace :
    CompactSpace (F.range⧸(CubeLocalHaar.conjugateLattice Γ σ).comap F.range.subtype) :=
  rationalConjugate_compactSpace d T.chart T.secondKind F.range.subtype
    continuous_subtype_val Subtype.val_injective T.rational Γ hΓ σ hσ

end ImageGeometry

end RationalLattice
end
 
end

section
noncomputable section
namespace RationalLattice
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (Γ : Subgroup G)

namespace ImageGeometry
variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
variable (A : CubeFaces.Filtration K) (F : K →* G) (T : ImageGeometry c A F)
variable (B : CoveredLattice c Γ) (σ : G) (hσ : IsRational c σ)
include B T hσ in
omit [TopologicalSpace K] [IsTopologicalGroup K] in
lemma covered_level_compact_reps (l : ℕ) :
    CompactGroupProducts.HasCompactReps ((A.level l).map F.rangeRestrict)
      ((CubeLocalHaar.conjugateLattice Γ σ).comap F.range.subtype) := by
  obtain ⟨C,hC,hCJ,hrep⟩:=T.level_compact_reps c A F B.small B.integer σ hσ l
  exact ⟨C,hC,hCJ,fun g hg=>by
    obtain ⟨a,ha,hag⟩:=hrep g hg
    exact ⟨a,ha,B.le hag⟩⟩
include B T hσ in
omit [TopologicalSpace K] [IsTopologicalGroup K] in
lemma covered_quotient_compactSpace :
    CompactSpace (F.range⧸(CubeLocalHaar.conjugateLattice Γ σ).comap F.range.subtype) := by
  let : CompactSpace (F.range⧸(CubeLocalHaar.conjugateLattice B.small σ).comap F.range.subtype):=
    T.quotient_compactSpace c A F B.small B.integer σ hσ
  let Δ:=(CubeLocalHaar.conjugateLattice B.small σ).comap F.range.subtype
  let Θ:=(CubeLocalHaar.conjugateLattice Γ σ).comap F.range.subtype
  have hle : Δ≤Θ:=fun _ h=>B.le h
  exact (CosetCover.surjective_map Δ Θ hle).compactSpace (CosetCover.continuous_map Δ Θ hle)

end ImageGeometry
end RationalLattice
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter
namespace ProbabilityMixtures
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
variable [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
lemma empirical_map (M : ℕ) (q : ℕ → X) (f : C(X,Y)) :
    (empirical M q).map f=
      empirical M (fun k=>f (q k)) := by
  classical
  apply Subtype.ext
  change Measure.map f (empirical M q : Measure X)=
    (empirical M (fun k=>f (q k)) : Measure Y)
  by_cases h : 0<M
  · let : Nonempty (Fin M):=⟨⟨0,h⟩⟩
    simp only [empirical,h,↓reduceDIte]
    change Measure.map f ((Fintype.card (Fin M):ℝ≥0∞)⁻¹ •
      ∑ k : Fin M,Measure.dirac (q k.val))=
      (Fintype.card (Fin M):ℝ≥0∞)⁻¹ • ∑ k : Fin M,Measure.dirac (f (q k.val))
    rw [Measure.map_smul,Measure.map_finset_sum]
    · simp only [Measure.map_dirac]
    · exact f.continuous.measurable.aemeasurable
    · exact f.continuous.measurable.aemeasurable
  · simp only [empirical,h,↓reduceDIte]
    exact Measure.map_dirac (q 0)
 

omit [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y] in
lemma empirical_preimage (M : ℕ) (q : ℕ → X) (f : X → Y) (S : Set Y) :
    (empirical M q : Measure X) (f ⁻¹' S)=
      (empirical M (fun k=>f (q k)) : Measure Y) S := by
  classical
  by_cases h : 0<M
  · let : Nonempty (Fin M):=⟨⟨0,h⟩⟩
    simp only [empirical,h,↓reduceDIte]
    change ((Fintype.card (Fin M):ℝ≥0∞)⁻¹ • ∑ k : Fin M,Measure.dirac (q k.val)) (f ⁻¹' S)=
      ((Fintype.card (Fin M):ℝ≥0∞)⁻¹ • ∑ k : Fin M,Measure.dirac (f (q k.val))) S
    simp only [Measure.smul_apply,Measure.finsetSum_apply,Measure.dirac_apply]
    rfl
  · simp only [empirical,h,↓reduceDIte]
    change Measure.dirac (q 0) (f ⁻¹' S)=Measure.dirac (f (q 0)) S
    simp only [Measure.dirac_apply]
    rfl

end ProbabilityMixtures

namespace AllLevelFactorization.Factorization
open RationalLattice CubeFaces
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Δ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (F : Factorization c Δ s K P L)
variable (C : (r : Fin F.period) → F.ResidueCover r)
variable [∀ r,MeasurableSpace ((C r).CubeSpace (ι:=Empty))]
variable [∀ r,BorelSpace ((C r).CubeSpace (ι:=Empty))]
variable [MeasurableSpace (G⧸Δ)] [BorelSpace (G⧸Δ)] [CompactSpace (G⧸Δ)]
variable [SecondCountableTopology (G⧸Δ)] [MeasurableSingletonClass (G⧸Δ)]
variable (Γ : Subgroup G) (hle : Δ≤Γ)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)] [MeasurableSingletonClass (G⧸Γ)]

def coveredPointMixture : ProbabilityMeasure (G⧸Γ):=
  CosetCover.probability Δ Γ hle (F.pointMixture C)

def coveredEmpiricalPointLaw (N : ℕ) : ProbabilityMeasure (G⧸Γ):=
  ProbabilityMixtures.empirical ⌊L (F.state.subseq N)⌋₊
    (fun k=>QuotientGroup.mk (P (F.state.subseq N) (k:ℤ)))

omit [IsTopologicalGroup G] [CompactSpace (G⧸Δ)] [SecondCountableTopology (G⧸Δ)] in
lemma coveredEmpiricalPointLaw_eq (N : ℕ) :
    F.coveredEmpiricalPointLaw Γ N=CosetCover.probability Δ Γ hle (F.empiricalPointLaw N) := by
  change ProbabilityMixtures.empirical ⌊L (F.state.subseq N)⌋₊
    (fun k=>QuotientGroup.mk (P (F.state.subseq N) (k:ℤ))) =
    (ProbabilityMixtures.empirical ⌊L (F.state.subseq N)⌋₊
      (fun k=>(QuotientGroup.mk (P (F.state.subseq N) (k:ℤ)) : G⧸Δ))).map
      (CosetCover.map Δ Γ hle)
  exact (ProbabilityMixtures.empirical_map ⌊L (F.state.subseq N)⌋₊
    (fun k=>(QuotientGroup.mk (P (F.state.subseq N) (k:ℤ)) : G⧸Δ))
    ⟨CosetCover.map Δ Γ hle,CosetCover.continuous_map Δ Γ hle⟩).symm

 

theorem covered_weak_point_law (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop) :
    Tendsto (F.coveredEmpiricalPointLaw Γ) atTop (𝓝 (F.coveredPointMixture C Γ hle)) := by
  have H:=ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    F.empiricalPointLaw (F.pointMixture C) (F.weak_point_law C hL ht)
    (CosetCover.continuous_map Δ Γ hle)
  exact H.congr (fun N=>(F.coveredEmpiricalPointLaw_eq Γ hle N).symm)

variable [CompactSpace (G⧸Γ)]
 
omit [MeasurableSingletonClass (G⧸Δ)] [MeasurableSingletonClass (G⧸Γ)] [CompactSpace (G⧸Γ)] in
lemma coveredPointMixture_integral (f : C(G⧸Γ,ℂ)) :
    (∫ y,f y ∂(F.coveredPointMixture C Γ hle : Measure _))=
      GlobalPointLaw.betaMixture (fun r=>(C r).pointHaar)
        (F.limitTest (f.comp ⟨CosetCover.map Δ Γ hle,CosetCover.continuous_map Δ Γ hle⟩)) := by
  change (∫ y,f y ∂((F.pointMixture C : Measure _).map (CosetCover.map Δ Γ hle)))=_
  rw [integral_map (CosetCover.continuous_map Δ Γ hle).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  exact F.pointMixture_integral C
    (f.comp ⟨CosetCover.map Δ Γ hle,CosetCover.continuous_map Δ Γ hle⟩)

end AllLevelFactorization.Factorization
end
 
end

section
 

 

noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace AllLevelFactorization
open RationalLattice CubeFaces
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} (c : RealCoordinates G n) (Γ : Subgroup G) (B : CoveredLattice c Γ)
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (F : Factorization c B.small s K P L)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)] [MeasurableSingletonClass (G⧸Γ)]

local instance smallMeasurable : MeasurableSpace (G⧸B.small):=borel _
local instance smallBorel : BorelSpace (G⧸B.small):=⟨rfl⟩
local instance smallCompact : CompactSpace (G⧸B.small):=by
  obtain ⟨S,hS,hrep⟩:=compact_reps_of_integerCoordinates c B.small B.integer
  exact (show CompactGroupProducts.HasCompactReps ⊤ B.small from
    ⟨S,hS,Set.subset_univ _,fun g _=>hrep g⟩).quotient_compactSpace
local instance smallT2 : T2Space (G⧸B.small):=by
  let : T2Space G:=c.coord.symm.t2Space
  let : DiscreteTopology B.small:=integerCoordinates_discrete c B.small B.integer
  let : IsClosed (B.small:Set G):=Subgroup.isClosed_of_discreteTopology
  infer_instance
local instance smallSecond : SecondCountableTopology (G⧸B.small):=by
  let : SecondCountableTopology G:=c.coord.secondCountableTopology
  infer_instance
local instance residueMeasurable (r : Fin F.period) :
    MeasurableSpace ((F.residueCover B.integer r).CubeSpace (ι:=Empty)):=borel _
local instance residueBorel (r : Fin F.period) :
    BorelSpace ((F.residueCover B.integer r).CubeSpace (ι:=Empty)):=⟨rfl⟩

 
def actualPointMixture : ProbabilityMeasure (G⧸Γ):=
  F.coveredPointMixture (fun r=>F.residueCover B.integer r) Γ B.le

 

lemma actual_weak_point_law (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop) :
    Tendsto (fun N=>ProbabilityMixtures.empirical ⌊L (F.state.subseq N)⌋₊
      (fun k=>(QuotientGroup.mk (P (F.state.subseq N) (k:ℤ)) : G⧸Γ)))
      atTop (𝓝 (actualPointMixture c Γ B F)) :=
  F.covered_weak_point_law (fun r=>F.residueCover B.integer r) Γ B.le hL ht

 

lemma actual_weak_point_law_map {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [MeasurableSingletonClass Y] (q : C(G⧸Γ,Y))
    (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop) :
    Tendsto (fun N=>ProbabilityMixtures.empirical ⌊L (F.state.subseq N)⌋₊
      (fun k=>q (QuotientGroup.mk (P (F.state.subseq N) (k:ℤ)))))
      atTop (𝓝 ((actualPointMixture c Γ B F).map q)) := by
  have H:=ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (actual_weak_point_law c Γ B F hL ht) q.continuous
  apply H.congr
  intro N
  exact ProbabilityMixtures.empirical_map _ _ q

 

omit [MeasurableSingletonClass (G⧸Γ)] in
lemma actualPointMixture_integral (f : C(G⧸Γ,ℂ)) :
    (∫ y,f y ∂(actualPointMixture c Γ B F : Measure _))=
      GlobalPointLaw.betaMixture (fun r=>(F.residueCover B.integer r).pointHaar)
        (F.limitTest (f.comp ⟨CosetCover.map B.small Γ B.le,
          CosetCover.continuous_map B.small Γ B.le⟩)) := by
  let : CompactSpace (G⧸Γ):=covered_quotient_compact c Γ B
  exact F.coveredPointMixture_integral (fun r=>F.residueCover B.integer r) Γ B.le f

variable (K : Filtration G) (w : Fin n → ℕ)
variable (hsk : MalcevCharacters.SecondKind c) (hmono : Monotone w)
variable (hK : ∀ k (g : G),g∈K.level k ↔ ∀ i,w i<k → c.coord g i=0)
variable (h0 : K.level 0=⊤) (h1 : K.level 1=⊤) (hs : K.level (s+1)=⊥)
variable (P : ℕ → ℤ → G) (hP : ∀ N,P N∈CubePolynomials.polynomials K 0)
variable (L : ℕ → ℝ) (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
include hsk hmono hK h0 h1 hs hP hL ht in
 

theorem actual_point_law_exists :
    ∃ F : Factorization c B.small s K P L,
      Tendsto (fun N=>ProbabilityMixtures.empirical ⌊L (F.state.subseq N)⌋₊
        (fun k=>(QuotientGroup.mk (P (F.state.subseq N) (k:ℤ)) : G⧸Γ)))
        atTop (𝓝 (actualPointMixture c Γ B F)) := by
  let F:=coveredFactorization c Γ B s K w hsk hmono hK h0 h1 hs P hP L hL
  exact ⟨F,actual_weak_point_law c Γ B F hL ht⟩

end AllLevelFactorization

end
end
end

end OAI
