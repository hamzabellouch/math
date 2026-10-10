import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.WeightedLinear01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open MeasureTheory Filter Topology Set TopologicalSpace
end
 
end

section
 

noncomputable section
open MeasureTheory Filter Topology Set MvPolynomial
namespace WeightedBoxes
open PolynomialShearPoint FilteredShears.PolynomialShears
variable {σ : Type*} [Fintype σ]

def boxLaw (w : σ → ℕ) (E : ℝ) : ProbabilityMeasure (σ → ℝ) :=
  ⟨normalizedRestriction volume (weightedBox w (max E 1)),by
    constructor
    rw [normalizedRestriction,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel ((ENNReal.toReal_pos_iff.mp (rect_volume_pos _ (fun i=>
      pow_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) _))).1.ne') (rect_finite _)⟩

lemma boxLaw_eq {w : σ → ℕ} {E : ℝ} (hE : 1≤E) :
    (boxLaw w E : Measure (σ → ℝ))=normalizedRestriction volume (weightedBox w E) := by
  exact congrArg (fun t=>normalizedRestriction volume (weightedBox w t)) (max_eq_left hE)

omit [Fintype σ] in
lemma pointMap_continuous (A : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ) :
    Continuous (pointMap A) := by
  apply continuous_pi
  intro i
  exact (A (X i)).continuous_eval

 

theorem boxLaw_shear_invariance (w : σ → ℕ) (hw : ∀ i,0<w i)
    (A : shears (R:=ℝ) w) :
    ∃ ε : ℝ → ℝ,Tendsto ε atTop (𝓝 0) ∧
      ∀ E B,MeasurableSet B →
        |((boxLaw w E).map (pointMap A.val.toAlgHom) : Measure (σ → ℝ)).real B-
          (boxLaw w E : Measure (σ → ℝ)).real B|≤ε E := by
  let p:σ → MvPolynomial σ ℝ:=fun i=>A.val (X i)-X i
  have hp (i : σ) : StrictDegree w (w i) (p i) := A.property i
  obtain ⟨ε,hε,hb⟩:=weightedBoxLaw_invariance w hw p hp
  refine ⟨fun E=>ε (max E 1),hε.comp (tendsto_atTop_mono (fun E=>le_max_left E 1) tendsto_id),?_⟩
  intro E B hB
  have he : pointMap A.val.toAlgHom=(fun x i=>x i+eval x (p i)) := by
    funext x i
    simp [pointMap,p]
  change |((normalizedRestriction volume (weightedBox w (max E 1))).map
    (pointMap A.val.toAlgHom)).real B-(normalizedRestriction volume
      (weightedBox w (max E 1))).real B|≤_
  rw [he]
  exact hb _ B hB

end WeightedBoxes
end
 
end

section
 

noncomputable section
open MeasureTheory Filter Topology Set TopologicalSpace
namespace RationalLattice
open MalcevCharacters WeightedBoxes PolynomialShearPoint FilteredShears.PolynomialShears
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (H : CubeFaces.Filtration G) (w : Fin n → ℕ) (hw : ∀ i,0<w i)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)
variable (Γ : Subgroup G) [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

def expQuotient : C((Fin n → ℝ),G⧸Γ) :=
  ⟨fun x=>QuotientGroup.mk (canonicalExp c x),
    continuous_quot_mk.comp (canonicalExp_continuous c)⟩

def weightedCoverLaw (E : ℝ) : ProbabilityMeasure (G⧸Γ) :=
  (boxLaw w E).map (expQuotient c Γ)

include hsk hw hH in
 

lemma weightedCover_translation_invariance [PseudoMetrizableSpace (G⧸Γ)]
    [SeparableSpace (G⧸Γ)] (a : G) :
    ∃ ε : ℝ → ℝ,Tendsto ε atTop (𝓝 0) ∧
      ∀ E A,MeasurableSet A →
        |((weightedCoverLaw c w Γ E).map (a • ·) : Measure (G⧸Γ)).real A-
          (weightedCoverLaw c w Γ E : Measure (G⧸Γ)).real A|≤ε E := by
  let : PseudoMetricSpace (G⧸Γ):=pseudoMetrizableSpacePseudoMetric (G⧸Γ)
  let D (x : Fin n → ℝ):=canonicalLog c (a*canonicalExp c x)-x
  obtain ⟨A,hA,_⟩:=exists_shear w hw D (fun i=>
    log_left_displacement_weighted c hsk H w hH hw a i)
  obtain ⟨ε,hε,hεb⟩:=boxLaw_shear_invariance w hw A
  refine ⟨ε,hε,?_⟩
  intro E B hB
  apply AsymptoticProbability.pushed_event_bound (boxLaw w E) (expQuotient c Γ)
    (expQuotient c Γ).continuous.measurable (pointMap A.val.toAlgHom)
    (pointMap_continuous A.val.toAlgHom).measurable (a • ·) (measurable_const_smul a)
    _ (hεb E) B hB
  intro x
  rw [hA]
  have he : x+D x=canonicalLog c (a*canonicalExp c x) := by dsimp [D]; abel
  rw [he]
  change (QuotientGroup.mk (canonicalExp c (canonicalLog c (a*canonicalExp c x))) : G⧸Γ)=
    a • QuotientGroup.mk (canonicalExp c x)
  rw [canonicalExp_log]
  rfl

include hsk hw hH in
 

theorem weightedCover_weak_haar
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (μ : ProbabilityMeasure (G⧸Γ))
    [SMulInvariantMeasure G (G⧸Γ) (μ:Measure (G⧸Γ))] :
    Tendsto (weightedCoverLaw c w Γ) atTop (𝓝 μ) := by
  let : T2Space G:=c.coord.symm.t2Space
  let : SecondCountableTopology G:=c.coord.secondCountableTopology
  let : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  let : IsClosed (Γ:Set G):=Subgroup.isClosed_of_discreteTopology
  obtain ⟨K,hK,hrep⟩:=compact_reps_of_integerCoordinates c Γ hΓ
  let : CompactSpace (G⧸Γ):=(show CompactGroupProducts.HasCompactReps ⊤ Γ from
    ⟨K,hK,Set.subset_univ _,fun g _=>hrep g⟩).quotient_compactSpace
  let : MetricSpace (G⧸Γ):=metrizableSpaceMetric (G⧸Γ)
  apply AsymptoticProbability.weak_haar_of_unique (G:=G) (weightedCoverLaw c w Γ) μ
  · intro ν hν
    let :=hν
    obtain ⟨hair,hhair,hunique⟩:=existsUnique_coordinateHaar c Γ hΓ
    exact (hunique ν hν).trans (hunique μ inferInstance).symm
  · intro a
    obtain ⟨ε,hε,hb⟩:=weightedCover_translation_invariance c hsk H w hw hH Γ a
    exact ⟨ε,hε,Eventually.of_forall hb⟩

end RationalLattice
end
 
end

section
 

noncomputable section
open MeasureTheory Filter Topology Set TopologicalSpace
namespace AsymptoticProbability
lemma map_event_bound {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    (μ ν : ProbabilityMeasure Y) (q : Y → X) (hq : Measurable q) {ε : ℝ}
    (h : ∀ B,MeasurableSet B → |(μ:Measure Y).real B-(ν:Measure Y).real B|≤ε) :
    ∀ A,MeasurableSet A →
      |(μ.map q : Measure X).real A-
        (ν.map q : Measure X).real A|≤ε := by
  intro A hA
  change |(Measure.map q (μ:Measure Y)).real A-(Measure.map q (ν:Measure Y)).real A|≤ε
  rw [map_measureReal_apply hq hA,map_measureReal_apply hq hA]
  exact h _ (hA.preimage hq)
end AsymptoticProbability

namespace RationalLattice
open MalcevCharacters WeightedBoxes PolynomialShearPoint FilteredShears.PolynomialShears
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (H : CubeFaces.Filtration G) (w : Fin n → ℕ) (hw : ∀ i,0<w i)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)
variable (Γ : Subgroup G) [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

def weightedShearLaw (A : shears (R:=ℝ) w) (E : ℝ) : ProbabilityMeasure (G⧸Γ) :=
  ((boxLaw w E).map (pointMap A.val.toAlgHom)).map (expQuotient c Γ)

include hw in
omit [IsTopologicalGroup G] in
lemma weightedShearLaw_event_bound (A : shears (R:=ℝ) w) :
    ∃ ε : ℝ → ℝ,Tendsto ε atTop (𝓝 0) ∧
      ∀ E B,MeasurableSet B →
        |(weightedShearLaw c w Γ A E : Measure (G⧸Γ)).real B-
          (weightedCoverLaw c w Γ E : Measure (G⧸Γ)).real B|≤ε E := by
  obtain ⟨ε,hε,hb⟩:=boxLaw_shear_invariance w hw A
  exact ⟨ε,hε,fun E=>AsymptoticProbability.map_event_bound _ _ _
    (expQuotient c Γ).continuous.measurable (hb E)⟩

include hsk hw hH in
 

theorem weightedShear_weak_haar
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (μ : ProbabilityMeasure (G⧸Γ))
    [SMulInvariantMeasure G (G⧸Γ) (μ:Measure (G⧸Γ))]
    (A : shears (R:=ℝ) w) :
    Tendsto (weightedShearLaw c w Γ A) atTop (𝓝 μ) := by
  let : T2Space G:=c.coord.symm.t2Space
  let : SecondCountableTopology G:=c.coord.secondCountableTopology
  let : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  let : IsClosed (Γ:Set G):=Subgroup.isClosed_of_discreteTopology
  obtain ⟨K,hK,hrep⟩:=compact_reps_of_integerCoordinates c Γ hΓ
  let : CompactSpace (G⧸Γ):=(show CompactGroupProducts.HasCompactReps ⊤ Γ from
    ⟨K,hK,Set.subset_univ _,fun g _=>hrep g⟩).quotient_compactSpace
  let : MetricSpace (G⧸Γ):=metrizableSpaceMetric (G⧸Γ)
  obtain ⟨ε,hε,hb⟩:=weightedShearLaw_event_bound c w hw Γ A
  apply AsymptoticProbability.same_weak_limit (weightedCoverLaw c w Γ)
    (weightedShearLaw c w Γ A) hε _ (weightedCover_weak_haar c hsk H w hw hH Γ hΓ μ)
  exact Eventually.of_forall (fun E B hB=>by rw [abs_sub_comm]; exact hb E B hB)

include hsk hw hH in
 

theorem weightedShear_pointImage_limit {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (μ : ProbabilityMeasure (G⧸Γ))
    [SMulInvariantMeasure G (G⧸Γ) (μ:Measure (G⧸Γ))]
    (A : shears (R:=ℝ) w) (q : C(G⧸Γ,X)) :
    Tendsto (fun E=>(weightedShearLaw c w Γ A E).map q)
      atTop (𝓝 (μ.map q)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (weightedShear_weak_haar c hsk H w hw hH Γ hΓ μ A) q.continuous

end RationalLattice
end
 
end

section
 

noncomputable section
namespace PolynomialShearPoint
open FilteredShears.PolynomialShears
variable {σ J : Type*} (w : σ → ℕ)

 

instance shearPointAction : MulAction (shears (R:=ℝ) w) (σ → ℝ) where
  smul A x := pointMap A.val.symm.toAlgHom x
  one_smul x := pointMap_id x
  mul_smul A B x := by
    change pointMap (A*B).val.symm.toAlgHom x =
      pointMap A.val.symm.toAlgHom (pointMap B.val.symm.toAlgHom x)
    rw [pointMap_comp]
    rfl

@[simp] lemma shear_smul (A : shears (R:=ℝ) w) (x : σ → ℝ) :
    A • x = pointMap A.val.symm.toAlgHom x := rfl

abbrev CoverGroup (J : Type*) := shears (R:=ℝ) w × Multiplicative (J → ℤ)
abbrev CoverState (J : Type*) := (σ → ℝ) × (J → ℤ)

instance coverAction : MulAction (CoverGroup w J) (CoverState (σ:=σ) J) where
  smul A x := (A.1 • x.1, A.2.toAdd + x.2)
  one_smul x := by
    change ((1 : shears (R:=ℝ) w) • x.1, (0 : J → ℤ)+x.2)=x
    simp
  mul_smul A B x := by
    change ((A.1*B.1) • x.1, (A.2.toAdd+B.2.toAdd)+x.2)=
      (A.1 • (B.1 • x.1), A.2.toAdd+(B.2.toAdd+x.2))
    rw [mul_smul,add_assoc]

@[simp] lemma cover_smul_fst (A : CoverGroup w J) (x : CoverState (σ:=σ) J) :
    (A • x).1 = A.1 • x.1 := rfl
@[simp] lemma cover_smul_snd (A : CoverGroup w J) (x : CoverState (σ:=σ) J) :
    (A • x).2 = A.2.toAdd + x.2 := rfl

lemma cover_lowerCentralSeries {s : ℕ} (hs : 1 ≤ s) (hw : ∀ i, w i ≤ s) :
    (⊤ : Subgroup (CoverGroup w J)).lowerCentralSeries s = ⊥ := by
  rw [Subgroup.top_lowerCentralSeries_prod,shear_lowerCentralSeries_eq_bot w hw]
  have ha : (⊤ : Subgroup (Multiplicative (J → ℤ))).lowerCentralSeries s = ⊥ := by
    apply le_antisymm _ bot_le
    calc
      _ ≤ (⊤ : Subgroup (Multiplicative (J → ℤ))).lowerCentralSeries 1 :=
        Subgroup.lowerCentralSeries_antitone _ hs
      _ = ⊥ := by simp [Subgroup.lowerCentralSeries_succ,CommGroup.center_eq_top]
  rw [ha,Subgroup.bot_prod_bot]

end PolynomialShearPoint

end
end
end

end OAI
