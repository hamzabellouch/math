import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeRational01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open scoped BigOperators Topology
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology commutatorElement
open Filter MeasureTheory
namespace BaseCubeLaw
open CubeFaces CubeLocalHaar RationalLattice MalcevCharacters
open CubeHorizontalIrrationality ComparableBoxLeibman CubeTaylorExpansion
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n : ℕ} (c : RealCoordinates G n) (H : Filtration G)
variable (q : ℕ → ℕ) (hq : ∀ k,q k ≤ n)
variable (hH : ∀ k (x : G),x∈H.level k ↔ ∀ i : Fin n,i.val < q k → c.coord x i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)

include hH hΓ in
omit [IsTopologicalGroup G] in
lemma level_compact_reps (k : ℕ) : CompactGroupProducts.HasCompactReps (H.level k) Γ := by
  have he : H.level k=coordinateTail c (q k) := by
    ext g
    exact hH k g
  rw [he]
  exact coordinateTail_compact_reps c Γ hΓ (q k)

 
def Irrational (s : ℕ) (a : ℕ→∀ k : ℕ,H.level k) (L : ℕ→ℝ) : Prop :=
  ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
    ξ≠1 → Continuous ξ → RationalCharacter Γ ξ →
    (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
    (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
      ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
        ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
    Tendsto (fun N : ℕ=>‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(L N)^j) atTop atTop

variable [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]
variable [BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]

include hΓ in
 

theorem exists_scaled_cube_law (h01 : H.level 0=H.level 1)
    (s : ℕ) (hs : H.level (s+1)=⊥) :
    ∃ μ : ProbabilityMeasure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ),
      SMulInvariantMeasure (cube H (Finset.univ : Finset ι) 0) _ (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)) ∧
      ∀ (v : ℕ) (e : Option ι≃Fin v) (L : ℕ→ℝ),Tendsto L atTop atTop →
      ∀ (a : ℕ→∀ k : ℕ,H.level k),Irrational H Γ s a L →
      ∀ (c₀ C₀ : ℝ),0 < c₀ → 0 < C₀ →
      ∀ (d₀ : ℕ),0 < d₀ → ∀ (r : Fin v→ℤ)
        (T : Set C(((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ),ℂ)),
        IsCompact T → ∀ η : ℝ,0 < η → ∀ᶠ N : ℕ in atTop,
        ∀ lo hi : Fin v→ℝ,
          (∀ i,c₀*L N ≤ hi i-lo i) →
          (∀ i,-C₀*L N ≤ lo i ∧ hi i ≤ C₀*L N) →
          ∀ f : C(((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ),ℂ),
            f∈T →
            ‖(𝔼 x∈integerBox v lo hi,f (QuotientGroup.mk
              (cubePolynomial c H (fun k=> {i : Fin n | i.val < q k})
                (fun k g=>hH k g) (a N) s
                (fun i=>((r (e i)+(d₀:ℤ)*x (e i):ℤ):ℝ)))))-
                (∫ y,f y ∂(μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)))‖ < η := by
  let : T2Space G:=c.coord.symm.t2Space
  let : SecondCountableTopology G:=c.coord.secondCountableTopology
  let : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  obtain ⟨μ,hμ,_⟩:=existsUnique_cubeHaar (ι:=ι) H h01 s hs Γ
    (level_compact_reps c H q hH Γ hΓ) (isDiscrete_iff_discreteTopology.mpr inferInstance)
  let : SMulInvariantMeasure (cube H (Finset.univ : Finset ι) 0) _ (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)):=hμ
  obtain ⟨D,cc,hsk,hcc,hlevels⟩:=CubeRationalCharts.cube_chart_from_base (ι:=ι)
    c q H hH h01 s hs Γ hΓ
  choose p hp hp' using hlevels
  let : MetricSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ):=
    coordinateQuotientMetric cc (cubeLattice H Γ) hcc
  refine ⟨μ,hμ,?_⟩
  intro v e L ht a hirr c₀ C₀ hc₀ hC₀ d₀ hd₀ r T hT η hη
  exact haar_limit_compact_scaled (t:=D) (d:=0) c H
    (fun k=> {i : Fin n | i.val < q k}) (fun k g=>hH k g) Γ h01 s hs e
    cc hsk p hp hp' hcc rfl L ht (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)) a hirr c₀ C₀ hc₀ hC₀ d₀ hd₀ r T hT η hη

end BaseCubeLaw
end
 
end

section
 

 

noncomputable section
open scoped Topology commutatorElement
open Filter
namespace AllLevelFactorization.Factorization
open AllLevelDomains AllLevelStates RationalLattice CubeFaces MalcevCharacters
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (F : Factorization c Γ s K P L)

structure ResidueCover (r : Fin F.period) where
  lattice : Subgroup F.state.domain.Carrier
  chart : RealCoordinates F.state.domain.Carrier F.state.domain.dim
  secondKind : SecondKind chart
  integer_lattice : ∀ x,x∈lattice ↔ ∀ i,∃ z : ℤ,chart.coord x i=z
  le_old : lattice ≤ F.state.domain.lattice
  le_induced : lattice ≤ Γ.comap (conjugateEmbedding F.state.domain.embed (F.residue r))
  finite_old : (lattice.subgroupOf F.state.domain.lattice).FiniteIndex
  finite_induced : (lattice.subgroupOf
    (Γ.comap (conjugateEmbedding F.state.domain.embed (F.residue r)))).FiniteIndex
  adapted : ∀ k (x : F.state.domain.Carrier),x∈F.state.domain.filtration.level k ↔
    ∀ i : Fin F.state.domain.dim,i.val < F.state.domain.cutoff k → chart.coord x i=0
  rational_iff : ∀ x,IsRational chart x ↔ IsRational F.state.domain.chart x

theorem residueCover_exists
    (hΓ : ∀ x : G,x∈Γ ↔ ∀ i,∃ z : ℤ,c.coord x i=z) (r : Fin F.period) :
    Nonempty (F.ResidueCover r) := by
  let D:=F.state.domain
  obtain ⟨Δ,e,he,hΔ,hle,hconj,hfinite,hfinite',hadapt,hrat⟩:=
    rational_conjugate_cover c D.chart D.secondKind D.embed D.continuous D.injective
      D.rational_image Γ D.lattice hΓ D.integer_lattice (F.residue r) (F.residue_rational r)
  exact ⟨{ lattice:=Δ
           chart:=e
           secondKind:=he
           integer_lattice:=hΔ
           le_old:=hle
           le_induced:=hconj
           finite_old:=hfinite
           finite_induced:=hfinite'
           adapted:=fun k=>hadapt (D.filtration.level k) (D.cutoff k) (D.adapted k)
           rational_iff:=hrat }⟩

def residueCover
    (hΓ : ∀ x : G,x∈Γ ↔ ∀ i,∃ z : ℤ,c.coord x i=z) (r : Fin F.period) :
    F.ResidueCover r := Classical.choice (F.residueCover_exists hΓ r)

namespace ResidueCover
variable {F} {r : Fin F.period} (C : F.ResidueCover r)

omit [IsTopologicalGroup G] in
theorem irrational (hL : ∀ N,0 < L N) :
    BaseCubeLaw.Irrational F.state.domain.filtration C.lattice s F.state.coeff
      (L∘F.state.subseq) := by
  let := C.finite_old
  intro j hj hjs ξ hne hc hrat hnext hbr
  have hr:= (FiniteCoverCharacters.rationalCharacter_iff C.lattice
    F.state.domain.lattice C.le_old ξ).mp hrat
  have hn (x : F.state.domain.filtration.level j)
      (hx : x.val∈F.state.domain.filtration.level (j+1)) : ξ x=1 := hnext x.val hx
  have hb (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a+b=j)
      (x : F.state.domain.Carrier) (hx : x∈F.state.domain.filtration.level a)
      (y : F.state.domain.Carrier) (hy : y∈F.state.domain.filtration.level b)
      (hh : ⁅x,y⁆∈F.state.domain.filtration.level j) : ξ ⟨⁅x,y⁆,hh⟩=1 :=
    hbr a b ha hb hab x hx y hy
  have hi:=F.irrational j hj hjs ξ hne hc hr hn hb
  simpa only [Function.comp_apply,abs_of_pos (hL _),TriangularLatticeRecovery.circleNorm,mul_comm] using hi

end ResidueCover

end AllLevelFactorization.Factorization
end
 
end

section
 

 

noncomputable section
open scoped Topology
namespace CosetCover
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (Δ Θ : Subgroup G) (hle : Δ≤Θ)

def map : G⧸Δ → G⧸Θ := Quotient.lift QuotientGroup.mk (by
  intro x y h
  exact QuotientGroup.eq.mpr (hle (QuotientGroup.leftRel_apply.mp h)))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma map_mk (x : G) : map Δ Θ hle (QuotientGroup.mk x)=QuotientGroup.mk x := rfl

omit [IsTopologicalGroup G] in
lemma continuous_map : Continuous (map Δ Θ hle) :=
  (QuotientGroup.isQuotientMap_mk Δ).continuous_iff.mpr QuotientGroup.continuous_mk

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma surjective_map : Function.Surjective (map Δ Θ hle) := by
  intro x
  induction x using Quotient.inductionOn with | h x => exact ⟨QuotientGroup.mk x,rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma map_smul (g : G) (x : G⧸Δ) : map Δ Θ hle (g • x)=g • map Δ Θ hle x := by
  induction x using Quotient.inductionOn with | h x => rfl

variable [MeasurableSpace (G⧸Δ)] [BorelSpace (G⧸Δ)]
variable [MeasurableSpace (G⧸Θ)] [BorelSpace (G⧸Θ)]

def probability (μ : MeasureTheory.ProbabilityMeasure (G⧸Δ)) :
    MeasureTheory.ProbabilityMeasure (G⧸Θ) :=
  μ.map (map Δ Θ hle)

lemma probability_invariant (μ : MeasureTheory.ProbabilityMeasure (G⧸Δ))
    [MeasureTheory.SMulInvariantMeasure G (G⧸Δ) (μ : MeasureTheory.Measure _)] :
    MeasureTheory.SMulInvariantMeasure G (G⧸Θ)
      (probability Δ Θ hle μ : MeasureTheory.Measure _) := by
  rw [probability, MeasureTheory.ProbabilityMeasure.toMeasure_map]
  exact MeasureTheory.smulInvariantMeasure_map (μ : MeasureTheory.Measure _) _
    (map_smul Δ Θ hle) (continuous_map Δ Θ hle).measurable
end CosetCover

namespace EmbeddedCubeHaar
open CubeFaces CubeLocalHaar RationalLattice MeasureTheory
variable {G H ι : Type} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable [Fintype ι] [DecidableEq ι]
variable (F : H →* G) (hc : Continuous F) (K : Filtration H) (Λ : Subgroup G) (σ : G)

abbrev inducedLattice : Subgroup H := Λ.comap (conjugateEmbedding F σ)

def baseImage : ((cube K (Finset.univ : Finset ι) 0)⧸cubeLattice K (inducedLattice F Λ σ)) →
    (Finset ι→G⧸Λ) :=
  Quotient.lift (fun g w=>QuotientGroup.mk (F (g.val w)*σ)) (by
    intro g h he
    funext w
    apply QuotientGroup.eq.mpr
    have hh := (QuotientGroup.leftRel_apply.mp he) w
    change conjugateEmbedding F σ ((g.val w)⁻¹*h.val w)∈Λ at hh
    simpa [conjugateEmbedding_apply,mul_assoc] using hh)

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp] lemma baseImage_mk (g : cube K (Finset.univ : Finset ι) 0) (w : Finset ι) :
    baseImage F K Λ σ (QuotientGroup.mk g) w=QuotientGroup.mk (F (g.val w)*σ) := rfl

include hc in
omit [IsTopologicalGroup H] in
lemma baseImage_continuous : Continuous (baseImage (ι:=ι) F K Λ σ) := by
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  apply continuous_pi
  intro w
  exact QuotientGroup.continuous_mk.comp
    ((hc.comp ((continuous_apply w).comp continuous_subtype_val)).mul continuous_const)

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H] in
lemma baseImage_injective : Function.Injective (baseImage (ι:=ι) F K Λ σ) := by
  intro x y h
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      apply QuotientGroup.eq.mpr
      intro w
      have hh:=QuotientGroup.eq.mp (congrFun h w)
      change (F (x.val w)*σ)⁻¹*(F (y.val w)*σ)∈Λ at hh
      change conjugateEmbedding F σ ((x.val w)⁻¹*y.val w)∈Λ
      simpa [conjugateEmbedding_apply,mul_assoc] using hh

variable (Δ : Subgroup H) (hle : Δ ≤ inducedLattice F Λ σ)

include hle in
omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H] in
theorem cubeInclusion : cubeLattice (ι:=ι) K Δ ≤ cubeLattice K (inducedLattice F Λ σ) :=
  fun _ hx w=>hle (hx w)

def coverImage : ((cube K (Finset.univ : Finset ι) 0)⧸cubeLattice K Δ) → (Finset ι→G⧸Λ) :=
  baseImage F K Λ σ ∘ CosetCover.map _ _ (cubeInclusion F K Λ σ Δ hle)

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp] lemma coverImage_mk (g : cube K (Finset.univ : Finset ι) 0) (w : Finset ι) :
    coverImage F K Λ σ Δ hle (QuotientGroup.mk g) w=QuotientGroup.mk (F (g.val w)*σ) := rfl

include hc in
omit [IsTopologicalGroup H] in
lemma coverImage_continuous : Continuous (coverImage (ι:=ι) F K Λ σ Δ hle) :=
  (baseImage_continuous F hc K Λ σ).comp (CosetCover.continuous_map _ _ _)

def haarImage (a : Finset ι→G)
    (x : (cube K (Finset.univ : Finset ι) 0)⧸cubeLattice K Δ) : Finset ι→G⧸Λ :=
  fun w=>a w • coverImage F K Λ σ Δ hle x w

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp] lemma haarImage_mk (a : Finset ι→G) (g : cube K (Finset.univ : Finset ι) 0) (w : Finset ι) :
    haarImage F K Λ σ Δ hle a (QuotientGroup.mk g) w=
      QuotientGroup.mk (a w*F (g.val w)*σ) := by
  change QuotientGroup.mk (a w*(F (g.val w)*σ))=QuotientGroup.mk (a w*F (g.val w)*σ)
  rw [mul_assoc]

include hc in
omit [IsTopologicalGroup H] in
lemma haarImage_continuous : Continuous (fun p : (Finset ι→G)×
    ((cube K (Finset.univ : Finset ι) 0)⧸cubeLattice K Δ)=>
      haarImage F K Λ σ Δ hle p.1 p.2) := by
  apply continuous_pi
  intro w
  exact ((continuous_apply w).comp continuous_fst).smul
    ((continuous_apply w).comp ((coverImage_continuous F hc K Λ σ Δ hle).comp continuous_snd))

variable [MeasurableSpace ((cube K (Finset.univ : Finset ι) 0)⧸cubeLattice K Δ)]
variable [BorelSpace ((cube K (Finset.univ : Finset ι) 0)⧸cubeLattice K Δ)]
variable [MeasurableSpace (G⧸Λ)] [BorelSpace (G⧸Λ)] [SecondCountableTopology (G⧸Λ)]

def imageProbability (μ : ProbabilityMeasure
    ((cube K (Finset.univ : Finset ι) 0)⧸cubeLattice K Δ)) (a : Finset ι→G) :
    ProbabilityMeasure (Finset ι→G⧸Λ) :=
  μ.map (haarImage F K Λ σ Δ hle a)

include hc in
omit [IsTopologicalGroup H] in
lemma integral_imageProbability (μ : ProbabilityMeasure
    ((cube K (Finset.univ : Finset ι) 0)⧸cubeLattice K Δ))
    (a : Finset ι→G) (f : C((Finset ι→G⧸Λ),ℂ)) :
    (∫ y,f y ∂(imageProbability F K Λ σ Δ hle μ a : Measure _))=
      ∫ x,f (haarImage F K Λ σ Δ hle a x) ∂(μ : Measure _) :=
  integral_map
    (((haarImage_continuous F hc K Λ σ Δ hle).comp
      (continuous_const.prodMk continuous_id)).measurable.aemeasurable)
    f.continuous.aestronglyMeasurable

variable [FirstCountableTopology G]

include hc in
omit [IsTopologicalGroup H] in
lemma imageProbability_continuous (μ : ProbabilityMeasure
    ((cube K (Finset.univ : Finset ι) 0)⧸cubeLattice K Δ)) :
    Continuous (imageProbability F K Λ σ Δ hle μ) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  have he (a : Finset ι→G) :
      (∫ y,f y ∂(imageProbability F K Λ σ Δ hle μ a : Measure _))=
        ∫ x,f (haarImage F K Λ σ Δ hle a x) ∂(μ : Measure _) :=
    integral_map
      (((haarImage_continuous F hc K Λ σ Δ hle).comp
        (continuous_const.prodMk continuous_id)).measurable.aemeasurable)
      f.continuous.aestronglyMeasurable
  simp_rw [he]
  apply continuous_of_dominated (bound:=fun _=>‖f‖)
  · intro a
    exact (f.continuous.comp ((haarImage_continuous F hc K Λ σ Δ hle).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · intro a
    exact Filter.Eventually.of_forall (fun x=>f.norm_coe_le_norm _)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun x=>f.continuous.comp
      ((haarImage_continuous F hc K Λ σ Δ hle).comp (continuous_id.prodMk continuous_const)))

end EmbeddedCubeHaar

end
end

end OAI
