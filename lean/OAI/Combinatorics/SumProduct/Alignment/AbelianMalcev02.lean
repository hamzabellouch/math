import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AbelianMalcev01
import OAI.Combinatorics.SumProduct.Alignment.MalcevHorizontal03
import OAI.Combinatorics.SumProduct.Alignment.RationalTail02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
end
end
 

 
section
noncomputable section
namespace AbelianMalcevTorus
open RationalLattice MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (hadd : ∀ g h : G, ∀ i : Fin n, c.coord (g*h) i=c.coord g i+c.coord h i)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable (mtr : MetricSpace (G⧸Γ))
variable (htop : mtr.toUniformSpace.toTopologicalSpace=(inferInstance : TopologicalSpace (G⧸Γ)))

 

def metricHomeomorph : @Homeomorph (G⧸Γ) (UnitAddTorus (Fin n))
    mtr.toUniformSpace.toTopologicalSpace inferInstance := by
  refine @Homeomorph.mk _ _ mtr.toUniformSpace.toTopologicalSpace inferInstance
    ((quotientHomeomorph c hadd Γ hΓ).toEquiv) ?_ ?_
  · rw [htop]
    exact (quotientHomeomorph c hadd Γ hΓ).continuous_toFun
  · rw [htop]
    exact (quotientHomeomorph c hadd Γ hΓ).continuous_invFun

omit [IsTopologicalGroup G] in
@[simp] lemma metricHomeomorph_apply [IsTopologicalGroup G] (x : G⧸Γ) :
    metricHomeomorph c hadd Γ hΓ mtr htop x=quotientHomeomorph c hadd Γ hΓ x := rfl

include hΓ htop in
omit [IsTopologicalGroup G] in
lemma metric_compact [IsTopologicalGroup G] :
    @CompactSpace (G⧸Γ) mtr.toUniformSpace.toTopologicalSpace := by
  rw [htop]
  exact quotient_compact c Γ hΓ

variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
include htop in
omit [IsTopologicalGroup G] in
lemma metric_borelSpace [IsTopologicalGroup G] :
    @BorelSpace (G⧸Γ) mtr.toUniformSpace.toTopologicalSpace inferInstance := by
  rw [htop]
  infer_instance

theorem metric_coordinateHaar_map (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (G⧸Γ) μ] :
    Measure.map (metricHomeomorph c hadd Γ hΓ mtr htop) μ = FourierObstruction.torusHaar (Fin n) := by
  have he : (metricHomeomorph c hadd Γ hΓ mtr htop : (G⧸Γ) → UnitAddTorus (Fin n))=
    quotientHomeomorph c hadd Γ hΓ := funext (metricHomeomorph_apply c hadd Γ hΓ mtr htop)
  rw [he]
  exact coordinateHaar_map c hadd Γ hΓ μ

end AbelianMalcevTorus
end
end
 

 
section
noncomputable section
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
namespace AbelianMalcevTorus
open RationalLattice CubeFaces LeibmanSquare MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (hadd : ∀ g h : G, ∀ i : Fin n, c.coord (g*h) i=c.coord g i+c.coord h i)

 

def additiveCoordinates : RealCoordinates G n where
  coord := c.coord
  one_coord := c.one_coord
  correction _ := 0
  mul_coord g h i := by simpa using hadd g h i

abbrev integerCharacter (k : Fin n → ℤ) : G →* Multiplicative ℝ :=
  MalcevHorizontal.character (additiveCoordinates c hadd) le_rfl (fun _ => rfl) k

omit [IsTopologicalGroup G] in
lemma integerCharacter_apply [IsTopologicalGroup G] (k : Fin n → ℤ) (g : G) :
    (integerCharacter c hadd k g).toAdd=∑ i, (k i:ℝ)*c.coord g i := rfl

lemma basis_integerCharacter (i : Fin n) (g : G) :
    (integerCharacter c hadd (Pi.single i 1) g).toAdd=c.coord g i := by
  classical
  rw [integerCharacter_apply]
  simp [Pi.single_apply]

variable (H : Filtration G)
include hadd in
 

theorem polynomial_coordinates (s : ℕ) (hs : H.level (s+1)=⊥)
    (f : ℤ → G) (hf : Polynomial H 0 f) :
    ∃ p : Fin n → ℝ[X], (∀ i, (p i).natDegree ≤ s) ∧
      ∀ z : ℤ, ∀ i, (p i).eval (z:ℝ)=c.coord (f z) i := by
  have hh (i : Fin n) := character_polynomial H s hs hf (integerCharacter c hadd (Pi.single i 1))
  choose p hp he using hh
  exact ⟨p,hp,fun z i => (he i z).trans (basis_integerCharacter c hadd i (f z))⟩

variable (hsk : SecondKind c)
include hsk in
 

lemma coordinates_additive_of_commutator_bot (hcomm : _root_.commutator G ≤ (⊥ : Subgroup G)) :
    ∀ g h : G, ∀ i : Fin n, c.coord (g*h) i=c.coord g i+c.coord h i := by
  intro g h i
  apply MalcevCharacters.prefix_coord_mul c hsk ⊥ n hcomm _ i i.isLt g h
  intro a ha j _
  have ha' : a=1 := ha
  rw [ha',c.one_coord]

include hsk in
lemma coordinates_additive_of_secondLevel_bot (h1 : H.level 1=⊤) (h2 : H.level 2=⊥) :
    ∀ g h : G, ∀ i : Fin n, c.coord (g*h) i=c.coord g i+c.coord h i := by
  apply coordinates_additive_of_commutator_bot c hsk
  have hc := H.commutator_le 1 1
  simpa only [h1,show 1+1=2 from rfl,h2,← _root_.commutator_def] using hc

end AbelianMalcevTorus
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace TorusLeibman
open MeasureTheory PolynomialWeyl FourierObstruction
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {ι : Type*} [Fintype ι]

 

theorem quantitative_homeomorphic_torus (e : X ≃ₜ UnitAddTorus ι)
    (μ : Measure X) [IsProbabilityMeasure μ] (hmap : Measure.map e μ=torusHaar ι)
    (d : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, 0<A ∧ ∀ N : ℕ, 0<N → ∀ p : ι → Polynomial ℝ,
      (∀ i, (p i).natDegree ≤ d) →
      (∃ F : C(X,ℂ), LipschitzWith 1 F ∧ ‖F‖ ≤ 1 ∧
        δ ≤ ‖mean N (fun n => F (e.symm (polynomialOrbit p n)))-(∫ x, F x ∂μ)‖) →
      ∃ k : ι → ℤ, k≠0 ∧ (∀ i, |(k i:ℝ)| ≤ A) ∧ ∃ m : ℕ → ℤ,
        ∀ j : ℕ, 0<j → j ≤ d →
          |(∑ i, (k i:ℝ)*(p i).coeff j)-m j| ≤ (A:ℝ)/(N:ℝ)^j := by
  obtain ⟨K,hK,hunit⟩ := compact_superset_unit_lipschitz X
  let pull := ContinuousMap.compCLM ℂ ℂ (⟨e.symm,e.symm.continuous⟩ : C(UnitAddTorus ι,X))
  have hK' : IsCompact (pull '' K) := hK.image pull.continuous
  obtain ⟨S,hS,η,hη,htest⟩ := CompactFamilyDescent.finite_unit_lipschitz_obstruction
    (pull '' K) hK' δ 2 hδ (by norm_num)
  obtain ⟨A,hA,hprod⟩ := quantitative_torus_leibman (ι:=ι) d η hη
  refine ⟨A,hA,?_⟩
  intro N hN p hp ⟨F,hFL,hFn,hdisc⟩
  apply hprod N hN p hp
  have hint : (∫ t, pull F t ∂torusHaar ι)=(∫ x, F x ∂μ) := by
    rw [← hmap,integral_map e.measurable.aemeasurable (pull F).continuous.aestronglyMeasurable]
    simp [pull]
  have hlarge : ∃ Φ∈pull '' K, δ ≤ ‖discrepancy (torusHaar ι) N (polynomialOrbit p) Φ‖ := by
    refine ⟨pull F,⟨F,hunit F hFL hFn,rfl⟩,?_⟩
    change δ ≤ ‖mean N (fun n => pull F (polynomialOrbit p n))-_‖
    rw [hint]
    exact hdisc
  obtain ⟨Φ,hΦ,hdΦ⟩ := htest (discrepancy (torusHaar ι) N (polynomialOrbit p))
    (discrepancy_bound _ N hN _) hlarge
  exact ⟨Φ,(hS Φ hΦ).1,(hS Φ hΦ).2,hdΦ⟩

end TorusLeibman
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace AbelianMalcevTorus
open RationalLattice CubeFaces LeibmanSquare MeasureTheory MalcevHorizontal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (hadd : ∀ g h : G, ∀ i : Fin n, c.coord (g*h) i=c.coord g i+c.coord h i)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hadd hΓ htop in
 

theorem quantitative_abelian_producer (H : Filtration G) (s : ℕ) (hs : H.level (s+1)=⊥)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G →* Multiplicative ℝ),
      (∀ χ∈U, Continuous χ ∧ (∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z)) ∧
    ∃ A : ℝ, 0<A ∧ ∀ N : ℕ, 0<N → ∀ f : ℤ → G, Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖ ≤ 1 ∧
        δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ χ∈U, χ≠1 ∧ ∃ P : ℝ[X], P.natDegree ≤ s ∧
        (∀ z : ℤ, P.eval (z:ℝ)=(χ (f z)).toAdd) ∧
        ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  let e := metricHomeomorph c hadd Γ hΓ mtr htop
  obtain ⟨A,hA,hprod⟩ := TorusLeibman.quantitative_homeomorphic_torus e μ
    (metric_coordinateHaar_map c hadd Γ hΓ mtr htop μ) s δ hδ
  let c' := additiveCoordinates c hadd
  let hz : ∀ i : Fin n, c'.correction (Fin.castLE le_rfl i)=0 := fun _ => rfl
  let U := boundedCharacters c' le_rfl hz A
  refine ⟨U,?_,(A:ℝ),by exact_mod_cast hA,?_⟩
  · intro χ hχ
    exact ⟨boundedCharacters_continuous c' le_rfl hz A χ hχ,
      boundedCharacters_integral c' le_rfl hz A Γ hΓ χ hχ⟩
  · intro N hN f hf hdisc
    obtain ⟨p,hp,hpe⟩ := polynomial_coordinates c hadd H s hs f hf
    have heval (k : ℕ) : e.symm (TorusLeibman.polynomialOrbit p k)=QuotientGroup.mk (f k) := by
      apply e.injective
      rw [e.apply_symm_apply]
      change TorusLeibman.polynomialOrbit p k=torusProjection c (f k)
      ext i
      simp only [TorusLeibman.polynomialOrbit,torusProjection]
      rw [← hpe (k:ℤ) i]
      simp only [Int.cast_natCast]
    obtain ⟨k,hk,hkA,z,hz⟩ := hprod N hN p hp (by
      obtain ⟨F,hFL,hFn,hF⟩ := hdisc
      refine ⟨F,hFL,hFn,?_⟩
      change δ ≤ ‖PolynomialWeyl.mean N (fun n => F (QuotientGroup.mk (f n)))-(∫ x, F x ∂μ)‖ at hF
      simpa only [heval] using hF)
    have hkAi : ∀ i, |k i| ≤ (A:ℤ) := by
      intro i
      exact_mod_cast hkA i
    refine ⟨integerCharacter c hadd k,mem_boundedCharacters c' le_rfl _ A k hkAi,
      character_ne_one c' le_rfl _ hk,TorusLeibman.characterPolynomial k p,
      TorusLeibman.characterPolynomial_degree k p s hp,?_,?_⟩
    · intro t
      rw [integerCharacter_apply]
      simp only [TorusLeibman.characterPolynomial,eval_finsetSum,eval_smul,smul_eq_mul,hpe]
    · intro j hj
      by_cases hjs : j ≤ s
      · exact ⟨z j,by simpa only [TorusLeibman.characterPolynomial_coeff] using hz j hj hjs⟩
      · refine ⟨0,?_⟩
        have hdeg := TorusLeibman.characterPolynomial_degree k p s hp
        rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (Nat.lt_of_not_ge hjs))]
        simp only [Int.cast_zero,sub_zero,abs_zero]
        positivity

end AbelianMalcevTorus

end
end
end
end
end

end OAI
