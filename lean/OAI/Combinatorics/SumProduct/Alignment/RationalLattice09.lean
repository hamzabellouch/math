import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevCentral01
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
end
end
 

 
section
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)

include hΓ in
 
lemma coordinate_quotient_t2 : T2Space (G⧸Γ) := by
  let : T2Space G := c.coord.symm.t2Space
  let : DiscreteTopology Γ := integerCoordinates_discrete c Γ hΓ
  have hc : IsClosed (Γ : Set G) := Γ.isClosed_of_discreteTopology
  apply (t2Space_iff_of_isOpenQuotientMap (QuotientGroup.isOpenQuotientMap_mk (N:=Γ))).mpr
  have he : {p : G×G | (QuotientGroup.mk p.1 : G⧸Γ)=QuotientGroup.mk p.2}=
      (fun p : G×G => p.1⁻¹*p.2) ⁻¹' (Γ:Set G) := by
    ext p
    exact QuotientGroup.eq
  rw [he]
  exact hc.preimage (continuous_fst.inv.mul continuous_snd)

include hΓ in
lemma coordinate_quotient_metrizable : TopologicalSpace.MetrizableSpace (G⧸Γ) := by
  let : T2Space (G⧸Γ) := coordinate_quotient_t2 c Γ hΓ
  let : CompactSpace (G⧸Γ) := AbelianMalcevTorus.quotient_compact c Γ hΓ
  let : SecondCountableTopology G := c.coord.secondCountableTopology
  infer_instance

 

abbrev coordinateQuotientMetric : MetricSpace (G⧸Γ) :=
  letI := coordinate_quotient_metrizable c Γ hΓ
  TopologicalSpace.metrizableSpaceMetric (G⧸Γ)

lemma coordinateQuotientMetric_topology :
    (coordinateQuotientMetric c Γ hΓ).toUniformSpace.toTopologicalSpace=
    QuotientGroup.instTopologicalSpace Γ := rfl

end RationalLattice
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace AbelianMalcevTorus
open RationalLattice MalcevCharacters CubeFaces LeibmanSquare MeasureTheory RationalQuotientFunctions
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n r : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c) (hr : r ≤ n)
variable (N Γ : Subgroup G) [N.Normal] (hcomm : _root_.commutator G ≤ N)
variable (hN : ∀ g : G, g∈N ↔ ∀ i : Fin n, i.val<r → c.coord g i=0)
variable (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk hr hcomm hN hΓ in
 

theorem quantitative_abelian_quotient_observable (H : Filtration G) (s : ℕ) (hs : H.level (s+1)=⊥)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (F : C(G⧸Γ,ℂ)) (hF : ∀ g a, a∈N → F (QuotientGroup.mk (g*a))=F (QuotientGroup.mk g))
    (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    ∃ U : Finset (G→*Multiplicative ℝ),
      (∀ χ∈U, Continuous χ ∧ (∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z)) ∧
    ∃ A : ℝ, 0<A ∧ ∀ L : ℕ, 0<L → ∀ f : ℤ→G, Polynomial H 0 f →
      δ ≤ ‖FourierObstruction.discrepancy μ L (fun k => QuotientGroup.mk (f k)) F‖ →
      ∃ χ∈U, χ≠1 ∧ ∃ P : ℝ[X], P.natDegree ≤ s ∧
        (∀ z : ℤ, P.eval (z:ℝ)=(χ (f z)).toAdd) ∧
        ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(L:ℝ)^j := by
  classical
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let cQ := MalcevPrefixQuotient.quotientChart c hr N hN
  let ΓQ := Γ.map (QuotientGroup.mk' N)
  have hΓQ : ∀ g : G⧸N, g∈ΓQ ↔ ∀ i, ∃ z : ℤ, cQ.coord g i=z :=
    MalcevPrefixQuotient.quotient_lattice c hr N hN Γ hΓ
  have hadd : ∀ g h : G⧸N, ∀ i, cQ.coord (g*h) i=cQ.coord g i+cQ.coord h i := by
    intro g h i
    induction g using Quotient.inductionOn with | h g =>
      induction h using Quotient.inductionOn with | h h =>
        exact prefix_coord_mul c hsk N r hcomm (fun a ha => (hN a).mp ha)
          (MalcevPrefixQuotient.embed hr i) i.isLt g h
  let : MetricSpace ((G⧸N)⧸ΓQ) := coordinateQuotientMetric cQ ΓQ hΓQ
  let : CompactSpace ((G⧸N)⧸ΓQ) := quotient_compact cQ ΓQ hΓQ
  let : MeasurableSpace ((G⧸N)⧸ΓQ) := borel _
  let : BorelSpace ((G⧸N)⧸ΓQ) := ⟨rfl⟩
  let Q := quotientMap N Γ
  have hQ : Continuous Q := continuous_quotientMap N Γ
  let ν := Measure.map Q μ
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hQ.measurable.aemeasurable).mpr inferInstance
  let : SMulInvariantMeasure (G⧸N) ((G⧸N)⧸ΓQ) ν := CentralQuotientAction.invariant_quotientMap N Γ μ
  obtain ⟨FQ,hFQ,_⟩ := existsUnique_normalDescend N Γ
    (⟨fun g => F (QuotientGroup.mk g),F.continuous.comp QuotientGroup.continuous_mk⟩ : C(G,ℂ)) hF
    (fun g a ha => congrArg F (QuotientGroup.mk_mul_of_mem g ha))
  have hFQall : ∀ x : G⧸Γ, FQ (Q x)=F x := by
    intro x
    induction x using Quotient.inductionOn with | h g => exact hFQ g
  let HQ := mapFiltration H (QuotientGroup.mk' N)
  have hsQ : HQ.level (s+1)=⊥ := by
    change (H.level (s+1)).map (QuotientGroup.mk' N)=⊥
    rw [hs,Subgroup.map_bot]
  obtain ⟨U,hU,A,hA,hprod⟩ := quantitative_abelian_compact_producer cQ hadd ΓQ hΓQ rfl
    HQ s hsQ ν {FQ} (isCompact_singleton) δ hδ
  let liftχ : (G⧸N →* Multiplicative ℝ) → (G→*Multiplicative ℝ) := fun χ => χ.comp (QuotientGroup.mk' N)
  refine ⟨U.image liftχ,?_,A,hA,?_⟩
  · intro χ hχ
    obtain ⟨ξ,hξ,rfl⟩ := Finset.mem_image.mp hχ
    refine ⟨(hU ξ hξ).1.comp QuotientGroup.continuous_mk,?_⟩
    intro g hg
    exact (hU ξ hξ).2 _ ⟨g,hg,rfl⟩
  · intro L hL f hf hdisc
    have hint : (∫ x, FQ x ∂ν)=(∫ x,F x ∂μ) := by
      rw [show ν=Measure.map Q μ from rfl,integral_map hQ.measurable.aemeasurable FQ.continuous.aestronglyMeasurable]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hFQall
    have hdiscQ : δ ≤ ‖FourierObstruction.discrepancy ν L
        (fun k => QuotientGroup.mk (QuotientGroup.mk' N (f k))) FQ‖ := by
      change δ ≤ ‖PolynomialWeyl.mean L (fun k => FQ (QuotientGroup.mk (QuotientGroup.mk' N (f k))))-(∫ x,FQ x ∂ν)‖
      simp only [hFQ,hint]
      exact hdisc
    obtain ⟨χ,hχ,hχ0,P,hP,hPe,hPc⟩ := hprod L hL (fun z => QuotientGroup.mk' N (f z))
      (polynomial_map H (QuotientGroup.mk' N) hf) ⟨FQ,Set.mem_singleton FQ,hdiscQ⟩
    refine ⟨liftχ χ,Finset.mem_image.mpr ⟨χ,hχ,rfl⟩,?_,P,hP,hPe,hPc⟩
    intro he
    apply hχ0
    apply MonoidHom.ext
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
    exact congrArg (fun ψ : G→*Multiplicative ℝ => ψ g) he

end AbelianMalcevTorus
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevCentralTorus RationalTailCoordinates UnitAddTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥) (hcomm : H.level 2=_root_.commutator G)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs hcomm hqbound hq2 hq hΓ in
 

theorem quadratic_eigenfunction_observable
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+d), i.val<t → c.coord g i=0 :=
      fun g => by simpa only [hq2] using hq 2 g
    letI := tailAction c hsk (H.level 2) Γ (last_central_ambient H h1 2 hs) htail hΓ
    ∀ (F : C(G⧸Γ,ℂ)) (k : Fin d→ℤ), TorusVerticalFourier.HasWeight k F →
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖ →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+d), i.val<t → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq 2 g
  let hcent := last_central_ambient H h1 2 hs
  let := tailAction c hsk (H.level 2) Γ hcent htail hΓ
  let := continuous_tailAction c hsk (H.level 2) Γ hcent htail hΓ
  let := invariant_tailAction c hsk (H.level 2) Γ hcent htail hΓ μ
  dsimp only
  intro F k hw
  by_cases hk : k=0
  · have hF : ∀ g a, a∈H.level 2 → F (QuotientGroup.mk (g*a))=F (QuotientGroup.mk g) := by
      intro g a ha
      have he := hw (torusProjection (tailCoordinates c (H.level 2) htail) ⟨a,ha⟩) (QuotientGroup.mk g)
      rw [tailProjection_vadd c hsk (H.level 2) Γ hcent htail hΓ] at he
      simpa only [hk,mFourier_zero,ContinuousMap.one_apply,one_mul] using he
    obtain ⟨U,hU,A,hA,hprod⟩ := quantitative_abelian_quotient_observable c hsk
      (Nat.le_add_right t d) (H.level 2) Γ hcomm.ge htail hΓ H 2 hs μ F hF δ hδ
    refine ⟨U,A,hA,1,by decide,?_⟩
    intro N hN f hf _ hdisc
    obtain ⟨ξ,hξ,hξ0,P,hP,hPe,hPc⟩ := hprod N hN f hf hdisc
    exact ⟨ξ,hξ,hξ0,(hU ξ hξ).1,(hU ξ hξ).2,P,hP,hPe,hPc⟩
  · let D : ℝ := 1+‖F‖
    have hD : 0<D := by dsimp [D]; positivity
    let F' : C(G⧸Γ,ℂ) := (D:ℂ)⁻¹ • F
    have hw' : TorusVerticalFourier.HasWeight k F' := hw.smul _
    have hF' : ∀ x, ‖F' x‖ ≤ 1 := by
      intro x
      change ‖(D:ℂ)⁻¹ * F x‖ ≤ 1
      rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
      have hFx := F.norm_coe_le_norm x
      apply (inv_mul_le_iff₀ hD).mpr
      dsimp [D]
      linarith
    let χ : G→ℂ := fun g => if hg : g∈H.level 2 then
      mFourier k (torusProjection (tailCoordinates c (H.level 2) htail) ⟨g,hg⟩) else 1
    have hχ : ∀ g∈H.level 2, ‖χ g‖=1 := by
      intro g hg
      simp only [χ,dite_eq_left hg]
      exact TorusVerticalFourier.character_norm _ _
    have hright : ∀ a∈H.level 2, ∀ g : G,
        F' (QuotientGroup.mk (g*a))=χ a*F' (QuotientGroup.mk g) := by
      intro a ha g
      have he := hw' (torusProjection (tailCoordinates c (H.level 2) htail) ⟨a,ha⟩) (QuotientGroup.mk g)
      rw [tailProjection_vadd c hsk (H.level 2) Γ hcent htail hΓ] at he
      simpa only [χ,dite_eq_left ha] using he
    obtain ⟨s,hs⟩ := TorusVerticalFourier.character_nontrivial hk
    obtain ⟨a,ha⟩ := torusProjection_surjective (tailCoordinates c (H.level 2) htail) s
    have hχa : χ a.val≠1 := by simpa only [χ,dite_eq_left a.property,ha] using hs
    obtain ⟨U,A,hA,N₀,hN₀,hprod⟩ := quadratic_source_vertical_correlation c hsk H h0 h1
      (show H.level 3=⊥ from ‹H.level 3=⊥›) hcomm q hqbound hq2 hq Γ hΓ F' hF' χ hχ hright a.val a.property hχa
      (δ/D) (div_pos hδ hD)
    refine ⟨U,A,hA,N₀,hN₀,?_⟩
    intro N hN f hf hf0 hdisc
    apply hprod N hN f hf hf0
    have hzero := TorusVerticalFourier.integral_hasWeight_eq_zero μ F' hk hw'
    have hdisc' : δ/D ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F'‖ := by
      change δ/D ≤ ‖FourierObstruction.discrepancy μ N _ ((D:ℂ)⁻¹ • F)‖
      rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD,div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hdisc (inv_nonneg.mpr hD.le)
    change δ/D ≤ ‖mean N (fun n => F' (QuotientGroup.mk (f n)))-(∫ x,F' x ∂μ)‖ at hdisc'
    simpa only [hzero,sub_zero] using hdisc'

end SquareInduction
end
end
 

 

end
end
end

end OAI
