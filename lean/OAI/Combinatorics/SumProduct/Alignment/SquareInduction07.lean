import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction06
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
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
variable (H : Filtration G) (h1 : H.level 1=⊤) (hs : H.level 3=⊥)
variable [∀ i, (H.level i).Normal]
variable (q : ℕ→ℕ) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h1 hs hq2 hq hΓ in
 

theorem quadratic_zero_weight_observable
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i=0 :=
      fun g => by simpa only [hq2] using hq 2 g
    letI := tailAction c hsk (H.level 2) Γ (last_central_ambient H h1 2 hs) htail hΓ
    ∀ F : C(G⧸Γ,ℂ), TorusVerticalFourier.HasWeight (0 : Fin d→ℤ) F →
      ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
        ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
        δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖ →
          ∃ ξ∈U, QuadraticCharacterData Γ A N f ξ := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq 2 g
  let hcent := last_central_ambient H h1 2 hs
  let := tailAction c hsk (H.level 2) Γ hcent htail hΓ
  dsimp only
  intro F hw
  have hcomm : _root_.commutator G ≤ H.level 2 := by
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact SquareHorizontalCharacter.commutator_mem H h1 a b
  have hF : ∀ g a, a∈H.level 2 → F (QuotientGroup.mk (g*a))=F (QuotientGroup.mk g) := by
    intro g a ha
    have he := hw (torusProjection (tailCoordinates c (H.level 2) htail) ⟨a,ha⟩) (QuotientGroup.mk g)
    rw [tailProjection_vadd c hsk (H.level 2) Γ hcent htail hΓ] at he
    simpa only [mFourier_zero,ContinuousMap.one_apply,one_mul] using he
  obtain ⟨U,hU,A,hA,hprod⟩ := quantitative_abelian_quotient_observable c hsk
    (Nat.le_add_right t d) (H.level 2) Γ hcomm htail hΓ H 2 hs μ F hF δ hδ
  refine ⟨U,A,hA,1,by decide,?_⟩
  intro N hN f hf _ hdisc
  obtain ⟨ξ,hξ,hξ0,P,hP,hPe,hPc⟩ := hprod N hN f hf hdisc
  exact ⟨ξ,hξ,hξ0,(hU ξ hξ).1,(hU ξ hξ).2,P,hP,hPe,hPc⟩

end SquareInduction
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevCentralTorus RationalTailCoordinates UnitAddTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+(d+1))) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+(d+1)) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+(d+1)), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs hqbound hq2 hq hΓ in
 

theorem quadratic_eigenfunction_of_rank
    (IH : QuadraticRankStatement G (t+(d+1)) d)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+(d+1)), i.val<t → c.coord g i=0 :=
      fun g => by simpa only [hq2] using hq 2 g
    letI := tailAction c hsk (H.level 2) Γ (last_central_ambient H h1 2 hs) htail hΓ
    ∀ (F : C(G⧸Γ,ℂ)) (k : Fin (d+1)→ℤ), TorusVerticalFourier.HasWeight k F →
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖ →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+(d+1)), i.val<t → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq 2 g
  let hcent := last_central_ambient H h1 2 hs
  let := tailAction c hsk (H.level 2) Γ hcent htail hΓ
  let := continuous_tailAction c hsk (H.level 2) Γ hcent htail hΓ
  let := invariant_tailAction c hsk (H.level 2) Γ hcent htail hΓ μ
  dsimp only
  intro F k hw
  by_cases hk : k=0
  · subst k
    exact quadratic_zero_weight_observable c hsk H h1 hs q hq2 hq Γ hΓ μ δ hδ F hw
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
    have hzero := TorusVerticalFourier.integral_hasWeight_eq_zero μ F' hk hw'
    obtain ⟨U,A,hA,N₀,hN₀,hprod⟩ := quadratic_vertical_unbounded_of_rank c hsk H h0 h1
      (show H.level 3=⊥ from ‹H.level 3=⊥›) q hqbound hq2 hq Γ hΓ IH μ F' hF' hzero χ hχ hright a.val a.property hχa
      (δ/D) (div_pos hδ hD)
    refine ⟨U,A,hA,N₀,hN₀,?_⟩
    intro N hN f hf hf0 hdisc
    apply hprod N hN f hf hf0
    have hdisc' : δ/D ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F'‖ := by
      change δ/D ≤ ‖FourierObstruction.discrepancy μ N _ ((D:ℂ)⁻¹ • F)‖
      rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD,div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hdisc (inv_nonneg.mpr hD.le)
    change δ/D ≤ ‖mean N (fun n => F' (QuotientGroup.mk (f n)))-(∫ x,F' x ∂μ)‖ at hdisc'
    simpa only [hzero,sub_zero] using hdisc'

end SquareInduction
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
variable (H : Filtration G) (h1 : H.level 1=⊤) (hs : H.level 3=⊥)
variable [∀ i, (H.level i).Normal]
variable (q : ℕ→ℕ) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h1 hs hq2 hq hΓ in
 

omit [∀ i, (H.level i).Normal] in
theorem normalized_estimate_of_eigen [∀ i, (H.level i).Normal]
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (heigen :
      letI : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
      letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
      let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i=0 :=
        fun g => by simpa only [hq2] using hq 2 g
      letI := tailAction c hsk (H.level 2) Γ (last_central_ambient H h1 2 hs) htail hΓ
      ∀ η : ℝ, 0<η → ∀ F : C(G⧸Γ,ℂ), ∀ k : Fin d→ℤ,
        TorusVerticalFourier.HasWeight k F →
      ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      η ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖ →
        ∃ ξ∈U, QuadraticCharacterData Γ A N f ξ)
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    QuadraticNormalizedEstimate H Γ μ K δ := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+d), i.val<t → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq 2 g
  let hcent := last_central_ambient H h1 2 hs
  let := tailAction c hsk (H.level 2) Γ hcent htail hΓ
  let := continuous_tailAction c hsk (H.level 2) Γ hcent htail hΓ
  let E := {F : C(G⧸Γ,ℂ) // F∈TorusVerticalFourier.eigenfunctions (d:=Fin d)}
  have hd : (Submodule.span ℂ (Set.range (fun F : E => F.val))).topologicalClosure=⊤ := by
    change (Submodule.span ℂ (Set.range ((↑) : E → C(G⧸Γ,ℂ)))).topologicalClosure=⊤
    have he : Set.range ((↑) : E → C(G⧸Γ,ℂ))=TorusVerticalFourier.eigenfunctions (d:=Fin d) := by
      ext F
      exact ⟨fun ⟨x,hx⟩ => hx ▸ x.property,fun hF => ⟨⟨F,hF⟩,rfl⟩⟩
    rw [he]
    exact
      (TorusVerticalFourier.eigenfunctions_dense (d:=Fin d) (X:=G⧸Γ))
  obtain ⟨S,η,hη,htest⟩ := TorusVerticalFourier.finite_tests_of_dense_span (fun F : E => F.val)
    hd K hK δ 2 hδ (by norm_num)
  have hproduce (F : E) :
      ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
        ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
        η ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F.val‖ →
        ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
          ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
            ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
    obtain ⟨k,hk⟩ := F.property
    exact heigen η hη F.val k hk
  choose U A hA N₀ hN₀ hp using hproduce
  let B : ℝ := 1+∑ F∈S,A F
  let M : ℕ := 1+∑ F∈S,N₀ F
  have hB : 0<B := by
    have hh : 0 ≤ ∑ F∈S,A F := Finset.sum_nonneg (fun F _ => (hA F).le)
    dsimp [B]
    linarith
  have hM : 0<M := by dsimp [M]; omega
  refine ⟨S.biUnion U,B,hB,M,hM,?_⟩
  intro N hMN f hf hf0 hdisc
  have hN : 0<N := hM.trans_le hMN
  obtain ⟨F,hF,hlarge⟩ := htest (FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)))
    (FourierObstruction.discrepancy_bound μ N hN _) hdisc
  have hFi : N₀ F ≤ M := by
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hF).trans (Nat.le_add_left _ _)
  obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,hPc⟩ := hp F N (hFi.trans hMN) f hf hf0 hlarge
  have hAB : A F ≤ B := by
    have hh := Finset.single_le_sum (f:=A) (fun F (_ : F∈S) => (hA F).le) hF
    dsimp [B]
    linarith
  refine ⟨ξ,Finset.mem_biUnion.mpr ⟨F,hF,hξ⟩,hξ0,hξc,hξΓ,P,hP,hPe,?_⟩
  intro j hj
  obtain ⟨z,hz⟩ := hPc j hj
  exact ⟨z,hz.trans (div_le_div_of_nonneg_right hAB (by positivity))⟩

end SquareInduction

end
end
end
end
end

end OAI
