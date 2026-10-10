import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction12
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevCentralTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t e d : ℕ} (c : RealCoordinates G (t+e)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+e) (hq2 : q s=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+e), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs2 hs hqbound hq2 hq hΓ in
 

theorem degree_eigenfunction_of_rank
    (hrank : (t+e)-q 2=d+1) (ID : DegreeStatement (s-1))
    (IH : DegreeRankStatement G s (t+e) d)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    let htail : ∀ g : G, g∈H.level s ↔ ∀ i : Fin (t+e), i.val<t → c.coord g i=0 :=
      fun g => by simpa only [hq2] using hq s g
    letI := tailAction c hsk (H.level s) Γ (last_central_ambient H h1 s hs) htail hΓ
    ∀ (F : C(G⧸Γ,ℂ)) (k : Fin e→ℤ), TorusVerticalFourier.HasWeight k F →
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖ →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ s ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let htail : ∀ g : G, g∈H.level s ↔ ∀ i : Fin (t+e), i.val<t → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq s g
  let hcent := last_central_ambient H h1 s hs
  let := tailAction c hsk (H.level s) Γ hcent htail hΓ
  let := continuous_tailAction c hsk (H.level s) Γ hcent htail hΓ
  let := invariant_tailAction c hsk (H.level s) Γ hcent htail hΓ μ
  dsimp only
  intro F k hw
  by_cases hk : k=0
  · subst k
    exact degree_zero_weight_observable c hsk H h0 h1 s (by omega) hs q hq2 hq Γ hΓ ID μ δ hδ F hw
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
    let χ : G→ℂ := fun g => if hg : g∈H.level s then
      mFourier k (torusProjection (tailCoordinates c (H.level s) htail) ⟨g,hg⟩) else 1
    have hχ : ∀ g∈H.level s, ‖χ g‖=1 := by
      intro g hg
      simp only [χ,dite_eq_left hg]
      exact TorusVerticalFourier.character_norm _ _
    have hright : ∀ a∈H.level s, ∀ g : G,
        F' (QuotientGroup.mk (g*a))=χ a*F' (QuotientGroup.mk g) := by
      intro a ha g
      have he := hw' (torusProjection (tailCoordinates c (H.level s) htail) ⟨a,ha⟩) (QuotientGroup.mk g)
      rw [tailProjection_vadd c hsk (H.level s) Γ hcent htail hΓ] at he
      simpa only [χ,dite_eq_left ha] using he
    obtain ⟨aT,haT⟩ := TorusVerticalFourier.character_nontrivial hk
    obtain ⟨a,ha⟩ := torusProjection_surjective (tailCoordinates c (H.level s) htail) aT
    have hχa : χ a.val≠1 := by simpa only [χ,dite_eq_left a.property,ha] using haT
    have hzero := TorusVerticalFourier.integral_hasWeight_eq_zero μ F' hk hw'
    obtain ⟨U,A,hA,N₀,hN₀,hprod⟩ := degree_vertical_unbounded_rank_any c hsk H h0 h1 s hs2 hs
      q hqbound hq hrank Γ hΓ ID IH μ F' hF' hzero χ hχ hright a.val a.property hχa
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
variable (s : ℕ) (H : Filtration G) (h1 : H.level 1=⊤) (hs : H.level (s+1)=⊥)
variable [∀ i, (H.level i).Normal]
variable (q : ℕ→ℕ) (hq2 : q s=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h1 hs hq2 hq hΓ in
 

omit [∀ i, (H.level i).Normal] in
theorem degree_normalized_estimate_of_eigen [∀ i, (H.level i).Normal]
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (heigen :
      letI : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
      letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
      let htail : ∀ g : G, g∈H.level s ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i=0 :=
        fun g => by simpa only [hq2] using hq s g
      letI := tailAction c hsk (H.level s) Γ (last_central_ambient H h1 s hs) htail hΓ
      ∀ η : ℝ, 0<η → ∀ F : C(G⧸Γ,ℂ), ∀ k : Fin d→ℤ,
        TorusVerticalFourier.HasWeight k F →
      ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      η ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖ →
        ∃ ξ∈U, DegreeCharacterData s Γ A N f ξ)
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    DegreeNormalizedEstimate s H Γ μ K δ := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let htail : ∀ g : G, g∈H.level s ↔ ∀ i : Fin (t+d), i.val<t → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq s g
  let hcent := last_central_ambient H h1 s hs
  let := tailAction c hsk (H.level s) Γ hcent htail hΓ
  let := continuous_tailAction c hsk (H.level s) Γ hcent htail hΓ
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
          ∃ P : ℝ[X], P.natDegree ≤ s ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
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
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevCentralTorus RationalTailCoordinates UnitAddTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (s : ℕ) (H : Filtration G) (h0 : H.level 0=⊤)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include h0 hΓ in
 

theorem degree_compact_estimate_of_normalized
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (hnormalized :
      letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
      ∀ K : Set C(G⧸Γ,ℂ), IsCompact K → ∀ δ : ℝ, 0<δ →
        DegreeNormalizedEstimate s H Γ μ K δ)
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    DegreeCompactEstimate s H Γ μ K δ := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  obtain ⟨C,hC,hrep⟩ := compact_reps_of_integerCoordinates c Γ hΓ
  let Q : C(G⧸Γ,G⧸Γ) := ContinuousMap.id _
  let T := fun p : G×C(G⧸Γ,ℂ) => FiniteCoverObservable.translated Q p.1 p.2
  let K' := T '' (C ×ˢ K)
  have hK' : IsCompact K' := (hC.prod hK).image (FiniteCoverObservable.continuous_translated Q)
  obtain ⟨U,A,hA,N₀,hN₀,hprod⟩ := hnormalized K' hK' δ hδ
  refine ⟨U,A,hA,N₀,hN₀,?_⟩
  intro N hN f hf ⟨F,hF,hdisc⟩
  obtain ⟨v,hv,hγ⟩ := hrep (f 0)
  let γ := v⁻¹*f 0
  have hav : f 0=v*γ := by simp [γ]
  let g : ℤ→G := fun n => γ*(f 0)⁻¹*f n*γ⁻¹
  obtain ⟨hg,hg0,hge⟩ := constant_normalization H h0 Γ hf v γ hγ hav
  let F' := T (v,F)
  have hF' : F'∈K' := ⟨(v,F),⟨hv,hF⟩,rfl⟩
  have he (n : ℕ) : F' (QuotientGroup.mk (g n))=F (QuotientGroup.mk (f n)) := by
    change F (QuotientGroup.mk (v*g n))=F (QuotientGroup.mk (f n))
    rw [hge]
  have hint : (∫ x,F' x ∂μ)=(∫ x,F x ∂μ) := by
    change (∫ x,F (v • x) ∂μ)=_
    exact integral_smul_eq_self F
  have hdisc' : δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (g k)) F'‖ := by
    change δ ≤ ‖mean N (fun n => F' (QuotientGroup.mk (g n)))-(∫ x,F' x ∂μ)‖
    change δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))-(∫ x,F x ∂μ)‖ at hdisc
    simpa only [he,hint] using hdisc
  obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,hPc⟩ := hprod N hN g hg hg0 ⟨F',hF',hdisc'⟩
  refine ⟨ξ,hξ,hξ0,hξc,hξΓ,P+Polynomial.C (ξ (f 0)).toAdd,?_,?_,?_⟩
  · exact natDegree_add_le_of_degree_le hP (by simp)
  · intro z
    simp only [eval_add,eval_C,hPe,g,map_mul,map_inv,toAdd_mul,toAdd_inv]
    ring
  · intro j hj
    obtain ⟨z,hz⟩ := hPc j hj
    refine ⟨z,?_⟩
    simpa only [coeff_add,coeff_C,ite_eq_right (Nat.ne_of_gt hj),add_zero] using hz

end SquareInduction

end
end
end
end
end

end OAI
