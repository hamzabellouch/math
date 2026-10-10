import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction13
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
namespace SquareInduction
open RationalLattice MalcevCharacters CubeFaces LeibmanSquare MeasureTheory AbelianMalcevTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 

theorem degree_abelian_compact {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
    (H : Filtration G) (h1 : H.level 1=⊤) (s : ℕ) (hs : H.level (s+1)=⊥)
    (h2 : H.level 2=⊥)
    (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
    [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    DegreeCompactEstimate s H Γ μ K δ := by
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  have hc : _root_.commutator G ≤ (⊥ : Subgroup G) := by
    rw [← h2]
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact SquareHorizontalCharacter.commutator_mem H h1 a b
  have hadd := coordinates_additive_of_commutator_bot c hsk hc
  obtain ⟨U,hU,A,hA,hprod⟩ := quantitative_abelian_compact_producer c hadd Γ hΓ rfl H s hs μ K hK δ hδ
  refine ⟨U,A,hA,1,by decide,?_⟩
  intro N hN f hf hdisc
  obtain ⟨χ,hχ,hχ0,P,hP,hPe,hPc⟩ := hprod N hN f hf hdisc
  exact ⟨χ,hχ,hχ0,(hU χ hχ).1,(hU χ hχ).2,P,hP,hPe,hPc⟩

end SquareInduction
end
end
 

 
section
noncomputable section
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevCentralTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 

theorem degree_rank_statement_of_lower (s : ℕ) (hs2 : 2 ≤ s)
    (ID : DegreeStatement (s-1)) (n k : ℕ) : DegreeRankStatement G s n k := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro c hsk H h0 h1 hs q hqbound hq hr Γ hΓ mΓ bΓ μ pμ sμ K hK δ hδ
    let : ∀ i, (H.level i).Normal := fun i => level_normal H h0 i
    cases he : n-q 2 with
    | zero =>
      have h2 : H.level 2=⊥ := by
        apply le_antisymm ?_ bot_le
        intro g hg
        change g=1
        apply c.coord.injective
        funext i
        rw [c.one_coord]
        exact (hq 2 g).mp hg i (by have := hqbound 2; omega)
      exact degree_abelian_compact c hsk H h1 s hs h2 Γ hΓ μ K hK δ hδ
    | succ d =>
      have hd : d<k := by omega
      have IH : DegreeRankStatement G s n d := ih d hd
      obtain ⟨e,hn⟩ := Nat.exists_eq_add_of_le (hqbound s)
      subst n
      apply degree_compact_estimate_of_normalized c s H h0 Γ hΓ μ ?_ K hK δ hδ
      intro K' hK' δ' hδ'
      apply degree_normalized_estimate_of_eigen c hsk s H h1 hs q rfl hq Γ hΓ μ ?_ K' hK' δ' hδ'
      dsimp only
      intro η hη
      exact degree_eigenfunction_of_rank c hsk H h0 h1 s hs2 hs q hqbound rfl hq Γ hΓ
        he ID IH μ η hη

 

theorem degree_statement (s : ℕ) : DegreeStatement s := by
  classical
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro G _ _ _ n k
    by_cases hs2 : 2 ≤ s
    · exact degree_rank_statement_of_lower s hs2 (ih (s-1) (by omega)) n k
    · intro c hsk H h0 h1 hs q hqbound hq hr Γ hΓ mΓ bΓ μ pμ sμ K hK δ hδ
      have h2 : H.level 2=⊥ := by
        apply le_antisymm _ bot_le
        calc
          H.level 2 ≤ H.level (s+1) := H.antitone (by omega)
          _ = ⊥ := hs
      exact degree_abelian_compact c hsk H h1 s hs h2 Γ hΓ μ K hK δ hδ

 

theorem degree_compact_producer {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
    (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤) (s : ℕ) (hs : H.level (s+1)=⊥)
    (q : ℕ→ℕ) (hqbound : ∀ i, q i ≤ n)
    (hq : ∀ i (g : G), g∈H.level i ↔ ∀ j : Fin n, j.val<q i → c.coord g j=0)
    (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
    [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    DegreeCompactEstimate s H Γ μ K δ :=
  degree_statement s G n (n-q 2) c hsk H h0 h1 hs q hqbound hq le_rfl Γ hΓ μ K hK δ hδ

end SquareInduction
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs hqbound hq hΓ in
 

omit [∀ i, (H.level i).Normal] in
theorem degree_general_compact_all_lengths [∀ i, (H.level i).Normal]
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F∈K, δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ s ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  obtain ⟨U,A,hA,M,hM,hprod⟩ := degree_compact_producer c hsk H h0 h1 s hs
    q hqbound hq Γ hΓ μ K hK (δ/2) (by positivity)
  let B : ℝ := A+(M:ℝ)^s
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨U,B,hB,?_⟩
  intro N hN f hf ⟨F,hF,hdisc⟩
  have hNr : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  by_cases hMN : M ≤ N
  · obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,hPc⟩ := hprod N hMN f hf ⟨F,hF,by linarith⟩
    refine ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,?_⟩
    intro j hj
    obtain ⟨z,hz⟩ := hPc j hj
    refine ⟨z,hz.trans (div_le_div_of_nonneg_right ?_ (by positivity))⟩
    dsimp [B]
    nlinarith [pow_nonneg (show (0:ℝ) ≤ M by positivity) s]
  · have hp : ∃ k∈Finset.range N,
        δ/2 ≤ ‖F (QuotientGroup.mk (f k))-(∫ x,F x ∂μ)‖ := by
      by_contra! hh
      have hsmall : ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖ ≤ δ/2 := by
        change ‖(𝔼 k∈Finset.range N,F (QuotientGroup.mk (f k)))-(∫ x,F x ∂μ)‖ ≤ _
        rw [← Finset.expect_const (s:=Finset.range N)
          (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)) (∫ x,F x ∂μ),← Finset.expect_sub_distrib]
        exact (RCLike.norm_expect_le (K:=ℂ)).trans (Finset.expect_le
          (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)) (fun k hk => (hh k hk).le))
      linarith
    obtain ⟨k,hk,hkdisc⟩ := hp
    have hc : LeibmanSquare.Polynomial H 0 (fun _ : ℤ => f k) :=
      polynomial_of_cube_mem H (const_mem (by rw [h0]; trivial))
    have hcd : δ/2 ≤ ‖FourierObstruction.discrepancy μ M
        (fun _ => QuotientGroup.mk (f k)) F‖ := by
      simpa only [FourierObstruction.discrepancy,LinearMap.coe_mk,AddHom.coe_mk,
        Finset.expect_const (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hM))] using hkdisc
    obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,_⟩ := hprod M le_rfl (fun _ => f k) hc ⟨F,hF,hcd⟩
    obtain ⟨P,hP,hPe⟩ := character_polynomial H s hs hf ξ
    refine ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,?_⟩
    intro j hj
    by_cases hjs : j ≤ s
    · refine ⟨round (P.coeff j),(abs_sub_round _).trans ?_⟩
      apply (le_div_iff₀ (pow_pos (by positivity : (0:ℝ)<N) j)).mpr
      have hNM : (N:ℝ) ≤ M := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hMN))
      have hpow : (N:ℝ)^j ≤ (M:ℝ)^s :=
        (pow_le_pow_right₀ hNr hjs).trans (pow_le_pow_left₀ (by positivity) hNM s)
      dsimp [B]
      nlinarith [pow_nonneg (show (0:ℝ) ≤ N by positivity) j]
    · refine ⟨0,?_⟩
      rw [coeff_eq_zero_of_natDegree_lt (hP.trans_lt (Nat.lt_of_not_ge hjs))]
      simp only [Int.cast_zero,sub_zero,abs_zero]
      positivity

end SquareInduction
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem degree_general_metric_producer
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖≤1 ∧
        δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ s ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let hCQ : @CompactSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) := quotient_compact c Γ hΓ
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨K,hK,hunit⟩ := FourierObstruction.compact_superset_unit_lipschitz (G⧸Γ)
  let e0 := @ContinuousMap.mk (G⧸Γ) (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ)
    mtr.toUniformSpace.toTopologicalSpace (fun x => x) (by rw [htop]; exact @continuous_id _ (QuotientGroup.instTopologicalSpace Γ))
  let pull := @ContinuousMap.compCLM (G⧸Γ) (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ)
    mtr.toUniformSpace.toTopologicalSpace ℂ ℂ _ _ _ _ _ _ e0
  have hK' : IsCompact (pull '' K) := hK.image pull.continuous
  obtain ⟨U,A,hA,hprod⟩ := degree_general_compact_all_lengths c hsk H h0 h1 s hs
    q hqbound hq Γ hΓ μ (pull '' K) hK' δ hδ
  refine ⟨U,A,hA,?_⟩
  intro N hN f hf ⟨F,hFL,hFn,hdisc⟩
  apply hprod N hN f hf
  refine ⟨pull F,⟨F,hunit F hFL hFn,rfl⟩,?_⟩
  change δ ≤ ‖mean N (fun k => F (QuotientGroup.mk (f k)))-(∫ x,F x ∂μ)‖
  exact hdisc

end SquareInduction

end
end
end
end
end

end OAI
