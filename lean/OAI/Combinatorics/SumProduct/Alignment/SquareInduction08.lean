import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction07
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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (H : Filtration G) (h0 : H.level 0=⊤)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include h0 hΓ in
 

theorem compact_estimate_of_normalized
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (hnormalized :
      letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
      ∀ K : Set C(G⧸Γ,ℂ), IsCompact K → ∀ δ : ℝ, 0<δ →
        QuadraticNormalizedEstimate H Γ μ K δ)
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    QuadraticCompactEstimate H Γ μ K δ := by
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
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevCentralTorus RationalTailCoordinates UnitAddTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 

theorem quadratic_rank_statement (n k : ℕ) : QuadraticRankStatement G n k := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro c hsk H h0 h1 hs q hqbound hq hr Γ hΓ mΓ bΓ μ pμ sμ K hK δ hδ
    let : ∀ i, (H.level i).Normal := fun i => level_normal H h0 i
    obtain ⟨d,hn⟩ := Nat.exists_eq_add_of_le (hqbound 2)
    subst n
    apply compact_estimate_of_normalized c H h0 Γ hΓ μ ?_ K hK δ hδ
    intro K' hK' δ' hδ'
    apply normalized_estimate_of_eigen c hsk H h1 hs q rfl hq Γ hΓ μ ?_ K' hK' δ' hδ'
    cases d with
    | zero =>
      dsimp only
      intro η hη F w hw
      have hzero : w=0 := by funext i; exact Fin.elim0 i
      subst w
      exact quadratic_zero_weight_observable c hsk H h1 hs q rfl hq Γ hΓ μ η hη F hw
    | succ d =>
      have hd : d<k := by omega
      have IH : QuadraticRankStatement G (q 2+(d+1)) d := ih d hd
      dsimp only
      intro η hη
      exact quadratic_eigenfunction_of_rank c hsk H h0 h1 hs q hqbound rfl hq Γ hΓ IH μ η hη

variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤) (hs : H.level 3=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ i, q i ≤ n)
variable (hq : ∀ i (g : G), g∈H.level i ↔ ∀ j : Fin n, j.val < q i → c.coord g j=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
include hsk h0 h1 hs hqbound hq hΓ in
 

theorem quadratic_general_compact_producer
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    QuadraticCompactEstimate H Γ μ K δ :=
  quadratic_rank_statement n (n-q 2) c hsk H h0 h1 hs q hqbound hq le_rfl Γ hΓ μ K hK δ hδ

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs hqbound hq hΓ in
 

omit [∀ i, (H.level i).Normal] in
theorem quadratic_general_compact_all_lengths [∀ i, (H.level i).Normal]
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F∈K, δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  obtain ⟨U,A,hA,M,hM,hprod⟩ := quadratic_general_compact_producer c hsk H h0 h1 hs
    q hqbound hq Γ hΓ μ K hK (δ/2) (by positivity)
  let B : ℝ := A+(M:ℝ)^2
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
    nlinarith [sq_nonneg (M:ℝ)]
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
    obtain ⟨P,hP,hPe⟩ := character_polynomial H 2 hs hf ξ
    refine ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,?_⟩
    intro j hj
    by_cases hj2 : j ≤ 2
    · refine ⟨round (P.coeff j),(abs_sub_round _).trans ?_⟩
      apply (le_div_iff₀ (pow_pos (by positivity : (0:ℝ)<N) j)).mpr
      have hNM : (N:ℝ) ≤ M := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hMN))
      have hpow : (N:ℝ)^j ≤ (M:ℝ)^2 :=
        (pow_le_pow_right₀ hNr hj2).trans (pow_le_pow_left₀ (by positivity) hNM 2)
      dsimp [B]
      nlinarith [pow_nonneg (show (0:ℝ) ≤ N by positivity) j]
    · refine ⟨0,?_⟩
      rw [coeff_eq_zero_of_natDegree_lt (hP.trans_lt (Nat.lt_of_not_ge hj2))]
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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem quadratic_general_metric_producer
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖≤1 ∧
        δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
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
  obtain ⟨U,A,hA,hprod⟩ := quadratic_general_compact_all_lengths c hsk H h0 h1 hs
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
