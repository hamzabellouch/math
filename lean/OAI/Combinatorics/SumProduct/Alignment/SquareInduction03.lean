import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice09
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
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
 

theorem quadratic_normalized_compact_producer
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      (∃ F∈K, δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
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
    exact quadratic_eigenfunction_observable c hsk H h0 h1 hs hcomm q hqbound hq2 hq Γ hΓ μ η hη F.val k hk
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
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥) (hcomm : H.level 2=_root_.commutator G)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs hcomm hqbound hq2 hq hΓ in
 

theorem quadratic_compact_producer
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F∈K, δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  obtain ⟨C,hC,hrep⟩ := compact_reps_of_integerCoordinates c Γ hΓ
  let Q : C(G⧸Γ,G⧸Γ) := ContinuousMap.id _
  let T := fun p : G×C(G⧸Γ,ℂ) => FiniteCoverObservable.translated Q p.1 p.2
  let K' := T '' (C ×ˢ K)
  have hK' : IsCompact K' := (hC.prod hK).image (FiniteCoverObservable.continuous_translated Q)
  obtain ⟨U,A,hA,N₀,hN₀,hprod⟩ := quadratic_normalized_compact_producer c hsk H h0 h1 hs hcomm
    q hqbound hq2 hq Γ hΓ μ K' hK' δ hδ
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
open scoped BigOperators
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
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
 

theorem quadratic_compact_all_lengths
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
  obtain ⟨U,A,hA,M,hM,hprod⟩ := quadratic_compact_producer c hsk H h0 h1 hs hcomm
    q hqbound hq2 hq Γ hΓ μ K hK (δ/2) (by positivity)
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
end
end
end

end OAI
