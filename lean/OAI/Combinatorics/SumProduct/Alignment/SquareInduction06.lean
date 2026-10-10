import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction05
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
open scoped commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters RationalTailCoordinates
open MeasureTheory PolynomialWeyl AbelianMalcevTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+(d+1))) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤) (hs : H.level 3=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+(d+1)) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+(d+1)), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs hqbound hq2 hq hΓ in
 

theorem quadratic_rank_factor_return
    (IH : QuadraticRankStatement G (t+(d+1)) d)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (ψ : H.level 2→*Multiplicative ℝ) (hψ : Continuous ψ)
    (hψΓ : ∀ g : H.level 2, g.val∈Γ → ∃ z : ℤ, (ψ g).toAdd=z)
    (hc : ∀ a b : G, ⁅a,b⁆∈ψ.ker.map (H.level 2).subtype) (hψ0 : ψ≠1)
    (B δ : ℝ) (hB : 0<B) (hδ : 0<δ) (Tmax : ℕ) (hTmax : 0<Tmax) :
    letI : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+(d+1)), i.val < t → c.coord g i=0 :=
      fun g => by simpa only [hq2] using hq 2 g
    let c₂ := tailCoordinates c (H.level 2) htail
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ T : ℕ, 0<T → T ≤ Tmax →
      ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
      CharacterFactorization.SmoothFactorizationAt H Γ c₂ ψ hc 1 B N T f →
      ∀ F : C(G⧸Γ,ℂ), LipschitzWith 1 F → ‖F‖ ≤ 1 →
      δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖ →
        ∃ ξ∈U, QuadraticCharacterData Γ A N f ξ := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+(d+1)), i.val < t → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq 2 g
  let c₂ := tailCoordinates c (H.level 2) htail
  let L := H.refine (ψ.ker.map (H.level 2).subtype) hc
  have hL0 : L.level 0=⊤ := by simpa [L,Filtration.refine] using h0
  have hL1 : L.level 1=⊤ := by simpa [L,Filtration.refine] using h1
  have hL3 : L.level 3=⊥ := by simp [L,Filtration.refine,hs]
  obtain ⟨Λ,e,hesk,hΛ,hle,hindex,q',hq',hq'2,hadapt⟩ :=
    strict_filtration_refinement_geometry c hsk H h0 h1 q hqbound hq2 hq Γ hΓ ψ hψ hψΓ hc hψ0
  let : (Λ.subgroupOf Γ).FiniteIndex := hindex
  let : MeasurableSpace (G⧸Λ) := borel (G⧸Λ)
  let : BorelSpace (G⧸Λ) := ⟨rfl⟩
  let : MetricSpace (G⧸Λ) := coordinateQuotientMetric e Λ hΛ
  let : CompactSpace (G⧸Λ) := quotient_compact e Λ hΛ
  obtain ⟨ν,hν,_⟩ := existsUnique_coordinateHaar e Λ hΛ
  let : SMulInvariantMeasure G (G⧸Λ) (ν : Measure (G⧸Λ)) := hν
  let μ' : ProbabilityMeasure (G⧸Γ) := ⟨μ,inferInstance⟩
  let : SMulInvariantMeasure G (G⧸Γ) (μ' : Measure (G⧸Γ)) := by change SMulInvariantMeasure G (G⧸Γ) μ; infer_instance
  have hmap := RationalLatticeCover.map_coordinateHaar c hΓ hle μ' ν
  obtain ⟨C,hC,hrep⟩ := compact_reps_of_integerCoordinates c Γ hΓ
  have hC' : ∀ g : G, ∃ v∈C, (QuotientGroup.mk g : G⧸Γ)=QuotientGroup.mk v := by
    intro g
    obtain ⟨v,hv,hvg⟩ := hrep g
    exact ⟨v,hv,(QuotientGroup.eq.mpr hvg).symm⟩
  obtain ⟨J,hJ,M₀,hM₀,S,hS,η,hη,hcov⟩ := FactorProgression.factor_cover_obstruction H Γ c₂
    (RationalLatticeCover.coverMap hle) (fun g => QuotientGroup.mk g) (fun _ => rfl)
    μ (ν : Measure (G⧸Λ)) hmap C hC hC' B δ hB hδ Tmax hTmax
  obtain ⟨V,A,hA,M₁,hM₁,hprod⟩ := IH e hesk L hL0 hL1 hL3 q' hq' hadapt
    (by rw [hq'2]; omega) Λ hΛ (ν : Measure (G⧸Λ)) (S : Set C(G⧸Λ,ℂ)) (S.finite_toSet.isCompact) η hη
  let Ξ := V.filter (fun ξ : G→*Multiplicative ℝ => Continuous ξ ∧ ∀ g∈Λ, ∃ z : ℤ, (ξ g).toAdd=z)
  have hΞc : ∀ ξ∈Ξ, Continuous ξ := fun ξ hξ => (Finset.mem_filter.mp hξ).2.1
  have hΞΓ : ∀ ξ∈Ξ, ∀ g∈Λ, ∃ z : ℤ, (ξ g).toAdd=z := fun ξ hξ => (Finset.mem_filter.mp hξ).2.2
  let M : ℕ := 2*J*Tmax
  have hM : 0<M := by dsimp [M]; positivity
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨U,hU,A',hA',htransfer⟩ := FactorCoefficientTransfer.finite_cover_factor_transfer H h0
    Λ Γ hle c₂ 2 hs Tmax Ξ hΞc hΞΓ A B M hA.le hMr
  let N₀ := M₀+M*M₁+6
  have hN₀ : 0<N₀ := by dsimp [N₀]; omega
  refine ⟨U,A',hA',N₀,hN₀,?_⟩
  intro N hNN T hT hTT f hf hfac F hFL hFn hdisc
  obtain ⟨e',b,f',hfac,he0,hep,hbp,hfp,hper,hev,hed⟩ := hfac
  have hn0 : M₀ ≤ N := by dsimp [N₀] at hNN; omega
  have hn6 : 2*(2+1) ≤ N := by dsimp [N₀] at hNN; omega
  have hev' : ∀ z : ℤ, |(z:ℝ)| ≤ N → ‖c₂.coord (e' z)‖ ≤ B := by simpa only [one_mul] using hev
  have hed' : ∀ z w : ℤ, |(z:ℝ)| ≤ N → |(w:ℝ)| ≤ N →
      ‖c₂.coord (e' z*(e' w)⁻¹)‖ ≤ (B/N)*|(z:ℝ)-(w:ℝ)| := by simpa only [one_mul] using hed
  obtain ⟨hK,hKN,w,hw,v,hv,hpp,Φ,hΦ,hlarge⟩ := hcov N hn0 T hT hTT L hL0
    f f' e' b hfp hfac hper hev' hed' F hFL hFn hdisc
  let K := N/(J*T)
  have hMK : M₁ ≤ K := by
    have hh : M*M₁ ≤ N := by dsimp [N₀] at hNN; omega
    change N ≤ M*K at hKN
    exact (Nat.le_of_mul_le_mul_left (hh.trans hKN) hM)
  obtain ⟨ξ,hξ,hnξ,hcξ,hΓξ,R,hR,hRe,hRc⟩ := hprod K hMK
    (fun z : ℤ => v⁻¹*f' ((T:ℤ)*z+w)*v) (polynomial_of_cube_mem _ hpp) ⟨Φ,hΦ,hlarge⟩
  have hξΞ : ξ∈Ξ := Finset.mem_filter.mpr ⟨hξ,hcξ,hΓξ⟩
  have hNKr : (N:ℝ) ≤ (M:ℝ)*K := by exact_mod_cast hKN
  obtain ⟨ω,hω,hω0,P,hP,hPe,hPc⟩ := htransfer N K hn6 hK hNKr T hT hTT (w:ℤ)
    (by positivity) (by exact_mod_cast hw.le) f f' e' b hf
    (polynomial_of_cube_mem _ hep) (polynomial_of_cube_mem _ hbp) hfac hper hev' v ξ hξΞ hnξ R hRe hRc
  exact ⟨ω,hω,hω0,(hU ω hω).1,(hU ω hω).2,P,hP,hPe,hPc⟩

end SquareInduction
end
end
 

 
section
noncomputable section
open scoped commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters RationalTailCoordinates
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevHorizontal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+(d+1))) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤) (hs : H.level 3=⊥)
variable [∀ i, (H.level i).Normal]
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+(d+1)) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+(d+1)), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs hqbound hq2 hq hΓ in
 

theorem quadratic_vertical_correlation_of_rank
    (IH : QuadraticRankStatement G (t+(d+1)) d)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (hF0 : (∫ x,F x ∂μ)=0) (χ : G→ℂ)
    (hχ : ∀ n∈H.level 2, ‖χ n‖=1)
    (hw : ∀ n∈H.level 2, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level 2) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      ‖horizontal c (Nat.le_add_right t (d+1)) (f 1)‖ ≤ 1 →
      δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
        ∃ ξ∈U, QuadraticCharacterData Γ A N f ξ := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  obtain ⟨S,hS,ε,hε,htest⟩ := CompactFamilyDescent.finite_unit_lipschitz_obstruction
    ({F} : Set C(G⧸Γ,ℂ)) isCompact_singleton δ 2 hδ (by norm_num)
  obtain ⟨U,V,A,hA,B,hB,Tmax,hTmax,M₀,hM₀,hproduces⟩ :=
    quadratic_source_factor_alternative c hsk H h0 h1 hs q hqbound hq2 hq Γ hΓ
      F hF χ hχ hw z hz hχz δ hδ
  let good := fun ψ : H.level 2→*Multiplicative ℝ =>
    ψ≠1 ∧ Continuous ψ ∧ (∀ g : H.level 2, g.val∈Γ → ∃ z : ℤ, (ψ g).toAdd=z) ∧
      ∃ hc : ∀ a b : G, ⁅a,b⁆∈ψ.ker.map (H.level 2).subtype, True
  let W := V.filter good
  let I := {ψ // ψ∈W}
  have hi (i : I) : good i.val := (Finset.mem_filter.mp i.property).2
  let hc (i : I) : ∀ a b : G, ⁅a,b⁆∈i.val.ker.map (H.level 2).subtype := (hi i).2.2.2.choose
  have hreturn (i : I) := quadratic_rank_factor_return c hsk H h0 h1 hs q hqbound hq2 hq Γ hΓ
    IH μ i.val (hi i).2.1 (hi i).2.2.1 (hc i) (hi i).1 B ε hB hε Tmax hTmax
  choose U' A' hA' M' hM' hr using hreturn
  let Amax := A+∑ i : I, A' i
  let Mmax := M₀+∑ i : I, M' i
  have hAmax : 0<Amax := by
    have : 0 ≤ ∑ i : I, A' i := Finset.sum_nonneg (fun _ _ => (hA' _).le)
    dsimp [Amax]; linarith
  have hMmax : 0<Mmax := by dsimp [Mmax]; omega
  have hAbi (i : I) : A' i ≤ Amax := by
    have hh := Finset.single_le_sum (f:=A') (fun _ _ => (hA' _).le) (Finset.mem_univ i)
    dsimp [Amax]; linarith
  have hMbi (i : I) : M' i ≤ Mmax := by
    have hh := Finset.single_le_sum (f:=M') (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [Mmax]; omega
  refine ⟨U∪Finset.univ.biUnion U',Amax,hAmax,Mmax,hMmax,?_⟩
  intro N hN f hf hf0 hlin hmean
  have hNM : M₀ ≤ N := by dsimp [Mmax] at hN; omega
  rcases hproduces N hNM f hf hf0 hlin hmean with hchar | hfac
  · obtain ⟨ξ,hξ,hd⟩ := hchar
    have hAA : A ≤ Amax := by
      have : 0 ≤ ∑ i : I, A' i := Finset.sum_nonneg (fun _ _ => (hA' _).le)
      dsimp [Amax]; linarith
    exact ⟨ξ,Finset.mem_union_left _ hξ,QuadraticCharacterData.mono hd hAA⟩
  · obtain ⟨ψ,hψ,hψ0,hψc,hψΓ,hψcomm,hstrict,T,hT,hTT,hfac⟩ := hfac
    let i : I := ⟨ψ,Finset.mem_filter.mpr ⟨hψ,hψ0,hψc,hψΓ,hψcomm,trivial⟩⟩
    have hdisc : δ ≤ ‖FourierObstruction.discrepancy μ N (fun n => QuotientGroup.mk (f n)) F‖ := by
      change δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))-(∫ x,F x ∂μ)‖
      simpa only [hF0,sub_zero] using hmean
    obtain ⟨Φ,hΦ,hlarge⟩ := htest (FourierObstruction.discrepancy μ N (fun n => QuotientGroup.mk (f n)))
      (FourierObstruction.discrepancy_bound μ N (hM₀.trans_le hNM) _) ⟨F,Set.mem_singleton F,hdisc⟩
    obtain ⟨ξ,hξ,hd⟩ := hr i N ((hMbi i).trans hN) T hT hTT f hf hfac
      Φ (hS Φ hΦ).1 (hS Φ hΦ).2 hlarge
    exact ⟨ξ,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hξ⟩),hd.mono (hAbi i)⟩

end SquareInduction
end
end
 

 
section
noncomputable section
open scoped commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters RationalTailCoordinates
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevHorizontal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+(d+1))) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤) (hs : H.level 3=⊥)
variable [∀ i, (H.level i).Normal]
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+(d+1)) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+(d+1)), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs hqbound hq2 hq hΓ in
 
theorem quadratic_vertical_unbounded_of_rank
    (IH : QuadraticRankStatement G (t+(d+1)) d)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (hF0 : (∫ x,F x ∂μ)=0) (χ : G→ℂ)
    (hχ : ∀ n∈H.level 2, ‖χ n‖=1)
    (hw : ∀ n∈H.level 2, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level 2) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
        ∃ ξ∈U, QuadraticCharacterData Γ A N f ξ := by
  obtain ⟨U,A,hA,N₀,hN₀,hdesc⟩ := quadratic_vertical_correlation_of_rank c hsk H h0 h1 hs
    q hqbound hq2 hq Γ hΓ IH μ F hF hF0 χ hχ hw z hz hχz δ hδ
  refine ⟨U,A,hA,N₀,hN₀,?_⟩
  intro N hNN f hf hf0 hmean
  let v := reduceCoordinates c (f 1) (t+(d+1))
  let γ := v⁻¹*f 1
  have hγ : γ∈Γ := reduceCoordinates_coset c Γ hΓ (f 1) (t+(d+1))
  have he : f 1=v*γ := by dsimp [γ]; group
  obtain ⟨hg,hg0,hg1,hge⟩ := lattice_linear_normalization H h1 Γ hf hf0 v γ hγ he
  obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,hPc⟩ := hdesc N hNN (fun n => f n*(γ^n)⁻¹)
    hg hg0 (by
      change ‖horizontal c (Nat.le_add_right t (d+1)) ((fun n : ℤ => f n*(γ^n)⁻¹) 1)‖ ≤ 1
      rw [hg1]; exact reduced_horizontal_bound c (Nat.le_add_right t (d+1)) _) (by simpa only [hge] using hmean)
  obtain ⟨a,ha⟩ := hξΓ γ hγ
  exact ⟨ξ,hξ,hξ0,hξc,hξΓ,integer_linear_return f γ ξ a ha P hP hPe A N hPc⟩

end SquareInduction

end
end
end
end
end

end OAI
