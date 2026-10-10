import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction08
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

local instance squareInduction09BinomialTopology : TopologicalSpace (G⧸Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem quadratic_general_leibman_binomial
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖≤1 ∧
        δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ b : Fin (t+d)→ℤ, b≠0 ∧ (∀ i, |(b i:ℝ)|≤A) ∧ (∀ a b : G, ξ (a*b*a⁻¹*b⁻¹)=1) ∧
          (∀ g : G, (ξ g).toAdd=∑ i, c.coord g i*(b i:ℝ)) ∧
        ∃ α : ℕ→ℝ, (∀ j : ℕ, 2<j → α j=0) ∧
          (∀ z : ℤ, (ξ (f z)).toAdd=∑ j : Fin 3, α j.val*(Ring.choose z j.val:ℤ)) ∧
          ∀ j : ℕ, 0<j → (N:ℝ)^j*‖(α j : UnitAddCircle)‖≤A := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,C,hC,hprod⟩ := quadratic_general_metric_producer c hsk H h0 h1 hs
    q hqbound hq Γ hΓ htop μ δ hδ
  let S : ℝ := ∑ ξ∈U, ∑ i, |(ξ (axis c i 1)).toAdd|
  have hS : 0≤S := Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  let A : ℝ := 1+S+BinomialDifference.conversionBound 2*C
  have hconv : 0<BinomialDifference.conversionBound 2*C :=
    mul_pos (BinomialDifference.conversionBound_pos 2) hC
  have hA : 0<A := by dsimp [A]; linarith
  refine ⟨U,A,hA,?_⟩
  intro N hN f hf hdisc
  obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,hPc⟩ := hprod N hN f hf hdisc
  obtain ⟨b,hb⟩ := integer_character_coordinates c hsk ξ Γ hΓ hξc hξΓ
  have hbi (i : Fin (t+d)) : (b i:ℝ)=(ξ (axis c i 1)).toAdd := by
    rw [hb]
    simp [coord_axis,Pi.single_apply]
  refine ⟨ξ,hξ,hξ0,hξc,hξΓ,b,?_,?_,?_,hb,
    fun j => BinomialDifference.coefficient ℝ j P,?_,?_,?_⟩
  · intro hb0
    apply hξ0
    ext g
    apply Multiplicative.toAdd.injective
    change (ξ g).toAdd=0
    rw [hb,hb0]
    simp
  · intro i
    have h1 : |(ξ (axis c i 1)).toAdd| ≤ ∑ j, |(ξ (axis c j 1)).toAdd| :=
      Finset.single_le_sum (f := fun j : Fin (t+d) => |(ξ (axis c j 1)).toAdd|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : (∑ j, |(ξ (axis c j 1)).toAdd|)≤S :=
      Finset.single_le_sum (f := fun χ : G→*Multiplicative ℝ => ∑ j, |(χ (axis c j 1)).toAdd|) (fun χ _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) hξ
    rw [hbi]
    dsimp [A]
    linarith
  · intro a b
    apply Multiplicative.toAdd.injective
    simp only [map_mul,map_inv,toAdd_mul,toAdd_inv]
    change (ξ a).toAdd+(ξ b).toAdd+(-(ξ a).toAdd)+(-(ξ b).toAdd)=0
    ring
  · intro j hj
    exact BinomialDifference.coefficient_eq_zero ℝ j P (hP.trans_lt hj)
  · exact character_binomial_expansion H 2 hs hf ξ P hPe
  · intro j hj
    have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
    have hbnd := BinomialDifference.coefficient_bound 2 1 P hP (N:ℝ) C hNr hC.le
      (fun i hi => hPc i hi) j hj
    apply hbnd.trans
    dsimp [A]
    linarith

end SquareInduction
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevCentralTorus RationalTailCoordinates UnitAddTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 

def DegreeCharacterData (s : ℕ) (Γ : Subgroup G) (A : ℝ) (N : ℕ) (f : ℤ→G)
    (ξ : G→*Multiplicative ℝ) : Prop :=
  ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
    ∃ P : ℝ[X], P.natDegree ≤ s ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
      ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j

def DegreeCompactEstimate (s : ℕ) (H : Filtration G) (Γ : Subgroup G)
    [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)] [CompactSpace (G⧸Γ)]
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] (K : Set C(G⧸Γ,ℂ)) (δ : ℝ) : Prop :=
  ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
    (∃ F∈K, δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, DegreeCharacterData s Γ A N f ξ

def DegreeNormalizedEstimate (s : ℕ) (H : Filtration G) (Γ : Subgroup G)
    [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)] [CompactSpace (G⧸Γ)]
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] (K : Set C(G⧸Γ,ℂ)) (δ : ℝ) : Prop :=
  ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
    (∃ F∈K, δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, DegreeCharacterData s Γ A N f ξ

omit [IsTopologicalGroup G] in
lemma DegreeCharacterData.mono [IsTopologicalGroup G] {s : ℕ} {Γ : Subgroup G} {A B : ℝ} {N : ℕ} {f : ℤ→G}
    {ξ : G→*Multiplicative ℝ} (hd : DegreeCharacterData s Γ A N f ξ) (hAB : A≤B) :
    DegreeCharacterData s Γ B N f ξ := by
  obtain ⟨hξ,hc,hΓ,P,hP,hPe,hPc⟩ := hd
  refine ⟨hξ,hc,hΓ,P,hP,hPe,?_⟩
  intro j hj
  obtain ⟨z,hz⟩ := hPc j hj
  exact ⟨z,hz.trans (div_le_div_of_nonneg_right hAB (by positivity))⟩

 

def DegreeRankStatement (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (s n k : ℕ) : Prop :=
  ∀ (c : RealCoordinates G n), SecondKind c →
  ∀ (H : Filtration G), H.level 0=⊤ → H.level 1=⊤ → H.level (s+1)=⊥ →
  ∀ q : ℕ→ℕ, (∀ i, q i ≤ n) →
    (∀ i (g : G), g∈H.level i ↔ ∀ j : Fin n, j.val < q i → c.coord g j=0) →
    n-q 2 ≤ k →
  ∀ (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z),
  ∀ [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)],
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    ∀ (μ : Measure (G⧸Γ)), ∀ [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ],
    ∀ K : Set C(G⧸Γ,ℂ), IsCompact K → ∀ δ : ℝ, 0<δ →
      DegreeCompactEstimate s H Γ μ K δ

 

def DegreeStatement (s : ℕ) : Prop :=
  ∀ (G : Type), ∀ [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    ∀ n k : ℕ, DegreeRankStatement G s n k

end SquareInduction
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
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤) (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+(d+1)) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+(d+1)), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs2 hs hqbound hq2 hq hΓ in
 

theorem degree_rank_factor_return
    (IH : DegreeRankStatement G s (t+(d+1)) d)
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
        ∃ ξ∈U, DegreeCharacterData s Γ A N f ξ := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+(d+1)), i.val < t → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq 2 g
  let c₂ := tailCoordinates c (H.level 2) htail
  let L := H.refine (ψ.ker.map (H.level 2).subtype) hc
  have hL0 : L.level 0=⊤ := by simpa [L,Filtration.refine] using h0
  have hL1 : L.level 1=⊤ := by simpa [L,Filtration.refine] using h1
  have hL3 : L.level (s+1)=⊥ := by
    have he : s+1≠2 := by omega
    have he0 : s+1≠0 := by omega
    have he1 : s+1≠1 := by omega
    simp [L,Filtration.refine,hs]
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
    Λ Γ hle c₂ s hs Tmax Ξ hΞc hΞΓ A B M hA.le hMr
  let N₀ := M₀+M*M₁+2*(s+1)
  have hN₀ : 0<N₀ := by dsimp [N₀]; omega
  refine ⟨U,A',hA',N₀,hN₀,?_⟩
  intro N hNN T hT hTT f hf hfac F hFL hFn hdisc
  obtain ⟨e',b,f',hfac,he0,hep,hbp,hfp,hper,hev,hed⟩ := hfac
  have hn0 : M₀ ≤ N := by dsimp [N₀] at hNN; omega
  have hn6 : 2*(s+1) ≤ N := by dsimp [N₀] at hNN; omega
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
end
end
end

end OAI
