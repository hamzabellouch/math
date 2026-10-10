import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction10
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
open MeasureTheory PolynomialWeyl UniformSquareObservable AbelianMalcevTorus MalcevHorizontal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)

include hsk h0 h1 hs2 hs hqbound hq2 hq hΓ in
 

theorem degree_source_factor_alternative
    (IH : DegreeStatement (s-1))
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (χ : G→ℂ)
    (hχ : ∀ n∈H.level s, ‖χ n‖=1)
    (hw : ∀ n∈H.level s, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level s) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i=0 :=
      fun g => by simpa only [hq2] using hq 2 g
    let c₂ := tailCoordinates c (H.level 2) htail
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ V : Finset (H.level 2→*Multiplicative ℝ),
      ∃ A : ℝ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∃ Tmax : ℕ, 0<Tmax ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      ‖horizontal c (Nat.le_add_right t d) (f 1)‖ ≤ 1 →
      δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
      (∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ s ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j) ∨
      (∃ ψ∈V, ψ≠1 ∧ Continuous ψ ∧ (∀ x : H.level 2, x.val∈Γ → ∃ z : ℤ, (ψ x).toAdd=z) ∧
        ∃ hc : ∀ a b : G, ⁅a,b⁆∈ψ.ker.map (H.level 2).subtype,
        ψ.ker.map (H.level 2).subtype < H.level 2 ∧
        ∃ T : ℕ, 0<T ∧ T ≤ Tmax ∧
          CharacterFactorization.SmoothFactorizationAt H Γ c₂ ψ hc 1 B N T f) := by
  have htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq 2 g
  have hcomm : _root_.commutator G ≤ H.level 2 := by
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact SquareHorizontalCharacter.commutator_mem H h1 a b
  let cH := horizontalCoordinates c hsk (H.level 2) t hcomm (fun g hg => (htail g).mp hg)
  have hlin : ∀ i : Fin t, cH.correction (i.castLE (Nat.le_add_right t d))=0 := by
    intro i
    exact horizontalCoordinates_correction c hsk (H.level 2) t hcomm
      (fun g hg => (htail g).mp hg) _ i.isLt
  have hlevel : ∀ g : G, g∈H.level 2 ↔ horizontal cH (Nat.le_add_right t d) g=0 := by
    intro g
    rw [htail]
    constructor
    · intro hg
      funext i
      exact hg (i.castLE (Nat.le_add_right t d)) i.isLt
    · intro hg i hi
      exact congrFun hg (⟨i.val,hi⟩ : Fin t)
  let := last_normal H h0 (by omega : 1 ≤ s) hs
  let := PairTail.diagonal_normal (H.level 2) (H.level s) (last_central_ambient H h1 s hs)
  obtain ⟨cR,hskR,hΓR,hcRF⟩ := exists_adapted_sourceReducedCoordinates H h0 h1 s (by omega) hs
    c q hqbound hq2 hq Γ hΓ
  choose qR hqRbound hqR using hcRF
  exact degree_vertical_factor_alternative cH (Nat.le_add_right t d) hlin H h0 h1 s hs2 hs hlevel
    Γ hΓ cR hskR hΓR (tailCoordinates c (H.level 2) htail)
    (tail_secondKind c (H.level 2) htail hsk) (tailCoordinates_lattice c (H.level 2) htail Γ hΓ)
    (fun i => q (i.val+2)-t) (fun i x => tailCoordinates_adapted c (H.level 2) htail
      (H.level (i.val+2)) (q (i.val+2)) (hq (i.val+2)) x)
    IH qR hqRbound hqR 1 F hF χ hχ hw z hz hχz δ hδ

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+(d+1))) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤) (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1)=⊥)
variable [∀ i, (H.level i).Normal]
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+(d+1)) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+(d+1)), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs2 hs hqbound hq2 hq hΓ in
 

theorem degree_vertical_correlation_of_rank
    (ID : DegreeStatement (s-1))
    (IH : DegreeRankStatement G s (t+(d+1)) d)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (hF0 : (∫ x,F x ∂μ)=0) (χ : G→ℂ)
    (hχ : ∀ n∈H.level s, ‖χ n‖=1)
    (hw : ∀ n∈H.level s, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level s) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      ‖horizontal c (Nat.le_add_right t (d+1)) (f 1)‖ ≤ 1 →
      δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
        ∃ ξ∈U, DegreeCharacterData s Γ A N f ξ := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  obtain ⟨S,hS,ε,hε,htest⟩ := CompactFamilyDescent.finite_unit_lipschitz_obstruction
    ({F} : Set C(G⧸Γ,ℂ)) isCompact_singleton δ 2 hδ (by norm_num)
  obtain ⟨U,V,A,hA,B,hB,Tmax,hTmax,M₀,hM₀,hproduces⟩ :=
    degree_source_factor_alternative c hsk H h0 h1 s hs2 hs q hqbound hq2 hq Γ hΓ ID
      F hF χ hχ hw z hz hχz δ hδ
  let good := fun ψ : H.level 2→*Multiplicative ℝ =>
    ψ≠1 ∧ Continuous ψ ∧ (∀ g : H.level 2, g.val∈Γ → ∃ z : ℤ, (ψ g).toAdd=z) ∧
      ∃ hc : ∀ a b : G, ⁅a,b⁆∈ψ.ker.map (H.level 2).subtype, True
  let W := V.filter good
  let I := {ψ // ψ∈W}
  have hi (i : I) : good i.val := (Finset.mem_filter.mp i.property).2
  let hc (i : I) : ∀ a b : G, ⁅a,b⁆∈i.val.ker.map (H.level 2).subtype := (hi i).2.2.2.choose
  have hreturn (i : I) := degree_rank_factor_return c hsk H h0 h1 s hs2 hs q hqbound hq2 hq Γ hΓ
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
    exact ⟨ξ,Finset.mem_union_left _ hξ,DegreeCharacterData.mono hd hAA⟩
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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma degree_integer_linear_return [TopologicalSpace G] [IsTopologicalGroup G]
    (s : ℕ) (hs1 : 1 ≤ s) (f : ℤ→G) (γ : G) (ξ : G→*Multiplicative ℝ)
    (a : ℤ) (ha : (ξ γ).toAdd=(a:ℝ)) (P : ℝ[X]) (hP : P.natDegree ≤ s)
    (hPe : ∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z*(γ^z)⁻¹)).toAdd)
    (A : ℝ) (N : ℕ)
    (hPc : ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j) :
    ∃ Q : ℝ[X], Q.natDegree ≤ s ∧ (∀ z : ℤ, Q.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
      ∀ j : ℕ, 0<j → ∃ z : ℤ, |Q.coeff j-z| ≤ A/(N:ℝ)^j := by
  refine ⟨P+C (a:ℝ)*X,?_,?_,?_⟩
  · exact natDegree_add_le_of_degree_le hP ((natDegree_C_mul_le _ _).trans (by simpa using hs1))
  · intro z
    simp only [eval_add,eval_mul,eval_C,eval_X,hPe,map_mul,map_inv,map_zpow,
      toAdd_mul,toAdd_inv,toAdd_zpow,
      zsmul_eq_mul,ha]
    ring
  · intro j hj
    obtain ⟨z,hz⟩ := hPc j hj
    by_cases he : j=1
    · subst j
      refine ⟨z+a,?_⟩
      simpa only [coeff_add,coeff_C_mul,coeff_X_one,mul_one,Int.cast_add,add_sub_add_right_eq_sub] using hz
    · refine ⟨z,?_⟩
      simpa [coeff_add,coeff_C_mul,coeff_X,he,Ne.symm he] using hz

variable {t d : ℕ} (c : RealCoordinates G (t+(d+1))) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤) (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1)=⊥)
variable [∀ i, (H.level i).Normal]
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+(d+1)) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+(d+1)), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs2 hs hqbound hq2 hq hΓ in
 
theorem degree_vertical_unbounded_of_rank
    (ID : DegreeStatement (s-1))
    (IH : DegreeRankStatement G s (t+(d+1)) d)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (hF0 : (∫ x,F x ∂μ)=0) (χ : G→ℂ)
    (hχ : ∀ n∈H.level s, ‖χ n‖=1)
    (hw : ∀ n∈H.level s, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level s) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
        ∃ ξ∈U, DegreeCharacterData s Γ A N f ξ := by
  obtain ⟨U,A,hA,N₀,hN₀,hdesc⟩ := degree_vertical_correlation_of_rank c hsk H h0 h1 s hs2 hs
    q hqbound hq2 hq Γ hΓ ID IH μ F hF hF0 χ hχ hw z hz hχz δ hδ
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
  exact ⟨ξ,hξ,hξ0,hξc,hξΓ,degree_integer_linear_return s (by omega) f γ ξ a ha P hP hPe A N hPc⟩

end SquareInduction
end
end
 

 

end
end
end

end OAI
