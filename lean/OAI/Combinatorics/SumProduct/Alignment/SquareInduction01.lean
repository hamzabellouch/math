import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AbelianMalcev02
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
open scoped ComplexConjugate
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare PolynomialWeyl MeasureTheory UniformSquareObservable CompactFamilyDescent
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 

theorem uniform_unit_linear_square_descent
    (H : Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤)
    (Γ : Subgroup G) (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1) = ⊥)
    [TopologicalSpace.MetrizableSpace (ReducedSpace H h0 Γ s (le_trans (by decide : 1 ≤ 2) hs2) hs)]
    [CompactSpace (ReducedSpace H h0 Γ s (le_trans (by decide : 1 ≤ 2) hs2) hs)]
    (F : C(G ⧸ Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (χ : G → ℂ)
    (hχ : ∀ n ∈ H.level s, ‖χ n‖ = 1)
    (hw : ∀ n ∈ H.level s, ∀ x : G,
      F (QuotientGroup.mk (x*n)) = χ n * F (QuotientGroup.mk x))
    (z : G) (hz : z ∈ H.level s) (hχz : χ z ≠ 1)
    (C : Set G) (hCc : IsCompact C) (hC : ∀ g : G, ∃ c ∈ C, c⁻¹*g ∈ Γ)
    (δ : ℝ) (hδ : 0 < δ) :
    let R := restricted H h0
    letI := last_normal H h0 (by omega : 1 ≤ s) hs
    let π := QuotientGroup.mk' (R.level s)
    let Q := mapFiltration R π
    let X := ReducedSpace H h0 Γ s (le_trans (by decide : 1 ≤ 2) hs2) hs
    letI := TopologicalSpace.metrizableSpaceMetric X
    letI : MeasurableSpace X := borel X
    ∃ tests : Finset C(X,ℂ), (∀ Ψ∈tests, LipschitzWith 1 Ψ ∧ ‖Ψ‖ ≤ 1) ∧
      ∃ η : ℝ, 0 < η ∧
      ∀ μ : Measure X, IsProbabilityMeasure μ →
        SMulInvariantMeasure ((level H h0 1) ⧸ R.level s) X μ →
      ∀ (f : ℤ → G) (hf : Polynomial H 0 f) (hf0 : f 0=1),
      ∀ N T : ℕ, 0 < N → 0 < T →
        δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
        4 * (T : ℝ) / N ≤ δ^2/4 →
      ∃ A : Finset ℕ,
        (∀ h ∈ A, h < T) ∧ δ^2/8*T ≤ (A.card : ℝ) ∧
        ∀ h ∈ A, ∃ Ψ ∈ tests, ∃ v ∈ C, ∃ γ ∈ Γ,
          f 1^(h:ℤ) = v*γ ∧
          let p := fun n => π (linearNormalizedPair H h0 h1 hf
            (linearRemainder H h0 hf hf0 h) h v n)
          Polynomial Q 0 p ∧
          (∀ ts : List ℤ, s ≤ ts.length → ∀ n, iterDiff ts p n = 1) ∧
          η ≤ ‖mean N (fun n => Ψ (QuotientGroup.mk (p n))) -
            ∫ x, Ψ x ∂μ‖ := by
  classical
  let R := restricted H h0
  let := last_normal H h0 (by omega : 1 ≤ s) hs
  let π := QuotientGroup.mk' (R.level s)
  let X := ReducedSpace H h0 Γ s (le_trans (by decide : 1 ≤ 2) hs2) hs
  let := TopologicalSpace.metrizableSpaceMetric X
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨S,ε,hε,hdesc⟩ := uniform_dense_linear_square_descent H h0 h1 Γ s hs2 hs
    F hF χ hχ hw z hz hχz C hCc hC δ hδ
  let K : Set C(X,ℂ) := Subtype.val '' (S : Set {Ψ : C(X,ℂ) // Ψ∈lipschitzMaps})
  have hK : IsCompact K := (S.finite_toSet.image Subtype.val).isCompact
  obtain ⟨tests,htests,η,hη,htest⟩ := finite_unit_lipschitz_obstruction K hK ε 2 hε (by norm_num)
  refine ⟨tests,htests,η,hη,?_⟩
  intro μ hprob hinv f hf hf0 N T hN hT hdisc hboundary
  let := hprob
  obtain ⟨A,hAT,hA,hAd⟩ := hdesc μ hprob hinv f hf hf0 N T hN hT hdisc hboundary
  refine ⟨A,hAT,hA,?_⟩
  intro h ha
  obtain ⟨Ψ,hΨ,v,hv,γ,hγ,hfac,hp,hptop,hdisc⟩ := hAd h ha
  let p := fun n => π (linearNormalizedPair H h0 h1 hf
    (linearRemainder H h0 hf hf0 h) h v n)
  obtain ⟨Φ,hΦ,hdΦ⟩ := htest (FourierObstruction.discrepancy μ N (fun n => QuotientGroup.mk (p n)))
    (FourierObstruction.discrepancy_bound μ N hN _) ⟨Ψ.val,⟨Ψ,hΨ,rfl⟩,hdisc⟩
  exact ⟨Φ,hΦ,v,hv,γ,hγ,hfac,hp,hptop,hdΦ⟩

end SquareInduction
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl UniformSquareObservable AbelianMalcevTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable (hs : H.level 3=⊥)
variable [((restricted H h0).level 2).Normal]
variable (Γ : Subgroup G)
variable {r : ℕ} (cR : RealCoordinates ((level H h0 1)⧸(restricted H h0).level 2) r)
variable (hskR : SecondKind cR)
variable (hΓR : ∀ g, g∈((Γ.prod Γ).comap (level H h0 1).subtype).map
    (QuotientGroup.mk' ((restricted H h0).level 2)) ↔ ∀ i, ∃ z : ℤ, cR.coord g i=z)

include hskR hΓR hs in
 

theorem quadratic_square_characters
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (χ : G→ℂ)
    (hχ : ∀ n∈H.level 2, ‖χ n‖=1)
    (hw : ∀ n∈H.level 2, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level 2) (hχz : χ z≠1)
    (C : Set G) (hCc : IsCompact C) (hC : ∀ g : G, ∃ c∈C, c⁻¹*g∈Γ)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ Ξ : Finset (level H h0 1 →* Multiplicative ℝ),
      (∀ ξ∈Ξ, Continuous ξ ∧ ∀ x : level H h0 1, x.val∈Γ.prod Γ → ∃ z : ℤ, (ξ x).toAdd=z) ∧
    ∃ A : ℝ, 0<A ∧ ∃ ρ : ℝ, 0<ρ ∧
      ∀ (f : ℤ→G) (hf : Polynomial H 0 f) (hf0 : f 0=1),
      ∀ N T : ℕ, 0<N → 0<T →
        δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
        4*(T:ℝ)/N ≤ δ^2/4 →
      ∃ S : Finset ℕ, (∀ h∈S, h<T) ∧ ρ*T ≤ (S.card:ℝ) ∧
      ∃ ξ∈Ξ, ξ≠1 ∧ ∀ h∈S, ∃ v∈C, ∃ γ∈Γ,
        f 1^(h:ℤ)=v*γ ∧ ∃ W : ℝ[X], W.natDegree ≤ 1 ∧
          (∀ n : ℤ, W.eval (n:ℝ)=
            (ξ (linearNormalizedPair H h0 h1 hf (linearRemainder H h0 hf hf0 h) h v n)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |W.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let R := restricted H h0
  let π := QuotientGroup.mk' (R.level 2)
  let Q := mapFiltration R π
  let L := ((Γ.prod Γ).comap (level H h0 1).subtype).map π
  let K := (level H h0 1)⧸R.level 2
  let X := K⧸L
  have hQ := quotient_lowers_degree H h0 (by decide : 1≤2) hs
  have hadd := coordinates_additive_of_secondLevel_bot cR Q hskR hQ.2.1 hQ.2.2
  let e := quotientHomeomorph cR hadd L hΓR
  let : TopologicalSpace.MetrizableSpace X := e.isEmbedding.metrizableSpace
  let : CompactSpace X := quotient_compact cR L hΓR
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨μ,hμ,_⟩ := existsUnique_coordinateHaar cR L hΓR
  let : SMulInvariantMeasure K X (μ : Measure X) := hμ
  obtain ⟨tests,htests,η,hη,hdesc⟩ := uniform_unit_linear_square_descent H h0 h1 Γ 2 (by decide) hs
    F hF χ hχ hw z hz hχz C hCc hC δ hδ
  obtain ⟨U,hU,A,hA,hprod⟩ := quantitative_abelian_producer cR hadd L hΓR rfl Q 1 hQ.2.2
    (μ : Measure X) η hη
  let Ξ := U.image (fun ξ => ξ.comp π)
  refine ⟨Ξ,?_,A,hA,δ^2/(8*((U.card:ℝ)+1)),by positivity,?_⟩
  · intro ξ hξ
    obtain ⟨ζ,hζ,rfl⟩ := Finset.mem_image.mp hξ
    refine ⟨(hU ζ hζ).1.comp continuous_quotient_mk',?_⟩
    intro x hx
    exact (hU ζ hζ).2 (π x) (Subgroup.mem_map.mpr ⟨x,hx,rfl⟩)
  · intro f hf hf0 N T hN hT hmean hbound
    obtain ⟨S,hST,hS,hSd⟩ := hdesc (μ:Measure X) inferInstance hμ f hf hf0 N T hN hT hmean hbound
    have hget : ∀ h∈S, ∃ ξ∈U, ξ≠1 ∧ ∃ v∈C, ∃ γ∈Γ,
        f 1^(h:ℤ)=v*γ ∧ ∃ W : ℝ[X], W.natDegree ≤ 1 ∧
          (∀ n : ℤ, W.eval (n:ℝ)=
            (ξ (π (linearNormalizedPair H h0 h1 hf (linearRemainder H h0 hf hf0 h) h v n))).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |W.coeff j-z| ≤ A/(N:ℝ)^j := by
      intro h hh
      obtain ⟨Ψ,hΨ,v,hv,γ,hγ,hfac,hp,_,hd⟩ := hSd h hh
      obtain ⟨ξ,hξ,hξ0,W,hW,hWe,hWc⟩ := hprod N hN _ hp
        ⟨Ψ,(htests Ψ hΨ).1,(htests Ψ hΨ).2,hd⟩
      exact ⟨ξ,hξ,hξ0,v,hv,γ,hγ,hfac,W,hW,hWe,hWc⟩
    choose ξ hξ hξ0 v hv γ hγ hfac W hW hWe hWc using hget
    have hSne : S.Nonempty := by
      apply Finset.card_pos.mp
      have hpos : 0<δ^2/8*(T:ℝ) := by positivity
      have hc : 0<(S.card:ℝ) := hpos.trans_le hS
      exact_mod_cast hc
    let ξ' : ℕ → K →* Multiplicative ℝ := fun h => if hh : h∈S then ξ h hh else 1
    have hmap : ∀ h∈S, ξ' h∈U := by intro h hh; simpa [ξ',hh] using hξ h hh
    have hUne : U.Nonempty := by obtain ⟨h,hh⟩ := hSne; exact ⟨ξ' h,hmap h hh⟩
    have hcard : U.card • (δ^2/(8*((U.card:ℝ)+1))*(T:ℝ)) ≤ (S.card:ℝ) := by
      rw [nsmul_eq_mul]
      calc
        _ ≤ δ^2/8*(T:ℝ) := by
          have hu : (U.card:ℝ)/((U.card:ℝ)+1) ≤ 1 := by apply (div_le_one (by positivity)).mpr; linarith
          calc
            _ = ((U.card:ℝ)/((U.card:ℝ)+1)) * (δ^2/8*(T:ℝ)) := by
              field_simp
            _ ≤ 1*(δ^2/8*(T:ℝ)) := mul_le_mul_of_nonneg_right hu (by positivity)
            _ = _ := one_mul _
        _ ≤ _ := hS
    obtain ⟨ζ,hζ,hfiber⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmap hUne hcard
    let B := S.filter (fun h => ξ' h=ζ)
    have hBne : B.Nonempty := by
      apply Finset.card_pos.mp
      have hpos : 0<δ^2/(8*((U.card:ℝ)+1))*(T:ℝ) := by positivity
      have hc : 0<(B.card:ℝ) := hpos.trans_le hfiber
      exact_mod_cast hc
    have hζ0 : ζ≠1 := by
      obtain ⟨h,hh⟩ := hBne
      have hhS := (Finset.mem_filter.mp hh).1
      have hhζ : ξ h hhS=ζ := by simpa [ξ',hhS] using (Finset.mem_filter.mp hh).2
      exact hhζ ▸ hξ0 h hhS
    refine ⟨B,fun h hh => hST h (Finset.mem_filter.mp hh).1,hfiber,
      ζ.comp π,Finset.mem_image.mpr ⟨ζ,hζ,rfl⟩,?_,?_⟩
    · intro he
      apply hζ0
      apply MonoidHom.ext
      intro x
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (R.level 2) x
      exact DFunLike.congr_fun he y
    · intro h hh
      have hhS := (Finset.mem_filter.mp hh).1
      have hhζ : ξ h hhS=ζ := by simpa [ξ',hhS] using (Finset.mem_filter.mp hh).2
      refine ⟨v h hhS,hv h hhS,γ h hhS,hγ h hhS,hfac h hhS,W h hhS,hW h hhS,?_,hWc h hhS⟩
      intro n
      change _=(ζ (π _)).toAdd
      rw [← hhζ]
      exact hWe h hhS n

end SquareInduction
end
end
 

 
section
noncomputable section
open scoped BigOperators commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
namespace MalcevHorizontal
open RationalLattice CubeFaces LeibmanSquare SquareHorizontalCharacter RealCharacters MalcevCharacters CharacterFactorization
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n d : ℕ} (c : RealCoordinates G n) (hd : d  ≤  n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i)=0)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hlevel : ∀ g : G, g∈H.level 2 ↔ horizontal c hd g=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)

include hlin hlevel hΓ in
 

theorem uniform_character_of_commutator_level (hcomm : H.level 2=_root_.commutator G)
    (s : ℕ) (hs2 : 2  ≤  s) (hs : H.level (s+1)=⊥)
    (Ξ : Finset (level H h0 1 →* Multiplicative ℝ))
    (hΞc : ∀ ξ∈Ξ, Continuous ξ)
    (hΞΓ : ∀ ξ∈Ξ, ∀ x : level H h0 1, x.val∈Γ.prod Γ → ∃ z : ℤ, (ξ x).toAdd=z)
    (δ A : ℝ) (hδ : 0<δ) (hA : 0 ≤ A) :
    ∃ U : Finset (G →* Multiplicative ℝ), ∃ C : ℝ, 0<C ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ξ∈Ξ, ξ≠1 →
      ∀ (f : ℤ→G) (hf : Polynomial H 0 f) (hf0 : f 0=1),
      ‖horizontal c hd (f 1)‖ ≤ 1 →
      ∀ v : ℕ→G, (∀ h, ‖horizontal c hd (v h)‖ ≤ 1) →
      (∀ h, (v h)⁻¹*f 1^h∈Γ) →
      ∀ S : Finset ℕ, S⊆Finset.range N → δ*N ≤ (S.card:ℝ) →
      (∀ h∈S, ∃ W : ℝ[X],
        (∀ z : ℤ, W.eval (z:ℝ)=
          (ξ (linearNormalizedPair H h0 h1 hf (linearRemainder H h0 hf hf0 h) h (v h) z)).toAdd) ∧
        ∀ j : ℕ, 0<j → j ≤ s → ∃ z : ℤ, |W.coeff j-z| ≤ A/(N:ℝ)^j) →
      ∃ χ∈U, χ≠1 ∧ Continuous χ ∧ (∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ s ∧ (∀ z : ℤ, P.eval (z:ℝ)=(χ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ C/(N:ℝ)^j := by
  classical
  obtain ⟨R,hR,C,hC,N₀,hN₀,hdesc⟩ := geometric_scalar_descent c hd hlin H h0 h1 hlevel Γ hΓ
    s hs2 hs Ξ δ A hδ hA
  let U := boundedCharacters c hd hlin R ∪ scaledFamily (Ξ.image (fun ξ => ξ.comp (diagonal H h0 h1))) R
  refine ⟨U,C,hC,N₀,hN₀,?_⟩
  intro N hNN ξ hξ hξ0 f hf hf0 hf1 v hv hvΓ S hSN hS hsmall
  rcases hdesc N hNN ξ hξ (hΞc ξ hξ) (hΞΓ ξ hξ) f hf hf0 hf1 v hv hvΓ S hSN hS hsmall with hob | hz
  · obtain ⟨k,hk,hkR,χ,hχeq,hχ0,hχc,hχΓ,P,hP,hPe,hPc⟩ := hob
    refine ⟨χ,?_,hχ0,hχc,hχΓ,P,hP.trans (by omega),hPe,hPc⟩
    exact Finset.mem_union_left _ (hχeq ▸ mem_boundedCharacters c hd hlin R k hkR)
  · obtain ⟨hp,q,hq,hqR,P,Q,hP,hQ,hQ0,hQ1,hPe,hQe,hPc,hQc⟩ := hz
    have hd0 : ξ.comp (diagonal H h0 h1)≠1 := by
      intro he
      let χ := intScale (ξ.comp (lower H h0)) q
      have hc := zero_pairing_kernel H h0 h1 ξ q hp
      have hk := lower_kernel_lt H χ (intScale_ne_one _ hq (lower_ne_one_of_diagonal H h0 h1 ξ hξ0 he))
      have hle : H.level 2  ≤  χ.ker.map (H.level 2).subtype := by
        apply hcomm.le.trans
        rw [_root_.commutator_def]
        exact Subgroup.commutator_le.mpr (fun a _ b _ => hc a b)
      exact (not_le_of_gt hk) hle
    let χ := intScale (ξ.comp (diagonal H h0 h1)) q
    refine ⟨χ,Finset.mem_union_right _ (mem_scaledFamily (Finset.mem_image.mpr ⟨ξ,hξ,rfl⟩) hqR),
      intScale_ne_one _ hq hd0,intScale_continuous _ q ((hΞc ξ hξ).comp (diagonal_continuous H h0 h1)),
      intScale_integral _ q Γ (diagonal_integral H h0 h1 ξ Γ (hΞΓ ξ hξ)),
      Polynomial.C (q:ℝ)*P,(natDegree_C_mul_le _ _).trans hP,?_,?_⟩
    · intro z
      simp only [eval_mul,eval_C,hPe,intScale_apply,χ]
    · intro j hj
      simpa only [coeff_C_mul] using hPc j hj

end MalcevHorizontal

end
end
end
end
end

end OAI
