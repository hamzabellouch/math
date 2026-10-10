import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction09
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
namespace SquareInduction
 
theorem finite_dense_choice {α : Type*} (U : Finset α) (S : Finset ℕ)
    (ρ T : ℝ) (hρ : 0<ρ) (hT : 0<T) (hS : ρ*T ≤ (S.card:ℝ))
    (P : ℕ→α→Prop) (hget : ∀ h∈S, ∃ a∈U, P h a) :
    ∃ B : Finset ℕ, B⊆S ∧ B.Nonempty ∧ ρ/((U.card:ℝ)+1)*T ≤ (B.card:ℝ) ∧
      ∃ a∈U, ∀ h∈B, P h a := by
  classical
  have hSne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast (mul_pos hρ hT).trans_le hS)
  obtain ⟨h₀,hh₀⟩ := hSne
  obtain ⟨a₀,ha₀,_⟩ := hget h₀ hh₀
  choose a ha hPa using hget
  let f : ℕ→α := fun h => if hh : h∈S then a h hh else a₀
  have hmap : ∀ h∈S, f h∈U := by
    intro h hh
    simpa only [f,dite_eq_left hh] using ha h hh
  have hcard : U.card • (ρ/((U.card:ℝ)+1)*T) ≤ (S.card:ℝ) := by
    rw [nsmul_eq_mul]
    have hu : (U.card:ℝ)/((U.card:ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith
    calc
      _ = ((U.card:ℝ)/((U.card:ℝ)+1))*(ρ*T) := by ring
      _ ≤ 1*(ρ*T) := mul_le_mul_of_nonneg_right hu (mul_pos hρ hT).le
      _ ≤ _ := by simpa only [one_mul] using hS
  obtain ⟨a',ha',hfiber⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmap ⟨a₀,ha₀⟩ hcard
  let B := S.filter (fun h => f h=a')
  refine ⟨B,Finset.filter_subset _ _,?_,hfiber,a',ha',?_⟩
  · apply Finset.card_pos.mp
    have hp : 0<ρ/((U.card:ℝ)+1)*T := by positivity
    exact_mod_cast hp.trans_le hfiber
  · intro h hh
    have hhS := (Finset.mem_filter.mp hh).1
    have he : a h hhS=a' := by simpa only [f,dite_eq_left hhS] using (Finset.mem_filter.mp hh).2
    exact he ▸ hPa h hhS

end SquareInduction
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl UniformSquareObservable AbelianMalcevTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable (s : ℕ) (hs2 : 2≤ s) (hs : H.level (s+1)=⊥)
variable [((restricted H h0).level s).Normal]
variable (Γ : Subgroup G)
variable {r : ℕ} (cR : RealCoordinates ((level H h0 1)⧸(restricted H h0).level s) r)
variable (hskR : SecondKind cR)
variable (hΓR : ∀ g, g∈((Γ.prod Γ).comap (level H h0 1).subtype).map
    (QuotientGroup.mk' ((restricted H h0).level s)) ↔ ∀ i, ∃ z : ℤ, cR.coord g i=z)

include hskR hΓR hs hs2 in
 

theorem degree_square_characters
    (IH : DegreeStatement (s-1))
    (qR : ℕ→ℕ) (hqRbound : ∀ i, qR i ≤ r)
    (hqR : ∀ i g, g∈(mapFiltration (restricted H h0)
      (QuotientGroup.mk' ((restricted H h0).level s))).level i ↔
        ∀ j : Fin r, j.val<qR i → cR.coord g j=0)
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (χ : G→ℂ)
    (hχ : ∀ n∈H.level s, ‖χ n‖=1)
    (hw : ∀ n∈H.level s, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level s) (hχz : χ z≠1)
    (C : Set G) (hCc : IsCompact C) (hC : ∀ g : G, ∃ c∈C, c⁻¹*g∈Γ)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ Ξ : Finset (level H h0 1 →* Multiplicative ℝ),
      (∀ ξ∈Ξ, Continuous ξ ∧ ∀ x : level H h0 1, x.val∈Γ.prod Γ → ∃ z : ℤ, (ξ x).toAdd=z) ∧
    ∃ A : ℝ, 0<A ∧ ∃ ρ : ℝ, 0<ρ ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ (f : ℤ→G) (hf : Polynomial H 0 f) (hf0 : f 0=1),
      ∀ N T : ℕ, N₀ ≤ N → 0<T →
        δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
        4*(T:ℝ)/N ≤ δ^2/4 →
      ∃ S : Finset ℕ, (∀ h∈S, h<T) ∧ ρ*T ≤ (S.card:ℝ) ∧
      ∃ ξ∈Ξ, ξ≠1 ∧ ∀ h∈S, ∃ v∈C, ∃ γ∈Γ,
        f 1^(h:ℤ)=v*γ ∧ ∃ W : ℝ[X], W.natDegree ≤ s-1 ∧
          (∀ n : ℤ, W.eval (n:ℝ)=
            (ξ (linearNormalizedPair H h0 h1 hf (linearRemainder H h0 hf hf0 h) h v n)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |W.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let R := restricted H h0
  let π := QuotientGroup.mk' (R.level s)
  let Q := mapFiltration R π
  let L := ((Γ.prod Γ).comap (level H h0 1).subtype).map π
  let K := (level H h0 1)⧸R.level s
  let X := K⧸L
  have hQ := quotient_lowers_degree H h0 (by omega : 1≤ s) hs
  let : CompactSpace X := quotient_compact cR L hΓR
  let : MetricSpace X := coordinateQuotientMetric cR L hΓR
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨μ,hμ,_⟩ := existsUnique_coordinateHaar cR L hΓR
  let : SMulInvariantMeasure K X (μ : Measure X) := hμ
  obtain ⟨tests,htests,η,hη,hdesc⟩ := uniform_unit_linear_square_descent H h0 h1 Γ s hs2 hs
    F hF χ hχ hw z hz hχz C hCc hC δ hδ
  have hsQ : Q.level ((s-1)+1)=⊥ := by simpa only [Nat.sub_add_cancel (by omega : 1≤ s)] using hQ.2.2
  obtain ⟨U₀,A,hA,N₀,hN₀,hprod⟩ := IH K r r cR hskR Q hQ.1 hQ.2.1 hsQ qR hqRbound hqR
    (Nat.sub_le _ _) L hΓR (μ : Measure X) (tests : Set C(X,ℂ)) (Set.toFinite _).isCompact η hη
  let U := U₀.filter (fun ξ : K→*Multiplicative ℝ => Continuous ξ ∧ ∀ g∈L, ∃ z : ℤ, (ξ g).toAdd=z)
  have hU (ξ : K→*Multiplicative ℝ) (hξ : ξ∈U) : Continuous ξ ∧ ∀ g∈L, ∃ z : ℤ, (ξ g).toAdd=z :=
    (Finset.mem_filter.mp hξ).2
  let Ξ := U.image (fun ξ => ξ.comp π)
  refine ⟨Ξ,?_,A,hA,δ^2/(8*((U.card:ℝ)+1)),by positivity,N₀,hN₀,?_⟩
  · intro ξ hξ
    obtain ⟨ζ,hζ,rfl⟩ := Finset.mem_image.mp hξ
    refine ⟨(hU ζ hζ).1.comp continuous_quotient_mk',?_⟩
    intro x hx
    exact (hU ζ hζ).2 (π x) (Subgroup.mem_map.mpr ⟨x,hx,rfl⟩)
  · intro f hf hf0 N T hNN hT hmean hbound
    have hN : 0<N := hN₀.trans_le hNN
    obtain ⟨S,hST,hS,hSd⟩ := hdesc (μ:Measure X) inferInstance hμ f hf hf0 N T hN hT hmean hbound
    have hget : ∀ h∈S, ∃ ξ∈U, ξ≠1 ∧ ∃ v∈C, ∃ γ∈Γ,
        f 1^(h:ℤ)=v*γ ∧ ∃ W : ℝ[X], W.natDegree ≤ s-1 ∧
          (∀ n : ℤ, W.eval (n:ℝ)=
            (ξ (π (linearNormalizedPair H h0 h1 hf (linearRemainder H h0 hf hf0 h) h v n))).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |W.coeff j-z| ≤ A/(N:ℝ)^j := by
      intro h hh
      obtain ⟨Ψ,hΨ,v,hv,γ,hγ,hfac,hp,hzero,hd⟩ := hSd h hh
      have hdisc : η ≤ ‖FourierObstruction.discrepancy (μ:Measure X) N
          (fun k => QuotientGroup.mk (π (linearNormalizedPair H h0 h1 hf
            (linearRemainder H h0 hf hf0 h) h v k))) Ψ‖ := by
        exact hd
      obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,W,hW,hWe,hWc⟩ := hprod N hNN _ hp ⟨Ψ,hΨ,hdisc⟩
      have hξU : ξ∈U := Finset.mem_filter.mpr ⟨hξ,hξc,hξΓ⟩
      exact ⟨ξ,hξU,hξ0,v,hv,γ,hγ,hfac,W,hW,hWe,hWc⟩
    obtain ⟨B,hBS,hBne,hBd,ζ,hζ,hBdata⟩ := finite_dense_choice U S (δ^2/8) (T:ℝ)
      (by positivity) (by exact_mod_cast hT) hS _ hget
    have hζ0 : ζ≠1 := by
      obtain ⟨h,hh⟩ := hBne
      exact (hBdata h hh).1
    refine ⟨B,fun h hh => hST h (hBS hh),?_,
      ζ.comp π,Finset.mem_image.mpr ⟨ζ,hζ,rfl⟩,?_,?_⟩
    · simpa only [div_div] using hBd
    · intro he
      apply hζ0
      apply MonoidHom.ext
      intro x
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (R.level s) x
      exact DFunLike.congr_fun he y
    · intro h hh
      exact (hBdata h hh).2

end SquareInduction
end
end
 

 
section
noncomputable section
open scoped commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl UniformSquareObservable AbelianMalcevTorus MalcevHorizontal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n d r : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i)=0)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1)=⊥)
variable [((restricted H h0).level s).Normal]
variable (hlevel : ∀ g : G, g∈H.level 2 ↔ horizontal c hd g=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable (cR : RealCoordinates ((level H h0 1)⧸(restricted H h0).level s) r)
variable (hskR : SecondKind cR)
variable (hΓR : ∀ g, g∈((Γ.prod Γ).comap (level H h0 1).subtype).map
    (QuotientGroup.mk' ((restricted H h0).level s)) ↔ ∀ i, ∃ z : ℤ, cR.coord g i=z)

variable {m : ℕ} (c₂ : RealCoordinates (H.level 2) m) (hsk₂ : SecondKind c₂)
variable (hΓ₂ : ∀ x : H.level 2, x.val∈Γ ↔ ∀ i, ∃ z : ℤ, c₂.coord x i=z)
variable (r₂ : Fin (s+1)→ℕ)
variable (hlevel₂ : ∀ i (x : H.level 2), x.val∈H.level (i.val+2) ↔
  ∀ u : Fin m, u.val < r₂ i → c₂.coord x u=0)
include hlin hlevel hΓ hskR hΓR h1 hs2 hs hsk₂ hΓ₂ hlevel₂ in
 

theorem degree_vertical_factor_alternative
    (IH : DegreeStatement (s-1))
    (qR : ℕ→ℕ) (hqRbound : ∀ i, qR i ≤ r)
    (hqR : ∀ i g, g∈(mapFiltration (restricted H h0)
      (QuotientGroup.mk' ((restricted H h0).level s))).level i ↔
        ∀ j : Fin r, j.val<qR i → cR.coord g j=0)
    (E : ℝ)
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (χ : G→ℂ)
    (hχ : ∀ n∈H.level s, ‖χ n‖=1)
    (hw : ∀ n∈H.level s, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level s) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ V : Finset (H.level 2→*Multiplicative ℝ),
      ∃ A : ℝ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∃ Tmax : ℕ, 0<Tmax ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      ‖horizontal c hd (f 1)‖ ≤ 1 → δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
      (∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ s ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j) ∨
      (∃ ψ∈V, ψ≠1 ∧ Continuous ψ ∧ (∀ x : H.level 2, x.val∈Γ → ∃ z : ℤ, (ψ x).toAdd=z) ∧
        ∃ hc : ∀ a b : G, ⁅a,b⁆∈ψ.ker.map (H.level 2).subtype,
        ψ.ker.map (H.level 2).subtype < H.level 2 ∧
        ∃ T : ℕ, 0<T ∧ T ≤ Tmax ∧
          CharacterFactorization.SmoothFactorizationAt H Γ c₂ ψ hc E B N T f) := by
  classical
  let : T2Space G := c.coord.symm.t2Space
  obtain ⟨C,hCc,hC,hCb⟩ := compact_horizontal_representatives c hd Γ hΓ
  obtain ⟨Ξ,hΞ,B,hB,ρ,hρ,M₀,hM₀,hprod⟩ := degree_square_characters H h0 h1 s hs2 hs Γ cR hskR hΓR IH qR hqRbound hqR
    F hF χ hχ hw z hz hχz C hCc hC δ hδ
  obtain ⟨k,hk,hscale⟩ := square_shift_scales δ hδ
  have hden : 0<(2:ℝ)*k := by positivity
  obtain ⟨U,V,A,hA,B',hB',Tmax,hTmax,N₀,hN₀,hdesc⟩ :=
    uniform_character_or_proper_factorization c hd hlin H h0 h1 hlevel Γ hΓ c₂ hsk₂ hΓ₂
      s hs2 hs r₂ hlevel₂ Ξ (fun ξ h => (hΞ ξ h).1) (fun ξ h => (hΞ ξ h).2)
      (ρ/(2*k)) B E (div_pos hρ hden) hB.le
  refine ⟨U,V,A,hA,B',hB',Tmax,hTmax,N₀+2*k+M₀,by omega,?_⟩
  intro N hNN f hf hf0 hf1 hmean
  have hNN₀ : N₀ ≤ N := by omega
  have hNk : 2*k ≤ N := by omega
  have hNM₀ : M₀ ≤ N := by omega
  obtain ⟨hT,hTN,hTd,hbound⟩ := hscale N hNk
  have hN : 0<N := hN₀.trans_le hNN₀
  obtain ⟨S,hST,hS,ξ,hξ,hξ0,hdata⟩ := hprod f hf hf0 N (N/k) hNM₀ hT hmean hbound
  choose v hv γ hγ hfac W hW hWe hWc using hdata
  let v' : ℕ→G := fun h => if hh : h∈S then v h hh else reduceCoordinates c (f 1^h) n
  have hv' (h : ℕ) : ‖horizontal c hd (v' h)‖ ≤ 1 := by
    dsimp [v']; split_ifs with hh
    · exact hCb _ (hv h hh)
    · exact reduced_horizontal_bound c hd _
  have hvΓ' (h : ℕ) : (v' h)⁻¹*f 1^h∈Γ := by
    dsimp [v']; split_ifs with hh
    · have he : f 1^h=v h hh*γ h hh := by simpa only [zpow_natCast] using hfac h hh
      rw [he,inv_mul_cancel_left]
      exact hγ h hh
    · exact reduceCoordinates_coset c Γ hΓ _ n
  apply hdesc N hNN₀ ξ hξ hξ0 f hf hf0 hf1 v' hv' hvΓ' S
  · intro h hh
    exact Finset.mem_range.mpr ((hST h hh).trans_le hTN)
  · calc
      ρ/(2*k)*(N:ℝ) = ρ*((N:ℝ)/(2*k)) := by ring
      _  ≤  ρ*((N/k:ℕ):ℝ) := mul_le_mul_of_nonneg_left hTd hρ.le
      _  ≤  _ := hS
  · intro h hh
    refine ⟨W h hh,?_,fun j hj _ => hWc h hh j hj⟩
    simpa only [v',dite_eq_left hh] using hWe h hh

end SquareInduction

end
end
end
end
end

end OAI
