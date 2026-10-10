import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction04
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators
end
end
 

 
section
noncomputable section
open scoped commutatorElement
namespace RationalTailCoordinates
open RationalLattice MalcevCharacters CubeFaces
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r n : ℕ} (c : RealCoordinates G (r+(n+1))) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ r+(n+1)) (hq2 : q 2=r)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (r+(n+1)), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
include hsk h0 h1 hqbound hq2 hq hΓ in
 

theorem strict_filtration_refinement_geometry
    (χ : H.level 2→*Multiplicative ℝ) (hχ : Continuous χ)
    (hχΓ : ∀ g : H.level 2, g.val∈Γ → ∃ z : ℤ, (χ g).toAdd=z)
    (hc : ∀ a b : G, ⁅a,b⁆∈χ.ker.map (H.level 2).subtype) (hχ0 : χ≠1) :
    ∃ Λ : Subgroup G, ∃ e : RealCoordinates G (r+(n+1)), SecondKind e ∧
      (∀ g : G, g∈Λ ↔ ∀ i, ∃ z : ℤ, e.coord g i=z) ∧
      Λ≤Γ ∧ (Λ.subgroupOf Γ).FiniteIndex ∧
      ∃ q' : ℕ→ℕ, (∀ k, q' k ≤ r+(n+1)) ∧ q' 2=r+1 ∧
        ∀ k (g : G), g∈(H.refine (χ.ker.map (H.level 2).subtype) hc).level k ↔
          ∀ i : Fin (r+(n+1)), i.val < q' k → e.coord g i=0 := by
  classical
  have htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (r+(n+1)), i.val < r → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq 2 g
  have hcomm : _root_.commutator G ≤ χ.ker.map (H.level 2).subtype := by
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact hc a b
  obtain ⟨ψ,hψ,hagree,hint,_⟩ := exists_integer_extension c (H.level 2) htail hsk Γ hΓ χ hχ hχΓ hcomm
  have hnψ : ψ.comp (H.level 2).subtype≠1 := by rwa [hagree]
  obtain ⟨Λ,e,hesk,hΛ,hle,hindex,hr,hsecond,hall⟩ :=
    RationalCharacterFirst.exists_strict_refined_integer_cover c ψ Γ hΓ hψ hint (H.level 2) r htail hnψ
  have href (k : ℕ) (hk : 2 ≤ k) :
      (H.refine (χ.ker.map (H.level 2).subtype) hc).level k=H.level k⊓ψ.ker := by
    simp only [Filtration.refine,not_lt.mpr hk,ite_false]
    rw [mapped_kernel_eq_inter (H.level 2) χ ψ hagree,← inf_assoc,
      inf_eq_left.mpr (H.antitone hk)]
  have hsecond' : ∀ g : G, g∈(H.refine (χ.ker.map (H.level 2).subtype) hc).level 2 ↔
      ∀ i : Fin (r+(n+1)), i.val < r+1 → e.coord g i=0 := by
    intro g
    rw [href 2 le_rfl]
    exact hsecond g
  have hall' (k : ℕ) : ∃ u : ℕ, u ≤ r+(n+1) ∧
      ∀ g : G, g∈(H.refine (χ.ker.map (H.level 2).subtype) hc).level k ↔
        ∀ i : Fin (r+(n+1)), i.val < u → e.coord g i=0 := by
    by_cases hk : k < 2
    · refine ⟨0,by omega,?_⟩
      have htop : H.level k=⊤ := by rcases (by omega : k=0 ∨ k=1) with he | he <;> simpa only [he] using (by first | exact h0 | exact h1)
      intro g
      simp only [Filtration.refine,hk,ite_true,htop,Subgroup.mem_top,Nat.not_lt_zero,IsEmpty.forall_iff,implies_true]
    · obtain ⟨u,hu,he⟩ := hall (H.level k) (q k) (hqbound k) (hq k)
      refine ⟨u,hu,?_⟩
      intro g
      rw [href k (by omega)]
      exact he g
  choose q₀ hq₀ hq₀e using hall'
  let q' : ℕ→ℕ := fun k => if k=2 then r+1 else q₀ k
  refine ⟨Λ,e,hesk,hΛ,hle,hindex,q',?_,by simp [q'],?_⟩
  · intro k
    dsimp [q']
    split_ifs
    · omega
    · exact hq₀ k
  · intro k g
    by_cases hk : k=2
    · simpa only [hk,q',ite_true] using hsecond' g
    · simpa only [q',hk,ite_false] using hq₀e k g

end RationalTailCoordinates
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevCentralTorus RationalTailCoordinates UnitAddTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 

def QuadraticCharacterData (Γ : Subgroup G) (A : ℝ) (N : ℕ) (f : ℤ→G)
    (ξ : G→*Multiplicative ℝ) : Prop :=
  ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
    ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
      ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j

def QuadraticCompactEstimate (H : Filtration G) (Γ : Subgroup G)
    [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)] [CompactSpace (G⧸Γ)]
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] (K : Set C(G⧸Γ,ℂ)) (δ : ℝ) : Prop :=
  ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
    (∃ F∈K, δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, QuadraticCharacterData Γ A N f ξ

def QuadraticNormalizedEstimate (H : Filtration G) (Γ : Subgroup G)
    [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)] [CompactSpace (G⧸Γ)]
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] (K : Set C(G⧸Γ,ℂ)) (δ : ℝ) : Prop :=
  ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
    (∃ F∈K, δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, QuadraticCharacterData Γ A N f ξ

omit [IsTopologicalGroup G] in
lemma QuadraticCharacterData.mono [IsTopologicalGroup G]
    {Γ : Subgroup G} {A B : ℝ} {N : ℕ} {f : ℤ→G}
    {ξ : G→*Multiplicative ℝ} (hd : QuadraticCharacterData Γ A N f ξ) (hAB : A≤B) :
    QuadraticCharacterData Γ B N f ξ := by
  obtain ⟨hξ,hc,hΓ,P,hP,hPe,hPc⟩ := hd
  refine ⟨hξ,hc,hΓ,P,hP,hPe,?_⟩
  intro j hj
  obtain ⟨z,hz⟩ := hPc j hj
  exact ⟨z,hz.trans (div_le_div_of_nonneg_right hAB (by positivity))⟩

 

def QuadraticRankStatement (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n k : ℕ) : Prop :=
  ∀ (c : RealCoordinates G n), SecondKind c →
  ∀ (H : Filtration G), H.level 0=⊤ → H.level 1=⊤ → H.level 3=⊥ →
  ∀ q : ℕ→ℕ, (∀ i, q i ≤ n) →
    (∀ i (g : G), g∈H.level i ↔ ∀ j : Fin n, j.val < q i → c.coord g j=0) →
    n-q 2 ≤ k →
  ∀ (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z),
  ∀ [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)],
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    ∀ (μ : Measure (G⧸Γ)), ∀ [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ],
    ∀ K : Set C(G⧸Γ,ℂ), IsCompact K → ∀ δ : ℝ, 0<δ →
      QuadraticCompactEstimate H Γ μ K δ

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n d r : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i)=0)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥)
variable [((restricted H h0).level 2).Normal]
variable (hlevel : ∀ g : G, g∈H.level 2 ↔ horizontal c hd g=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable (cR : RealCoordinates ((level H h0 1)⧸(restricted H h0).level 2) r)
variable (hskR : SecondKind cR)
variable (hΓR : ∀ g, g∈((Γ.prod Γ).comap (level H h0 1).subtype).map
    (QuotientGroup.mk' ((restricted H h0).level 2)) ↔ ∀ i, ∃ z : ℤ, cR.coord g i=z)

variable {m : ℕ} (c₂ : RealCoordinates (H.level 2) m) (hsk₂ : SecondKind c₂)
variable (hΓ₂ : ∀ x : H.level 2, x.val∈Γ ↔ ∀ i, ∃ z : ℤ, c₂.coord x i=z)
variable (r₂ : Fin 3→ℕ)
variable (hlevel₂ : ∀ i (x : H.level 2), x.val∈H.level (i.val+2) ↔
  ∀ u : Fin m, u.val < r₂ i → c₂.coord x u=0)
include hlin hlevel hΓ hskR hΓR h1 hs hsk₂ hΓ₂ hlevel₂ in
 

theorem quadratic_vertical_factor_alternative (E : ℝ)
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (χ : G→ℂ)
    (hχ : ∀ n∈H.level 2, ‖χ n‖=1)
    (hw : ∀ n∈H.level 2, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level 2) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ V : Finset (H.level 2→*Multiplicative ℝ),
      ∃ A : ℝ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∃ Tmax : ℕ, 0<Tmax ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      ‖horizontal c hd (f 1)‖ ≤ 1 → δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
      (∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j) ∨
      (∃ ψ∈V, ψ≠1 ∧ Continuous ψ ∧ (∀ x : H.level 2, x.val∈Γ → ∃ z : ℤ, (ψ x).toAdd=z) ∧
        ∃ hc : ∀ a b : G, ⁅a,b⁆∈ψ.ker.map (H.level 2).subtype,
        ψ.ker.map (H.level 2).subtype < H.level 2 ∧
        ∃ T : ℕ, 0<T ∧ T ≤ Tmax ∧
          CharacterFactorization.SmoothFactorizationAt H Γ c₂ ψ hc E B N T f) := by
  classical
  let : T2Space G := c.coord.symm.t2Space
  obtain ⟨C,hCc,hC,hCb⟩ := compact_horizontal_representatives c hd Γ hΓ
  obtain ⟨Ξ,hΞ,B,hB,ρ,hρ,hprod⟩ := quadratic_square_characters H h0 h1 hs Γ cR hskR hΓR
    F hF χ hχ hw z hz hχz C hCc hC δ hδ
  obtain ⟨k,hk,hscale⟩ := square_shift_scales δ hδ
  have hden : 0<(2:ℝ)*k := by positivity
  obtain ⟨U,V,A,hA,B',hB',Tmax,hTmax,N₀,hN₀,hdesc⟩ :=
    uniform_character_or_proper_factorization c hd hlin H h0 h1 hlevel Γ hΓ c₂ hsk₂ hΓ₂
      2 (by decide) hs r₂ hlevel₂ Ξ (fun ξ h => (hΞ ξ h).1) (fun ξ h => (hΞ ξ h).2)
      (ρ/(2*k)) B E (div_pos hρ hden) hB.le
  refine ⟨U,V,A,hA,B',hB',Tmax,hTmax,max N₀ (2*k),lt_of_lt_of_le hN₀ (le_max_left _ _),?_⟩
  intro N hNN f hf hf0 hf1 hmean
  have hNN₀ := (le_max_left N₀ (2*k)).trans hNN
  have hNk := (le_max_right N₀ (2*k)).trans hNN
  obtain ⟨hT,hTN,hTd,hbound⟩ := hscale N hNk
  have hN : 0<N := hN₀.trans_le hNN₀
  obtain ⟨S,hST,hS,ξ,hξ,hξ0,hdata⟩ := hprod f hf hf0 N (N/k) hN hT hmean hbound
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
 

 
section
noncomputable section
open scoped commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters RationalTailCoordinates
open MeasureTheory PolynomialWeyl UniformSquareObservable AbelianMalcevTorus MalcevHorizontal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)

include hsk h0 h1 hs hqbound hq2 hq hΓ in
 

theorem quadratic_source_factor_alternative
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (χ : G→ℂ)
    (hχ : ∀ n∈H.level 2, ‖χ n‖=1)
    (hw : ∀ n∈H.level 2, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level 2) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    let htail : ∀ g : G, g∈H.level 2 ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i=0 :=
      fun g => by simpa only [hq2] using hq 2 g
    let c₂ := tailCoordinates c (H.level 2) htail
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ V : Finset (H.level 2→*Multiplicative ℝ),
      ∃ A : ℝ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∃ Tmax : ℕ, 0<Tmax ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      ‖horizontal c (Nat.le_add_right t d) (f 1)‖ ≤ 1 →
      δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
      (∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
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
  let := last_normal H h0 (by decide : 1 ≤ 2) hs
  let := PairTail.diagonal_normal (H.level 2) (H.level 2) (last_central_ambient H h1 2 hs)
  obtain ⟨cR,hskR,hΓR,_⟩ := exists_adapted_sourceReducedCoordinates H h0 h1 2 (by decide) hs
    c q hqbound hq2 hq Γ hΓ
  exact quadratic_vertical_factor_alternative cH (Nat.le_add_right t d) hlin H h0 h1 hs hlevel
    Γ hΓ cR hskR hΓR (tailCoordinates c (H.level 2) htail)
    (tail_secondKind c (H.level 2) htail hsk) (tailCoordinates_lattice c (H.level 2) htail Γ hΓ)
    (fun i => q (i.val+2)-t) (fun i x => tailCoordinates_adapted c (H.level 2) htail
      (H.level (i.val+2)) (q (i.val+2)) (hq (i.val+2)) x)
    1 F hF χ hχ hw z hz hχz δ hδ

end SquareInduction

end
end
end
end
end

end OAI
