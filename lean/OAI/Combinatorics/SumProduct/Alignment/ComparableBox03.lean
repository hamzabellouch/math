import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice20
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open scoped Topology
namespace FiniteCoverCharacters
open CubeHorizontalIrrationality
variable {G : Type*} [Group G]
variable (Λ Γ : Subgroup G) (hle : Λ≤Γ) [(Λ.subgroupOf Γ).FiniteIndex]

include hle in
 

theorem rationalCharacter_iff {K : Subgroup G} (χ : K →* Multiplicative ℝ) :
    RationalCharacter Λ χ ↔ RationalCharacter Γ χ := by
  constructor
  · rintro ⟨m,hm,hz⟩
    let D:=denominator Λ Γ
    refine ⟨m*D,Nat.mul_pos hm (denominator_pos Λ Γ),?_⟩
    intro x hx
    have hp : ((x^D : K):G)∈Λ:=pow_denominator_mem Λ Γ hle x.val hx
    obtain ⟨z,hz⟩:=hz (x^D) hp
    refine ⟨z,?_⟩
    simpa only [map_pow,toAdd_pow,nsmul_eq_mul,Nat.cast_mul,mul_assoc] using hz
  · rintro ⟨m,hm,hz⟩
    exact ⟨m,hm,fun x hx=>hz x (hle hx)⟩
end FiniteCoverCharacters

end
 
end

section
 

 

section
noncomputable section
open scoped BigOperators Topology
namespace ComparableBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
open SquareInduction BoxPolynomialLines PolynomialLineCoefficients CorrectedBoxLeibman TriangularLatticeRecovery
open Filter
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
local instance comparableBox03ScaledHaarTopology : TopologicalSpace (G⧸Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem haar_limit_of_horizontal_irrationality_scaled
    (L : ℕ→ℝ) (hL : Tendsto L atTop atTop)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (f : ℕ→(Fin v→ℤ)→G) (hf : ∀ N,LeibmanSquare.Polynomial H 0 (f N))
    (hirr : ∀ ξ : G→*Multiplicative ℝ, ξ≠1 → Continuous ξ →
      (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∃ a : ℕ→PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ N x,gridEval (a N) (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) ∧
        ∃ I,0 < totalDegree I ∧
          Tendsto (fun N => circleNorm (a N I)*(L N)^(totalDegree I)) atTop atTop)
    (c₀ C₀ : ℝ) (B : NNReal) (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∀ η : ℝ,0<η → ∀ᶠ N : ℕ in atTop,
      ∀ lo hi : Fin v→ℝ,
      (∀ i,c₀*(L N)≤hi i-lo i) →
      (∀ i,-C₀*(L N)≤lo i ∧ hi i≤C₀*(L N)) →
      ∀ F : C(G⧸Γ,ℂ),LipschitzWith B F → ‖F‖≤B →
        ‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk (f N x)))-(∫ y,F y ∂μ)‖<η := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  intro η hη
  obtain ⟨U,A,Z₀,hA,hZ₀,hprod⟩ := comparable_real_box c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop μ v c₀ C₀ B η hc₀ hC₀ hB hη
  have hlarge (ξ : G→*Multiplicative ℝ) : ∀ᶠ N : ℕ in atTop,
      ξ≠1 → Continuous ξ → (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∀ a : PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) →
        ∃ I,0<totalDegree I ∧ A<circleNorm (a I)*(L N)^(totalDegree I) := by
    by_cases hc : ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z)
    · obtain ⟨a,ha,I,hI,hlim⟩ := hirr ξ hc.1 hc.2.1 hc.2.2
      filter_upwards [hlim.eventually_gt_atTop A] with N hN
      intro _ _ _ b hb
      have hab : a N=b := gridEval_integer_injective (fun x => (ha N x).trans (hb x).symm)
      exact ⟨I,hI,by simpa only [hab] using hN⟩
    · exact Filter.Eventually.of_forall (by intro N hne hcont hint; exact (hc ⟨hne,hcont,hint⟩).elim)
  have hall : ∀ᶠ N : ℕ in atTop,∀ ξ∈U,
      ξ≠1 → Continuous ξ → (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∀ a : PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) →
        ∃ I,0<totalDegree I ∧ A<circleNorm (a I)*(L N)^(totalDegree I) :=
    (Filter.eventually_all_finset U).mpr (fun ξ _ => hlarge ξ)
  have hNlarge : ∀ᶠ N : ℕ in atTop,Z₀≤(L N) :=
    hL.eventually_ge_atTop Z₀
  filter_upwards [hall,hNlarge] with N hN hNZ
  intro lo hi hside hloc F hFL hFn
  by_contra hbad
  have hdisc : η≤‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk (f N x)))-(∫ y,F y ∂μ)‖ := le_of_not_gt hbad
  obtain ⟨ξ,hξ,hξne,hξc,hξΓ,a,ha,hat,hac⟩ := hprod (L N) hNZ lo hi hside hloc (f N) (hf N) ⟨F,hFL,hFn,hdisc⟩
  obtain ⟨I,hI,hIA⟩ := hN ξ hξ hξne hξc hξΓ a ha
  have hpow : 0<(L N)^(totalDegree I) := pow_pos (hZ₀.trans_le hNZ) _
  have hbnd := (le_div_iff₀ hpow).mp (hac I hI)
  exact (not_lt_of_ge hbnd) hIA

end ComparableBoxLeibman
end
end

section
noncomputable section
open scoped BigOperators Topology
namespace ComparableBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
open SquareInduction BoxPolynomialLines PolynomialLineCoefficients CorrectedBoxLeibman TriangularLatticeRecovery
open Filter
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
local instance scaledProgressionHaarTopology : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem haar_limit_fixed_progression_scaled
    (L : ℕ→ℝ) (hL : Tendsto L atTop atTop)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (f : ℕ→(Fin v→ℤ)→G) (hf : ∀ N,LeibmanSquare.Polynomial H 0 (f N))
    (hirr : ∀ ξ : G→*Multiplicative ℝ, ξ≠1 → Continuous ξ →
      (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∃ a : ℕ→PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ N x,gridEval (a N) (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) ∧
        ∃ I,0 < totalDegree I ∧
          Tendsto (fun N => circleNorm (a N I)*(L N)^(totalDegree I)) atTop atTop)
    (c₀ C₀ : ℝ) (B : NNReal) (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B)
    (d₀ : ℕ) (hd₀ : 0<d₀) (r : Fin v→ℤ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∀ η : ℝ,0<η → ∀ᶠ N : ℕ in atTop,
      ∀ lo hi : Fin v→ℝ,
      (∀ i,c₀*(L N)≤hi i-lo i) →
      (∀ i,-C₀*(L N)≤lo i ∧ hi i≤C₀*(L N)) →
      ∀ F : C(G⧸Γ,ℂ),LipschitzWith B F → ‖F‖≤B →
        ‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk
          (f N (fun i => r i+(d₀:ℤ)*x i))))-(∫ y,F y ∂μ)‖<η := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  intro η hη
  obtain ⟨U,A,Z₀,hA,hZ₀,hprod⟩ := comparable_real_box c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop μ v c₀ C₀ B η hc₀ hC₀ hB hη
  let D : ℕ := d₀^(v*s)
  have hD : 0<D := pow_pos hd₀ _
  let C : ℝ := 1+∑ i,|(r i:ℝ)|
  have hC : 1≤C := by dsimp [C]; linarith [Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => abs_nonneg (r i:ℝ))]
  have hrC (i : Fin v) : |(r i:ℝ)|≤C := by
    have hh := Finset.single_le_sum (f := fun i : Fin v => |(r i:ℝ)|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    dsimp [C]
    linarith
  let E : ℝ := ((s+1:ℕ)^v:ℝ)*(2^s*C^s)^v*((d₀:ℝ)^(v*s)*A)
  have hlarge (ξ : G→*Multiplicative ℝ) : ∀ᶠ N : ℕ in atTop,
      ξ≠1 → Continuous ξ → (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∀ a : PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) →
        ∃ I,0<totalDegree I ∧ E<circleNorm ((d₀:ℝ)^(v*s)*a I)*(L N)^(totalDegree I) := by
    by_cases hc : ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z)
    · have hΞΓ : ∀ g∈Γ,∃ z : ℤ,((ξ^D) g).toAdd=z := by
        intro g hg
        obtain ⟨z,hz⟩ := hc.2.2 g hg
        refine ⟨(D:ℤ)*z,?_⟩
        rw [character_pow_toAdd,hz]
        simp
      obtain ⟨a,ha,I,hI,hlim⟩ := hirr (ξ^D) (character_pow_ne ξ hc.1 D hD) (hc.2.1.pow D) hΞΓ
      filter_upwards [hlim.eventually_gt_atTop E] with N hN
      intro _ _ _ b hb
      have hab : a N=(fun I => (d₀:ℝ)^(v*s)*b I) := by
        apply gridEval_integer_injective
        intro x
        rw [ha,gridEval_mul,hb,character_pow_toAdd]
        simp [D]
      exact ⟨I,hI,by simpa only [hab] using hN⟩
    · exact Filter.Eventually.of_forall (by intro N hne hcont hint; exact (hc ⟨hne,hcont,hint⟩).elim)
  have hall : ∀ᶠ N : ℕ in atTop,∀ ξ∈U,
      ξ≠1 → Continuous ξ → (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∀ a : PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) →
        ∃ I,0<totalDegree I ∧ E<circleNorm ((d₀:ℝ)^(v*s)*a I)*(L N)^(totalDegree I) :=
    (Filter.eventually_all_finset U).mpr (fun ξ _ => hlarge ξ)
  have hNlarge : ∀ᶠ N : ℕ in atTop,max 1 Z₀≤(L N) :=
    hL.eventually_ge_atTop (max 1 Z₀)
  let φ : (Fin v→ℤ)→+(Fin v→ℤ) :=
    { toFun := fun x i => (d₀:ℤ)*x i
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp [mul_add] }
  filter_upwards [hall,hNlarge] with N hN hNZ
  have hNZ₀ : Z₀≤(L N) := (le_max_right _ _).trans hNZ
  have hN1 : 1≤(L N) := (le_max_left _ _).trans hNZ
  intro lo hi hside hloc F hFL hFn
  by_contra hbad
  have hdisc : η≤‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk
      (f N (fun i => r i+(d₀:ℤ)*x i))))-(∫ y,F y ∂μ)‖ := le_of_not_gt hbad
  have hgf := polynomial_affine H (hf N) φ r
  obtain ⟨ξ,hξ,hξne,hξc,hξΓ,b,hb,hbt,hbc⟩ := hprod (L N) hNZ₀ lo hi hside hloc
    (fun x => f N (r+φ x)) hgf ⟨F,hFL,hFn,hdisc⟩
  obtain ⟨a,ha⟩ := character_grid_expansion H s hs (hf N) ξ
  have hab : ∀ x : Fin v→ℤ,gridEval b (fun i => (x i:ℝ))=
      gridEval a (fun i => ((r i+(d₀:ℤ)*x i:ℤ):ℝ)) := by
    intro x
    rw [hb,ha]
    rfl
  have hbnd := gridAffine_recover_bound d₀ hd₀ r a b (L N) C A (zero_le_one.trans hN1) hC hA.le
    (fun i => (hrC i).trans (le_mul_of_one_le_right (zero_le_one.trans hC) hN1)) hab
    (fun I hI => (le_div_iff₀ (pow_pos (hZ₀.trans_le hNZ₀) _)).mp (hbc I hI))
  obtain ⟨I,hI,hIE⟩ := hN ξ hξ hξne hξc hξΓ a ha
  exact (not_lt_of_ge (hbnd I hI)) hIE

end ComparableBoxLeibman
end
end

section
noncomputable section
open scoped BigOperators Topology commutatorElement
namespace CubeHorizontalIrrationality
open CubeFaces HorizontalCubeCharacter Filter BooleanBinomial MvPolynomial
open CubeTaylorExpansion CorrectedBoxLeibman PolynomialLineCoefficients PolynomialWeyl TriangularLatticeRecovery
variable {G ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
omit [IsTopologicalGroup G] in
theorem coefficient_divergence_scaled (L : ℕ→ℝ) (H : Filtration G) (Γ : Subgroup G)
    (h01 : H.level 0=H.level 1) (s : ℕ) (hs : H.level (s+1)= ⊥)
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter Γ ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(L N)^j)
        atTop atTop)
    (χ : cube H (Finset.univ : Finset ι) 0→*Multiplicative ℝ)
    (hχne : χ≠1) (hχ : Continuous χ)
    (hχΓ : ∀ x : cube H (Finset.univ : Finset ι) 0,
      (∀ v,(x:Finset ι→G) v∈Γ) → ∃ z : ℤ,(χ x).toAdd=z) :
    ∃ e : Exponent ι,0 < degree e ∧ degree e ≤ s ∧
      Tendsto (fun N : ℕ => ‖(((scalarPolynomial H χ (a N) s).coeff e:ℝ):UnitAddCircle)‖*
        (L N)^(degree e)) atTop atTop := by
  obtain ⟨M⟩ := exists_maximalFace H Finset.univ h01 s hs χ hχne
  obtain ⟨hne,hc,hr,hn,hb⟩ := maximal_scaled_character Γ hχ hχΓ M
  refine ⟨isolatedExponent M.level M.face,?_,?_,?_⟩
  · rw [isolatedExponent_degree M.level M.face M.card_le]
    exact M.positive
  · rw [isolatedExponent_degree M.level M.face M.card_le]
    exact maximal_level_le M hs
  · have hh := hirr M.level M.positive (maximal_level_le M hs) _ hne hc hr hn hb
    simpa only [isolatedExponent_degree M.level M.face M.card_le,
      isolated_scalar_coefficient M _ s hs,scaleCharacter,MonoidHom.coe_mk,
      OneHom.coe_mk,toAdd_ofAdd,div_eq_mul_inv,mul_comm] using hh

theorem grid_irrationality_scaled (L : ℕ→ℝ) {n v : ℕ} (c : RationalLattice.RealCoordinates G n)
    (H : Filtration G) (S : ℕ→Set (Fin n))
    (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)
    (Γ : Subgroup G) (h01 : H.level 0=H.level 1)
    (s : ℕ) (hs : H.level (s+1)=⊥) (e : Option ι≃Fin v)
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter Γ ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(L N)^j)
        atTop atTop)
    (χ : cube H (Finset.univ : Finset ι) 0→*Multiplicative ℝ)
    (hχne : χ≠1) (hχ : Continuous χ)
    (hχΓ : ∀ x : cube H (Finset.univ : Finset ι) 0,
      (∀ w,(x:Finset ι→G) w∈Γ) → ∃ z : ℤ,(χ x).toAdd=z) :
    ∃ b : ℕ→PolynomialLineCoefficients.Grid v s→ℝ,
      (∀ N (x : Fin v→ℤ),gridEval (b N) (fun i => (x i:ℝ))=
        (χ (cubePolynomial c H S hH (a N) s (fun i => (x (e i):ℝ)))).toAdd) ∧
      ∃ I,0 < PolynomialLineCoefficients.totalDegree I ∧
        Tendsto (fun N => circleNorm (b N I)*(L N)^(PolynomialLineCoefficients.totalDegree I)) atTop atTop := by
  let p (N : ℕ) : MvPolynomial (Fin v) ℝ := rename e (scalarPolynomial H χ (a N) s)
  have hp (N : ℕ) : (p N).totalDegree ≤ s :=
    (MvPolynomial.totalDegree_rename_le _ _).trans (scalarPolynomial_totalDegree H χ (a N) s)
  refine ⟨fun N => polynomialGrid (p N),?_,?_⟩
  · intro N x
    rw [gridEval_polynomial _ (hp N)]
    exact (MvPolynomial.eval_rename _ _ _).trans (scalarPolynomial_eval c H S hH (a N) s _ χ hχ)
  · obtain ⟨m,hm,hmS,hlim⟩ := coefficient_divergence_scaled L H Γ h01 s hs a hirr χ hχne hχ hχΓ
    have hm' : (m.mapDomain e).sum (fun _ k => k) ≤ s := by rwa [renamed_degree]
    refine ⟨exponentGrid (m.mapDomain e) hm',?_,?_⟩
    · rwa [exponentGrid_degree,renamed_degree]
    · simpa only [circleNorm,polynomialGrid,gridExponent_exponentGrid,p,
        coeff_rename_mapDomain e e.injective,exponentGrid_degree,renamed_degree] using hlim

end CubeHorizontalIrrationality

end
end
end

end OAI
