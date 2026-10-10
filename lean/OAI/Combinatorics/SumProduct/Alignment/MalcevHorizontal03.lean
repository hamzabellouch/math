import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CharacterFactorization01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped BigOperators commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
end
end
 

 
section
open scoped BigOperators commutatorElement
noncomputable section
namespace RealCharacters
variable {G : Type*} [Group G]
def scaledFamily (Ξ : Finset (G →* Multiplicative ℝ)) (R : ℕ) : Finset (G →* Multiplicative ℝ) := by
  classical
  exact Ξ.biUnion (fun χ => (Finset.Icc (-(R:ℤ)) (R:ℤ)).image (intScale χ))
lemma mem_scaledFamily {Ξ : Finset (G →* Multiplicative ℝ)} {R : ℕ}
    {χ : G →* Multiplicative ℝ} {q : ℤ} (hχ : χ∈Ξ) (hq : |q| ≤ R) :
    intScale χ q∈scaledFamily Ξ R := by
  classical
  exact Finset.mem_biUnion.mpr ⟨χ,hχ,Finset.mem_image.mpr ⟨q,Finset.mem_Icc.mpr (abs_le.mp hq),rfl⟩⟩
lemma scaledFamily_continuous [TopologicalSpace G] (Ξ : Finset (G →* Multiplicative ℝ)) (R : ℕ)
    (hχ : ∀ χ∈Ξ, Continuous χ) : ∀ χ∈scaledFamily Ξ R, Continuous χ := by
  classical
  intro χ hm
  obtain ⟨ψ,hψ,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hm
  exact intScale_continuous ψ q (hχ ψ hψ)
lemma scaledFamily_integral (Ξ : Finset (G →* Multiplicative ℝ)) (R : ℕ) (Γ : Subgroup G)
    (hχ : ∀ χ∈Ξ, ∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z) :
    ∀ χ∈scaledFamily Ξ R, ∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z := by
  classical
  intro χ hm
  obtain ⟨ψ,hψ,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hm
  exact intScale_integral ψ q Γ (hχ ψ hψ)
end RealCharacters
namespace MalcevHorizontal
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n d : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i)=0)
def boundedCharacters (R : ℕ) : Finset (G →* Multiplicative ℝ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(R:ℤ)) (R:ℤ))).image (character c hd hlin)
omit [IsTopologicalGroup G] in
lemma mem_boundedCharacters (R : ℕ) (k : Fin d → ℤ) (hk : ∀ i, |k i| ≤ R) :
    character c hd hlin k∈boundedCharacters c hd hlin R := by
  classical
  exact Finset.mem_image.mpr ⟨k,Fintype.mem_piFinset.mpr (fun i => Finset.mem_Icc.mpr (abs_le.mp (hk i))),rfl⟩
omit [IsTopologicalGroup G] in
lemma boundedCharacters_continuous (R : ℕ) :
    ∀ χ∈boundedCharacters c hd hlin R, Continuous χ := by
  classical
  intro χ hm
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hm
  exact character_continuous c hd hlin k
omit [IsTopologicalGroup G] in
lemma boundedCharacters_integral (R : ℕ) (Γ : Subgroup G)
    (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z) :
    ∀ χ∈boundedCharacters c hd hlin R, ∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z := by
  classical
  intro χ hm
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hm
  exact fun _ hg => character_integer c hd hlin Γ hΓ k hg
end MalcevHorizontal
end
end
 

 
section
noncomputable section
open scoped BigOperators commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
namespace MalcevHorizontal
open RationalLattice CubeFaces LeibmanSquare SquareHorizontalCharacter
open RealCharacters CharacterFactorization MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable {n d m : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i)=0)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hlevel : ∀ g : G, g∈H.level 2 ↔ horizontal c hd g=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable (c₂ : RealCoordinates (H.level 2) m) (hsk₂ : SecondKind c₂)
variable (hΓ₂ : ∀ x : H.level 2, x.val∈Γ ↔ ∀ i, ∃ z : ℤ, c₂.coord x i=z)

include hlin hlevel hΓ hsk₂ hΓ₂ in
 

theorem uniform_character_or_proper_factorization (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1)=⊥)
    (r : Fin (s+1) → ℕ)
    (hlevel₂ : ∀ i (x : H.level 2), x.val∈H.level (i.val+2) ↔
      ∀ u : Fin m, u.val<r i → c₂.coord x u=0)
    (Ξ : Finset (level H h0 1 →* Multiplicative ℝ))
    (hΞc : ∀ ξ∈Ξ, Continuous ξ)
    (hΞΓ : ∀ ξ∈Ξ, ∀ x : level H h0 1, x.val∈Γ.prod Γ → ∃ z : ℤ, (ξ x).toAdd=z)
    (δ A E : ℝ) (hδ : 0<δ) (hA : 0 ≤ A) :
    ∃ U : Finset (G →* Multiplicative ℝ), ∃ V : Finset (H.level 2 →* Multiplicative ℝ),
    ∃ C : ℝ, 0<C ∧ ∃ B : ℝ, 0<B ∧ ∃ Tmax : ℕ, 0<Tmax ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ξ∈Ξ, ξ≠1 →
      ∀ (f : ℤ → G) (hf : Polynomial H 0 f) (hf0 : f 0=1),
      ‖horizontal c hd (f 1)‖ ≤ 1 →
      ∀ v : ℕ → G, (∀ h, ‖horizontal c hd (v h)‖ ≤ 1) →
      (∀ h, (v h)⁻¹*f 1^h∈Γ) →
      ∀ S : Finset ℕ, S⊆Finset.range N → δ*N ≤ (S.card:ℝ) →
      (∀ h∈S, ∃ W : ℝ[X],
        (∀ z : ℤ, W.eval (z:ℝ)=
          (ξ (linearNormalizedPair H h0 h1 hf (linearRemainder H h0 hf hf0 h) h (v h) z)).toAdd) ∧
        ∀ j : ℕ, 0<j → j ≤ s → ∃ z : ℤ, |W.coeff j-z| ≤ A/(N:ℝ)^j) →
      (∃ χ∈U, χ≠1 ∧ Continuous χ ∧ (∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ s ∧ (∀ z : ℤ, P.eval (z:ℝ)=(χ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ C/(N:ℝ)^j) ∨
      (∃ χ∈V, χ≠1 ∧ Continuous χ ∧ (∀ x : H.level 2, x.val∈Γ → ∃ z : ℤ, (χ x).toAdd=z) ∧
        ∃ hc : ∀ a b : G, ⁅a,b⁆∈χ.ker.map (H.level 2).subtype,
        χ.ker.map (H.level 2).subtype < H.level 2 ∧
        ∃ T : ℕ, 0<T ∧ T ≤ Tmax ∧ SmoothFactorizationAt H Γ c₂ χ hc E B N T f) := by
  classical
  obtain ⟨R,hR,C,hC,N₀,hN₀,hdesc⟩ := geometric_scalar_descent c hd hlin H h0 h1 hlevel Γ hΓ
    s hs2 hs Ξ δ A hδ hA
  let U := boundedCharacters c hd hlin R ∪
    scaledFamily (Ξ.image (fun ξ => ξ.comp (diagonal H h0 h1))) R
  let V := scaledFamily (Ξ.image (fun ξ => ξ.comp (lower H h0))) R
  have hVc : ∀ χ∈V, Continuous χ := by
    apply scaledFamily_continuous
    intro χ hm
    obtain ⟨ξ,hξ,rfl⟩ := Finset.mem_image.mp hm
    exact (hΞc ξ hξ).comp (lower_continuous H h0)
  have hVΓ : ∀ χ∈V, ∀ x : H.level 2, x.val∈Γ → ∃ z : ℤ, (χ x).toAdd=z := by
    apply scaledFamily_integral _ _ (Γ.comap (H.level 2).subtype)
    intro χ hm
    obtain ⟨ξ,hξ,rfl⟩ := Finset.mem_image.mp hm
    exact lower_integral H h0 ξ Γ (hΞΓ ξ hξ)
  obtain ⟨B,hB,Tmax,hTmax,hfactor⟩ := finite_lower_factorizations H Γ c₂ h0 hsk₂ hΓ₂ hs r hlevel₂
    V hVc hVΓ s E C hC.le
  refine ⟨U,V,C,hC,B,hB,Tmax,hTmax,N₀,hN₀,?_⟩
  intro N hNN ξ hξ hξ0 f hf hf0 hf1 v hv hvΓ S hSN hS hsmall
  have hN : 1 ≤ (N:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr (hN₀.trans_le hNN))
  rcases hdesc N hNN ξ hξ (hΞc ξ hξ) (hΞΓ ξ hξ) f hf hf0 hf1 v hv hvΓ S hSN hS hsmall with hob | hzero
  · left
    obtain ⟨k,hk,hkR,χ,hχeq,hχ0,hχc,hχΓ,P,hP,hPe,hPc⟩ := hob
    refine ⟨χ,?_,hχ0,hχc,hχΓ,P,hP.trans (by omega),hPe,hPc⟩
    exact Finset.mem_union_left _ (hχeq ▸ mem_boundedCharacters c hd hlin R k hkR)
  · obtain ⟨hp,q,hq,hqR,P,Q,hP,hQ,hQ0,hQ1,hPe,hQe,hPc,hQc⟩ := hzero
    by_cases hd0 : ξ.comp (diagonal H h0 h1)=1
    · right
      let χ := intScale (ξ.comp (lower H h0)) q
      have hχV : χ∈V := mem_scaledFamily (Finset.mem_image.mpr ⟨ξ,hξ,rfl⟩) hqR
      have hχ0 : χ≠1 := intScale_ne_one _ hq (lower_ne_one_of_diagonal H h0 h1 ξ hξ0 hd0)
      have hc : ∀ a b : G, ⁅a,b⁆∈χ.ker.map (H.level 2).subtype := zero_pairing_kernel H h0 h1 ξ q hp
      refine ⟨χ,hχV,hχ0,hVc χ hχV,hVΓ χ hχV,hc,lower_kernel_lt H χ hχ0,?_⟩
      apply hfactor χ hχV hc (N:ℝ) hN f hf hf0 (by rw [h1]; trivial) (Polynomial.C (q:ℝ)*Q)
      · exact (natDegree_C_mul_le _ _).trans hQ
      · intro z
        simp only [eval_mul,eval_C,hQe,intScale_apply,χ]
      · intro j hj
        simpa only [coeff_C_mul] using hQc j hj
    · left
      let χ := intScale (ξ.comp (diagonal H h0 h1)) q
      have hχU : χ∈U := Finset.mem_union_right _
        (mem_scaledFamily (Finset.mem_image.mpr ⟨ξ,hξ,rfl⟩) hqR)
      refine ⟨χ,hχU,intScale_ne_one _ hq hd0,
        intScale_continuous _ q ((hΞc ξ hξ).comp (diagonal_continuous H h0 h1)),
        intScale_integral _ q Γ (diagonal_integral H h0 h1 ξ Γ (hΞΓ ξ hξ)),
        Polynomial.C (q:ℝ)*P,(natDegree_C_mul_le _ _).trans hP,?_,?_⟩
      · intro z
        simp only [eval_mul,eval_C,hPe,intScale_apply,χ]
      · intro j hj
        simpa only [coeff_C_mul] using hPc j hj

end MalcevHorizontal
end
end
 

 
section
noncomputable section
open scoped commutatorElement
namespace LeibmanSquare
open CubeFaces CubePolynomials RationalLattice
variable {G : Type*} [Group G]
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)

include h1 in
 

lemma lattice_linear_normalization (Γ : Subgroup G) {f : ℤ → G}
    (hf : Polynomial H 0 f) (hf0 : f 0=1)
    (v γ : G) (hγ : γ∈Γ) (hav : f 1=v*γ) :
    let g:=fun n : ℤ => f n*(γ^n)⁻¹
    Polynomial H 0 g ∧ g 0=1 ∧ g 1=v ∧
      ∀ n, QuotientGroup.mk (g n)=(QuotientGroup.mk (f n):G⧸Γ) := by
  dsimp only
  have hlin : (fun n : ℤ => γ^n)∈polynomials H 0 := by
    simpa using NilpotentTaylor.binomial_mem (H:=H) 1 0 γ (by rw [Nat.add_zero,h1]; trivial)
  refine ⟨polynomial_of_cube_mem _ ((polynomials H 0).mul_mem
    (cube_mem_of_polynomial _ hf) ((polynomials H 0).inv_mem hlin)),?_,?_,?_⟩
  · simp [hf0]
  · simp [hav,mul_assoc]
  · intro n
    exact QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem (Γ.zpow_mem hγ n))

include h0 in
lemma polynomial_conjugate {f : ℤ → G} (hf : Polynomial H 0 f) (a : G) :
    Polynomial H 0 (fun n => a*f n*a⁻¹) := by
  apply polynomial_of_cube_mem
  apply (polynomials H 0).mul_mem
  · exact (polynomials H 0).mul_mem (const_mem (by rw [h0]; trivial))
      (cube_mem_of_polynomial _ hf)
  · exact const_mem (by rw [h0]; trivial)

include h0 in
 

lemma constant_normalization (Γ : Subgroup G) {f : ℤ → G}
    (hf : Polynomial H 0 f) (v γ : G) (hγ : γ∈Γ) (hav : f 0=v*γ) :
    let g:=fun n => γ*(f 0)⁻¹*f n*γ⁻¹
    Polynomial H 0 g ∧ g 0=1 ∧
      ∀ n, QuotientGroup.mk (v*g n)=(QuotientGroup.mk (f n):G⧸Γ) := by
  dsimp only
  have hp : Polynomial H 0 (fun n => γ*(f 0)⁻¹*f n*γ⁻¹) := by
    apply polynomial_of_cube_mem
    exact (polynomials H 0).mul_mem ((polynomials H 0).mul_mem
      (const_mem (by rw [h0]; trivial)) (cube_mem_of_polynomial _ hf))
      (const_mem (by rw [h0]; trivial))
  refine ⟨hp,by group,?_⟩
  intro n
  have he : v*(γ*(f 0)⁻¹*f n*γ⁻¹)=f n*γ⁻¹ := by rw [hav]; group
  rw [he,QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem hγ)]

end LeibmanSquare
end
end
 

 
section
noncomputable section
open scoped ComplexConjugate
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare PolynomialWeyl MeasureTheory UniformSquareObservable CompactFamilyDescent
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 

theorem uniform_dense_linear_square_descent
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
    ∃ tests : Finset {Ψ : C(X,ℂ) // Ψ ∈ lipschitzMaps (Y := X)},
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
          η ≤ ‖mean N (fun n => Ψ.val (QuotientGroup.mk (p n))) -
            ∫ x, Ψ.val x ∂μ‖ := by
  classical
  let R := restricted H h0
  let := last_normal H h0 (by omega : 1 ≤ s) hs
  let π := QuotientGroup.mk' (R.level s)
  let X := ReducedSpace H h0 Γ s (le_trans (by decide : 1 ≤ 2) hs2) hs
  let := TopologicalSpace.metrizableSpaceMetric X
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨tests,η,hη,htests⟩ := finite_square_tests H h0 Γ s (le_trans (by decide : 1 ≤ 2) hs2) hs F χ hχ hw
    (insert 1 C) (hCc.insert 1) (δ^2/8) 2 (by positivity) (by norm_num)
  refine ⟨tests,η,hη,?_⟩
  intro μ hprob hinv f hf hf0 N T hN hT hlarge hboundary
  let := hprob
  obtain ⟨A,hAT,hAc,hAd⟩ := SquareDifferences.exists_dense_one_sided hN hT
    (fun n => F (QuotientGroup.mk (f n))) (fun n => hF _) δ hδ hlarge hboundary
  refine ⟨A,hAT,hAc,?_⟩
  intro h ha
  obtain ⟨v,hv,hvΓ⟩ := hC (f 1^(h:ℤ))
  let γ:=v⁻¹*f 1^(h:ℤ)
  have hav : f 1^(h:ℤ)=v*γ := by dsimp [γ]; group
  let u:=linearRemainder H h0 hf hf0 (h:ℤ)
  let q:=linearNormalizedPair H h0 h1 hf u (h:ℤ) v
  let p:=fun n => π (q n)
  let Φ:=observable H h0 Γ s (le_trans (by decide : 1 ≤ 2) hs2) hs F χ hχ hw (1,v)
  have hΦ : ∀ x : level H h0 1, Φ (QuotientGroup.mk (π x))=balanced H h0 Γ F 1 v x := fun _ => rfl
  have hzero : (∫ x, Φ x ∂μ)=0 :=
    reduced_observable_mean_zero H h0 h1 Γ F 1 v s hs2 hs χ hw z hz hχz μ hinv Φ hΦ
  have heval (n : ℤ) : Φ (QuotientGroup.mk (p n))=
      F (QuotientGroup.mk (f n))*conj (F (QuotientGroup.mk (f (n+h)))) := by
    rw [hΦ]
    exact balanced_linearNormalizedPair H h0 h1 Γ F hf hf0 (f 1) u h v γ hvΓ hav
      (linearRemainder_mul H h0 hf hf0 h) n
  have hcorr : δ^2/8 ≤ ‖mean N (fun n => Φ (QuotientGroup.mk (p n)))‖ := by
    have hc := hAd h ha
    rw [SquareDifferences.norm_mean_derivative_swap N h 0] at hc
    convert hc using 1
    congr 1
    apply congrArg (mean N)
    funext n
    rw [heval]
    simp only [PolynomialWeyl.derivative,Nat.add_zero,Nat.cast_add]
  let L : C(X,ℂ) →ₗ[ℂ] ℂ := discrepancy μ N (fun n => QuotientGroup.mk (p n))
  have hL : ∀ Ψ, ‖L Ψ‖ ≤ 2 * ‖Ψ‖ := discrepancy_bound μ N hN _
  have hcorr' : δ^2/8 ≤ ‖L Φ‖ := by
    change δ^2/8 ≤ ‖mean N (fun n => Φ (QuotientGroup.mk (p n))) - ∫ x, Φ x ∂μ‖
    simpa only [hzero,sub_zero] using hcorr
  obtain ⟨Ψ,hΨ,hΨcorr⟩ := htests L hL ⟨1,Set.mem_insert _ _,v,Set.mem_insert_of_mem _ hv,hcorr'⟩
  obtain ⟨hp,hptop⟩ := linearNormalizedPair_reduced H h0 h1 hf u (h:ℤ) v
    (le_trans (by decide : 1 ≤ 2) hs2) hs
  exact ⟨Ψ,hΨ,v,hv,γ,hvΓ,hav,hp,hptop,hΨcorr⟩

end SquareInduction

end
end
end
end
end

end OAI
