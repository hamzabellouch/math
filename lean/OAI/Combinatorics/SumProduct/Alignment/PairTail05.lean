import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CompactFamily01
import OAI.Combinatorics.SumProduct.Alignment.CoordinateSubspace01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped commutatorElement Pointwise
namespace SquareInduction
open MeasureTheory
open scoped BigOperators
noncomputable section
section Probability
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

 

def discrepancy (N : ℕ) (x : ℕ → X) : C(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f := (𝔼 n ∈ Finset.range N, f (x n)) - ∫ t, f t ∂μ
  map_add' f g := by
    change (𝔼 n ∈ Finset.range N, (f (x n) + g (x n))) -
      ∫ t, f t + g t ∂μ = _
    rw [Finset.expect_add_distrib, integral_add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))]
    ring
  map_smul' z f := by
    change (𝔼 n ∈ Finset.range N, z • f (x n)) - ∫ t, z • f t ∂μ = _
    rw [← Finset.smul_expect, integral_smul]
    simp only [RingHom.id_apply, smul_sub]

theorem discrepancy_bound (N : ℕ) (hN : 0 < N) (x : ℕ → X) (f : C(X, ℂ)) :
    ‖discrepancy μ N x f‖ ≤ 2 * ‖f‖ := by
  have hm : ‖𝔼 n ∈ Finset.range N, f (x n)‖ ≤ ‖f‖ :=
    (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)) (fun n _ => f.norm_coe_le_norm _))
  have hi : ‖∫ t, f t ∂μ‖ ≤ ‖f‖ := by
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (f.norm_coe_le_norm))
  exact (norm_sub_le _ _).trans (by linarith only [hm, hi])

theorem discrepancy_const (N : ℕ) (hN : 0 < N) (x : ℕ → X) (z : ℂ) :
    discrepancy μ N x (ContinuousMap.const _ z) = 0 := by
  simp only [discrepancy, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.const_apply,
    Finset.expect_const (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)),
    integral_const, probReal_univ, one_smul, sub_self]
end Probability
end
end SquareInduction

namespace SquareInduction
open CubeFaces LeibmanSquare PolynomialWeyl UniformSquareObservable
open CompactFamilyDescent MeasureTheory Topology
open scoped BigOperators ComplexConjugate
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 

theorem uniform_dense_square_descent_tracked
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
      ∀ (f : ℤ → G), Polynomial H 0 f →
      ∀ N T : ℕ, 0 < N → 0 < T →
        δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
        4 * (T : ℝ) / N ≤ δ^2/2 →
      ∃ b ∈ Finset.range T, ∃ A : Finset ℕ,
        (∀ a ∈ A, a < T) ∧ δ^2/4*T ≤ (A.card : ℝ) ∧
        ∀ a ∈ A, ∃ Ψ ∈ tests, ∃ p : ℤ → (level H h0 1) ⧸ R.level s,
          ∃ u ∈ C, ∃ v ∈ C, ∃ γ ∈ Γ, ∃ ε ∈ Γ,
          f a = u*γ ∧ f b = v*ε ∧
          (∀ n : ℤ, ∃ x : level H h0 1, p n = π x ∧
            x.val = (u⁻¹*f (n+a)*γ⁻¹, v⁻¹*f (n+b)*ε⁻¹)) ∧
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
    C hCc (δ^2/4) 2 (by positivity) (by norm_num)
  refine ⟨tests,η,hη,?_⟩
  intro μ hprob hinv f hf N T hN hT hlarge hboundary
  let := hprob
  obtain ⟨b,hb,A,hAT,hAc,hAd⟩ := dense_reduced_square_orbits_tracked H h0 h1 Γ F hF s hs2 hs
    χ hχ hw C hC f hf N T hN hT δ hδ hlarge hboundary
  refine ⟨b,hb,A,hAT,hAc,?_⟩
  intro a ha
  obtain ⟨u,hu,v,hv,Φ,p,γ,hγ,ε,hε,hfa,hfb,hlift,hΦbound,hΦ,hp,hptop,heval,hcorr⟩ := hAd a ha
  have heq : Φ = observable H h0 Γ s (le_trans (by decide : 1 ≤ 2) hs2) hs F χ hχ hw (u,v) := by
    ext x
    induction x using Quotient.inductionOn with | h y =>
      induction y using Quotient.inductionOn with | h w =>
        exact hΦ w
  have hzero : (∫ x, Φ x ∂μ) = 0 :=
    reduced_observable_mean_zero H h0 h1 Γ F u v s hs2 hs χ hw z hz hχz μ hinv Φ hΦ
  let L : C(X,ℂ) →ₗ[ℂ] ℂ := discrepancy μ N (fun n => QuotientGroup.mk (p n))
  have hL : ∀ Ψ, ‖L Ψ‖ ≤ 2 * ‖Ψ‖ := discrepancy_bound μ N hN _
  have hcorr' : δ^2/4 ≤ ‖L (observable H h0 Γ s (le_trans (by decide : 1 ≤ 2) hs2) hs F χ hχ hw (u,v))‖ := by
    rw [← heq]
    change δ^2/4 ≤ ‖mean N (fun n => Φ (QuotientGroup.mk (p n))) - ∫ x, Φ x ∂μ‖
    simpa only [hzero,sub_zero] using hcorr
  obtain ⟨Ψ,hΨ,hΨcorr⟩ := htests L hL ⟨u,hu,v,hv,hcorr'⟩
  exact ⟨Ψ,hΨ,p,u,hu,v,hv,γ,hγ,ε,hε,hfa,hfb,hlift,hp,hptop,hΨcorr⟩

end
end SquareInduction

end
 

 
section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace SquareDifferences
open PolynomialWeyl

lemma norm_mean_derivative_swap (N a b : ℕ) (f : ℕ → ℂ) :
    ‖mean N (derivative a b f)‖=‖mean N (derivative b a f)‖ := by
  have he : mean N (derivative a b f)=conj (mean N (derivative b a f)) := by
    simp only [mean,derivative,map_expect (starRingEnd ℂ),map_mul,starRingEnd_self_apply]
    apply Finset.expect_congr rfl
    intro n _
    ring
  rw [he,RCLike.norm_conj]

lemma derivative_shift_error {N : ℕ} (hN : 0<N) (a b : ℕ) (hab : b≤a)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖≤1) :
    ‖mean N (derivative a b f)‖ ≤ ‖mean N (derivative (a-b) 0 f)‖+2*(b:ℝ)/N := by
  have he : derivative a b f = fun n => derivative (a-b) 0 f (n+b) := by
    funext n
    simp only [derivative,Nat.add_zero]
    congr 2
    omega
  have ht := norm_mean_shift_sub_le hN b (derivative (a-b) 0 f)
    (norm_derivative_le_one (a-b) 0 f hf)
  rw [←he] at ht
  have hn := norm_sub_norm_le (mean N (derivative a b f)) (mean N (derivative (a-b) 0 f))
  linarith

lemma nat_dist_image_card (S : Finset ℕ) (b : ℕ) :
    S.card ≤ 2*(S.image (fun a => Nat.dist a b)).card := by
  classical
  let A := S.image (fun a => Nat.dist a b)
  have hc := Finset.card_le_card_of_injOn (s:=S) (t:=A.product (Finset.univ : Finset Bool))
    (fun a => (Nat.dist a b,decide (b≤a))) (by
      intro a ha
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a,ha,rfl⟩,Finset.mem_univ _⟩) (by
      intro a ha c hc he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      have h3 : (b≤a) ↔ b≤c := by simpa only [Prod.snd,decide_eq_decide] using h2
      simp only [Nat.dist] at h1
      omega)
  simpa only [Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_bool,Nat.mul_comm,A] using hc

 

theorem exists_dense_one_sided {N T : ℕ} (hN : 0<N) (hT : 0<T)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖≤1) (δ : ℝ) (hδ : 0<δ)
    (hlarge : δ≤‖mean N f‖) (hboundary : 4*(T:ℝ)/N≤δ^2/4) :
    ∃ A : Finset ℕ, (∀ h∈A, h<T) ∧ δ^2/8*T≤(A.card:ℝ) ∧
      ∀ h∈A, δ^2/8≤‖mean N (derivative h 0 f)‖ := by
  classical
  obtain ⟨b,hb,S,hST,hSc,hcorr⟩ := exists_dense_derivatives hN hT f hf δ hδ hlarge
    (by nlinarith [sq_nonneg δ])
  have hbT := Finset.mem_range.mp hb
  refine ⟨S.image (fun a => Nat.dist a b),?_,?_,?_⟩
  · intro h hh
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hh
    have haT := hST a ha
    simp only [Nat.dist]
    omega
  · have hc := nat_dist_image_card S b
    have hc' : (S.card:ℝ)≤2*((S.image (fun a => Nat.dist a b)).card:ℝ) := by exact_mod_cast hc
    linarith
  · intro h hh
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hh
    have hsmall : ∀ k : ℕ, k<T → 2*(k:ℝ)/N≤δ^2/8 := by
      intro k hk
      have hk' : (k:ℝ)≤T := by exact_mod_cast hk.le
      have he : 2*(k:ℝ)/N≤2*(T:ℝ)/N :=
        div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg N)
      apply he.trans
      calc
        2*(T:ℝ)/N=(4*(T:ℝ)/N)/2 := by ring
        _ ≤ (δ^2/4)/2 := div_le_div_of_nonneg_right hboundary (by norm_num)
        _ = δ^2/8 := by ring
    have hc := hcorr a ha
    by_cases hab : b≤a
    · rw [Nat.dist_eq_sub_of_le_right hab]
      have he := derivative_shift_error hN a b hab f hf
      have hs := hsmall b hbT
      linarith
    · have hab' : a≤b := le_of_not_ge hab
      rw [Nat.dist_eq_sub_of_le hab']
      rw [norm_mean_derivative_swap N a b f] at hc
      have he := derivative_shift_error hN b a hab' f hf
      have hs := hsmall a (hST a ha)
      linarith

end SquareDifferences
end
end
 

 
section
open scoped commutatorElement
noncomputable section
namespace PairTail
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : Subgroup G) [K.Normal]

 
def diagonalEmbedding : G →* square K where
  toFun g := pair K g 1
  map_one' := by apply Subtype.ext; ext <;> simp [pair]
  map_mul' g h := by apply Subtype.ext; ext <;> simp [pair]
def lowerEmbedding : K →* square K where
  toFun u := pair K 1 u
  map_one' := by apply Subtype.ext; ext <;> simp [pair]
  map_mul' g h := by apply Subtype.ext; ext <;> simp [pair]
lemma diagonalEmbedding_continuous : Continuous (diagonalEmbedding K) :=
  (pair_continuous K).comp (continuous_id.prodMk continuous_const)
lemma lowerEmbedding_continuous : Continuous (lowerEmbedding K) :=
  (pair_continuous K).comp (continuous_const.prodMk continuous_id)
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma pair_decompose [TopologicalSpace G] [IsTopologicalGroup G] (g : G) (u : K) :
    pair K g u = diagonalEmbedding K g * lowerEmbedding K u := by
  apply Subtype.ext
  ext <;> simp [pair,diagonalEmbedding,lowerEmbedding]

variable (η : square K →* Multiplicative ℝ)
def baseCharacter : G →* Multiplicative ℝ := η.comp (diagonalEmbedding K)
def lowerCharacter : K →* Multiplicative ℝ := η.comp (lowerEmbedding K)
lemma baseCharacter_continuous (hη : Continuous η) : Continuous (baseCharacter K η) :=
  hη.comp (diagonalEmbedding_continuous K)
lemma lowerCharacter_continuous (hη : Continuous η) : Continuous (lowerCharacter K η) :=
  hη.comp (lowerEmbedding_continuous K)

 
lemma character_split (x : square K) :
    Multiplicative.toAdd (η x) = Multiplicative.toAdd (baseCharacter K η x.val.1) +
      Multiplicative.toAdd (lowerCharacter K η (difference K x)) := by
  conv_lhs => rw [← pair_first_difference K x,pair_decompose,map_mul]
  rfl

lemma character_nonzero (hη : η ≠ 1) : baseCharacter K η ≠ 1 ∨ lowerCharacter K η ≠ 1 := by
  by_contra h
  push Not at h
  apply hη
  ext x
  apply Multiplicative.toAdd.injective
  rw [character_split,h.1,h.2]
  simp

 

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma lowerCharacter_conj [TopologicalSpace G] [IsTopologicalGroup G] (g : G) (u : K) :
    lowerCharacter K η ⟨g*u*g⁻¹,(inferInstance : K.Normal).conj_mem _ u.property g⟩ =
      lowerCharacter K η u := by
  have he : lowerEmbedding K ⟨g*u*g⁻¹,(inferInstance : K.Normal).conj_mem _ u.property g⟩ =
      diagonalEmbedding K g * lowerEmbedding K u * (diagonalEmbedding K g)⁻¹ := by
    apply Subtype.ext
    ext <;> simp [pair,diagonalEmbedding,lowerEmbedding,mul_assoc]
  change η _ = η _
  rw [he,map_mul,map_mul,map_inv]
  simp [mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma lower_commutator_mem [TopologicalSpace G] [IsTopologicalGroup G]
    (g : G) (u : K) : ⁅g,u.val⁆ ∈ K :=
  K.mul_mem ((inferInstance : K.Normal).conj_mem _ u.property g) (K.inv_mem u.property)

lemma lowerCharacter_commutator (g : G) (u : K) :
    lowerCharacter K η ⟨⁅g,u.val⁆,lower_commutator_mem K g u⟩ = 1 := by
  let v : K := ⟨g*u*g⁻¹,(inferInstance : K.Normal).conj_mem _ u.property g⟩
  have he : (⟨⁅g,u.val⁆,lower_commutator_mem K g u⟩ : K) = v*u⁻¹ := by
    apply Subtype.ext
    rfl
  rw [he,map_mul,map_inv,lowerCharacter_conj]
  exact mul_inv_cancel _

variable (Γ : Subgroup G)
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma baseCharacter_integral [TopologicalSpace G] [IsTopologicalGroup G]
    (hη : ∀ x ∈ squareLattice K Γ, ∃ z : ℤ, Multiplicative.toAdd (η x) = z) :
    ∀ g ∈ Γ, ∃ z : ℤ, Multiplicative.toAdd (baseCharacter K η g) = z := by
  intro g hg
  apply hη (diagonalEmbedding K g)
  simpa [diagonalEmbedding,pair] using And.intro hg hg
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma lowerCharacter_integral [TopologicalSpace G] [IsTopologicalGroup G]
    (hη : ∀ x ∈ squareLattice K Γ, ∃ z : ℤ, Multiplicative.toAdd (η x) = z) :
    ∀ u : K, u.val ∈ Γ → ∃ z : ℤ, Multiplicative.toAdd (lowerCharacter K η u) = z := by
  intro u hu
  apply hη (lowerEmbedding K u)
  simpa [lowerEmbedding,pair] using And.intro Γ.one_mem hu

end PairTail

end
end
end
end
end

end OAI
