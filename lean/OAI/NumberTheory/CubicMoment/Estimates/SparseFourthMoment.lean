import OAI.NumberTheory.CubicMoment.Estimates.StructuredMeanValue
import OAI.NumberTheory.CubicMoment.Estimates.OrdinaryMixedSieve

namespace OAI

/-! The square of a structured error polynomial has controlled coefficient
energy. This supplies the fourth-moment estimate in the balanced range. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def productSupport (B : Finset Eisenstein) : Finset Eisenstein :=
  (B.product B).image (fun z => z.1*z.2)

def squareConvolution (B : Finset Eisenstein) (v : Eisenstein → ℂ) (n : Eisenstein) : ℂ :=
  ∑ z ∈ B.product B with z.1*z.2 = n, v z.1*v z.2

lemma second_moment_sq_le_card_fourth {ι : Type*} (P : Finset ι) (v : ι → ℂ) :
    (∑ p ∈ P, ‖v p‖^2)^2 ≤ (P.card:ℝ)*∑ p ∈ P, ‖v p‖^4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1:ℝ)) (fun p => ‖v p‖^2)
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,← pow_mul] using h

/-- Every pair of products of `k` supported primes is the image of a
`2k`-prime tuple. Thus the multiplicity costs a constant depending on k. -/
lemma primeProduct_pair_fiber_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (n : Eisenstein) :
    (((orderedConvolutionSupport S).product (orderedConvolutionSupport S)).filter
      (fun z => z.1*z.2 = n)).card ≤
        (2*Fintype.card ι)^(2*Fintype.card ι) := by
  let S₂ : ι ⊕ ι → Finset Eisenstein := Sum.elim S S
  let T := (Fintype.piFinset S₂).filter (fun f => (∏ i, f i) = n)
  let φ (f : ι ⊕ ι → Eisenstein) : Eisenstein × Eisenstein :=
    (∏ i, f (Sum.inl i), ∏ i, f (Sum.inr i))
  have hcover : (((orderedConvolutionSupport S).product (orderedConvolutionSupport S)).filter
      (fun z => z.1*z.2 = n)) ⊆ T.image φ := by
    intro z hz
    obtain ⟨hz,hzn⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz₁,hz₂⟩ := Finset.mem_product.mp hz
    obtain ⟨f,hf,hfz⟩ := Finset.mem_image.mp hz₁
    obtain ⟨g,hg,hgz⟩ := Finset.mem_image.mp hz₂
    apply Finset.mem_image.mpr
    refine ⟨Sum.elim f g, Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      cases i with
      | inl i => exact Fintype.mem_piFinset.mp hf i
      | inr i => exact Fintype.mem_piFinset.mp hg i
    · simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hfz,hgz] using hzn
    · exact Prod.ext hfz hgz
  apply (Finset.card_le_card hcover).trans
  apply Finset.card_image_le.trans
  have h := prime_tuple_fiber_card S₂ (fun i => by
    cases i with
    | inl i => exact hS i
    | inr i => exact hS i) n
  simpa only [S₂,T,Fintype.card_sum,two_mul] using h

lemma squareConvolution_character (B : Finset Eisenstein) (v χ : Eisenstein → ℂ)
    (hχ : ∀ a b, χ (a*b) = χ a*χ b) :
    (∑ n ∈ productSupport B, squareConvolution B v n*χ n) =
      (∑ b ∈ B, v b*χ b)^2 := by
  unfold squareConvolution productSupport
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ n ∈ (B.product B).image (fun z => z.1*z.2),
        ∑ z ∈ B.product B with z.1*z.2 = n, (v z.1*v z.2)*χ (z.1*z.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
    _ = ∑ z ∈ B.product B, (v z.1*v z.2)*χ (z.1*z.2) :=
      Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) _
    _ = _ := by
      rw [Finset.product_eq_sprod,Finset.sum_product B B _,pow_two,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [hχ]
      ring

lemma squareConvolution_energy (B : Finset Eisenstein) (v : Eisenstein → ℂ)
    {K : ℝ} (hK : ∀ n ∈ productSupport B,
      (((B.product B).filter (fun z => z.1*z.2 = n)).card:ℝ) ≤ K) :
    (∑ n ∈ productSupport B, ‖squareConvolution B v n‖^2) ≤
      K*(∑ b ∈ B, ‖v b‖^2)^2 := by
  have hrow (n : Eisenstein) (hn : n ∈ productSupport B) :
      ‖squareConvolution B v n‖^2 ≤
        K * ∑ z ∈ B.product B with z.1*z.2 = n, ‖v z.1*v z.2‖^2 := by
    let T := (B.product B).filter (fun z => z.1*z.2 = n)
    have hc := complex_bilinear_rows_sq T (fun _ => (1:ℂ)) (fun z => v z.1*v z.2)
    simp only [one_mul,norm_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (hK n hn)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    _ ≤ ∑ n ∈ productSupport B,
        K * ∑ z ∈ B.product B with z.1*z.2 = n, ‖v z.1*v z.2‖^2 :=
      Finset.sum_le_sum hrow
    _ = K * ∑ z ∈ B.product B, ‖v z.1*v z.2‖^2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) _
    _ = _ := by
      simp only [norm_mul,mul_pow]
      rw [Finset.product_eq_sprod,Finset.sum_product B B _]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul,pow_two]

/-- Apply the ordinary character sieve to the actual squared polynomial.
The input multiplicity is purely arithmetic and is discharged below for
bounded-length products of primes. -/
theorem ordinary_mixed_fourth_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q Z : ℝ), 1 ≤ Q → 1 ≤ Z →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (B : Finset Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, b ≠ 0 ∧ norm b ≤ Z) →
      ∀ (K : ℝ), (∀ n ∈ productSupport B,
        (((B.product B).filter (fun z => z.1*z.2 = n)).card:ℝ) ≤ K) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^4) ≤
        C*Q^ε*(Q^2+Z^2)*K*(∑ b ∈ B, ‖v b‖^2)^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_finite hHuxley hε
  refine ⟨C,hC,?_⟩
  intro Q Z hQ hZ P B hP hB K hK v
  have hBB : ∀ n ∈ productSupport B, n ≠ 0 ∧ norm n ≤ Z^2 := by
    intro n hn
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    refine ⟨mul_ne_zero (hB a ha).1 (hB b hb).1,?_⟩
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul (hB a ha).2 (hB b hb).2 (norm_nonneg b) (by linarith)
  have he (p : Eisenstein × Eisenstein) (hp : p ∈ P) :
      ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^4 =
      ‖∑ n ∈ productSupport B, squareConvolution B v n*mixedCubic p.1 p.2 n‖^2 := by
    rw [squareConvolution_character B v _ (mixedCubic_mul (hP p hp).1.1 (hP p hp).1.2.1),
      norm_pow]
    ring
  calc
    _ = ∑ p ∈ P, ‖∑ n ∈ productSupport B,
        squareConvolution B v n*mixedCubic p.1 p.2 n‖^2 := Finset.sum_congr rfl he
    _ ≤ C*Q^ε*(Q^2+Z^2)*∑ n ∈ productSupport B, ‖squareConvolution B v n‖^2 :=
      hbound Q (Z^2) hQ (one_le_pow₀ hZ) P (productSupport B) hP hBB _
    _ ≤ C*Q^ε*(Q^2+Z^2)*(K*(∑ b ∈ B, ‖v b‖^2)^2) :=
      mul_le_mul_of_nonneg_left (squareConvolution_energy B v hK) (by positivity)
    _ = _ := by ring

theorem primeProduct_mixed_fourth_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset Eisenstein),
      (∀ i, ∀ p ∈ S i, primaryPrime p) →
      ∀ (Q Z : ℝ), 1 ≤ Q → 1 ≤ Z →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Z) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        v b*mixedCubic p.1 p.2 b‖^4) ≤
      C*Q^ε*(Q^2+Z^2)*((2*Fintype.card ι)^(2*Fintype.card ι):ℕ)*
        (∑ b ∈ orderedConvolutionSupport S, ‖v b‖^2)^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_fourth_moment hHuxley hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ S hS Q Z hQ hZ hprod P hP v
  apply hbound Q Z hQ hZ P (orderedConvolutionSupport S) hP
  · intro b hb
    refine ⟨orderedConvolutionSupport_ne_zero S hS b hb,?_⟩
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    exact hprod f hf
  · intro n _
    exact Nat.cast_le.mpr (primeProduct_pair_fiber_card S hS n)

/-- The actual repeated-prime error saves a power in the fourth moment,
uniformly under fixed angular and arbitrary real norm twists. -/
theorem primeConvolutionError_twisted_fourth_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hHuxley : HuxleyAdditiveLargeSieve) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y c Q : ℝ),
      1 ≤ Y → 1 ≤ Q → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y^c < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ (ℓ : ℤ) (u : ℝ) (ν : Eisenstein → ℂ),
      (∀ b ∈ orderedConvolutionSupport S, ‖ν b‖ ≤ 1) →
      (∑ p ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        squarefreeConvolutionError S w b *
          (theta ℓ b * normTwist u b * ν b) * mixedCubic p.1 p.2 b‖^4) ≤
        C*Q^ε*(Q^2+Y^2)*Y^(2-c)*
          (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^4 := by
  obtain ⟨C₀,hC₀,hfourth⟩ := primeProduct_mixed_fourth_moment hHuxley hε
  obtain ⟨K,hK,henergy⟩ := primeConvolutionError_power_energy (ι := ι)
  let N : ℝ := ((2*Fintype.card ι)^(2*Fintype.card ι):ℕ)
  refine ⟨C₀*(N+1)*K^2,by dsimp [N]; positivity,?_⟩
  intro S w M Y c Q hY hQ hM hS hprod hw P hP ℓ u ν hν
  have hY0 : 0 < Y := by linarith
  have hprime : ∀ i, ∀ p ∈ S i, primaryPrime p := fun i p hp => (hS i p hp).1
  let v : Eisenstein → ℂ := fun b => squarefreeConvolutionError S w b *
    (theta ℓ b * normTwist u b * ν b)
  let A : ℝ := ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i)
  have hE : (∑ b ∈ orderedConvolutionSupport S, ‖v b‖^2) ≤ K*Y^(1-c/2)*A^2 := by
    apply (coefficient_twist_energy_le (orderedConvolutionSupport S)
      (squarefreeConvolutionError S w) (fun b => theta ℓ b * normTwist u b * ν b) ?_).trans
      (henergy S w M Y c hY0 hM hS hprod hw)
    intro b hb
    simpa only [norm_mul,norm_theta (orderedConvolutionSupport_ne_zero S hprime b hb),
      norm_normTwist,one_mul,mul_one] using hν b hb
  have hfour := hfourth S hprime Q Y hQ hY hprod P hP v
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpow : (Y^(1-c/2))^2 = Y^(2-c) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
    congr 1
    ring
  have he : (K*Y^(1-c/2)*A^2)^2 = K^2*Y^(2-c)*A^4 := by
    rw [mul_pow,mul_pow,hpow]
    ring
  calc
    _ ≤ C₀*Q^ε*(Q^2+Y^2)*N*(∑ b ∈ orderedConvolutionSupport S, ‖v b‖^2)^2 := hfour
    _ ≤ C₀*Q^ε*(Q^2+Y^2)*N*(K*Y^(1-c/2)*A^2)^2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hE 2) (by positivity)
    _ = (C₀*N*K^2)*Q^ε*(Q^2+Y^2)*Y^(2-c)*A^4 := by rw [he]; ring
    _ ≤ _ := by
      dsimp only [A]
      gcongr
      linarith

end CubicFirstMoment

end

end OAI
