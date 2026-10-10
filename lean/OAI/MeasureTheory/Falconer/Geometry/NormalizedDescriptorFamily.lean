import OAI.MeasureTheory.Falconer.Estimates.UniformDescriptorFactors
import OAI.MeasureTheory.Falconer.Geometry.NormalizedInverseFactors
import OAI.MeasureTheory.Falconer.Fourier.DescriptorDerivativeScale
import Mathlib.Tactic.FinCases

namespace OAI

/-! # One normalized descriptor inverse family for every large scale

The operator, its finite index set, and all constants are chosen before the
scale label. Every original descriptor remains in the support condition.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem equal_scale_product_derivatives {d K : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (B C : Space d → ℂ) (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C)
    (hb : ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k B x‖ ≤ D^k)
    (hc : ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k C x‖ ≤ D^k) :
    ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k (fun z => B z*C z) x‖ ≤ (2 : ℝ)^K*D^k := by
  classical
  let f : Fin 2 → Space d → ℂ := fun i => if i = 0 then B else C
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ContDiff ℝ ∞ (f i) := by
    intro i _
    fin_cases i
    · simpa [f] using hB
    · simpa [f] using hC
  intro k hk x
  have hfb : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ∀ l ≤ K,
      ‖iteratedFDeriv ℝ l (f i) x‖ ≤ D^l := by
    intro i _ l hl
    fin_cases i
    · simpa [f] using hb l hl x
    · simpa [f] using hc l hl x
  have h := ambient_mask_product_derivatives Finset.univ f hD K x hf hfb k hk
  have hprod : (fun z => ∏ i : Fin 2, f i z) = fun z => B z*C z := by
    funext z
    simp [Fin.prod_univ_two,f]
  rw [hprod] at h
  have htwo : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
  rw [htwo,mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) (pow_nonneg hD _))

theorem normalized_descriptor_inverse_family {I : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (n j K P : ℕ) {σ : ℝ} (hσ : 0 < σ)
    (Q : I → DyadicCube (n+3)) (hQ : ∀ a, 0 < (Q a).side)
    (ρ : I → Measure (Space (n+3))) (f : I → ℝ → ℝ) (N L J i t : I → ℕ)
    (B : I → Finset PlanarFalconer.PolicyDescriptor)
    (hB : ∀ a b, b ∈ B a → PlanarFalconer.descriptorAnchor b ≤ t a)
    (S : I → PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3)))
    (hcard : ∀ a, (B a).card ≤ (N a+1)^P)
    (hlength : ∀ a b, b ∈ B a → PlanarFalconer.descriptorLength b ≤ L a)
    (hsep : ∀ a b, b ∈ B a → ∀ w ∈ S a b, ∀ z ∈ S a b, w ≠ z →
      descriptorMaskRadius (N a) σ b/2 ≤ dist w z) :
    let F : I × Space (n+3) → Space (n+3) → ℂ := fun p z =>
      (descriptorAmbientProduct (Q p.1) (ρ p.1) (f p.1) (N p.1)
        σ (J p.1) (i p.1) (B p.1) (S p.1) p.2 z : ℂ)
    ∃ N₀ : ℕ, ∃ T : SmoothSeparation (I × Space (n+3)) (I × Space (n+3)) (Space (n+3)),
      ∃ p q : T.index → ℕ, ∃ A E : T.index → ℝ,
      (∀ k : T.index, Measurable (Function.uncurry (T.left k)) ∧
        Measurable (Function.uncurry (T.right k))) ∧
      (∀ k, p k+q k ≤ 2*j ∧ 1 ≤ A k ∧ 1 ≤ E k) ∧
      (∀ x y z, localInverseAmplitude n (fun w => F x w*F y w) j z = T.value x y z) ∧
      (∀ a, N₀ ≤ N a → ∀ D : ℝ, descriptorDerivativeScale (N a) σ (L a) ≤ D →
        ∀ k : T.index,
          ChartSymbolControl K
            (normalizedEndpoint (A k*D^(p k)) (fun x w => T.left k (a,x) w)) 1 D ∧
          ChartSymbolControl K
            (normalizedEndpoint (E k*D^(q k)) (fun x w => T.right k (a,x) w)) 1 D) ∧
      (∀ D : ℝ, 1 ≤ D → ∀ k,
        (A k*D^(p k))*(E k*D^(q k)) ≤ A k*E k*D^(2*j)) ∧
      (∀ a b (D : ℝ), 1 ≤ D → ∀ (x y : Space (n+3)) (w : Sphere (n+3)),
        localInverseAmplitude n (fun z => F (a,x) z*F (b,y) z) j w =
          ∑ k : T.index, ((A k*E k*D^(p k+q k) : ℝ) : ℂ)*
            (normalizedEndpoint (A k*D^(p k)) (fun x w => T.left k (a,x) w) x w*
              normalizedEndpoint (E k*D^(q k)) (fun y w => T.right k (b,y) w) y w)) ∧
      (∀ a (D : ℝ) (k : T.index) (w : Sphere (n+3)),
        (∀ x, normalizedEndpoint (A k*D^(p k)) (fun x w => T.left k (a,x) w) x w ≠ 0 →
          ∀ b ∈ B a, (x,w) ∈ descriptorEndpointGood (Q a) (ρ a) (f a) (N a)
            σ (J a) (i a+1) b) ∧
        (∀ x, normalizedEndpoint (E k*D^(q k)) (fun x w => T.right k (a,x) w) x w ≠ 0 →
          ∀ b ∈ B a, (x,w) ∈ descriptorEndpointGood (Q a) (ρ a) (f a) (N a)
            σ (J a) (i a+1) b)) := by
  let F : I × Space (n+3) → Space (n+3) → ℂ := fun p z =>
    (descriptorAmbientProduct (Q p.1) (ρ p.1) (f p.1) (N p.1)
      σ (J p.1) (i p.1) (B p.1) (S p.1) p.2 z : ℂ)
  obtain ⟨T,horder,hmeas,hvalue,hsupport⟩ := uniform_descriptor_inverse_factors n j
    Q hQ ρ f N (fun _ => σ) J i t B hB S
  change T.HasOrder F F (2*j) at horder
  obtain ⟨p,q,A,E,hpq,hnorm⟩ := horder.normalizedChartFamily (n := n+1) hmeas K
  obtain ⟨N₀,hscale⟩ := uniform_descriptor_global_scale (n+3) (K+2*j) P hσ
  refine ⟨N₀,T,p,q,A,E,hmeas,hpq,hvalue,?_,?_,?_,?_⟩
  · intro a hNa D hD k
    have hD1 : 1 ≤ D := (descriptorDerivativeScale_ge_one (N a) hσ.le (L a)).trans hD
    have hb : ∀ x l, l ≤ K+2*j → ∀ z, ‖iteratedFDeriv ℝ l (F (a,x)) z‖ ≤ 1*D^l := by
      intro x l hl z
      have hs := hscale (N a) hNa (Q a) (ρ a) (f a) (J a) (i a) (L a) (B a) (S a)
        (hcard a) (hlength a) (hsep a) x z l hl
      have hpow : (descriptorDerivativeScale (N a) σ (L a))^l ≤ D^l :=
        pow_le_pow_left₀
          (zero_le_one.trans (descriptorDerivativeScale_ge_one (N a) hσ.le (L a))) hD l
      simpa only [one_mul] using hs.trans hpow
    have hh := hnorm a 1 1 D le_rfl le_rfl hD1 hb hb k
    simpa only [mul_one] using And.intro hh.1 hh.2.1
  · intro D hD k
    have he := endpoint_order_product_le (hpq k).1
      (zero_le_one.trans (hpq k).2.1) (zero_le_one.trans (hpq k).2.2)
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hD
    simpa only [mul_one] using he
  · intro a b D hD x y w
    rw [hvalue]
    change (∑ k : T.index, T.left k (a,x) w*T.right k (b,y) w) = _
    apply Finset.sum_congr rfl
    intro k _
    have hp : 0 < A k*D^(p k) := mul_pos
      (zero_lt_one.trans_le (hpq k).2.1) (pow_pos (zero_lt_one.trans_le hD) _)
    have hq : 0 < E k*D^(q k) := mul_pos
      (zero_lt_one.trans_le (hpq k).2.2) (pow_pos (zero_lt_one.trans_le hD) _)
    have he := normalizedEndpoint_product_restore hp hq
      (fun x w => T.left k (a,x) w) (fun y w => T.right k (b,y) w) x y w
    have hc : (A k*D^(p k))*(E k*D^(q k)) = A k*E k*D^(p k+q k) := by
      rw [pow_add]
      ring
    rwa [hc] at he
  · intro a D k w
    constructor
    · intro x hx
      exact (hsupport w k).1 (a,x) (normalizedEndpoint_ne_zero _ _ _ _ hx)
    · intro x hx
      exact (hsupport w k).2 (a,x) (normalizedEndpoint_ne_zero _ _ _ _ hx)

end Falconer

end OAI
