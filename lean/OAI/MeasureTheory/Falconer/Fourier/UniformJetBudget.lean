import OAI.MeasureTheory.Falconer.Fourier.NormalizedJetDerivatives
import OAI.MeasureTheory.Falconer.Measures.AmbientMaskProductBudget

namespace OAI

/-! # A fixed derivative budget for each normalized mask jet

One constant is selected before all scales and descriptor lists. Only the
sum of actual derivative orders pays an amplitude cost.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

 theorem normalizedAmbientDescriptorJet_uniform_budget (d K L : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PlanarFalconer.PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ D : ℝ, 1 ≤ D → (descriptorMaskRadius N σ b)⁻¹ ≤ D →
      ∀ k ≤ K, ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ t ≤ L, ∀ (x z : Space d),
        ‖iteratedFDeriv ℝ t (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x) z‖ ≤
          A^(k+t)*D^t := by
  classical
  choose C hC hbound using fun k t => normalizedAmbientDescriptorJet_derivatives d k t
  let A := 1+∑ p ∈ (Finset.range (K+1)).product (Finset.range (L+1)), C p.1 p.2
  have hA : 1 ≤ A := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg
      (fun p (_ : p ∈ (Finset.range (K+1)).product (Finset.range (L+1))) => hC p.1 p.2))
  have hCA (k t : ℕ) (hk : k ≤ K) (ht : t ≤ L) : C k t ≤ A := by
    have hp : (k,t) ∈ (Finset.range (K+1)).product (Finset.range (L+1)) :=
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩
    have hh := Finset.single_le_sum
      (fun p (_ : p ∈ (Finset.range (K+1)).product (Finset.range (L+1))) => hC p.1 p.2) hp
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨A,hA,?_⟩
  intro Q ρ m N σ J i b S hsep D hD hscale k hk v hv t ht x z
  by_cases hzero : k+t = 0
  · have hk0 : k = 0 := by omega
    have ht0 : t = 0 := by omega
    subst k
    subst t
    simp only [norm_iteratedFDeriv_zero,normalizedAmbientDescriptorJet,pow_zero,
      iteratedFDeriv_zero_apply,one_mul,zero_add]
    have h := descriptorAmbientMask_global_bounds Q ρ m N σ J i b S x z
    simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  · apply (hbound k t Q ρ m N σ J i b S hsep v hv x z).trans
    exact mul_le_mul ((hCA k t hk ht).trans (le_self_pow₀ hA hzero))
      (pow_le_pow_left₀ (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) hscale t)
      (pow_nonneg (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) t)
      (pow_nonneg (zero_le_one.trans hA) (k+t))

 theorem rescaledAmbientDescriptorJet_budget {d k L : ℕ}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PlanarFalconer.PolicyDescriptor)
    (S : Finset (Sphere d)) (v : Fin k → Space d)
    {A D : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ t ≤ L, ∀ x z,
      ‖iteratedFDeriv ℝ t (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x) z‖ ≤
        A^(k+t)*D^t) (x z : Space d) (t : ℕ) (ht : t ≤ L) :
    ‖iteratedFDeriv ℝ t (fun w => A⁻¹^k *
      normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x w) z‖ ≤ (A*D)^t := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  change ‖iteratedFDeriv ℝ t (fun w => A⁻¹^k •
      normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x w) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    ((normalizedAmbientDescriptorJet_contDiff Q ρ m N σ J i b S k v x).of_le (by simp)).contDiffAt,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hAp.le) k)]
  calc
    _ ≤ A⁻¹^k*(A^(k+t)*D^t) :=
      mul_le_mul_of_nonneg_left (hbound t ht x z) (pow_nonneg (inv_nonneg.mpr hAp.le) k)
    _ = (A*D)^t := by
      rw [pow_add,mul_pow]
      calc
        _ = (A⁻¹*A)^k*(A^t*D^t) := by rw [mul_pow]; ring
        _ = _ := by rw [inv_mul_cancel₀ hAp.ne',one_pow,one_mul]


private theorem weighted_jet_product_bound {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι]
    (F : Finset ι) (f : ι → E → ℝ) (c : ι → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (L : ℕ) (z : E) (hc : ∀ i ∈ F, 0 ≤ c i)
    (hf : ∀ i ∈ F, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ F, ∀ t ≤ L, ‖iteratedFDeriv ℝ t (f i) z‖ ≤ c i*D^t) :
    ∀ t ≤ L, ‖iteratedFDeriv ℝ t (fun w => ∏ i ∈ F, f i w) z‖ ≤
      (∏ i ∈ F, c i)*((F.card:ℝ)*D)^t := by
  induction F using Finset.induction_on with
  | empty =>
    intro t _
    cases t with
    | zero => simp
    | succ t => simp [iteratedFDeriv_succ_const]
  | @insert i F hi ih =>
    have hcF : ∀ j ∈ F, 0 ≤ c j := fun j hj => hc j (Finset.mem_insert_of_mem hj)
    have hfF : ∀ j ∈ F, ContDiff ℝ ∞ (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hbF : ∀ j ∈ F, ∀ t ≤ L, ‖iteratedFDeriv ℝ t (f j) z‖ ≤ c j*D^t :=
      fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hih := ih hcF hfF hbF
    intro t ht
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hff : ContDiff ℝ ∞ (fun w => ∏ j ∈ F, f j w) := contDiff_prod hfF
    simp only [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]
    apply (norm_iteratedFDeriv_mul_le hfi hff z (by simp : (t:ℕ∞ω) ≤ ∞)).trans
    calc
      _ ≤ ∑ q ∈ Finset.range (t+1), (t.choose q:ℝ)*(c i*D^q)*
          ((∏ j ∈ F, c j)*((F.card:ℝ)*D)^(t-q)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqt : q ≤ t := by have := Finset.mem_range.mp hq; omega
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hb i (Finset.mem_insert_self _ _) q (hqt.trans ht))
            (Nat.cast_nonneg _))
          (hih (t-q) ((Nat.sub_le _ _).trans ht)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hc i (Finset.mem_insert_self _ _))
            (pow_nonneg hD _)))
      _ = (c i*(∏ j ∈ F, c j)) *
          (∑ q ∈ Finset.range (t+1), (t.choose q:ℝ)*D^q*((F.card:ℝ)*D)^(t-q)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = (c i*(∏ j ∈ F, c j))*(D+(F.card:ℝ)*D)^t := by
        congr 1
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = _ := by congr 2; ring

 theorem normalizedAmbientJetProduct_uniform_budget (d K L : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {ι : Type*} (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
      (b : ι → PlanarFalconer.PolicyDescriptor) (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
      (k : ι → ℕ) (v : (j : ι) → Fin (k j) → Space d),
      (∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z → descriptorMaskRadius N σ (b j)/2 ≤ dist w z) →
      (∑ j ∈ F, k j) ≤ K → (∀ j ∈ F, ∀ t, ‖v j t‖ ≤ 1) →
      ∀ D : ℝ, 1 ≤ D → (∀ j ∈ F, (descriptorMaskRadius N σ (b j))⁻¹ ≤ D) →
      ∀ x z t, t ≤ L →
        ‖iteratedFDeriv ℝ t (fun w => ∏ j ∈ F,
          normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x w) z‖ ≤
        A^K*((F.card:ℝ)*A*D)^t := by
  classical
  obtain ⟨A,hA,hbound⟩ := normalizedAmbientDescriptorJet_uniform_budget d K L
  refine ⟨A,hA,?_⟩
  intro ι Q ρ m N σ J i F b S k v hsep horder hv D hD hscale x z t ht
  have hb : ∀ j ∈ F, ∀ q ≤ L,
      ‖iteratedFDeriv ℝ q
        (normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x) z‖ ≤
        A^(k j)*(A*D)^q := by
    intro j hj q hq
    have hk : k j ≤ K := (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) hj).trans horder
    convert hbound Q ρ m N σ J i (b j) (S (b j)) (hsep j hj) D hD (hscale j hj)
      (k j) hk (v j) (hv j hj) q hq x z using 1
    rw [pow_add,mul_pow]
    ring
  have h := weighted_jet_product_bound F
    (fun j => normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x)
    (fun j => A^(k j)) (mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hD)) L z
    (fun j _ => pow_nonneg (zero_le_one.trans hA) _)
    (fun j _ => normalizedAmbientDescriptorJet_contDiff Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x)
    hb t ht
  rw [Finset.prod_pow_eq_pow_sum] at h
  apply h.trans
  have hAK := pow_le_pow_right₀ hA horder
  calc
    _ = A^(∑ j ∈ F, k j)*((F.card:ℝ)*A*D)^t := by rw [mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hAK (pow_nonneg (by positivity) _)

end Falconer

end OAI
