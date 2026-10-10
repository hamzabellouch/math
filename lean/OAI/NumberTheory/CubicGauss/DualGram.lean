import Mathlib
import OAI.NumberTheory.CubicGauss.GramPoisson
import OAI.NumberTheory.CubicGauss.LaplaceBounds

namespace OAI

/-! Gaussian smoothing, transformed cubic Gram sums and dual operator bounds. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment
open HeckeTheta

lemma real_gaussian_summable (r : ℝ) (hr : 0 < r) :
    Summable (fun m : Eisenstein => Real.exp (-r*norm m)) := by
  have hs := (lattice_gaussian_summable (r/Real.pi) 0 (div_pos hr Real.pi_pos)).norm
  simp only [add_zero,Complex.norm_exp] at hs
  convert hs using 1
  ext m
  congr 1
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero]
  field_simp
  rfl

lemma gaussian_pair_summable (χ ψ : Eisenstein → ℂ) (u v : ℂ)
    (hχ : ∀ h, ‖χ h‖ ≤ 1) (hψ : ∀ h, ‖ψ h‖ ≤ 1)
    (r x y : ℝ) (hr : 0 < r) (hx : |x| ≤ (1/10 : ℝ)) (hy : |y| ≤ (1/10 : ℝ)) :
    Summable (fun h : Eisenstein => (u*χ h)*star (v*ψ h)*
      Complex.exp (-((r*norm h:ℝ):ℂ)*(1-x)*(1-y))) := by
  have hxa : 0 < 1-x := by have := (abs_le.mp hx).2; linarith
  have hxb : 0 < 1-y := by have := (abs_le.mp hy).2; linarith
  have hm : 0 < r*(1-x)*(1-y)/Real.pi := by positivity
  have hs := bounded_gaussian_summable
    (fun h => (u*χ h)*star (v*ψ h)) (‖u‖*‖v‖) (by
      intro h
      rw [norm_mul,norm_star,norm_mul,norm_mul]
      exact mul_le_mul (by simpa using
        (mul_le_mul_of_nonneg_left (hχ h) (_root_.norm_nonneg u)))
        (by simpa using (mul_le_mul_of_nonneg_left (hψ h) (_root_.norm_nonneg v)))
        (by positivity) (_root_.norm_nonneg u)) _ hm
  convert hs using 1
  ext h
  congr 1
  congr 1
  push_cast
  field_simp

lemma gaussian_kernel_summable {θ : Type*} (S : Finset θ)
    (χ : Eisenstein → θ → ℂ) (u : θ → ℂ) (x : θ → ℝ)
    (hχ : ∀ h a, ‖χ h a‖ ≤ 1) (hx : ∀ a ∈ S, |x a| ≤ (1/10 : ℝ))
    (r : ℝ) (hr : 0 < r) :
    Summable (fun h : Eisenstein => ∑ a ∈ S, ∑ b ∈ S,
      (u a * χ h a) * star (u b * χ h b) *
        Complex.exp (-((r*norm h : ℝ):ℂ)*(1-x a)*(1-x b))) := by
  apply summable_sum
  intro a ha
  apply summable_sum
  intro b hb
  have hxa : 0 < 1-x a := by have := (abs_le.mp (hx a ha)).2; linarith
  have hxb : 0 < 1-x b := by have := (abs_le.mp (hx b hb)).2; linarith
  have hm : 0 < r*(1-x a)*(1-x b)/Real.pi := by positivity
  have hs := bounded_gaussian_summable
    (fun h => (u a*χ h a)*star (u b*χ h b)) (‖u a‖*‖u b‖) (by
      intro h
      rw [norm_mul,norm_star,norm_mul,norm_mul]
      exact mul_le_mul (by simpa using (mul_le_mul_of_nonneg_left (hχ h a)
        (_root_.norm_nonneg (u a)))) (by simpa using
        (mul_le_mul_of_nonneg_left (hχ h b) (_root_.norm_nonneg (u b))))
        (by positivity) (_root_.norm_nonneg (u a))) _ hm
  convert hs using 1
  ext h
  congr 1
  congr 1
  push_cast
  field_simp

 

theorem gaussian_lattice_gram_bound {θ : Type*} (S : Finset θ)
    (χ : Eisenstein → θ → ℂ) (u : θ → ℂ) (x : θ → ℝ)
    (hχ : ∀ h a, ‖χ h a‖ ≤ 1) (hx : ∀ a ∈ S, |x a| ≤ (1/10 : ℝ))
    (r : ℝ) (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (hop : ∀ (H : Finset Eisenstein) (v : θ → ℂ),
      ∑ h ∈ H, Real.exp (-r*norm h/2) * ‖∑ a ∈ S,v a*χ h a‖^2 ≤
        K*∑ a ∈ S,‖v a‖^2) :
    ‖∑' h : Eisenstein, ∑ a ∈ S, ∑ b ∈ S,
      (u a*χ h a)*star (u b*χ h b)*
        Complex.exp (-((r*norm h:ℝ):ℂ)*(1-x a)*(1-x b))‖ ≤
      7*K*∑ a ∈ S,‖u a‖^2 := by
  have hs := gaussian_kernel_summable S χ u x hχ hx r hr
  apply le_of_tendsto (hs.hasSum.norm)
  apply Filter.Eventually.of_forall
  intro H
  exact SieveKernel.gaussian_weighted_gram_bound H S χ u x (fun h => r*norm h) hK hx
    (fun h _ => mul_nonneg hr.le (norm_nonneg h)) (by
      intro v
      simpa only [neg_mul] using hop H v)

end CubicFirstMoment

namespace CubicFirstMoment
open HeckeTheta

def cubicG (a : Eisenstein) : ℂ :=
  if ha : primary a then heckeGauss a (primary_ne_zero ha) (compositeCubicChar a ha) else 0

lemma cubicG_eq {a : Eisenstein} (ha : primary a) :
    cubicG a = heckeGauss a (primary_ne_zero ha) (compositeCubicChar a ha) := by
  simp [cubicG,ha]

lemma norm_cubicG {a : Eisenstein} (ha : primary a) (hs : Squarefree a) :
    ‖cubicG a‖ = Real.sqrt (norm a) := by
  rw [cubicG_eq ha]
  exact composite_gauss_norm a ha hs

def sieveFiber (N : ℝ) (S : Finset Eisenstein) (k : Eisenstein) : Finset Eisenstein :=
  (squarefreePrimaryBall N).filter (fun a => k*a ∈ S)

@[simp] lemma mem_sieveFiber {N : ℝ} {S : Finset Eisenstein} {k a : Eisenstein} :
    a ∈ sieveFiber N S k ↔ a ∈ squarefreePrimaryBall N ∧ k*a ∈ S := by
  simp [sieveFiber]

lemma sum_product_explicit {α β : Type*} (S : Finset α) (T : Finset β)
    (f : α × β → ℂ) : (∑ v ∈ S.product T,f v) = ∑ a ∈ S,∑ b ∈ T,f (a,b) :=
  Finset.sum_product S T f

lemma sum_common_by_fiber (N : ℝ) (S : Finset Eisenstein)
    (f : Eisenstein → Eisenstein → Eisenstein → ℂ) :
    (∑ v ∈ commonTriples N S, f v.1 v.2.1 v.2.2) =
      ∑ k ∈ squarefreePrimaryBall N, ∑ a ∈ sieveFiber N S k,
        ∑ b ∈ sieveFiber N S k, if IsCoprime a b then f k a b else 0 := by
  simp only [commonTriples,Finset.sum_filter,sieveFiber]
  rw [sum_product_explicit]
  simp_rw [sum_product_explicit]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hka : k*a ∈ S
  · simp only [hka,true_and,ite_true]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hkb : k*b ∈ S <;> simp [hkb]
  · simp [hka]

def cubicDualPair (s : ℝ) (a b : Eisenstein) : ℂ :=
  (cubicG a * star (cubicG b)) / (norm (a*b) : ℂ) *
    ∑' h : Eisenstein,
      Complex.exp (-(4*(Real.pi:ℂ))/(3*s*norm (a*b))*(norm h:ℂ)) *
        (star (cubicSymbol a h) * cubicSymbol b h)

 

theorem cubic_gaussian_gram_transform {N : ℝ} (S : Finset Eisenstein)
    (hS : S ⊆ squarefreePrimaryBall N) (u : Eisenstein → ℂ)
    (t : ℝ) (ht : 0 < t) :
    (∑' m : Eisenstein, (cubicRowEnergy S u m : ℂ) *
      Complex.exp (-(Real.pi:ℂ)*t*(norm m:ℂ))) =
      ∑ k ∈ squarefreePrimaryBall N,
        ∑ d ∈ primaryDivisors k, (idealMoebius d : ℂ) *
          (2/((Real.sqrt 3:ℂ)*t*norm d)) *
          ∑ a ∈ sieveFiber N S k, ∑ b ∈ sieveFiber N S k,
            (if IsCoprime a b then (1:ℂ) else 0) *
              (u (k*a)*cubicSymbol a d) * star (u (k*b)*cubicSymbol b d) *
                cubicDualPair (t*norm d) a b := by
  have hsum (v : CommonIndex) (hv : v ∈ commonTriples N S) :
      Summable (fun m : Eisenstein =>
        (u (v.1*v.2.1)*star (u (v.1*v.2.2))) *
        (if IsCoprime v.1 m then (1:ℂ) else 0) *
        (cubicSymbol v.2.1 m*star (cubicSymbol v.2.2 m)) *
        Complex.exp (-(Real.pi:ℂ)*t*(norm m:ℂ))) := by
    have hv := mem_commonTriples.mp hv
    apply bounded_gaussian_summable _ ‖u (v.1*v.2.1)*star (u (v.1*v.2.2))‖ _ t ht
    intro m
    rw [norm_mul,norm_mul]
    have hi : ‖if IsCoprime v.1 m then (1:ℂ) else 0‖ ≤ 1 := by split_ifs <;> norm_num
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hi (_root_.norm_nonneg _))
      (cubicCorrelation_norm_le (mem_squarefreePrimaryBall.mp hv.2.1).1
        (mem_squarefreePrimaryBall.mp hv.2.2.1).1 m) (_root_.norm_nonneg _) (by positivity)).trans_eq
          (by ring)
  simp_rw [cubic_row_common_gram S hS u,Finset.sum_mul]
  rw [Summable.tsum_finsetSum hsum]
  have he (k a b : Eisenstein) (hv : (k,a,b) ∈ commonTriples N S) :
      (∑' m : Eisenstein, (u (k*a)*star (u (k*b))) *
        (if IsCoprime k m then (1:ℂ) else 0) *
        (cubicSymbol a m*star (cubicSymbol b m)) *
        Complex.exp (-(Real.pi:ℂ)*t*(norm m:ℂ))) =
      ∑ d ∈ primaryDivisors k, (idealMoebius d : ℂ) *
        (2/((Real.sqrt 3:ℂ)*t*norm d)) *
        (u (k*a)*cubicSymbol a d) * star (u (k*b)*cubicSymbol b d) *
          cubicDualPair (t*norm d) a b := by
    have hv := mem_commonTriples.mp hv
    obtain ⟨hk,hks,_⟩ := mem_squarefreePrimaryBall.mp hv.1
    obtain ⟨ha,has,_⟩ := mem_squarefreePrimaryBall.mp hv.2.1
    obtain ⟨hb,hbs,_⟩ := mem_squarefreePrimaryBall.mp hv.2.2.1
    simp_rw [mul_assoc (u (k*a)*star (u (k*b)))]
    rw [tsum_mul_left,cubic_common_correlation_poisson hk hks ha hb has hbs hv.2.2.2.2.2 t ht,
      sum_primaryDivisors hk hks,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    simp only [cubicDualPair,cubicG_eq ha,cubicG_eq hb,star_mul,Complex.ofReal_mul]
    ring
  rw [Finset.sum_congr rfl (fun v hv => he v.1 v.2.1 v.2.2 hv)]
  rw [sum_common_by_fiber N S (fun k a b => ∑ d ∈ primaryDivisors k,
    (idealMoebius d : ℂ) * (2/((Real.sqrt 3:ℂ)*t*norm d)) *
      (u (k*a)*cubicSymbol a d) * star (u (k*b)*cubicSymbol b d) *
        cubicDualPair (t*norm d) a b)]
  apply Finset.sum_congr rfl
  intro k hk
  have ite_sum (a b : Eisenstein) (f : Eisenstein → ℂ) :
      (if IsCoprime a b then ∑ d ∈ primaryDivisors k,f d else 0) =
        ∑ d ∈ primaryDivisors k,if IsCoprime a b then f d else 0 := by
    split_ifs <;> simp_all
  simp_rw [ite_sum,Finset.sum_comm (s := sieveFiber N S k) (t := primaryDivisors k)]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp_all only [one_mul,zero_mul] <;> ring

end CubicFirstMoment

namespace CubicFirstMoment

def cubicDualForm (s : ℝ) (S : Finset Eisenstein) (u : Eisenstein → ℂ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, (u a*star (u b))*cubicDualPair s a b

 

theorem cubic_dual_form_bound (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (s L K : ℝ) (hs : 0 < s) (hL : 0 < L) (hK : 0 ≤ K)
    (hn : ∀ a ∈ S, L ≤ norm a ∧ norm a ≤ (10/9:ℝ)*L)
    (hop : ∀ (H : Finset Eisenstein) (v : Eisenstein → ℂ),
      ∑ h ∈ H, Real.exp (-(4*Real.pi/(3*s*L^2))*norm h/2) *
        ‖∑ a ∈ S, v a*star (cubicSymbol a h)‖^2 ≤ K*∑ a ∈ S, ‖v a‖^2) :
    ‖cubicDualForm s S u‖ ≤ (7*K/L)*∑ a ∈ S, ‖u a‖^2 := by
  let r := 4*Real.pi/(3*s*L^2)
  let x := fun a : Eisenstein => 1-L/norm a
  let v := fun a : Eisenstein => u a*cubicG a/(norm a:ℂ)
  let χ := fun h a : Eisenstein => if primary a then star (cubicSymbol a h) else 0
  have hr : 0 < r := by dsimp [r]; positivity
  have hχ (h a : Eisenstein) : ‖χ h a‖ ≤ 1 := by
    dsimp only [χ]
    split_ifs with ha
    · rw [norm_star]; exact norm_cubicSymbol_le_one ha h
    · norm_num
  have hx (a : Eisenstein) (ha : a ∈ S) : |x a| ≤ (1/10:ℝ) := by
    obtain ⟨h1,h2⟩ := hn a ha
    have hna := hL.trans_le h1
    have h3 : L/norm a ≤ 1 := (div_le_one hna).mpr h1
    have h4 : (9/10:ℝ) ≤ L/norm a := (le_div_iff₀ hna).mpr (by linarith)
    dsimp [x]
    rw [abs_le]
    constructor <;> linarith
  let F := fun a b h : Eisenstein => (v a*χ h a)*star (v b*χ h b)*
    Complex.exp (-((r*norm h:ℝ):ℂ)*(1-x a)*(1-x b))
  have hF (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) (hb : b ∈ S) :
      Summable (F a b) :=
    gaussian_pair_summable (fun h => χ h a) (fun h => χ h b) (v a) (v b)
      (fun h => hχ h a) (fun h => hχ h b) r (x a) (x b) hr (hx a ha) (hx b hb)
  have he (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) (hb : b ∈ S) :
      (u a*star (u b))*cubicDualPair s a b = ∑' h : Eisenstein,F a b h := by
    have han : norm a ≠ 0 := ne_of_gt (hL.trans_le (hn a ha).1)
    have hbn : norm b ≠ 0 := ne_of_gt (hL.trans_le (hn b hb).1)
    have hLC : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    have hanC : (norm a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr han
    have hbnC : (norm b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hbn
    unfold cubicDualPair
    rw [← mul_assoc,← tsum_mul_left]
    apply tsum_congr
    intro h
    have hexp : -(4*(Real.pi:ℂ))/(3*s*norm (a*b))*(norm h:ℂ) =
        -((r*norm h:ℝ):ℂ)*(1-x a)*(1-x b) := by
      dsimp [r,x]
      simp only [norm_mul_eq,Complex.ofReal_mul,Complex.ofReal_div,
        Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_sub,Complex.ofReal_one]
      field_simp [hanC,hbnC,hLC]
      ring
    dsimp only [F,v,χ]
    rw [ite_eq_left (hS a ha).1,ite_eq_left (hS b hb).1,hexp]
    have hc_mul (z w : ℂ) : (starRingEnd ℂ) (z*w) =
        (starRingEnd ℂ) z * (starRingEnd ℂ) w := map_mul _ z w
    have hc_div (z w : ℂ) : (starRingEnd ℂ) (z/w) =
        (starRingEnd ℂ) z / (starRingEnd ℂ) w := map_div₀ _ z w
    have hc_star (z : ℂ) : (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := star_star z
    have hc_real (y : ℝ) : (starRingEnd ℂ) (y:ℂ) = (y:ℂ) := Complex.conj_ofReal y
    simp only [star_mul,Complex.star_def,hc_mul,hc_div,hc_star,hc_real,
      norm_mul_eq,Complex.ofReal_mul]
    ring
  have hid : cubicDualForm s S u = ∑' h : Eisenstein, ∑ a ∈ S, ∑ b ∈ S,F a b h := by
    unfold cubicDualForm
    rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hF a ha b hb))]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Summable.tsum_finsetSum (fun b hb => hF a ha b hb)]
    exact Finset.sum_congr rfl (fun b hb => he a ha b hb)
  have hop' (H : Finset Eisenstein) (w : Eisenstein → ℂ) :
      ∑ h ∈ H, Real.exp (-r*norm h/2)*‖∑ a ∈ S,w a*χ h a‖^2 ≤
        K*∑ a ∈ S,‖w a‖^2 := by
    have heχ (h : Eisenstein) : (∑ a ∈ S,w a*χ h a) =
        ∑ a ∈ S,w a*star (cubicSymbol a h) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [χ,ite_eq_left (hS a ha).1]
    simpa only [heχ,r] using hop H w
  have hb := gaussian_lattice_gram_bound S χ v x hχ hx r hr K hK hop'
  rw [← hid] at hb
  have hvnorm (a : Eisenstein) (ha : a ∈ S) : ‖v a‖^2 = ‖u a‖^2/norm a := by
    have hna : 0 < norm a := hL.trans_le (hn a ha).1
    dsimp [v]
    rw [norm_div,norm_mul,norm_cubicG (hS a ha).1 (hS a ha).2,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hna,div_pow,mul_pow,
      Real.sq_sqrt (norm_nonneg a)]
    field_simp [ne_of_gt hna]
  have hsum : ∑ a ∈ S,‖v a‖^2 ≤ (∑ a ∈ S,‖u a‖^2)/L := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro a ha
    rw [hvnorm a ha]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hL (hn a ha).1
  apply hb.trans
  calc
    _ ≤ 7*K*((∑ a ∈ S,‖u a‖^2)/L) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end CubicFirstMoment
end

end OAI
