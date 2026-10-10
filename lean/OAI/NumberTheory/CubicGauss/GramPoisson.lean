import Mathlib
import OAI.NumberTheory.CubicGauss.CubeOperators
import OAI.NumberTheory.CubicGauss.DivisorWeights

namespace OAI

/-! Cubic Gram expansions and their residue-Poisson transforms. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma dvd_common_of_coprime {d k x y : Eisenstein} (hxy : IsCoprime x y)
    (hx : d ∣ k*x) (hy : d ∣ k*y) : d ∣ k := by
  obtain ⟨a,b,hab⟩ := hxy
  have he : k = a*(k*x)+b*(k*y) := by calc
    _ = k*(a*x+b*y) := by rw [hab,mul_one]
    _ = _ := by ring
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right hx a) (dvd_mul_of_dvd_right hy b)

lemma primary_common_split_unique {k x y l v w : Eisenstein}
    (hk : primary k) (hl : primary l) (hxy : IsCoprime x y) (hvw : IsCoprime v w)
    (ha : k*x=l*v) (hb : k*y=l*w) : k=l ∧ x=v ∧ y=w := by
  have hkl : k ∣ l := dvd_common_of_coprime hvw
    (ha ▸ dvd_mul_right k x) (hb ▸ dvd_mul_right k y)
  have hlk : l ∣ k := dvd_common_of_coprime hxy
    (ha.symm ▸ dvd_mul_right l v) (hb.symm ▸ dvd_mul_right l w)
  have he : k=l := primary_associated_eq hk hl (associated_of_dvd_dvd hkl hlk)
  subst l
  exact ⟨rfl,mul_left_cancel₀ (primary_ne_zero hk) ha,
    mul_left_cancel₀ (primary_ne_zero hk) hb⟩

abbrev CommonIndex := Eisenstein × Eisenstein × Eisenstein

def commonTriples (N : ℝ) (S : Finset Eisenstein) : Finset CommonIndex :=
  ((squarefreePrimaryBall N).product ((squarefreePrimaryBall N).product
    (squarefreePrimaryBall N))).filter fun v =>
      v.1*v.2.1 ∈ S ∧ v.1*v.2.2 ∈ S ∧ IsCoprime v.2.1 v.2.2

lemma mem_commonTriples {N : ℝ} {S : Finset Eisenstein} {k a b : Eisenstein} :
    (k,a,b) ∈ commonTriples N S ↔
      k ∈ squarefreePrimaryBall N ∧ a ∈ squarefreePrimaryBall N ∧
      b ∈ squarefreePrimaryBall N ∧ k*a ∈ S ∧ k*b ∈ S ∧ IsCoprime a b := by
  simp only [commonTriples,Finset.mem_filter]
  constructor
  · rintro ⟨hv,h1,h2,h3⟩
    obtain ⟨hk,hab⟩ := Finset.mem_product.mp hv
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    exact ⟨hk,ha,hb,h1,h2,h3⟩
  · rintro ⟨hk,ha,hb,h1,h2,h3⟩
    exact ⟨Finset.mem_product.mpr ⟨hk,Finset.mem_product.mpr ⟨ha,hb⟩⟩,h1,h2,h3⟩

 

theorem sum_commonTriples {N : ℝ} (S : Finset Eisenstein)
    (hS : S ⊆ squarefreePrimaryBall N) (f : Eisenstein → Eisenstein → ℂ) :
    ∑ v ∈ commonTriples N S, f (v.1*v.2.1) (v.1*v.2.2) =
      ∑ a ∈ S, ∑ b ∈ S, f a b := by
  rw [← Finset.sum_product S S (fun v : Eisenstein × Eisenstein => f v.1 v.2)]
  apply Finset.sum_bij (fun v _ => (v.1*v.2.1,v.1*v.2.2))
  · rintro ⟨k,a,b⟩ hv
    have hv := mem_commonTriples.mp hv
    exact Finset.mem_product.mpr ⟨hv.2.2.2.1,hv.2.2.2.2.1⟩
  · rintro ⟨k,a,b⟩ hv ⟨l,c,d⟩ hw he
    have hv := mem_commonTriples.mp hv
    have hw := mem_commonTriples.mp hw
    obtain ⟨h1,h2,h3⟩ := primary_common_split_unique
      (mem_squarefreePrimaryBall.mp hv.1).1 (mem_squarefreePrimaryBall.mp hw.1).1
      hv.2.2.2.2.2 hw.2.2.2.2.2 (congrArg Prod.fst he) (congrArg Prod.snd he)
    simp only [Prod.mk.injEq]; exact ⟨h1,h2,h3⟩
  · rintro ⟨a,b⟩ hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hap,has,han⟩ := mem_squarefreePrimaryBall.mp (hS ha)
    obtain ⟨hbp,hbs,hbn⟩ := mem_squarefreePrimaryBall.mp (hS hb)
    obtain ⟨k,x,y,hk,hx,hy,hks,hxs,hys,hkx,hky,hxy,hek,hel⟩ :=
      common_squarefree_split hap hbp has hbs
    have hkn : norm k ≤ N := (norm_le_of_dvd (primary_ne_zero hap) ⟨x,hek⟩).trans han
    have hxn : norm x ≤ N := (norm_le_of_dvd (primary_ne_zero hap)
      ⟨k,by rw [hek,mul_comm]⟩).trans han
    have hyn : norm y ≤ N := (norm_le_of_dvd (primary_ne_zero hbp)
      ⟨k,by rw [hel,mul_comm]⟩).trans hbn
    refine ⟨(k,x,y),mem_commonTriples.mpr ⟨mem_squarefreePrimaryBall.mpr ⟨hk,hks,hkn⟩,
      mem_squarefreePrimaryBall.mpr ⟨hx,hxs,hxn⟩,mem_squarefreePrimaryBall.mpr ⟨hy,hys,hyn⟩,
      hek ▸ ha,hel ▸ hb,hxy⟩,?_⟩
    exact Prod.ext hek.symm hel.symm
  · intro v hv; rfl

lemma cubic_common_gram {k a b : Eisenstein} (hk : primary k) (ha : primary a)
    (hb : primary b) (m : Eisenstein) :
    cubicSymbol (k*a) m * star (cubicSymbol (k*b) m) =
      (if IsCoprime k m then (1:ℂ) else 0) *
        (cubicSymbol a m * star (cubicSymbol b m)) := by
  rw [cubicSymbol_mul_lower (primary_ne_zero hk) (primary_ne_zero ha),
    cubicSymbol_mul_lower (primary_ne_zero hk) (primary_ne_zero hb),star_mul]
  have he : cubicSymbol k m * star (cubicSymbol k m) =
      if IsCoprime k m then (1:ℂ) else 0 := by
    split_ifs with h
    · rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,
        norm_cubicSymbol_of_isCoprime hk h]; norm_num
    · rw [cubicSymbol_eq_zero_of_not_isCoprime hk h,zero_mul]
  calc
    _ = (cubicSymbol k m * star (cubicSymbol k m)) *
      (cubicSymbol a m * star (cubicSymbol b m)) := by ring
    _ = _ := by rw [he]

 
theorem cubic_row_common_gram {N : ℝ} (S : Finset Eisenstein)
    (hS : S ⊆ squarefreePrimaryBall N) (u : Eisenstein → ℂ) (m : Eisenstein) :
    (cubicRowEnergy S u m : ℂ) =
      ∑ v ∈ commonTriples N S,
        (u (v.1*v.2.1) * star (u (v.1*v.2.2))) *
        (if IsCoprime v.1 m then (1:ℂ) else 0) *
        (cubicSymbol v.2.1 m * star (cubicSymbol v.2.2 m)) := by
  have he : (cubicRowEnergy S u m : ℂ) =
      ∑ a ∈ S, ∑ b ∈ S, (u a * star (u b)) *
        (cubicSymbol a m * star (cubicSymbol b m)) := by
    unfold cubicRowEnergy
    rw [← Complex.normSq_eq_norm_sq,← Complex.mul_conj,← Complex.star_def,star_sum,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [star_mul]
    ring
  rw [he,← sum_commonTriples S hS]
  apply Finset.sum_congr rfl
  rintro ⟨k,a,b⟩ hv
  have hv := mem_commonTriples.mp hv
  rw [cubic_common_gram (mem_squarefreePrimaryBall.mp hv.1).1
    (mem_squarefreePrimaryBall.mp hv.2.1).1
    (mem_squarefreePrimaryBall.mp hv.2.2.1).1]
  ring


open HeckeTheta

lemma bounded_gaussian_summable (f : Eisenstein → ℂ) (C : ℝ)
    (hf : ∀ m, ‖f m‖ ≤ C) (t : ℝ) (ht : 0 < t) :
    Summable (fun m : Eisenstein => f m *
      Complex.exp (-(Real.pi:ℂ)*t*(norm m:ℂ))) := by
  have hs := ((lattice_gaussian_summable t 0 ht).norm).mul_left C
  simp only [add_zero] at hs
  apply hs.of_norm_bounded
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hf m) (_root_.norm_nonneg _)

lemma cubicCorrelation_norm_le {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (m : Eisenstein) : ‖cubicSymbol a m * star (cubicSymbol b m)‖ ≤ 1 := by
  rw [norm_mul,norm_star]
  exact (mul_le_mul (norm_cubicSymbol_le_one ha m) (norm_cubicSymbol_le_one hb m)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul _)

lemma dvdIndicator_norm_le (d m : Eisenstein) :
    ‖if d ∣ m then (1:ℂ) else 0‖ ≤ 1 := by split_ifs <;> norm_num

lemma tsum_dvd_indicator (d : Eisenstein) (hd : d ≠ 0) (f : Eisenstein → ℂ) :
    (∑' m : Eisenstein, (if d ∣ m then (1:ℂ) else 0) * f m) =
      ∑' n : Eisenstein, f (d*n) := by
  have he := (mul_right_injective₀ hd).tsum_eq
    (f := fun m => (if d ∣ m then (1:ℂ) else 0) * f m) (by
      intro m hm
      by_cases h : d ∣ m
      · obtain ⟨n,hn⟩ := h; exact ⟨n,hn.symm⟩
      · simp [h,Function.mem_support] at hm)
  simpa only [dvd_mul_right,ite_true,one_mul] using he.symm

lemma cubic_dvd_correlation_theta {a b d : Eisenstein} (ha : primary a) (hb : primary b)
    (hd : d ≠ 0) (t : ℝ) :
    (∑' m : Eisenstein, ((if d ∣ m then (1:ℂ) else 0) *
      (cubicSymbol a m * star (cubicSymbol b m))) *
        Complex.exp (-(Real.pi:ℂ)*t*(norm m:ℂ))) =
    (cubicSymbol a d * star (cubicSymbol b d)) *
      ∑' n : Eisenstein, (cubicSymbol a n * star (cubicSymbol b n)) *
        Complex.exp (-(Real.pi:ℂ)*(t*norm d)*(norm n:ℂ)) := by
  simp_rw [mul_assoc (if _ then _ else _)]
  rw [tsum_dvd_indicator d hd]
  simp_rw [cubicSymbol_mul_upper ha,cubicSymbol_mul_upper hb,star_mul,norm_mul_eq,
    Complex.ofReal_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [show -(Real.pi:ℂ)*t*((norm d:ℂ)*norm n) =
    -(Real.pi:ℂ)*((t:ℂ)*norm d)*norm n by ring]
  ring

 

theorem cubic_common_correlation_poisson {k a b : Eisenstein}
    (hk : primary k) (hks : Squarefree k) (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) (hab : IsCoprime a b)
    (t : ℝ) (ht : 0 < t) :
    (∑' m : Eisenstein, ((if IsCoprime k m then (1:ℂ) else 0) *
      (cubicSymbol a m * star (cubicSymbol b m))) *
        Complex.exp (-(Real.pi:ℂ)*t*(norm m:ℂ))) =
      ∑ S ∈ (primaryPrimeFactors k).powerset,
        let d := ∏ p ∈ S,p
        ((idealMoebius d : ℂ) * (cubicSymbol a d * star (cubicSymbol b d))) *
          (2 * (heckeGauss a (primary_ne_zero ha) (compositeCubicChar a ha) *
            star (heckeGauss b (primary_ne_zero hb) (compositeCubicChar b hb))) /
              ((Real.sqrt 3 : ℂ) * (t*norm d) * norm (a*b))) *
          ∑' h : Eisenstein,
            Complex.exp (-(4*(Real.pi:ℂ))/(3*(t*norm d)*norm (a*b))*(norm h:ℂ)) *
              (star (cubicSymbol a h) * cubicSymbol b h) := by
  have hd (S : Finset Eisenstein) (hS : S ∈ (primaryPrimeFactors k).powerset) :
      (∏ p ∈ S,p) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (primaryPrimeFactor_spec hk ((Finset.mem_powerset.mp hS) hp)).1.2.ne_zero
  have hsum (S : Finset Eisenstein) (hS : S ∈ (primaryPrimeFactors k).powerset) :
      Summable (fun m : Eisenstein => ((idealMoebius (∏ p ∈ S,p) : ℂ) *
        (if (∏ p ∈ S,p) ∣ m then (1:ℂ) else 0)) *
        (cubicSymbol a m * star (cubicSymbol b m)) *
          Complex.exp (-(Real.pi:ℂ)*t*(norm m:ℂ))) := by
    apply bounded_gaussian_summable _ ‖(idealMoebius (∏ p ∈ S,p) : ℂ)‖ _ t ht
    intro m
    rw [norm_mul,norm_mul]
    have h := mul_le_mul_of_nonneg_left (dvdIndicator_norm_le (∏ p ∈ S,p) m)
      (_root_.norm_nonneg (idealMoebius (∏ p ∈ S,p) : ℂ))
    exact (mul_le_mul h (cubicCorrelation_norm_le ha hb m) (_root_.norm_nonneg _)
      (by positivity)).trans_eq (by ring)
  simp_rw [coprime_indicator_moebius hk hks,Finset.sum_mul]
  rw [Summable.tsum_finsetSum hsum]
  apply Finset.sum_congr rfl
  intro S hS
  simp_rw [mul_assoc (idealMoebius _ : ℂ)]
  rw [tsum_mul_left,cubic_dvd_correlation_theta ha hb (hd S hS),
    ← Complex.ofReal_mul t (norm (∏ p ∈ S,p)),
    cubic_correlation_poisson ha hb hsa hsb hab (t*norm (∏ p ∈ S,p))
      (mul_pos ht (norm_pos_of_ne_zero (hd S hS)))]
  ring

end CubicFirstMoment
end

end OAI
