import OAI.Geometry.TranslativeCovering.PatternGeometry

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace PatternRounding
abbrev Space (n : ℕ) := SphericalLaw.Space n
open Set Metric MeasureTheory SphericalLaw LocalizationRounding PatternGeometry
open LatticeAveraging LocalizationGood
open scoped ENNReal BigOperators Classical

lemma finite_sum_le_field {n : ℕ} {I : Type u_1} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (f : Space n → ℝ≥0∞) (y : Space n) (S : Finset (I×Λ)) :
    ∑ q ∈ S,f (y-p q.1-q.2.val) ≤ field Λ p f y := by
  calc
    _ ≤ ∑' q : I×Λ,f (y-p q.1-q.2.val) := ENNReal.sum_le_tsum S
    _ = _ := by rw [ENNReal.tsum_prod',tsum_fintype]; rfl

lemma finite_weight {n : ℕ} {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (a β C : ℝ) (y : Space n) (S : Finset (I×Λ))
    (hS : ∀ q ∈ S,‖y-p q.1-q.2.val‖ ≤ β)
    (hW : field Λ p (weightedFn a β) y ≤ ENNReal.ofReal C) (hC : 0 ≤ C) :
    ∑ q ∈ S,weight n a ‖y-p q.1-q.2.val‖ ≤ C := by
  have hn (q : I×Λ) : 0 ≤ weight n a ‖y-p q.1-q.2.val‖ := by
    dsimp [weight]; positivity
  have hs := finite_sum_le_field Λ p (weightedFn a β) y S
  have he : (∑ q ∈ S,weightedFn a β (y-p q.1-q.2.val)) =
      ENNReal.ofReal (∑ q ∈ S,weight n a ‖y-p q.1-q.2.val‖) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => hn q)]
    apply Finset.sum_congr rfl
    intro q hq
    have hm : y-p q.1-q.2.val ∈ closedBall (0 : Space n) β := mem_closedBall_zero_iff.mpr (hS q hq)
    simp only [weightedFn,Set.indicator_of_mem hm,weight]
  rw [he] at hs
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (hs.trans hW)

lemma good_transfer {n : ℕ} {I : Type u_3} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (S : Finset (I×Λ)) (z y : Space n)
    {a D r L β h C : ℝ} (ha : 0 < a) (hh : 0 < h) (hC : 0 ≤ C)
    (hbuf : L+Real.sqrt n*h/2 ≤ β) (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h/2) ≤ 1)
    (hy : y ∈ closedBall (0 : Space n) D) (hg : y+z ∈ good Λ p a r β (ENNReal.ofReal C)) :
    y ∈ roundedGood (fun q : S => rounded h (p q.val.1+q.val.2.val-z))
      a D (r-Real.sqrt n*h/2) L (2*C) := by
  let c : S → Space n := fun q => p q.val.1+q.val.2.val-z
  let c' : S → Space n := fun q => rounded h (c q)
  have he (q : S) : y-c q = y+z-p q.val.1-q.val.2.val := by dsimp [c]; abel
  have hi (q : S) : r ≤ ‖y-c q‖ := by rw [he]; exact (inner_zero Λ p r (y+z)).mp hg.1 q.val.1 q.val.2
  have hr (q : S) : r-Real.sqrt n*h/2 ≤ ‖y-c' q‖ := by
    have herror := residual_error hh (c q) y
    have hh' := neg_le_of_abs_le herror
    change -(Real.sqrt n*h/2) ≤ ‖y-c' q‖-‖y-c q‖ at hh'
    linarith only [hi q,hh']
  let Q := relevant c' L y
  let T : Finset (I×Λ) := Q.image Subtype.val
  have hT (q : S) (hq : q ∈ Q) : ‖y-c q‖ ≤ β := by
    have hround := (Finset.mem_filter.mp hq).2
    have herror := residual_error hh (c q) y
    have hh' := neg_le_of_abs_le herror
    change -(Real.sqrt n*h/2) ≤ ‖y-c' q‖-‖y-c q‖ at hh'
    linarith only [hround,hh',hbuf]
  have hs : ∑ q ∈ Q,weight n a ‖y-c q‖ ≤ C := by
    have ht : ∀ q ∈ T,‖y+z-p q.1-q.2.val‖ ≤ β := by
      intro q hq
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
      rw [← he j]
      exact hT j hj
    have hh := finite_weight Λ p a β C (y+z) T ht hg.2.2 hC
    rw [Finset.sum_image (fun _ _ _ _ he => Subtype.ext he)] at hh
    simpa only [← he] using hh
  have hsw : ∑ q ∈ Q,weight n a ‖y-c' q‖ ≤ 2*C := by
    calc
      _ ≤ ∑ q ∈ Q,2*weight n a ‖y-c q‖ := Finset.sum_le_sum fun q _ =>
        (weight_transfer ha hh (c q) y).trans (by
          have hw : 0 ≤ weight n a ‖y-c q‖ := by dsimp [weight]; positivity
          exact mul_le_mul_of_nonneg_right (by linarith only [hlip]) hw)
      _ = 2*(∑ q ∈ Q,weight n a ‖y-c q‖) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)
  refine ⟨hy,hr,?_,hsw⟩
  have hc : (Q.card:ℝ) ≤ ∑ q ∈ Q,weight n a ‖y-c' q‖ := by
    calc
      _ = ∑ _q ∈ Q,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun q _ => by
        dsimp [weight]
        have : 0 ≤ (n:ℝ)*max (1-‖y-c' q‖^2/a^2) 0 := by positivity
        linarith only [this]
  exact hc.trans hsw

end PatternRounding

end OAI
