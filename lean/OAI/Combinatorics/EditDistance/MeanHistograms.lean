import OAI.Combinatorics.EditDistance.Histograms

namespace OAI

/-!
# Mean histograms as finite cut distances
-/

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

section MeanHistogram
variable {I J X : Type*} [Fintype I] [Fintype J]

noncomputable def meanHistogram (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (f g : J → X) : ℝ :=
  ∑ h : I → Bool, probability w a h * histogramDistance (fun j => key c h (f j)) (fun j => key c h (g j))

lemma meanHistogram_nonneg {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 ≤ a)
    (c : I → X → Bool) (f g : J → X) : 0 ≤ meanHistogram w a c f g :=
  sum_nonneg (fun h _ => mul_nonneg (probability_nonneg hw ha h) (histogramDistance_nonneg _ _))

lemma meanHistogram_upper {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 ≤ a)
    (c : I → X → Bool) (f g : J → X) :
    meanHistogram w a c f g ≤ 2*a*∑ j, distance w c (f j) (g j) := by
  calc
    _ ≤ ∑ h : I → Bool, probability w a h * (2*∑ j, sep (key c h (f j)) (key c h (g j))) :=
      sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (histogramDistance_le _ _) (probability_nonneg hw ha h))
    _ = 2*∑ j : J, ∑ h : I → Bool, probability w a h * sep (key c h (f j)) (key c h (g j)) := by
      simp_rw [mul_left_comm (probability w a _ : ℝ) 2,mul_sum]
      rw [sum_comm]
    _ ≤ 2*∑ j : J, a*distance w c (f j) (g j) := by
      apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact sum_le_sum (fun j _ => separation_bound w a c (f j) (g j))
    _ = _ := by rw [←mul_sum]; ring

lemma mean_cross_collisions (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (f g : J → X) :
    (∑ h : I → Bool, probability w a h *
      (∑ i : J, ∑ j : J, hit (key c h (f i)) (key c h (g j)))) =
      ∑ i : J, ∑ j : J, Real.exp (-a*distance w c (f i) (g j)) := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply Eq.trans ?_ (collision_probability w a c (f i) (g j))
  apply sum_congr rfl
  intro h _
  congr 1
  by_cases he : key c h (f i) = key c h (g j) <;> simp [hit,he]

theorem meanHistogram_lower {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 ≤ a)
    (c : I → X → Bool) (f g : J → X) {R : ℝ} (hR : ∀ i j, R ≤ distance w c (f i) (g j)) :
    2*(Fintype.card J : ℝ)*(1-(Fintype.card J : ℝ)^2*Real.exp (-a*R)) ≤
      meanHistogram w a c f g := by
  have hc : (∑ i : J, ∑ j : J, Real.exp (-a*distance w c (f i) (g j))) ≤
      (Fintype.card J : ℝ)^2*Real.exp (-a*R) := by
    calc
      _ ≤ ∑ _i : J, ∑ _j : J, Real.exp (-a*R) := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j _
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left (hR i j) ha]
      _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring
  have hp : (∑ h : I → Bool, probability w a h *
      (2*(Fintype.card J : ℝ)*(1-∑ i : J, ∑ j : J, hit (key c h (f i)) (key c h (g j))))) ≤
      meanHistogram w a c f g :=
    sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (histogramDistance_lower _ _) (probability_nonneg hw ha h))
  have he : (∑ h : I → Bool, probability w a h *
      (2*(Fintype.card J : ℝ)*(1-∑ i : J, ∑ j : J, hit (key c h (f i)) (key c h (g j))))) =
      2*(Fintype.card J : ℝ)*(1-∑ i : J, ∑ j : J, Real.exp (-a*distance w c (f i) (g j))) := by
    simp_rw [mul_left_comm (probability w a _) (2*(Fintype.card J : ℝ))]
    rw [←mul_sum]
    congr 1
    simp_rw [mul_sub,mul_one]
    rw [sum_sub_distrib,probability_sum,mean_cross_collisions]
  rw [he] at hp
  apply le_trans ?_ hp
  gcongr

noncomputable def rate (s : ℕ) : ℝ := Real.log (2*(s : ℝ)^2)/(s : ℝ)

lemma rate_nonneg {s : ℕ} (hs : 0 < s) : 0 ≤ rate s := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  apply div_nonneg (Real.log_nonneg (by nlinarith)) (by positivity)

lemma rate_exp {s : ℕ} (hs : 0 < s) : Real.exp (-rate s*(s : ℝ)) = 1/(2*(s : ℝ)^2) := by
  have sp : (0 : ℝ) < s := by exact_mod_cast hs
  rw [rate,neg_mul,div_mul_cancel₀ _ sp.ne',Real.exp_neg,Real.exp_log (by positivity)]
  simp only [one_div]

lemma meanHistogram_separated {s : ℕ} (hs : 0 < s) {w : I → ℝ} (hw : ∀ i, 0 ≤ w i)
    (c : I → X → Bool) (f g : Fin s → X)
    (hR : ∀ i j, (s : ℝ) ≤ distance w c (f i) (g j)) :
    (s : ℝ) ≤ meanHistogram w (rate s) c f g := by
  have hh := meanHistogram_lower hw (rate_nonneg hs) c f g hR
  rw [Fintype.card_fin,rate_exp hs] at hh
  have sp : (0 : ℝ) < s := by exact_mod_cast hs
  have he : 2*(s : ℝ)*(1-(s : ℝ)^2*(1/(2*(s : ℝ)^2))) = (s : ℝ) := by
    field_simp
    ring
  simpa only [he] using hh

end MeanHistogram
end EditCutHash

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

lemma histogramDistance_shift {K : Type*} [Fintype K] {s : ℕ}
    (f g : Fin (s+1) → K) (h : ∀ i : Fin s, f i.castSucc = g i.succ) :
    histogramDistance f g ≤ 2 := by
  have hc (z : K) : count f z-count g z = hit (f (Fin.last s)) z-hit (g 0) z := by
    unfold count
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_succ]
    simp_rw [h]
    ring
  unfold histogramDistance
  simp_rw [hc]
  rw [hit_distance]
  have hh := sep_le_one (f (Fin.last s)) (g 0)
  linarith

lemma meanHistogram_shift {I X : Type*} [Fintype I] {s : ℕ} (hs : 0 < s)
    {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 ≤ a)
    (c : I → X → Bool) (f g : Fin s → X)
    (h : ∀ i : Fin (s-1), f ⟨i.val,by omega⟩ = g ⟨i.val+1,by omega⟩) :
    meanHistogram w a c f g ≤ 2 := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have hd (r : I → Bool) : histogramDistance (fun i => key c r (f i)) (fun i => key c r (g i)) ≤ 2 := by
    apply histogramDistance_shift
    intro i
    congr 1
    exact h ⟨i.val,by omega⟩
  calc
    _ ≤ ∑ r : I → Bool, probability w a r * 2 :=
      sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hd r) (probability_nonneg hw ha r))
    _ = 2 := by rw [←sum_mul,probability_sum,one_mul]

@[simp] lemma meanHistogram_self {I J X : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (f : J → X) :
    meanHistogram w a c f f = 0 := by
  simp [meanHistogram,histogramDistance]

end EditCutHash

end OAI
