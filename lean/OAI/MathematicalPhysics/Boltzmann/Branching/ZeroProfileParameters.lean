import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralTime
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBranchingBlocks

namespace OAI

section

/-! # A polynomial zero-seed supersolution uniform in the smallest jet scale -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.ZeroProfile

def profile (D : ℝ) (m : ℕ) (t : ℝ) : ℝ := D*t^(m+1)

def source (M C B δ : ℝ) (m : ℕ) (t y : ℝ) : ℝ := M/(t+δ)*y+C*y^2+B*t^m

theorem source_le_derivative {M C B D δ t : ℝ} {m : ℕ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : B ≤ D) (hD : 0 ≤ D) (hδ : 0 < δ)
    (ht : 0 < t) (ht₁ : t ≤ 1) (hsmall : C*D*t ≤ 1)
    (hm : M+2 ≤ (m+1 : ℕ)) :
    source M C B δ m t (profile D m t) ≤ D*(m+1 : ℕ)*t^m := by
  have hlinear : M/(t+δ)*(D*t^(m+1)) ≤ M*D*t^m := by
    have hr : t/(t+δ) ≤ 1 := (div_le_one (by positivity : 0 < t+δ)).mpr (by linarith)
    calc
      _ = (M*D*t^m)*(t/(t+δ)) := by rw [pow_succ]; ring
      _ ≤ (M*D*t^m)*1 := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := mul_one _
  have hpow : t^(m+2) ≤ t := by
    rw [show m+2 = (m+1)+1 by omega,pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ht.le ht₁) ht.le).trans_eq (one_mul t)
  have hq : C*D*t^(m+2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hD)).trans hsmall
  have hquad : C*(D*t^(m+1))^2 ≤ D*t^m := by
    calc
      _ = (D*t^m)*(C*D*t^(m+2)) := by simp only [pow_succ]; ring
      _ ≤ (D*t^m)*1 := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := mul_one _
  have hforcing : B*t^m ≤ D*t^m := mul_le_mul_of_nonneg_right hB (pow_nonneg ht.le _)
  have hcoef := mul_le_mul_of_nonneg_right hm (show 0 ≤ D*t^m by positivity)
  unfold source profile
  nlinarith only [hlinear,hquad,hforcing,hcoef]

theorem profile_hasDerivAt (D : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (profile D m) (D*(m+1 : ℕ)*t^m) t := by
  convert ((hasDerivAt_id t).pow (m+1)).const_mul D using 1
  · rfl
  · simp only [Nat.add_sub_cancel, mul_one, id_eq]
    ring

end BoltzmannNonuniqueness.ZeroProfile

end

end

section

/-! # Damped integral supersolution for the zero hot seed -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.ZeroProfile

theorem integral_supersolution {M C B D δ T L t : ℝ} {m : ℕ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : B ≤ D) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hT₁ : T ≤ 1) (hsmall : C*D*T ≤ 1)
    (hm : M+2 ≤ (m+1 : ℕ)) (ht : t ∈ Icc 0 T) :
    (∫ r in 0..t, Real.exp (-L*(t-r)) *
      (source M C B δ m r (profile D m r)+L*profile D m r)) ≤ profile D m t := by
  by_cases ht0 : t=0
  · simp [ht0,profile]
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have huc : ContDiff ℝ 1 (profile D m) := by unfold profile; fun_prop
  have hden : ContinuousOn (fun r => M/(r+δ)) (Icc 0 t) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const)
      (fun r hr => ne_of_gt (by linarith [hr.1]))
  have hgc : ContinuousOn (fun r => source M C B δ m r (profile D m r)) (Icc 0 t) :=
    ((hden.mul huc.continuous.continuousOn).add
      ((huc.continuous.continuousOn.pow 2).const_mul C)).add
        ((continuousOn_id.pow m).const_mul B)
  have h := DampedSupersolution.integral_bound (L := L) htp
    (fun _ _ _ => huc.contDiffOn.absolutelyContinuousOnInterval)
    (show Tendsto (profile D m) (𝓝[>] 0) (𝓝 0) from by
      simpa [profile] using huc.continuous.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
    (huc.continuous.intervalIntegrable 0 t) (hgc.intervalIntegrable_of_Icc htp.le) (by
      filter_upwards [] with r hr
      have hd := profile_hasDerivAt D m r
      refine ⟨?_,?_⟩
      · simpa only [hd.deriv] using hd
      · rw [hd.deriv]
        exact source_le_derivative hM hC hB hD hδ hr.1 (hr.2.trans (ht.2.trans hT₁))
          ((mul_le_mul_of_nonneg_left (hr.2.trans ht.2) (mul_nonneg hC hD)).trans hsmall) hm)
  simpa only [mul_zero,zero_add] using h

end BoltzmannNonuniqueness.ZeroProfile

end

end

section

/-! # One-sided Lipschitz estimate for the scalar hot majorant -/

noncomputable section

namespace BoltzmannNonuniqueness.ZeroProfile

theorem source_difference {M C B δ L R t z u : ℝ} {m : ℕ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : 0 < δ)
    (ht : 0 ≤ t) (hz : 0 ≤ z) (hu : 0 ≤ u) (hzR : z ≤ R) (huR : u ≤ R) :
    (source M C B δ m t z+L*z)-(source M C B δ m t u+L*u) ≤
      (M/δ+2*C*R+L)*max 0 (z-u) := by
  have hd : 0 ≤ M/(t+δ) := div_nonneg hM (by linarith)
  have hdle : M/(t+δ) ≤ M/δ :=
    div_le_div_of_nonneg_left hM hδ (by linarith)
  have hc : 0 ≤ M/(t+δ)+C*(z+u)+L := by positivity
  have hcle : M/(t+δ)+C*(z+u)+L ≤ M/δ+2*C*R+L := by
    nlinarith [mul_nonneg hC (show 0 ≤ R-z by linarith),
      mul_nonneg hC (show 0 ≤ R-u by linarith)]
  have he : (source M C B δ m t z+L*z)-(source M C B δ m t u+L*u) =
      (M/(t+δ)+C*(z+u)+L)*(z-u) := by unfold source; ring
  rw [he]
  by_cases hzu : 0 ≤ z-u
  · rw [max_eq_right hzu]
    exact mul_le_mul_of_nonneg_right hcle hzu
  · rw [max_eq_left (le_of_not_ge hzu),mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_ge hzu)

end BoltzmannNonuniqueness.ZeroProfile

end

end

section

/-! # Uniform polynomial bound for a zero-seed scalar integral inequality -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.ZeroProfile

theorem le_profile {M C B D δ T L R : ℝ} {m : ℕ} {z : ℝ → ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : B ≤ D) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hT : 0 ≤ T) (hT₁ : T ≤ 1) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hsmall : C*D*T ≤ 1) (hm : M+2 ≤ (m+1 : ℕ))
    (hzc : ContinuousOn z (Icc 0 T)) (hzb : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ R)
    (hz : ∀ t ∈ Icc 0 T, z t ≤ ∫ r in 0..t,
      Real.exp (-L*(t-r))*(source M C B δ m r (z r)+L*z r)) :
    ∀ t ∈ Icc 0 T, z t ≤ profile D m t := by
  have huc : ContinuousOn (profile D m) (Icc 0 T) := by unfold profile; fun_prop
  have hden : ContinuousOn (fun r => M/(r+δ)) (Icc 0 T) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const)
      (fun r hr => ne_of_gt (by linarith [hr.1]))
  have hgc (y : ℝ → ℝ) (hy : ContinuousOn y (Icc 0 T)) :
      ContinuousOn (fun r => source M C B δ m r (y r)+L*y r) (Icc 0 T) := by
    exact (((hden.mul hy).add ((hy.pow 2).const_mul C)).add
      ((continuousOn_id.pow m).const_mul B)).add (hy.const_mul L)
  apply PositiveScalarComparison.le_supersolution (a := 0)
    (G := fun r y => source M C B δ m r y+L*y) hT hL
    (show 0 ≤ M/δ+2*C*(R+D)+L by positivity) hzc huc
    ((hgc z hzc).intervalIntegrable_of_Icc hT)
    ((hgc (profile D m) huc).intervalIntegrable_of_Icc hT)
  · intro t ht
    simpa only [mul_zero,zero_add] using hz t ht
  · intro t ht
    simpa only [mul_zero,zero_add] using integral_supersolution hM hC hB hD hδ hT₁ hsmall hm ht
  · intro t ht
    have hp : 0 ≤ profile D m t := mul_nonneg hD (pow_nonneg ht.1 _)
    have hpD : profile D m t ≤ D := by
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 (ht.2.trans hT₁)) hD).trans_eq (mul_one D)
    exact source_difference hM hC hL hδ ht.1 (hzb t ht).1 hp
      ((hzb t ht).2.trans (le_add_of_nonneg_right hD))
      (hpD.trans (le_add_of_nonneg_left hR))

theorem profile_le_square {D T t : ℝ} {m : ℕ} (hD : 0 ≤ D)
    (hT₁ : T ≤ 1) (hDT : D*T ≤ 1) (hm : 2 ≤ m) (ht : t ∈ Icc 0 T) :
    profile D m t ≤ t^2 := by
  have ht₁ : t ≤ 1 := ht.2.trans hT₁
  have hp : t^(m-2) ≤ 1 := pow_le_one₀ ht.1 ht₁
  have hDt : D*t ≤ 1 := (mul_le_mul_of_nonneg_left ht.2 hD).trans hDT
  have hfac : (D*t)*t^(m-2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hD ht.1)).trans (by simpa using hDt)
  calc
    profile D m t = ((D*t)*t^(m-2))*t^2 := by
      unfold profile
      rw [show m+1 = (m-2)+2+1 by omega,pow_succ,pow_add]
      ring
    _ ≤ 1*t^2 := mul_le_mul_of_nonneg_right hfac (sq_nonneg t)
    _ = t^2 := one_mul _

end BoltzmannNonuniqueness.ZeroProfile

end

end

section

/-! # A positive uniform time for the polynomial zero-seed comparison -/

noncomputable section

namespace BoltzmannNonuniqueness.ZeroProfile

private theorem small_product {a t : ℝ} (ha : 0 ≤ a) (ht : t ≤ (a+1)⁻¹) : a*t ≤ 1 := by
  calc
    a*t ≤ a*(a+1)⁻¹ := mul_le_mul_of_nonneg_left ht ha
    _ = a/(a+1) := (div_eq_mul_inv _ _).symm
    _ ≤ 1 := (div_le_one (by linarith : 0 < a+1)).mpr (by linarith)

theorem parameters_exist {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (E : ℕ → ℝ) (hE : ∀ m, 0 ≤ E m) :
    ∃ (m : ℕ) (D T : ℝ), 2 ≤ m ∧ 0 < D ∧ 0 < T ∧ T ≤ 1/32 ∧
      M+2 ≤ (m+1 : ℕ) ∧ (M+C)*E m ≤ D ∧ C*D*T ≤ 1 ∧
      E m*T^(m+1) ≤ 1 ∧ D*T ≤ 1 := by
  obtain ⟨m,hm⟩ := exists_nat_gt (M+2)
  have hEm := hE m
  let D := (M+C)*E m+1
  have hD : 0 < D := by dsimp [D]; positivity
  let T := min (1/32 : ℝ) (min (C*D+1)⁻¹ (min (E m+1)⁻¹ (D+1)⁻¹))
  have hT : 0 < T := by dsimp [T]; positivity
  have hT₃₂ : T ≤ 1/32 := min_le_left _ _
  have hTc : T ≤ (C*D+1)⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hTe : T ≤ (E m+1)⁻¹ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hTd : T ≤ (D+1)⁻¹ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hm₂ : 2 ≤ m := by
    have h : (2:ℝ) < m := by linarith
    have hn : 2 < m := by exact_mod_cast h
    omega
  refine ⟨m,D,T,hm₂,hD,hT,hT₃₂,?_,?_,small_product (mul_nonneg hC hD.le) hTc,?_,small_product hD.le hTd⟩
  · push_cast
    linarith
  · dsimp [D]
    linarith
  · have hp : T^(m+1) ≤ T := by
      rw [pow_succ]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (pow_le_one₀ hT.le (show T ≤ 1 by linarith)) hT.le
    exact (mul_le_mul_of_nonneg_left hp (hE m)).trans (small_product (hE m) hTe)

end BoltzmannNonuniqueness.ZeroProfile

end

end

end OAI
