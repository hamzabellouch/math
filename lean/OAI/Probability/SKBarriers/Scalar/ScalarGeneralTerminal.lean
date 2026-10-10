import Mathlib
import OAI.Probability.SKBarriers.Scalar.DyadicScalar
import OAI.Probability.SKBarriers.Scalar.UniformDerivativeLimit

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarStep_mass_lipschitz_general {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {v B : ℝ} (hvB : |v| ≤ B)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) (x : ℝ) :
    |scalarStep b v f x-scalarStep a v f x| ≤
      gaussianMassBound ((K:ℝ)*B)*(K:ℝ)^2*v^2*|b-a| := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hB : (K:ℝ)*|v| ≤ (K:ℝ)*B := mul_le_mul_of_nonneg_left hvB K.coe_nonneg
  have hbnd (y : ℝ) : |f (x+v*y)-f (x+v*0)| ≤ ((K:ℝ)*|v|)*|y| := by
    have H := hLip.norm_sub_le (x+v*y) (x+v*0)
    simpa only [Real.norm_eq_abs,mul_zero,add_zero,add_sub_cancel_left,abs_mul,mul_assoc] using H
  have H := gaussianStep_mass_lipschitz (hf.compCLM L) x
    (mul_nonneg K.coe_nonneg (abs_nonneg v)) hB hbnd ha hb
  change |scalarStep b v f x-scalarStep a v f x| ≤
    gaussianMassBound ((K:ℝ)*B)*((K:ℝ)*|v|)^2*|b-a| at H
  simpa only [mul_pow,sq_abs,mul_assoc] using H

def scalarTimeMassConstantK (β : ℝ) (K : ℝ≥0) : ℝ :=
  gaussianMassBound ((K:ℝ)*|β|)*(K:ℝ)^2*β^2

theorem scalarTimeMassConstantK_nonneg (β : ℝ) (K : ℝ≥0) :
    0 ≤ scalarTimeMassConstantK β K := by
  exact mul_nonneg (mul_nonneg (gaussianMassBound_pos _).le (sq_nonneg _)) (sq_nonneg _)

theorem scalarTimeStep_mass_lipschitz_general {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {t : ℝ≥0} (ht : t ≤ 1)
    {m m' : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (hm' : m' ∈ Icc (0:ℝ) 1) (x : ℝ) :
    |scalarTimeStep β m' t f x-scalarTimeStep β m t f x| ≤
      scalarTimeMassConstantK β K * (t:ℝ) * |m'-m| := by
  have hst : Real.sqrt (t:ℝ) ≤ 1 := (Real.sqrt_le_one).mpr ht
  have hv : |β*Real.sqrt (t:ℝ)| ≤ |β| := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (abs_nonneg _) hst
  have H := scalarStep_mass_lipschitz_general hf hLip hv hm hm' x
  simpa only [scalarTimeStep,scalarTimeMassConstantK,mul_pow,Real.sq_sqrt t.coe_nonneg,mul_assoc] using H

theorem dyadicScalar_successive_bound_general {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α (n+1) s t f x-dyadicScalar β α n s t f x| ≤
      scalarTimeMassConstantK β K*(t:ℝ)/(2:ℝ)^(n+1)*(α (s+t)-α s) := by
  induction n generalizing f s t x with
  | zero =>
    simp only [dyadicScalar_succ,dyadicScalar_zero]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    have htc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    have H (z) := scalarTimeStep_mass_lipschitz_general hf hLip β hhalf (hα s)
      (hα (s+(t:ℝ)/2)) z
    have H' := scalarStep_uniform_nonexpansive
      (scalarTimeStep_regular hf β (α (s+(t:ℝ)/2)) (t/2))
      (scalarTimeStep_regular hf β (α s) (t/2)) (hα s).1 H
      (β*Real.sqrt ((t/2:ℝ≥0):ℝ)) x
    change |scalarTimeStep β (α s) (t/2) _ x-scalarTimeStep β (α s) (t/2) _ x| ≤ _ at H'
    rw [scalarTimeStep_semigroup hf,show t/2+t/2=t by ring] at H'
    apply H'.trans
    rw [htc,abs_of_nonneg (sub_nonneg.mpr (hmono (by linarith [t.coe_nonneg])))]
    change scalarTimeMassConstantK β K*((t:ℝ)/2)*(α (s+(t:ℝ)/2)-α s) ≤ _
    have hM := hmono (show s+(t:ℝ)/2 ≤ s+(t:ℝ) by linarith [t.coe_nonneg])
    have hC := scalarTimeMassConstantK_nonneg β K
    calc
      _  ≤  scalarTimeMassConstantK β K*((t:ℝ)/2)*(α (s+t)-α s) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hM _) (by positivity)
      _ = _ := by ring
  | succ n ih =>
    rw [dyadicScalar_succ β α (n+1) s t f,dyadicScalar_succ β α n s t f]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    have htc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    let f₁ := dyadicScalar β α (n+1) (s+(t:ℝ)/2) (t/2) f
    let f₀ := dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f
    have hf₁ : BoundedDerivs f₁ := dyadicScalar_regular hf β α _ _ _
    have hf₀ : BoundedDerivs f₀ := dyadicScalar_regular hf β α _ _ _
    have hl₀ : LipschitzWith K f₀ := dyadicScalar_lipschitz hf hLip β hα _ _ _
    have H₁ := dyadicScalar_uniform_nonexpansive hf₁ hf₀ β hα (n+1) s (t/2)
      (fun z => ih hf hLip (s+(t:ℝ)/2) (t/2) hhalf z) x
    have H₂ := ih hf₀ hl₀ s (t/2) hhalf x
    calc
      _  ≤  |dyadicScalar β α (n+1) s (t/2) f₁ x-dyadicScalar β α (n+1) s (t/2) f₀ x|+
          |dyadicScalar β α (n+1) s (t/2) f₀ x-dyadicScalar β α n s (t/2) f₀ x| := abs_sub_le _ _ _
      _  ≤  _+_ := add_le_add H₁ H₂
      _ = _ := by rw [htc,show s+(t:ℝ)/2+(t:ℝ)/2=s+t by ring,pow_succ (2:ℝ) (n+1)]; ring

theorem dyadicScalar_successive_geometric_general {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α (n+1) s t f x-dyadicScalar β α n s t f x| ≤
      scalarTimeMassConstantK β K*(1/2:ℝ)^n := by
  have H := dyadicScalar_successive_bound_general hf hLip β hα hmono n s t ht x
  have hC := scalarTimeMassConstantK_nonneg β K
  have ht' : (t:ℝ) ≤ 1 := ht
  have ho : α (s+t)-α s ≤ 1 := by linarith [(hα (s+t)).2,(hα s).1]
  apply H.trans
  calc
    _ ≤ scalarTimeMassConstantK β K*(t:ℝ)/(2:ℝ)^(n+1) :=
      mul_le_of_le_one_right (by positivity) ho
    _ ≤ scalarTimeMassConstantK β K/(2:ℝ)^(n+1) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_right hC ht') (by positivity)
    _ = scalarTimeMassConstantK β K*(1/2:ℝ)^(n+1) := by rw [div_pow,one_pow]; ring
    _ ≤ scalarTimeMassConstantK β K*(1/2:ℝ)^n := by
      rw [pow_succ]
      nlinarith [mul_nonneg hC (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n)]

def scalarCDFOperator (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => dyadicScalar β α n s t f x)

theorem dyadicScalar_general_uniform {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => dyadicScalar β α n s t f) (scalarCDFOperator β α s t f) atTop :=
  (geometric_uniform_limit (fun n => dyadicScalar β α n s t f)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
    (fun n x => dyadicScalar_successive_geometric_general hf hLip β hα hmono n s t ht x)).1

theorem dyadicScalar_general_error {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (n : ℕ) (x : ℝ) :
    |dyadicScalar β α n s t f x-scalarCDFOperator β α s t f x| ≤
      2*scalarTimeMassConstantK β K*(1/2:ℝ)^n := by
  have H := (geometric_uniform_limit (fun n => dyadicScalar β α n s t f)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
    (fun n x => dyadicScalar_successive_geometric_general hf hLip β hα hmono n s t ht x)).2 n x
  dsimp [scalarCDFOperator]
  convert H using 1; ring

end SK.Analytic

end
end

end OAI
