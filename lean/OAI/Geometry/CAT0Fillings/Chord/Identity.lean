import Mathlib
import OAI.Geometry.CAT0Fillings.Chord.NonnegativeMeasure
import OAI.Geometry.CAT0Fillings.Chord.Fubini
import OAI.Geometry.CAT0Fillings.Sobolev.CriticalNorm
import OAI.Geometry.CAT0Fillings.Chord.Bubble

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
lemma quotient_bound_real {n W M E r : ℝ} (hn : 0 < n) (hW : 0 < W) (hM : 0 ≤ M)
    (h : n*W*M^r ≤ E*W^r) : (M/W)^r ≤ E/(n*W) := by
  rw [Real.div_rpow hM hW.le]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hW _) (mul_pos hn hW)).mpr
  simpa only [mul_comm (M^r) (n*W)] using h
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
lemma critical_quotient_bound (I : H →L[ℝ] Lp ℝ 2 μ) (E : H → ℝ) {p n : ℝ}
    (hp : 0 < p) (hn : 0 < n) (v P : H) (hW : 0 < criticalMass I p v)
    (hE : E v = n*criticalMass I p v)
    (hmin : E v*(criticalNorm I p P)^2 ≤ E P*(criticalNorm I p v)^2) :
    (criticalMass I p P/criticalMass I p v)^(2/p) ≤ E P/(n*criticalMass I p v) := by
  rw [criticalNorm_sq I hp,criticalNorm_sq I hp,hE] at hmin
  exact quotient_bound_real hn hW (criticalMass_nonneg I p P) hmin
lemma critical_ratio_product (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (v P : H)
    (hW : 0 < criticalMass I p v) (w : α → ℝ)
    (hw : 0 ≤ᵐ[μ] w) (hP : (I P : α → ℝ) =ᵐ[μ] fun x => I v x*w x) :
    criticalMass I p P/criticalMass I p v =
      ∫ x, (w x)^p ∂ChordMeasure.probability μ (fun x => |I v x|^p) := by
  rw [ChordMeasure.integral_probability μ _
    ((Lp.aestronglyMeasurable (I v)).aemeasurable.abs.pow_const p).aestronglyMeasurable
    (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _) hW]
  congr 1
  apply integral_congr_ae
  filter_upwards [hw,hP] with x hx hPx
  rw [hPx,abs_mul,abs_of_nonneg hx,Real.mul_rpow (abs_nonneg _) hx]
lemma critical_scalar_start (I : H →L[ℝ] Lp ℝ 2 μ) (E : H → ℝ) {p n β : ℝ}
    (hp : 0 < p) (hn : 0 < n) (v P : H) (hW : 0 < criticalMass I p v)
    (hE : E v = n*criticalMass I p v)
    (hmin : E v*(criticalNorm I p P)^2 ≤ E P*(criticalNorm I p v)^2)
    (w F : α → ℝ) (hw : 0 ≤ᵐ[μ] w)
    (hP : (I P : α → ℝ) =ᵐ[μ] fun x => I v x*w x)
    (hEP : E P ≤ n*(∫ x, |I v x|^p*(w x)^2 ∂μ)+β*n*(∫ x, |I v x|^p*F x ∂μ)) :
    (∫ x, (w x)^p ∂ChordMeasure.probability μ (fun x => |I v x|^p))^(2/p) ≤
      (∫ x, (w x)^2 ∂ChordMeasure.probability μ (fun x => |I v x|^p))+
        β*(∫ x, F x ∂ChordMeasure.probability μ (fun x => |I v x|^p)) := by
  rw [←critical_ratio_product I p v P hW w hw hP]
  apply (critical_quotient_bound I E hp hn v P hW hE hmin).trans
  rw [ChordMeasure.integral_probability μ _ ((Lp.aestronglyMeasurable (I v)).aemeasurable.abs.pow_const p).aestronglyMeasurable
        (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _) hW,
      ChordMeasure.integral_probability μ _ ((Lp.aestronglyMeasurable (I v)).aemeasurable.abs.pow_const p).aestronglyMeasurable
        (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _) hW]
  change E P/(n*criticalMass I p v) ≤ _
  apply (div_le_iff₀ (mul_pos hn hW)).mpr
  convert hEP using 1; try rfl
  have hW0 : (∫ x, |I v x|^p ∂μ) ≠ 0 := hW.ne'
  dsimp only [ChordMeasure.total,criticalMass]
  field_simp
end CAT0Fillings.AnalyticMinimizer
end

section
open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.Conformal
lemma bubble_derivative_square {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) :
    (chordBubbleD q a t)^2 = 4*q^2*a^2*t^2*(1+a*t^2)^(-2*q-2) := by
  have hb : 0 ≤ 1+a*t^2 := by positivity
  unfold chordBubbleD
  rw [mul_pow,←Real.rpow_mul_natCast hb,Nat.cast_ofNat]
  rw [show (-q-1)*2 = -2*q-2 by ring]
  ring
lemma profile_substitution {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (hnq : (n:ℝ) = 2*q+2) (t : ℝ) :
    averageProfile n (chordBubbleD q a) t =
      2*q^2*a^2*t^2*(∫ u in (0:ℝ)..1, u^(q+1)*(1+a*t^2*u)^(-2*q-2)) := by
  let g : ℝ → ℝ := fun u => u^(q+1)*(1+a*t^2*u)^(-2*q-2)
  have hg : ContinuousOn g (Icc 0 1) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun u hu => Or.inr (by linarith))
    · have hb : Continuous (fun u : ℝ => 1+a*t^2*u) := by fun_prop
      exact hb.continuousOn.rpow_const (fun u hu => Or.inl (ne_of_gt (by
        have hu0 : 0 ≤ u := hu.1
        positivity)))
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0:ℝ)) (b := 1) (f := fun τ : ℝ => τ^2) (f' := fun τ => 2*τ) (g := g)
    (fun τ _ => by
      convert (hasDerivAt_id τ).pow 2 using 1 <;> try rfl
      norm_num)
    (by fun_prop) (hg.mono (by
      rintro u ⟨τ,hτ,rfl⟩
      simp only [uIcc_of_le zero_le_one,mem_Icc] at hτ ⊢
      exact ⟨sq_nonneg _,pow_le_one₀ hτ.1 hτ.2⟩))
  norm_num only [zero_pow,one_pow] at hsub
  unfold averageProfile
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one,
    ←hsub,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro τ hτ
  have hτ0 : 0 ≤ τ := (show τ ∈ Icc (0:ℝ) 1 by simpa only [uIcc_of_le zero_le_one] using hτ).1
  have hpow : (τ^2)^(q+1) = τ^n := by
    rw [←Real.rpow_natCast_mul hτ0,Nat.cast_ofNat,show 2*(q+1) = (n:ℝ) by linarith,Real.rpow_natCast]
  have hnat : τ^(n-1)*τ^2 = τ^n*τ := by
    rw [←pow_add,←pow_succ]
    congr 1
    omega
  dsimp only [Function.comp_apply,g]
  rw [bubble_derivative_square ha,hpow]
  have hbase : 1+a*(τ*t)^2 = 1+a*t^2*τ^2 := by ring
  rw [hbase]
  calc
    _ = 4*q^2*a^2*t^2*(τ^(n-1)*τ^2)*(1+a*t^2*τ^2)^(-2*q-2) := by ring
    _ = _ := by rw [hnat]; ring

lemma profile_scalar_identity {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (hnq : (n:ℝ) = 2*q+2) (t : ℝ) :
    (chordBubble q a t)^2 + (1/(2*q))*t^2*averageProfile n (chordBubbleD q a) t =
      q*(∫ u in (0:ℝ)..1, u^(q-1)*(1+a*t^2*u)^(-2*q-2)) := by
  rw [profile_substitution hn hq ha hnq t]
  have hw : (chordBubble q a t)^2 = (1+a*t^2)^(-2*q) := by
    unfold chordBubble
    rw [←Real.rpow_mul_natCast (show 0 ≤ 1+a*t^2 by positivity),Nat.cast_ofNat,show -q*2 = -2*q by ring]
  rw [hw]
  have h := ChordIdentity.scalar_identity hq (show 0 ≤ a*t^2 by positivity)
  convert h using 1
  field_simp
end CAT0Fillings.Conformal
end

end OAI
