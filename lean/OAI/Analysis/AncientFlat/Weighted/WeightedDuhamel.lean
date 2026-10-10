import Mathlib

namespace OAI
noncomputable section

namespace WeightedDuhamel

open Set Filter MeasureTheory
open scoped SchwartzMap Topology

namespace SchwartzConvolution
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scaled_weighted_majorant (g : SchwartzMap V E) (a b : ℝ) (ha : 0 < a) (K L : ℕ) :
    ∃ B : V → ℝ, Integrable B ∧ Integrable (fun x => (1+‖x‖)^L * B x) ∧
      (∀ x, 0 ≤ B x) ∧ ∀ c ∈ Icc a b, ∀ x,
      ‖(c⁻¹)^K • g (c⁻¹ • x)‖ ≤ B x := by
  let N := Module.finrank ℝ V + 1 + L
  let M := max b 1
  let C := 2^N * (Finset.Iic (N,0)).sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) g
  have hC : 0 ≤ C := by positivity
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdec (z : V) : (1+‖z‖)^N * ‖g z‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N,0)) le_rfl le_rfl g z
  refine ⟨fun x => ((a⁻¹)^K*(M^N*C))/(1+‖x‖)^N, ?_, ?_, ?_, ?_⟩
  · have hi : Integrable (fun x : V => (1+‖x‖)^(-(N : ℝ))) :=
      integrable_one_add_norm (by dsimp [N]; push_cast; linarith)
    simpa only [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+‖(_ : V)‖),
      Real.rpow_natCast, div_eq_mul_inv] using hi.const_mul ((a⁻¹)^K*(M^N*C))
  · have hi : Integrable (fun x : V => (1+‖x‖)^(-(Module.finrank ℝ V + 1 : ℝ))) :=
      integrable_one_add_norm (by linarith)
    have he (x : V) : (1+‖x‖)^L * (((a⁻¹)^K*(M^N*C))/(1+‖x‖)^N) =
        ((a⁻¹)^K*(M^N*C)) * (1+‖x‖)^(-(Module.finrank ℝ V + 1 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), ← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast]
      dsimp [N]
      rw [pow_add]
      field_simp
      rw [pow_add]
      ring
    simp_rw [he]
    exact hi.const_mul _
  · intro x
    positivity
  · intro c hc x
    have hcpos : 0 < c := ha.trans_le hc.1
    have hcM : c ≤ M := hc.2.trans (le_max_left _ _)
    have hnx : ‖x‖ = c * ‖c⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos),
        ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
    have hs : 1+‖x‖ ≤ M*(1+‖c⁻¹ • x‖) := by
      rw [hnx, mul_add, mul_one]
      exact add_le_add (le_max_right b 1) (mul_le_mul_of_nonneg_right hcM (norm_nonneg _))
    have hg : ‖g (c⁻¹ • x)‖ * (1+‖x‖)^N ≤ M^N*C := by
      calc
        _ ≤ ‖g (c⁻¹ • x)‖ * (M * (1+‖c⁻¹ • x‖))^N := by gcongr
        _ = M^N * ((1+‖c⁻¹ • x‖)^N * ‖g (c⁻¹ • x)‖) := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hdec _) (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = (c⁻¹)^K * (‖g (c⁻¹ • x)‖ * (1+‖x‖)^N) := by ring
      _ ≤ (a⁻¹)^K * (‖g (c⁻¹ • x)‖ * (1+‖x‖)^N) := by
        gcongr
        exact hc.1
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)

end SchwartzConvolution

open Set Filter MeasureTheory
open scoped SchwartzMap Topology
namespace SchwartzTimeScale
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def euler (K : SchwartzMap V E) (N : ℕ) : SchwartzMap V E :=
  (-(N : ℝ)/4) • K - (1/4 : ℝ) •
    (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ E).flip
      (by fun_prop : Function.HasTemperateGrowth (fun y : V => y))
      (SchwartzMap.fderivCLM ℝ V E K))

lemma euler_apply (K : SchwartzMap V E) (N : ℕ) (y : V) :
    euler K N y = (-(N : ℝ)/4) • K y-(1/4 : ℝ) • (fderiv ℝ K y y) := rfl

def atTime (K : SchwartzMap V E) (N : ℕ) (q : ℝ) (y : V) : E :=
  q^(-(N : ℝ)/4) • K (q^(-(1 : ℝ)/4) • y)

lemma hasDerivAt_atTime (K : SchwartzMap V E) (N : ℕ) (q : ℝ) (hq : 0 < q) (y : V) :
    HasDerivAt (fun s => atTime K N s y)
      (atTime (euler K N) (N+4) q y) q := by
  have h1 := Real.hasDerivAt_rpow_const (p := -(N : ℝ)/4) (Or.inl hq.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := -(1 : ℝ)/4) (Or.inl hq.ne')
  have hK := (K.hasFDerivAt (q^(-(1 : ℝ)/4) • y)).comp_hasDerivAt q (h2.smul_const y)
  have hd := h1.smul hK
  convert hd using 1
  · rfl
  · dsimp only [atTime,Function.comp_apply,Pi.smul_apply]
    rw [euler_apply,smul_sub]
    simp only [ContinuousLinearMap.map_smul,smul_smul]
    have he1 : q^(-((N+4 : ℕ) : ℝ)/4) = q^(-(N : ℝ)/4-1) := by
      congr 1
      push_cast
      ring
    have he2 : q^(-(N : ℝ)/4) * (-(1 : ℝ)/4*q^(-(1 : ℝ)/4-1)) =
        -(q^(-(N : ℝ)/4-1)*(1/4))*q^(-(1 : ℝ)/4) := by
      calc
        _ = (-(1 : ℝ)/4)*q^(-(N : ℝ)/4+(-(1 : ℝ)/4-1)) := by rw [Real.rpow_add hq]; ring
        _ = (-(1 : ℝ)/4)*q^((-(N : ℝ)/4-1)+(-(1 : ℝ)/4)) := by congr 2; ring
        _ = _ := by rw [Real.rpow_add hq]; ring
    rw [he1,he2]
    module

lemma atTime_eq_scaled (K : SchwartzMap V E) (N : ℕ) (q : ℝ) (hq : 0 < q) (y : V) :
    atTime K N q y = ((q^(1/4 : ℝ))⁻¹)^N • K ((q^(1/4 : ℝ))⁻¹ • y) := by
  unfold atTime
  rw [show -(1 : ℝ)/4 = -(1/4 : ℝ) by ring,Real.rpow_neg hq.le]
  congr 1
  rw [← Real.rpow_natCast,← Real.rpow_neg hq.le,← Real.rpow_mul hq.le]
  congr 1
  ring
end SchwartzTimeScale

namespace SourceFrozenCancellation
open SchwartzTimeScale
open scoped BoundedContinuousFunction
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma parameter_envelope (K : SchwartzMap V E) (N : ℕ) (α β : ℝ) (hα : 0 < α) :
    ∃ B : V → ℝ, Integrable B ∧ Integrable (fun z => (1+‖z‖)*B z) ∧
      (∀ z, 0 ≤ B z) ∧ ∀ a ∈ Icc α β, ∀ z, ‖atTime K N a z‖ ≤ B z := by
  obtain ⟨B,hB,hw,hp,hb⟩ := SchwartzConvolution.scaled_weighted_majorant K
    (α^(1/4 : ℝ)) (β^(1/4 : ℝ)) (by positivity) N 1
  refine ⟨B,hB,by simpa only [pow_one] using hw,hp,?_⟩
  intro a ha z
  rw [atTime_eq_scaled K N a (hα.trans_le ha.1)]
  exact hb _ ⟨Real.rpow_le_rpow hα.le ha.1 (by norm_num),
    Real.rpow_le_rpow (hα.trans_le ha.1).le ha.2 (by norm_num)⟩ z

omit [CompleteSpace E] in
lemma parameter_lipschitz_envelope (K : SchwartzMap V E) (N : ℕ) (α β : ℝ) (hα : 0 < α) :
    ∃ C : V → ℝ, Integrable C ∧ Integrable (fun z => (1+‖z‖)*C z) ∧
      (∀ z, 0 ≤ C z) ∧ ∀ a ∈ Icc α β, ∀ b ∈ Icc α β, ∀ z,
        ‖atTime K N a z-atTime K N b z‖ ≤ C z*‖a-b‖ := by
  obtain ⟨C,hC,hw,hp,hb⟩ := parameter_envelope (euler K N) (N+4) α β hα
  refine ⟨C,hC,hw,hp,fun a ha b hb' z => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q hq => (hasDerivAt_atTime K N q (hα.trans_le hq.1) z).hasDerivWithinAt)
    (fun q hq => hb q hq z) (convex_Icc α β) hb' ha

omit [CompleteSpace E] in
lemma integral_atTime_zero (K : SchwartzMap V E) (N : ℕ) (a : ℝ) (ha : 0 < a)
    (hK : ∫ z, K z = 0) : ∫ z, atTime K N a z = 0 := by
  simp_rw [atTime_eq_scaled K N a ha]
  rw [integral_smul,Measure.integral_comp_inv_smul_of_nonneg volume _ (by positivity)]
  simp only [hK,smul_zero]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace E] in
lemma continuous_variable (K : SchwartzMap V E) (N : ℕ) (a : V → ℝ) (ha : Continuous a)
    (hp : ∀ z, 0 < a z) : Continuous (fun z => atTime K N (a z) z) := by
  unfold atTime
  exact (ha.rpow_const (fun z => Or.inl (hp z).ne')).smul
    (K.continuous.comp ((ha.rpow_const (fun z => Or.inl (hp z).ne')).smul continuous_id))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] in
lemma integrable_envelope_power (B : V → ℝ) (hB : Integrable B)
    (hW : Integrable (fun z => (1+‖z‖)*B z)) (hp : ∀ z, 0 ≤ B z)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) : Integrable (fun z => ‖z‖^γ*B z) := by
  apply hW.mono'
  · exact (continuous_norm.rpow_const (fun _ => Or.inr hγ)).aestronglyMeasurable.mul
      hB.aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hp z))]
    apply mul_le_mul_of_nonneg_right _ (hp z)
    by_cases hz : ‖z‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg _) hz hγ).trans (by linarith [norm_nonneg z])
    · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hz) hγ1
      rw [Real.rpow_one] at hh
      exact hh.trans (by linarith)

omit [CompleteSpace E] in

lemma norm_normalized_source_integral (K : SchwartzMap V E) (N : ℕ)
    (α β : ℝ) (hα : 0 < α) (hK : ∫ z, K z = 0)
    (B C : V → ℝ) (hB : Integrable B) (hBw : Integrable (fun z => (1+‖z‖)*B z))
    (hBp : ∀ z, 0 ≤ B z) (hC : Integrable C) (hCw : Integrable (fun z => (1+‖z‖)*C z))
    (hCp : ∀ z, 0 ≤ C z)
    (hb : ∀ a ∈ Icc α β, ∀ z, ‖atTime K N a z‖ ≤ B z)
    (hc : ∀ a ∈ Icc α β, ∀ b ∈ Icc α β, ∀ z,
      ‖atTime K N a z-atTime K N b z‖ ≤ C z*‖a-b‖)
    (A : V → ℝ) (hA : Continuous A) (hAr : ∀ y, A y ∈ Icc α β)
    (L : ℝ) (_hL : 0 ≤ L) (hAL : ∀ x y, ‖A x-A y‖ ≤ L*‖x-y‖)
    (f : V →ᵇ ℂ) (γ H : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H)
    (hhold : ∀ x y, ‖f x-f y‖ ≤ H*‖x-y‖^γ) (r : ℝ) (hr : 0 < r) (x : V) :
    ‖∫ z, f (x-r • z) • atTime K N (A (x-r • z)) z‖ ≤
      H*r^γ*(∫ z, ‖z‖^γ*B z)+‖f‖*L*r*(∫ z, ‖z‖*C z) := by
  let a : V → ℝ := fun z => A (x-r • z)
  have ha : Continuous a := hA.comp (continuous_const.sub (continuous_const.smul continuous_id))
  have hp (z : V) : 0 < a z := hα.trans_le (hAr _).1
  have hi : Integrable (fun z => f (x-r • z) • atTime K N (a z) z) := by
    apply (hB.const_mul ‖f‖).mono'
    · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul
        (continuous_variable K N a ha hp)).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)
  have hi₀ : Integrable (fun z => f x • atTime K N (A x) z) := by
    apply (hB.const_mul ‖f x‖).mono'
    · exact ((continuous_variable K N (fun _ => A x) continuous_const
        (fun _ => hα.trans_le (hAr x).1)).const_smul (f x)).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hb _ (hAr x) z) (norm_nonneg _)
  have hzero : ∫ z, f x • atTime K N (A x) z = 0 := by
    rw [integral_smul,integral_atTime_zero K N (A x) (hα.trans_le (hAr x).1) hK,smul_zero]
  have hiB := integrable_envelope_power B hB hBw hBp γ hγ hγ1
  have hiC : Integrable (fun z => ‖z‖*C z) := by
    simpa using integrable_envelope_power C hC hCw hCp 1 (by norm_num) le_rfl
  have hd (z : V) : ‖(x-r • z)-x‖ = r*‖z‖ := by
    rw [sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  calc
    _ = ‖∫ z, (f (x-r • z) • atTime K N (a z) z-f x • atTime K N (A x) z)‖ := by
      rw [integral_sub hi hi₀,hzero,sub_zero]
    _ ≤ ∫ z, ‖f (x-r • z) • atTime K N (a z) z-f x • atTime K N (A x) z‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, (H*r^γ)*(‖z‖^γ*B z)+(‖f‖*L*r)*(‖z‖*C z) := by
      apply integral_mono (hi.sub hi₀).norm ((hiB.const_mul _).add (hiC.const_mul _))
      intro z
      have hdec : f (x-r • z) • atTime K N (a z) z-f x • atTime K N (A x) z =
          (f (x-r • z)-f x) • atTime K N (a z) z+
          f x • (atTime K N (a z) z-atTime K N (A x) z) := by module
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [hdec]
      apply (norm_add_le _ _).trans
      rw [norm_smul,norm_smul]
      have hF : ‖f (x-r • z)-f x‖ ≤ H*r^γ*‖z‖^γ := by
        simpa only [hd,Real.mul_rpow hr.le (norm_nonneg _),mul_assoc] using hhold (x-r • z) x
      have hcoef : ‖atTime K N (a z) z-atTime K N (A x) z‖ ≤ C z*(L*r*‖z‖) := by
        exact (hc _ (hAr _) _ (hAr x) z).trans
          (mul_le_mul_of_nonneg_left (by simpa only [hd,mul_assoc] using hAL (x-r • z) x) (hCp z))
      calc
        _ ≤ (H*r^γ*‖z‖^γ)*B z+‖f‖*(C z*(L*r*‖z‖)) :=
          add_le_add (mul_le_mul hF (hb _ (hAr _) z) (norm_nonneg _) (by positivity))
            (mul_le_mul (f.norm_coe_le_norm x) hcoef (norm_nonneg _) (norm_nonneg _))
        _ = _ := by ring
    _ = _ := by rw [integral_add (hiB.const_mul _) (hiC.const_mul _),integral_const_mul,integral_const_mul]
end SourceFrozenCancellation
open Set Filter MeasureTheory
open scoped SchwartzMap ContDiff FourierTransform BoundedContinuousFunction Convolution Topology

namespace SchwartzDerivatives
section Iterated
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def iterated (g : SchwartzMap V E) : (n : ℕ) →
    SchwartzMap V (ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E)
  | 0 => g.postcompCLM (continuousMultilinearCurryFin0 ℝ V E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  | n+1 => (SchwartzMap.fderivCLM ℝ V _ (iterated g n)).postcompCLM
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => V) E).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma iterated_coe (g : SchwartzMap V E) (n : ℕ) :
    (iterated g n : V → ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E) =
      iteratedFDeriv ℝ n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    change ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => V) E).symm ∘
      fderiv ℝ (iterated g n)) = _
    rw [ih]

lemma iterated_apply (g : SchwartzMap V E) (n : ℕ) (x : V) :
    iterated g n x = iteratedFDeriv ℝ n g x := congrFun (iterated_coe g n) x

end Iterated

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma integral_fderiv (g : SchwartzMap V E) :
    ∫ x : V, fderiv ℝ g x = 0 := by
  have h := congrArg (fun f : SchwartzMap V (V →L[ℝ] E) => f 0)
    (SchwartzMap.fourier_fderivCLM_eq (𝕜 := ℝ) g)
  simpa [SchwartzMap.fourier_coe, Real.fourier_eq,
    SchwartzMap.smulRightCLM_apply_apply, SchwartzMap.fderivCLM_apply] using h

lemma integral_iterated (g : SchwartzMap V E) (n : ℕ) :
    ∫ x : V, iteratedFDeriv ℝ (n+1) g x = 0 := by
  let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => V) E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let : ContinuousENorm (V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E) :=
    @SeminormedAddGroup.toContinuousENorm (V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E) inferInstance
  have hi : Integrable (fun x : V => fderiv ℝ (iterated g n) x) :=
    (SchwartzMap.fderivCLM ℝ V _ (iterated g n)).integrable
  rw [iteratedFDeriv_succ_eq_comp_left, ← iterated_coe g n]
  change (∫ x, L (fderiv ℝ (iterated g n) x)) = 0
  have hh := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
    (E := V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E)
    (Fₗ := ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => V) E) L hi
  exact hh.trans (by rw [integral_fderiv, map_zero])

end SchwartzDerivatives

open Set Filter MeasureTheory
open scoped SchwartzMap Topology ContDiff BoundedContinuousFunction

namespace ScaledSchwartzConvolution
section ScaledDecay
universe u
variable {V E : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)] in
lemma scaled_decay (g : SchwartzMap V E) (a b : ℝ) (ha : 0 < a) (K N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Icc a b, ∀ z,
      (1+‖z‖)^N * ‖(c⁻¹)^K • g (c⁻¹ • z)‖ ≤ C := by
  let M := max b 1
  let D := 2^N * (Finset.Iic (N,0)).sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) g
  have hD : 0 ≤ D := by positivity
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdec (z : V) : (1+‖z‖)^N * ‖g z‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N,0)) le_rfl le_rfl g z
  refine ⟨(a⁻¹)^K*(M^N*D), by positivity, ?_⟩
  intro c hc z
  have hcpos : 0 < c := ha.trans_le hc.1
  have hcM : c ≤ M := hc.2.trans (le_max_left _ _)
  have hn : ‖z‖ = c * ‖c⁻¹ • z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos),
      ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  have hs : 1+‖z‖ ≤ M*(1+‖c⁻¹ • z‖) := by
    rw [hn, mul_add, mul_one]
    exact add_le_add (le_max_right b 1) (mul_le_mul_of_nonneg_right hcM (norm_nonneg _))
  have hg : (1+‖z‖)^N * ‖g (c⁻¹ • z)‖ ≤ M^N*D := by
    calc
      _ ≤ (M*(1+‖c⁻¹ • z‖))^N * ‖g (c⁻¹ • z)‖ := by gcongr
      _ = M^N * ((1+‖c⁻¹ • z‖)^N * ‖g (c⁻¹ • z)‖) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdec _) (by positivity)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ = (c⁻¹)^K * ((1+‖z‖)^N * ‖g (c⁻¹ • z)‖) := by ring
    _ ≤ (a⁻¹)^K * ((1+‖z‖)^N * ‖g (c⁻¹ • z)‖) := by gcongr; exact hc.1
    _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)

lemma shifted_majorant (g : SchwartzMap V E) (a b : ℝ) (ha : 0 < a) (K : ℕ) (x₀ : V) :
    ∃ B : V → ℝ, Integrable B ∧ ∀ c ∈ Icc a b, ∀ x ∈ Metric.ball x₀ 1, ∀ y,
      ‖(c⁻¹)^K • g (c⁻¹ • (x-y))‖ ≤ B y := by
  let N := Module.finrank ℝ V + 1
  obtain ⟨C,hC,hdec⟩ := scaled_decay g a b ha K N
  refine ⟨fun y => (2^N*C)/(1+‖x₀-y‖)^N, ?_, ?_⟩
  · have hi : Integrable (fun z : V => (1+‖z‖)^(-(N : ℝ))) :=
      integrable_one_add_norm (by dsimp [N]; norm_num)
    simpa only [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+‖x₀-_‖),
      Real.rpow_natCast, div_eq_mul_inv] using (hi.comp_sub_left x₀).const_mul (2^N*C)
  · intro c hc x hx y
    have hd : ‖x₀-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hx
    have hn : ‖x₀-y‖ ≤ ‖x₀-x‖ + ‖x-y‖ := by simpa only [sub_add_sub_cancel] using norm_add_le (x₀-x) (x-y)
    have hs : 1+‖x₀-y‖ ≤ 2*(1+‖x-y‖) := by nlinarith [norm_nonneg (x-y)]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ ‖(c⁻¹)^K • g (c⁻¹ • (x-y))‖ * (2*(1+‖x-y‖))^N := by gcongr
      _ = 2^N * ((1+‖x-y‖)^N * ‖(c⁻¹)^K • g (c⁻¹ • (x-y))‖) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdec c hc _) (by positivity)

variable {A F : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {a b : ℝ} (ha : 0 < a) (c : V → ℝ) (hc : Continuous c) (hcb : ∀ y, c y ∈ Icc a b)

def value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A) (g : SchwartzMap V E) (K : ℕ) (x : V) : F :=
  ∫ y, L (f y) ((c y)⁻¹^K • g ((c y)⁻¹ • (x-y)))

include ha hc hcb
lemma integrable_integrand (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) (x : V) :
    Integrable (fun y => L (f y) ((c y)⁻¹^K • g ((c y)⁻¹ • (x-y)))) := by
  obtain ⟨B,hB,hbound⟩ := shifted_majorant g a b ha K x
  have hci : Continuous (fun y => (c y)⁻¹) := hc.inv₀ (fun y => (ha.trans_le (hcb y).1).ne')
  refine (hB.const_mul (‖L‖*‖f‖)).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((L.continuous.comp f.continuous).clm_apply
      ((hci.pow K).smul (g.continuous.comp (hci.smul (continuous_const.sub continuous_id))))).aestronglyMeasurable
  · exact (L.le_opNorm₂ _ _).trans <| mul_le_mul
      (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg L))
      (hbound (c y) (hcb y) x (Metric.mem_ball_self zero_lt_one) y)
      (norm_nonneg _) (by positivity)

lemma hasFDerivAt_value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) (x₀ : V) :
    HasFDerivAt (value c L f g K)
      (value c (L.precompR V) f (SchwartzMap.fderivCLM ℝ V E g) (K+1) x₀) x₀ := by
  let g' := SchwartzMap.fderivCLM ℝ V E g
  obtain ⟨B,hB,hbound⟩ := shifted_majorant g' a b ha (K+1) x₀
  have hd (x y : V) : HasFDerivAt (fun x => (c y)⁻¹^K • g ((c y)⁻¹ • (x-y)))
      ((c y)⁻¹^(K+1) • g' ((c y)⁻¹ • (x-y))) x := by
    have h := ((g.hasFDerivAt ((c y)⁻¹ • (x-y))).comp x
      (((hasFDerivAt_id x).sub (hasFDerivAt_const y x)).const_smul (c y)⁻¹)).const_smul ((c y)⁻¹^K)
    convert h using 1
    · rfl
    · ext v
      simp [g',SchwartzMap.fderivCLM_apply,pow_succ,smul_smul]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds x₀ zero_lt_one)
  · exact Eventually.of_forall fun x => (integrable_integrand ha c hc hcb L f g K x).aestronglyMeasurable
  · exact integrable_integrand ha c hc hcb L f g K x₀
  · exact (integrable_integrand ha c hc hcb (L.precompR V) f g' (K+1) x₀).aestronglyMeasurable
  · filter_upwards with y x hx
    change ‖(L (f y)).comp ((c y)⁻¹^(K+1) • g' ((c y)⁻¹ • (x-y)))‖ ≤ _
    calc
      _ ≤ ‖L (f y)‖ * ‖(c y)⁻¹^(K+1) • g' ((c y)⁻¹ • (x-y))‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖L‖*‖f‖) * ‖(c y)⁻¹^(K+1) • g' ((c y)⁻¹ • (x-y))‖ := by
        gcongr
        exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg L))
      _ ≤ (‖L‖*‖f‖)*B y := mul_le_mul_of_nonneg_left (hbound (c y) (hcb y) x hx y) (by positivity)
  · exact hB.const_mul (‖L‖*‖f‖)
  · filter_upwards with y x _
    exact (L (f y)).hasFDerivAt.comp x (hd x y)

lemma contDiff_value_nat (n : ℕ) (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) : ContDiff ℝ n (value c L f g K) := by
  induction n generalizing E F K with
  | zero =>
      rw [Nat.cast_zero,contDiff_zero]
      exact continuous_iff_continuousAt.mpr (fun x => (hasFDerivAt_value ha c hc hcb L f g K x).continuousAt)
  | succ n ih =>
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_hasFDerivAt]
      exact ⟨value c (L.precompR V) f (SchwartzMap.fderivCLM ℝ V E g) (K+1),
        ih (L.precompR V) (SchwartzMap.fderivCLM ℝ V E g) (K+1), hasFDerivAt_value ha c hc hcb L f g K⟩

lemma contDiff_value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) : ContDiff ℝ ∞ (value c L f g K) :=
  contDiff_infty.mpr (fun n => contDiff_value_nat ha c hc hcb n L f g K)

lemma fderiv_value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) :
    fderiv ℝ (value c L f g K) = value c (L.precompR V) f (SchwartzMap.fderivCLM ℝ V E g) (K+1) := by
  funext x
  exact (hasFDerivAt_value ha c hc hcb L f g K x).fderiv

lemma fderiv_value_apply (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) (x v : V) :
    fderiv ℝ (value c L f g K) x v =
      ∫ y, L (f y) ((c y)⁻¹^(K+1) • fderiv ℝ g ((c y)⁻¹ • (x-y)) v) := by
  rw [fderiv_value ha c hc hcb L f g K, value,
    ContinuousLinearMap.integral_apply
      (integrable_integrand ha c hc hcb (L.precompR V) f (SchwartzMap.fderivCLM ℝ V E g) (K+1) x)]
  rfl

lemma second_fderiv_value_apply (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) (x v w : V) :
    fderiv ℝ (fderiv ℝ (value c L f g K)) x v w =
      ∫ y, L (f y) ((c y)⁻¹^(K+2) • fderiv ℝ (fderiv ℝ g) ((c y)⁻¹ • (x-y)) v w) := by
  rw [fderiv_value ha c hc hcb L f g K, fderiv_value_apply ha c hc hcb]
  rw [ContinuousLinearMap.integral_apply]
  · rfl
  · exact integrable_integrand ha c hc hcb (L.precompR V) f
      (SchwartzMap.evalCLM ℝ V (V →L[ℝ] E) v
        (SchwartzMap.fderivCLM ℝ V (V →L[ℝ] E) (SchwartzMap.fderivCLM ℝ V E g))) (K+2) x

end ScaledDecay

section LaplacianValue
open scoped Laplacian
universe u
variable {V E F A : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {a b : ℝ} (ha : 0 < a) (c : V → ℝ) (hc : Continuous c) (hcb : ∀ y, c y ∈ Icc a b)

include ha hc hcb
lemma laplacian_value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) :
    Δ (value c L f g K) = value c L f (Δ g : SchwartzMap V E) (K+2) := by
  funext x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    second_fderiv_value_apply ha c hc hcb]
  rw [value]
  simp_rw [SchwartzMap.laplacian_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.smul_sum, map_sum]
  rw [integral_finsetSum]
  · rfl
  · intro i _
    exact integrable_integrand ha c hc hcb L f
      (SchwartzMap.evalCLM ℝ V E ((stdOrthonormalBasis ℝ V) i)
        (SchwartzMap.evalCLM ℝ V (V →L[ℝ] E) ((stdOrthonormalBasis ℝ V) i)
          (SchwartzMap.fderivCLM ℝ V (V →L[ℝ] E) (SchwartzMap.fderivCLM ℝ V E g)))) (K+2) x

lemma bilaplacian_value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) :
    Δ (Δ (value c L f g K)) = value c L f (Δ (Δ g : SchwartzMap V E) : SchwartzMap V E) (K+4) := by
  rw [laplacian_value ha c hc hcb, laplacian_value ha c hc hcb]

end LaplacianValue

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {a b : ℝ} (ha : 0 < a) (c : V → ℝ) (hc : Continuous c) (hcb : ∀ y, c y ∈ Icc a b)

include ha hc hcb
lemma iteratedFDeriv_value_smul (f : V →ᵇ ℂ) (g : SchwartzMap V E) (K n : ℕ) :
    iteratedFDeriv ℝ n (value c (ContinuousLinearMap.lsmul ℝ ℂ) f g K) =
      value c (ContinuousLinearMap.lsmul ℝ ℂ) f (SchwartzDerivatives.iterated g n) (K+n) := by
  induction n with
  | zero =>
    funext x
    let L := (continuousMultilinearCurryFin0 ℝ V E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hi : Integrable (fun y => f y • ((c y)⁻¹^K • g ((c y)⁻¹ • (x-y)))) :=
      integrable_integrand ha c hc hcb (ContinuousLinearMap.lsmul ℝ ℂ) f g K x
    change L (∫ y, f y • (c y)⁻¹^K • g ((c y)⁻¹ • (x-y))) =
      ∫ y, f y • ((c y)⁻¹^K • L (g ((c y)⁻¹ • (x-y))))
    rw [← ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) L hi]
    apply integral_congr_ae
    filter_upwards with y
    ext m
    rfl
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, ih, fderiv_value ha c hc hcb]
    funext x
    let g' := SchwartzMap.fderivCLM ℝ V _ (SchwartzDerivatives.iterated g n)
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => V) E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hi := integrable_integrand ha c hc hcb
      (E := V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E)
      (F := V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E)
      ((ContinuousLinearMap.lsmul ℝ ℂ).precompR V) f g' (K+n+1) x
    change L (∫ y, ((ContinuousLinearMap.lsmul ℝ ℂ).precompR V) (f y)
        ((c y)⁻¹^(K+n+1) • g' ((c y)⁻¹ • (x-y)))) =
      ∫ y, f y • ((c y)⁻¹^(K+(n+1)) • L (g' ((c y)⁻¹ • (x-y))))
    simp only [← Nat.add_assoc]
    rw [← ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) L hi]
    apply integral_congr_ae
    filter_upwards with y
    ext m
    rfl

lemma iteratedFDeriv_value_smul_apply (f : V →ᵇ ℂ) (g : SchwartzMap V E) (K n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (value c (ContinuousLinearMap.lsmul ℝ ℂ) f g K) x =
      ∫ y, f y • ((c y)⁻¹^(K+n) • iteratedFDeriv ℝ n g ((c y)⁻¹ • (x-y))) := by
  rw [iteratedFDeriv_value_smul ha c hc hcb]
  simp only [value,ContinuousLinearMap.lsmul_apply,SchwartzDerivatives.iterated_apply]
end ScaledSchwartzConvolution
open Set Filter MeasureTheory
open scoped Topology SchwartzMap
namespace SourceFrozenScaling
variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma normalized_integral (f : V → ℂ) (g : V → E) (c : V → ℝ) (r : ℝ) (hr : 0 < r)
    (K : ℕ) (x : V) :
    (∫ y, f y • ((r*c y)⁻¹^K • g ((r*c y)⁻¹ • (x-y)))) =
      (r^Module.finrank ℝ V*(r⁻¹)^K) • ∫ z, f (x-r • z) •
        ((c (x-r • z))⁻¹^K • g ((c (x-r • z))⁻¹ • z)) := by
  rw [← integral_sub_left_eq_self (fun y : V =>
    f y • ((r*c y)⁻¹^K • g ((r*c y)⁻¹ • (x-y)))) volume x]
  simp only [sub_sub_self]
  let F : V → E := fun z => f (x-r • z) •
    ((c (x-r • z))⁻¹^K • g ((c (x-r • z))⁻¹ • z))
  have he (y : V) : f (x-y) • ((r*c (x-y))⁻¹^K • g ((r*c (x-y))⁻¹ • y)) =
      (r⁻¹)^K • F (r⁻¹ • y) := by
    dsimp [F]
    rw [smul_inv_smul₀ hr.ne',mul_inv,mul_pow]
    rw [mul_comm r⁻¹ ((c (x-y))⁻¹),mul_smul]
    rw [mul_smul,smul_comm (f (x-y)) ((r⁻¹)^K)]
  simp_rw [he]
  rw [integral_smul,Measure.integral_comp_inv_smul_of_nonneg volume F hr.le,smul_smul]
  congr 1
  ring

lemma dimension_cancel (r : ℝ) (hr : r ≠ 0) (d n : ℕ) :
    r^d*(r⁻¹)^(d+n) = (r⁻¹)^n := by
  rw [pow_add,← mul_assoc,← mul_pow,mul_inv_cancel₀ hr,one_pow,one_mul]

lemma normalized_integral_order (f : V → ℂ) (g : V → E) (c : V → ℝ)
    (r : ℝ) (hr : 0 < r) (n : ℕ) (x : V) :
    (∫ y, f y • ((r*c y)⁻¹^(Module.finrank ℝ V+n) • g ((r*c y)⁻¹ • (x-y)))) =
      (r⁻¹)^n • ∫ z, f (x-r • z) •
        ((c (x-r • z))⁻¹^(Module.finrank ℝ V+n) • g ((c (x-r • z))⁻¹ • z)) := by
  rw [normalized_integral f g c r hr,dimension_cancel r hr.ne']
end SourceFrozenScaling

namespace SourceFrozenRows
section Value
open ScaledSchwartzConvolution SchwartzTimeScale
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def value (K : SchwartzMap V ℂ) (A : V → ℝ) (r : ℝ) (f : V →ᵇ ℂ) : V → ℂ :=
  ScaledSchwartzConvolution.value (fun y => r*(A y)^(1/4 : ℝ))
    (ContinuousLinearMap.lsmul ℝ ℂ) f K (Module.finrank ℝ V)

def row (K : SchwartzMap V ℂ) (A : V → ℝ) (r : ℝ) (f : V →ᵇ ℂ)
    (j : ℕ) : V → V [×j]→L[ℝ] ℂ :=
  ScaledSchwartzConvolution.value (fun y => r*(A y)^(1/4 : ℝ))
    (ContinuousLinearMap.lsmul ℝ ℂ) f (SchwartzDerivatives.iterated K j) (Module.finrank ℝ V+j)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
lemma radius_bounds (A : V → ℝ) (α β : ℝ) (hα : 0 < α)
    (hA : ∀ y, A y ∈ Icc α β) (r : ℝ) (hr : 0 < r) (y : V) :
    r*(A y)^(1/4 : ℝ) ∈ Icc (r*α^(1/4 : ℝ)) (r*β^(1/4 : ℝ)) := by
  constructor
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hα.le (hA y).1 (by norm_num)) hr.le
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (hα.trans_le (hA y).1).le (hA y).2 (by norm_num)) hr.le

lemma contDiff_value (K : SchwartzMap V ℂ) (A : V → ℝ) (hA : Continuous A)
    (α β : ℝ) (hα : 0 < α) (hAr : ∀ y, A y ∈ Icc α β)
    (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) : ContDiff ℝ ∞ (value K A r f) := by
  apply ScaledSchwartzConvolution.contDiff_value (a := r*α^(1/4 : ℝ))
    (b := r*β^(1/4 : ℝ)) (by positivity) _
    (continuous_const.mul (hA.rpow_const (fun _ => Or.inr (by norm_num))))
    (radius_bounds A α β hα hAr r hr)

lemma row_eq (K : SchwartzMap V ℂ) (A : V → ℝ) (hA : Continuous A)
    (α β : ℝ) (hα : 0 < α) (hAr : ∀ y, A y ∈ Icc α β)
    (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (j : ℕ) :
    row K A r f j = iteratedFDeriv ℝ j (value K A r f) := by
  symm
  apply ScaledSchwartzConvolution.iteratedFDeriv_value_smul (a := r*α^(1/4 : ℝ))
    (b := r*β^(1/4 : ℝ)) (by positivity) _
    (continuous_const.mul (hA.rpow_const (fun _ => Or.inr (by norm_num))))
    (radius_bounds A α β hα hAr r hr)

lemma row_normalized (K : SchwartzMap V ℂ) (A : V → ℝ)
    (hAp : ∀ y, 0 < A y) (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (j : ℕ) (x : V) :
    row K A r f j x = (r⁻¹)^j • ∫ z, f (x-r • z) •
      atTime (SchwartzDerivatives.iterated K j) (Module.finrank ℝ V+j) (A (x-r • z)) z := by
  unfold row ScaledSchwartzConvolution.value
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [SourceFrozenScaling.normalized_integral_order _ _ _ r hr]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [atTime_eq_scaled _ _ _ (hAp _)]

lemma exists_row_holder_bound (K : SchwartzMap V ℂ) (j : ℕ) (hj : 0 < j)
    (α β : ℝ) (hα : 0 < α) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (A : V → ℝ) (_hA : Continuous A) (_hAr : ∀ y, A y ∈ Icc α β)
        (L : ℝ) (_hL : 0 ≤ L) (_hAL : ∀ x y, ‖A x-A y‖ ≤ L*‖x-y‖)
        (f : V →ᵇ ℂ) (H : ℝ) (_hH : 0 ≤ H)
        (_hhold : ∀ x y, ‖f x-f y‖ ≤ H*‖x-y‖^γ)
        (r : ℝ) (_hr : 0 < r) (x : V),
      ‖row K A r f j x‖ ≤ (r⁻¹)^j*(H*r^γ*C+‖f‖*L*r*D) := by
  let K' := SchwartzDerivatives.iterated K j
  obtain ⟨B,hB,hBw,hBp,hb⟩ := SourceFrozenCancellation.parameter_envelope K' (Module.finrank ℝ V+j) α β hα
  obtain ⟨D,hD,hDw,hDp,hd⟩ := SourceFrozenCancellation.parameter_lipschitz_envelope K' (Module.finrank ℝ V+j) α β hα
  refine ⟨∫ z, ‖z‖^γ*B z, ∫ z, ‖z‖*D z,
    integral_nonneg (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hBp z)),
    integral_nonneg (fun z => mul_nonneg (norm_nonneg _) (hDp z)), ?_⟩
  intro A hA hAr L hL hAL f H hH hhold r hr x
  rw [row_normalized K A (fun y => hα.trans_le (hAr y).1) r hr,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hz : ∫ z, K' z = 0 := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    simp only [K',SchwartzDerivatives.iterated_apply]
    exact SchwartzDerivatives.integral_iterated K n
  exact SourceFrozenCancellation.norm_normalized_source_integral K' _ α β hα hz
    B D hB hBw hBp hD hDw hDp hb hd A hA hAr L hL hAL f γ H hγ hγ1 hH hhold r hr x
end Value

section ExistsRowZeroBound
open ScaledSchwartzConvolution SchwartzTimeScale
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma exists_row_zero_bound (K : SchwartzMap V ℂ) (α β : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : V → ℝ) (_hA : Continuous A)
      (_hAr : ∀ y, A y ∈ Icc α β) (r : ℝ) (_hr : 0 < r) (f : V →ᵇ ℂ) (x : V),
      ‖row K A r f 0 x‖ ≤ ‖f‖*C := by
  let K' := SchwartzDerivatives.iterated K 0
  obtain ⟨B,hB,_hw,hBp,hb⟩ := SourceFrozenCancellation.parameter_envelope K' (Module.finrank ℝ V+0) α β hα
  refine ⟨∫ z, B z,integral_nonneg hBp,?_⟩
  intro A hA hAr r hr f x
  rw [row_normalized K A (fun y => hα.trans_le (hAr y).1) r hr,pow_zero,one_smul]
  have hi : Integrable (fun z => f (x-r • z) •
      atTime K' (Module.finrank ℝ V+0) (A (x-r • z)) z) := by
    apply (hB.const_mul ‖f‖).mono'
    · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul
        (SourceFrozenCancellation.continuous_variable K' _ (fun z => A (x-r • z))
          (hA.comp (continuous_const.sub (continuous_const.smul continuous_id)))
          (fun z => hα.trans_le (hAr _).1))).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)
  change ‖∫ z, f (x-r • z) • atTime K' _ (A (x-r • z)) z‖ ≤ _
  calc
    _ ≤ ∫ z, ‖f (x-r • z) • atTime K' _ (A (x-r • z)) z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖f‖*B z := by
      apply integral_mono hi.norm (hB.const_mul ‖f‖)
      intro z
      dsimp only
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)
    _ = _ := integral_const_mul ..

lemma continuous_row (K : SchwartzMap V ℂ) (A : V → ℝ) (hA : Continuous A)
    (α β : ℝ) (hα : 0 < α) (hAr : ∀ y, A y ∈ Icc α β)
    (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (j : ℕ) : Continuous (row K A r f j) := by
  rw [row_eq K A hA α β hα hAr r hr]
  have hd : ContDiff ℝ (j+1) (value K A r f) :=
    by simpa only [Nat.cast_add,Nat.cast_one] using
      (contDiff_infty.mp (contDiff_value K A hA α β hα hAr r hr f) (j+1))
  exact hd.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_succ j)

lemma hasFDerivAt_row (K : SchwartzMap V ℂ) (A : V → ℝ) (hA : Continuous A)
    (α β : ℝ) (hα : 0 < α) (hAr : ∀ y, A y ∈ Icc α β)
    (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (j : ℕ) (x : V) :
    HasFDerivAt (row K A r f j)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ)
        (row K A r f (j+1) x)) x := by
  rw [row_eq K A hA α β hα hAr r hr f j,
    row_eq K A hA α β hα hAr r hr f (j+1)]
  have hd : ContDiff ℝ (j+1) (value K A r f) :=
    by simpa only [Nat.cast_add,Nat.cast_one] using
      (contDiff_infty.mp (contDiff_value K A hA α β hα hAr r hr f) (j+1))
  have hd' := (hd.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast Nat.lt_succ_self j) x).hasFDerivAt
  simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using hd'

lemma stronglyMeasurable_time_row (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (j : ℕ) (t : ℝ) (x : V) :
    StronglyMeasurable (fun s : ℝ => row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x) := by
  let c : ℝ × V → ℝ := fun p => (((t-p.1)^(1/4 : ℝ))*(A p.1 p.2)^(1/4 : ℝ))⁻¹
  have hc : Measurable c := by
    dsimp [c]
    exact (((measurable_const.sub measurable_fst).pow_const _).mul
      (hA.measurable.pow_const _)).inv
  have he : Continuous (fun p : ℝ × V => f p.1 p.2) := by fun_prop
  have hg := (SchwartzDerivatives.iterated K j).continuous
  have hm : StronglyMeasurable (fun p : ℝ × V => f p.1 p.2 •
      (c p ^ (Module.finrank ℝ V+j) • SchwartzDerivatives.iterated K j (c p • (x-p.2)))) :=
    he.stronglyMeasurable.smul ((hc.pow_const _).stronglyMeasurable.smul
      (hg.comp_stronglyMeasurable (hc.stronglyMeasurable.smul
        (continuous_const.sub continuous_snd).stronglyMeasurable)))
  exact hm.integral_prod_right'

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
lemma radius_weight (q : ℝ) (hq : 0 < q) (j : ℕ) (p : ℝ) :
    ((q^(1/4 : ℝ))⁻¹)^j*(q^(1/4 : ℝ))^p = q^((p-j)/4) := by
  rw [inv_pow,← Real.rpow_natCast,← Real.rpow_mul hq.le,← Real.rpow_neg hq.le,
    ← Real.rpow_mul hq.le,← Real.rpow_add hq]
  congr 1
  ring
end ExistsRowZeroBound

section IntegrableOnLagRpow
open SchwartzTimeScale
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integrableOn_lag_rpow (t p : ℝ) (ht : 0 ≤ t) (hp : -1 < p) :
    IntegrableOn (fun s : ℝ => (t-s)^p) (Ioo 0 t) := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) hp).comp_sub_left t
  simp only [sub_zero,sub_self] at hi
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).mp hi.symm

lemma exists_integrable_row_bound (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (α β : ℝ) (hα : 0 < α)
    (hAr : ∀ s y, A s y ∈ Icc α β) (L : ℝ) (hL : 0 ≤ L)
    (hAL : ∀ s x y, ‖A s x-A s y‖ ≤ L*‖x-y‖)
    (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (γ H t : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H)
    (hhold : ∀ s ∈ Ioo 0 t, ∀ x y : V, ‖f s x-f s y‖ ≤ H*‖x-y‖^γ)
    (j : ℕ) (hj4 : j ≤ 4) :
    ∃ b : ℝ → ℝ, IntegrableOn b (Ioo 0 t) ∧
      ∀ s ∈ Ioo 0 t, ∀ x : V,
        ‖row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x‖ ≤ b s := by
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hf.continuousOn
  have hAs (s : ℝ) : Continuous (A s) := hA.comp (continuous_const.prodMk continuous_id)
  by_cases hj : j = 0
  · subst j
    obtain ⟨C,hC,hb⟩ := exists_row_zero_bound K α β hα
    refine ⟨fun _ => M*C,integrableOn_const (hs := measure_Ioo_lt_top.ne),?_⟩
    intro s hs x
    exact (hb (A s) (hAs s) (hAr s) _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) x).trans
      (mul_le_mul_of_nonneg_right (hM s ⟨hs.1.le,hs.2.le⟩) hC)
  · obtain ⟨C,D,hC,hD,hb⟩ := exists_row_holder_bound K j (Nat.pos_of_ne_zero hj) α β hα γ hγ.le hγ1
    have hp : -1 < (γ-j)/4 := by
      have : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
      linarith
    have hp' : -1 < ((1 : ℝ)-j)/4 := by
      have : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
      linarith
    refine ⟨fun s => H*C*(t-s)^((γ-j)/4)+M*L*D*(t-s)^(((1 : ℝ)-j)/4),
      ((integrableOn_lag_rpow t _ ht hp).const_mul _).add
        ((integrableOn_lag_rpow t _ ht hp').const_mul _),?_⟩
    intro s hs x
    have hq : 0 < t-s := sub_pos.mpr hs.2
    have hr : 0 < (t-s)^(1/4 : ℝ) := Real.rpow_pos_of_pos hq _
    have he := hb (A s) (hAs s) (hAr s) L hL (hAL s) (f s) H hH
      (hhold s hs) _ hr x
    have heq : (((t-s)^(1/4 : ℝ))⁻¹)^j *
        (H*((t-s)^(1/4 : ℝ))^γ*C+‖f s‖*L*((t-s)^(1/4 : ℝ))*D) =
        H*C*(t-s)^((γ-j)/4)+‖f s‖*L*D*(t-s)^(((1 : ℝ)-j)/4) := by
      rw [mul_add]
      have h1 := radius_weight (t-s) hq j γ
      have h2 := radius_weight (t-s) hq j 1
      rw [Real.rpow_one] at h2
      calc
        _ = H*C*((((t-s)^(1/4 : ℝ))⁻¹)^j*((t-s)^(1/4 : ℝ))^γ) +
            ‖f s‖*L*D*((((t-s)^(1/4 : ℝ))⁻¹)^j*(t-s)^(1/4 : ℝ)) := by ring
        _ = _ := by rw [h1,h2]
    rw [heq] at he
    apply he.trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (hM s ⟨hs.1.le,hs.2.le⟩) hL) hD) (Real.rpow_nonneg hq.le _))

def integralRow (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (f : ℝ → (V →ᵇ ℂ)) (t : ℝ) (j : ℕ) (x : V) : V [×j]→L[ℝ] ℂ :=
  ∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x

variable (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (α β : ℝ) (hα : 0 < α)
    (hAr : ∀ s y, A s y ∈ Icc α β) (L : ℝ) (hL : 0 ≤ L)
    (hAL : ∀ s x y, ‖A s x-A s y‖ ≤ L*‖x-y‖)
    (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (γ H t : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H)
    (hhold : ∀ s ∈ Ioo 0 t, ∀ x y : V, ‖f s x-f s y‖ ≤ H*‖x-y‖^γ)
include hA hα hAr hf hAL hL hH ht hγ hγ1 hhold

lemma integrableOn_row (j : ℕ) (hj4 : j ≤ 4) (x : V) :
    IntegrableOn (fun s => row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x) (Ioo 0 t) := by
  obtain ⟨b,hi,hb⟩ := exists_integrable_row_bound K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j hj4
  exact hi.mono' (stronglyMeasurable_time_row K A hA f hf j t x).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs; exact hb s hs x)

lemma continuous_integralRow (j : ℕ) (hj4 : j ≤ 4) :
    Continuous (integralRow K A f t j) := by
  obtain ⟨b,hbi,hb⟩ := exists_integrable_row_bound K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j hj4
  apply continuous_of_dominated (bound := b)
  · intro x
    exact (stronglyMeasurable_time_row K A hA f hf j t x).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hb s hs x
  · exact hbi
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact continuous_row K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
      _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) j

lemma hasFDerivAt_integralRow (j : ℕ) (hj4 : j+1 ≤ 4) (x : V) :
    HasFDerivAt (integralRow K A f t j)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ)
        (integralRow K A f t (j+1) x)) x := by
  let C := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  let : ContinuousENorm (V →L[ℝ] V [×j]→L[ℝ] ℂ) :=
    @SeminormedAddGroup.toContinuousENorm (V →L[ℝ] V [×j]→L[ℝ] ℂ) inferInstance
  have hi := integrableOn_row K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold (j+1) hj4 x
  have hcomm := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
    (E := V [×(j+1)]→L[ℝ] ℂ) (Fₗ := V →L[ℝ] V [×j]→L[ℝ] ℂ) C hi
  change HasFDerivAt (fun x => ∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x)
    (C (∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) x)) x
  rw [← hcomm]
  obtain ⟨b,hbi,hb⟩ := exists_integrable_row_bound K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold (j+1) hj4
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun x s => C (row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) x)) (bound := b) (univ_mem : univ ∈ 𝓝 x)
  · exact Eventually.of_forall fun z => (stronglyMeasurable_time_row K A hA f hf j t z).aestronglyMeasurable
  · exact integrableOn_row K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j (by omega) x
  · exact (C.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_time_row K A hA f hf (j+1) t x)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    change ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ)
      (row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) z)‖ ≤ b s
    rw [LinearIsometryEquiv.norm_map]
    exact hb s hs z
  · exact hbi
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    exact hasFDerivAt_row K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
      _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) j z

lemma contDiff_integralRow (j n : ℕ) (hjn : j+n ≤ 4) :
    ContDiff ℝ n (integralRow K A f t j) := by
  induction n generalizing j with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_integralRow K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j (by omega)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
    let C : (V [×(j+1)]→L[ℝ] ℂ) →L[ℝ] (V →L[ℝ] V [×j]→L[ℝ] ℂ) := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    refine ⟨fun x => C (integralRow K A f t (j+1) x), ?_, ?_⟩
    · exact contDiff_const.clm_apply (ih (j+1) (by omega))
    · intro x
      exact hasFDerivAt_integralRow K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j (by omega) x

end IntegrableOnLagRpow
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def duhamel (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (f : ℝ → (V →ᵇ ℂ)) (t : ℝ) (x : V) : ℂ :=
  ∫ s in Ioo 0 t, value K (A s) ((t-s)^(1/4 : ℝ)) (f s) x

variable (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (α β : ℝ) (hα : 0 < α)
    (hAr : ∀ s y, A s y ∈ Icc α β) (L : ℝ) (hL : 0 ≤ L)
    (hAL : ∀ s x y, ‖A s x-A s y‖ ≤ L*‖x-y‖)
    (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (γ H t : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H)
    (hhold : ∀ s ∈ Ioo 0 t, ∀ x y : V, ‖f s x-f s y‖ ≤ H*‖x-y‖^γ)
include hA hα hAr hf hAL hL hH ht hγ hγ1 hhold

lemma duhamel_eq_integralRow_zero (x : V) : duhamel K A f t x =
    (continuousMultilinearCurryFin0 ℝ V ℂ) (integralRow K A f t 0 x) := by
  let C := (continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have hc := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
    (E := V [×0]→L[ℝ] ℂ) (Fₗ := ℂ) C
    (integrableOn_row K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold 0 (by omega) x)
  change (∫ s in Ioo 0 t, value K (A s) ((t-s)^(1/4 : ℝ)) (f s) x) =
    C (∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) 0 x)
  rw [← hc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [row_eq K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
    _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _),iteratedFDeriv_zero_eq_comp]
  exact (LinearIsometryEquiv.apply_symm_apply _ _).symm

lemma contDiff_duhamel : ContDiff ℝ 4 (duhamel K A f t) := by
  have he : duhamel K A f t = fun x => (continuousMultilinearCurryFin0 ℝ V ℂ)
      (integralRow K A f t 0 x) :=
    funext (duhamel_eq_integralRow_zero K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold)
  rw [he]
  let C : (V [×0]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    (continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  change ContDiff ℝ 4 (fun x => C (integralRow K A f t 0 x))
  exact contDiff_const.clm_apply
    (contDiff_integralRow K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold 0 4 (by omega))

lemma iteratedFDeriv_duhamel (j : ℕ) (hj : j ≤ 4) :
    iteratedFDeriv ℝ j (duhamel K A f t) = integralRow K A f t j := by
  induction j with
  | zero =>
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    change (continuousMultilinearCurryFin0 ℝ V ℂ).symm (duhamel K A f t x) = _
    rw [duhamel_eq_integralRow_zero K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold,
      LinearIsometryEquiv.symm_apply_apply]
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left,ih (by omega)]
    funext x
    dsimp only [Function.comp_apply]
    rw [(hasFDerivAt_integralRow K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j hj x).fderiv]
    exact LinearIsometryEquiv.symm_apply_apply _ _

lemma exists_norm_iteratedFDeriv_duhamel_bound (j : ℕ) (hj : j ≤ 4) :
    ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j (duhamel K A f t) x‖ ≤ C := by
  obtain ⟨b,hi,hb⟩ := exists_integrable_row_bound K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j hj
  refine ⟨∫ s in Ioo 0 t, b s,fun x => ?_⟩
  rw [iteratedFDeriv_duhamel K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j hj]
  apply norm_integral_le_of_norm_le hi
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact hb s hs x
end SourceFrozenRows

namespace BetaWeights

def density (σ ρ t s : ℝ) : ℝ := s^(-σ)*(t-s)^(-ρ)

lemma density_nonneg (σ ρ t s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) : 0 ≤ density σ ρ t s := by
  exact mul_nonneg (Real.rpow_nonneg hs _) (Real.rpow_nonneg (sub_nonneg.mpr hst) _)

lemma intervalIntegrable_one (σ ρ : ℝ) (hσ : σ < 1) (hρ : ρ < 1) :
    IntervalIntegrable (density σ ρ 1) volume 0 1 := by
  have hb := (Complex.betaIntegral_convergent
    (u := ((1-σ : ℝ) : ℂ)) (v := ((1-ρ : ℝ) : ℂ)) (by simpa using sub_pos.mpr hσ)
      (by simpa using sub_pos.mpr hρ)).norm
  apply hb.congr_ae
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  dsimp only [density]
  rw [norm_mul]
  have hq : ((1-σ : ℝ) : ℂ)-1 = ((-σ : ℝ) : ℂ) := by push_cast; ring
  have hr : ((1-ρ : ℝ) : ℂ)-1 = ((-ρ : ℝ) : ℂ) := by push_cast; ring
  rw [hq,hr,show (1 : ℂ)-(x : ℂ) = ((1-x : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_real,Complex.norm_cpow_real,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hx.1,abs_of_pos (sub_pos.mpr hx.2)]

lemma density_scaled (σ ρ t s : ℝ) (ht : 0 < t) (hs : s ∈ Ioo 0 1) :
    density σ ρ t (t*s) = (t^(-σ)*t^(-ρ))*density σ ρ 1 s := by
  unfold density
  rw [show t-t*s = t*(1-s) by ring,Real.mul_rpow ht.le hs.1.le,
    Real.mul_rpow ht.le (sub_nonneg.mpr hs.2.le)]
  ring

lemma intervalIntegrable (σ ρ : ℝ) (hσ : σ < 1) (hρ : ρ < 1) (t : ℝ) (ht : 0 < t) :
    IntervalIntegrable (density σ ρ t) volume 0 t := by
  rw [← IntervalIntegrable.comp_mul_left_iff ht.ne']
  simp only [zero_div,div_self ht.ne']
  apply ((intervalIntegrable_one σ ρ hσ hρ).const_mul (t^(-σ)*t^(-ρ))).congr_ae
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hmem : ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) 1), s ∈ Ioo 0 1 := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem] with s hs
  exact (density_scaled σ ρ t s ht hs).symm

lemma integral_scale (σ ρ t : ℝ) (ht : 0 < t) :
    (∫ s in 0..t, density σ ρ t s) = t^(1-σ-ρ)*(∫ s in 0..1, density σ ρ 1 s) := by
  have hc := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (density σ ρ t) t
  simp only [mul_zero,mul_one,smul_eq_mul] at hc
  rw [← hc]
  have he : (∫ s in 0..1, density σ ρ t (t*s)) =
      (t^(-σ)*t^(-ρ))*(∫ s in 0..1, density σ ρ 1 s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),← ae_restrict_iff' measurableSet_Ioc,← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact density_scaled σ ρ t s ht hs
  rw [he,← mul_assoc]
  congr 1
  calc
    _ = t^(1 : ℝ)*(t^(-σ)*t^(-ρ)) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add ht,← Real.rpow_add ht]; congr 1; ring
end BetaWeights

namespace SourceFrozenRows
open ScaledSchwartzConvolution SchwartzTimeScale
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma stronglyMeasurable_time_row_of_stronglyMeasurable
    (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (f : ℝ → (V →ᵇ ℂ))
    (hf : StronglyMeasurable f) (j : ℕ) (t : ℝ) (x : V) :
    StronglyMeasurable (fun s : ℝ => row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x) := by
  let c : ℝ × V → ℝ := fun p => (((t-p.1)^(1/4 : ℝ))*(A p.1 p.2)^(1/4 : ℝ))⁻¹
  have hc : Measurable c := by
    dsimp [c]
    exact (((measurable_const.sub measurable_fst).pow_const _).mul
      (hA.measurable.pow_const _)).inv
  have he' : Continuous (fun p : (V →ᵇ ℂ) × V => p.1 p.2) := by fun_prop
  have he : StronglyMeasurable (fun p : ℝ × V => f p.1 p.2) :=
    he'.comp_stronglyMeasurable
      ((hf.comp_measurable measurable_fst).prodMk continuous_snd.stronglyMeasurable)
  have hg := (SchwartzDerivatives.iterated K j).continuous
  have hm : StronglyMeasurable (fun p : ℝ × V => f p.1 p.2 •
      (c p ^ (Module.finrank ℝ V+j) • SchwartzDerivatives.iterated K j (c p • (x-p.2)))) :=
    he.smul ((hc.pow_const _).stronglyMeasurable.smul
      (hg.comp_stronglyMeasurable (hc.stronglyMeasurable.smul
        (continuous_const.sub continuous_snd).stronglyMeasurable)))
  exact hm.integral_prod_right'

lemma exists_integrable_row_bound_weighted (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (α β : ℝ) (hα : 0 < α)
    (hAr : ∀ s y, A s y ∈ Icc α β) (L : ℝ) (hL : 0 ≤ L)
    (hAL : ∀ s x y, ‖A s x-A s y‖ ≤ L*‖x-y‖)
    (f : ℝ → (V →ᵇ ℂ)) (σ τ M H γ t : ℝ)
    (hσ : σ < 1) (hτ : τ < 1) (_hM : 0 ≤ M) (hH : 0 ≤ H)
    (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hfn : ∀ s ∈ Ioo 0 t, ‖f s‖ ≤ M*s^(-σ))
    (hhold : ∀ s ∈ Ioo 0 t, ∀ x y : V, ‖f s x-f s y‖ ≤ (H*s^(-τ))*‖x-y‖^γ)
    (j : ℕ) (hj4 : j ≤ 4) :
    ∃ b : ℝ → ℝ, IntegrableOn b (Ioo 0 t) ∧
      ∀ s ∈ Ioo 0 t, ∀ x : V,
        ‖row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x‖ ≤ b s := by
  have hAs (s : ℝ) : Continuous (A s) := hA.comp (continuous_const.prodMk continuous_id)
  by_cases hj : j = 0
  · subst j
    obtain ⟨C,hC,hb⟩ := exists_row_zero_bound K α β hα
    have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (BetaWeights.intervalIntegrable σ 0 hσ (by norm_num) t ht)
    refine ⟨fun s => (M*C)*BetaWeights.density σ 0 t s,hi.const_mul _,?_⟩
    intro s hs x
    have hh := (hb (A s) (hAs s) (hAr s) ((t-s)^(1/4 : ℝ)) (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) x).trans
      (mul_le_mul_of_nonneg_right (hfn s hs) hC)
    simpa only [BetaWeights.density,neg_zero,Real.rpow_zero,mul_one,mul_assoc,mul_comm,mul_left_comm] using hh
  · obtain ⟨C,D,hC,hD,hb⟩ := exists_row_holder_bound K j (Nat.pos_of_ne_zero hj) α β hα γ hγ.le hγ1
    have hp : ((j : ℝ)-γ)/4 < 1 := by
      have : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
      linarith
    have hp' : ((j : ℝ)-1)/4 < 1 := by
      have : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
      linarith
    have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (BetaWeights.intervalIntegrable τ ((j-γ)/4) hτ hp t ht)
    have hi' := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (BetaWeights.intervalIntegrable σ ((j-1)/4) hσ hp' t ht)
    refine ⟨fun s => (H*C)*BetaWeights.density τ ((j-γ)/4) t s+
        (M*L*D)*BetaWeights.density σ ((j-1)/4) t s,
      (hi.const_mul _).add (hi'.const_mul _),?_⟩
    intro s hs x
    have hq : 0 < t-s := sub_pos.mpr hs.2
    have hr : 0 < (t-s)^(1/4 : ℝ) := Real.rpow_pos_of_pos hq _
    have hsτ : 0 ≤ H*s^(-τ) := mul_nonneg hH (Real.rpow_nonneg hs.1.le _)
    have he := hb (A s) (hAs s) (hAr s) L hL (hAL s) (f s) (H*s^(-τ)) hsτ
      (hhold s hs) _ hr x
    have heq : (((t-s)^(1/4 : ℝ))⁻¹)^j *
        ((H*s^(-τ))*((t-s)^(1/4 : ℝ))^γ*C+‖f s‖*L*((t-s)^(1/4 : ℝ))*D) =
        (H*s^(-τ))*C*(t-s)^((γ-j)/4)+‖f s‖*L*D*(t-s)^(((1 : ℝ)-j)/4) := by
      rw [mul_add]
      have h1 := radius_weight (t-s) hq j γ
      have h2 := radius_weight (t-s) hq j 1
      rw [Real.rpow_one] at h2
      calc
        _ = (H*s^(-τ))*C*((((t-s)^(1/4 : ℝ))⁻¹)^j*((t-s)^(1/4 : ℝ))^γ) +
            ‖f s‖*L*D*((((t-s)^(1/4 : ℝ))⁻¹)^j*(t-s)^(1/4 : ℝ)) := by ring
        _ = _ := by rw [h1,h2]
    rw [heq] at he
    apply he.trans
    have hn := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hfn s hs) hL) hD)
      (Real.rpow_nonneg hq.le (((1 : ℝ)-j)/4))
    calc
      _ ≤ (H*s^(-τ))*C*(t-s)^((γ-j)/4)+(M*s^(-σ))*L*D*(t-s)^(((1 : ℝ)-j)/4) :=
        add_le_add le_rfl hn
      _ = _ := by
        unfold BetaWeights.density
        rw [show -((↑j-γ)/4) = (γ-j)/4 by ring,show -(((j:ℝ)-1)/4) = ((1:ℝ)-j)/4 by ring]
        ring
end SourceFrozenRows

namespace WeightedSourceFrozenRows
open SourceFrozenRows
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (α β : ℝ) (hα : 0 < α)
    (hAr : ∀ s y, A s y ∈ Icc α β) (L : ℝ) (hL : 0 ≤ L)
    (hAL : ∀ s x y, ‖A s x-A s y‖ ≤ L*‖x-y‖)
    (f : ℝ → (V →ᵇ ℂ)) (hf : StronglyMeasurable f) (σ τ M H γ t : ℝ)
    (hσ : σ < 1) (hτ : τ < 1) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hfn : ∀ s ∈ Ioo 0 t, ‖f s‖ ≤ M*s^(-σ))
    (hhold : ∀ s ∈ Ioo 0 t, ∀ x y : V, ‖f s x-f s y‖ ≤ (H*s^(-τ))*‖x-y‖^γ)
include hA hα hAr hf hAL hL hH ht hγ hγ1 hhold hσ hτ hM hfn

lemma integrableOn_row (j : ℕ) (hj4 : j ≤ 4) (x : V) :
    IntegrableOn (fun s => row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x) (Ioo 0 t) := by
  obtain ⟨b,hi,hb⟩ := SourceFrozenRows.exists_integrable_row_bound_weighted K A hA α β hα hAr L hL hAL f σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j hj4
  exact hi.mono' (stronglyMeasurable_time_row_of_stronglyMeasurable K A hA f hf j t x).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs; exact hb s hs x)

lemma continuous_integralRow (j : ℕ) (hj4 : j ≤ 4) :
    Continuous (integralRow K A f t j) := by
  obtain ⟨b,hbi,hb⟩ := SourceFrozenRows.exists_integrable_row_bound_weighted K A hA α β hα hAr L hL hAL f σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j hj4
  apply continuous_of_dominated (bound := b)
  · intro x
    exact (stronglyMeasurable_time_row_of_stronglyMeasurable K A hA f hf j t x).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hb s hs x
  · exact hbi
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact continuous_row K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
      _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) j

lemma hasFDerivAt_integralRow (j : ℕ) (hj4 : j+1 ≤ 4) (x : V) :
    HasFDerivAt (integralRow K A f t j)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ)
        (integralRow K A f t (j+1) x)) x := by
  let C := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  let : ContinuousENorm (V →L[ℝ] V [×j]→L[ℝ] ℂ) :=
    @SeminormedAddGroup.toContinuousENorm (V →L[ℝ] V [×j]→L[ℝ] ℂ) inferInstance
  have hi := integrableOn_row K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold (j+1) hj4 x
  have hcomm := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
    (E := V [×(j+1)]→L[ℝ] ℂ) (Fₗ := V →L[ℝ] V [×j]→L[ℝ] ℂ) C hi
  change HasFDerivAt (fun x => ∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x)
    (C (∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) x)) x
  rw [← hcomm]
  obtain ⟨b,hbi,hb⟩ := SourceFrozenRows.exists_integrable_row_bound_weighted K A hA α β hα hAr L hL hAL f σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold (j+1) hj4
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun x s => C (row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) x)) (bound := b) (univ_mem : univ ∈ 𝓝 x)
  · exact Eventually.of_forall fun z => (stronglyMeasurable_time_row_of_stronglyMeasurable K A hA f hf j t z).aestronglyMeasurable
  · exact integrableOn_row K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j (by omega) x
  · exact (C.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_time_row_of_stronglyMeasurable K A hA f hf (j+1) t x)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    change ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ)
      (row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) z)‖ ≤ b s
    rw [LinearIsometryEquiv.norm_map]
    exact hb s hs z
  · exact hbi
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    exact hasFDerivAt_row K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
      _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) j z

lemma contDiff_integralRow (j n : ℕ) (hjn : j+n ≤ 4) :
    ContDiff ℝ n (integralRow K A f t j) := by
  induction n generalizing j with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_integralRow K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j (by omega)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
    let C : (V [×(j+1)]→L[ℝ] ℂ) →L[ℝ] (V →L[ℝ] V [×j]→L[ℝ] ℂ) := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    refine ⟨fun x => C (integralRow K A f t (j+1) x), ?_, ?_⟩
    · exact contDiff_const.clm_apply (ih (j+1) (by omega))
    · intro x
      exact hasFDerivAt_integralRow K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j (by omega) x

lemma duhamel_eq_integralRow_zero (x : V) : duhamel K A f t x =
    (continuousMultilinearCurryFin0 ℝ V ℂ) (integralRow K A f t 0 x) := by
  let C := (continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have hc := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
    (E := V [×0]→L[ℝ] ℂ) (Fₗ := ℂ) C
    (integrableOn_row K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold 0 (by omega) x)
  change (∫ s in Ioo 0 t, value K (A s) ((t-s)^(1/4 : ℝ)) (f s) x) =
    C (∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) 0 x)
  rw [← hc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [row_eq K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
    _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _),iteratedFDeriv_zero_eq_comp]
  exact (LinearIsometryEquiv.apply_symm_apply _ _).symm

lemma contDiff_duhamel : ContDiff ℝ 4 (duhamel K A f t) := by
  have he : duhamel K A f t = fun x => (continuousMultilinearCurryFin0 ℝ V ℂ)
      (integralRow K A f t 0 x) :=
    funext (duhamel_eq_integralRow_zero K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold)
  rw [he]
  let C : (V [×0]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    (continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  change ContDiff ℝ 4 (fun x => C (integralRow K A f t 0 x))
  exact contDiff_const.clm_apply
    (contDiff_integralRow K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold 0 4 (by omega))

lemma iteratedFDeriv_duhamel (j : ℕ) (hj : j ≤ 4) :
    iteratedFDeriv ℝ j (duhamel K A f t) = integralRow K A f t j := by
  induction j with
  | zero =>
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    change (continuousMultilinearCurryFin0 ℝ V ℂ).symm (duhamel K A f t x) = _
    rw [duhamel_eq_integralRow_zero K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold,
      LinearIsometryEquiv.symm_apply_apply]
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left,ih (by omega)]
    funext x
    dsimp only [Function.comp_apply]
    rw [(hasFDerivAt_integralRow K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j hj x).fderiv]
    exact LinearIsometryEquiv.symm_apply_apply _ _

lemma exists_norm_iteratedFDeriv_duhamel_bound (j : ℕ) (hj : j ≤ 4) :
    ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j (duhamel K A f t) x‖ ≤ C := by
  obtain ⟨b,hi,hb⟩ := SourceFrozenRows.exists_integrable_row_bound_weighted K A hA α β hα hAr L hL hAL f σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j hj
  refine ⟨∫ s in Ioo 0 t, b s,fun x => ?_⟩
  rw [iteratedFDeriv_duhamel K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j hj]
  apply norm_integral_le_of_norm_le hi
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact hb s hs x
end WeightedSourceFrozenRows

end WeightedDuhamel

end

end OAI
