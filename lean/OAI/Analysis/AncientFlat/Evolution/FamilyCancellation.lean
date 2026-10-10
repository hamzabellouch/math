import OAI.Analysis.AncientFlat.Regularity.SchauderCancel

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction SchwartzMap
namespace SourceFrozenCancellation
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma norm_normalized_family (k : ℝ → V → E)
    (α β : ℝ) (hk : ∀ a : V → ℝ, Continuous a → (∀ z, a z ∈ Icc α β) →
      Continuous (fun z => k (a z) z)) (hz : ∀ a ∈ Icc α β, ∫ z, k a z=0)
    (B C : V → ℝ) (hB : Integrable B) (hBw : Integrable (fun z => (1+‖z‖)*B z))
    (hBp : ∀ z, 0 ≤ B z) (hC : Integrable C) (hCw : Integrable (fun z => (1+‖z‖)*C z))
    (hCp : ∀ z, 0 ≤ C z)
    (hb : ∀ a ∈ Icc α β, ∀ z, ‖k a z‖ ≤ B z)
    (hc : ∀ a ∈ Icc α β, ∀ b ∈ Icc α β, ∀ z,
      ‖k a z-k b z‖ ≤ C z*‖a-b‖)
    (A : V → ℝ) (hA : Continuous A) (hAr : ∀ y, A y ∈ Icc α β)
    (L : ℝ) (_hL : 0 ≤ L) (hAL : ∀ x y, ‖A x-A y‖ ≤ L*‖x-y‖)
    (f : V →ᵇ ℂ) (γ H : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H)
    (hhold : ∀ x y, ‖f x-f y‖ ≤ H*‖x-y‖^γ) (r : ℝ) (hr : 0 < r) (x : V) :
    ‖∫ z, f (x-r • z) • k (A (x-r • z)) z‖ ≤
      H*r^γ*(∫ z, ‖z‖^γ*B z)+‖f‖*L*r*(∫ z, ‖z‖*C z) := by
  let a : V → ℝ := fun z => A (x-r • z)
  have ha : Continuous a := hA.comp (continuous_const.sub (continuous_const.smul continuous_id))
  have hi : Integrable (fun z => f (x-r • z) • k (a z) z) := by
    apply (hB.const_mul ‖f‖).mono'
    · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul
        (hk a ha (fun z => hAr _))).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)
  have hi₀ : Integrable (fun z => f x • k (A x) z) := by
    apply (hB.const_mul ‖f x‖).mono'
    · exact ((hk (fun _ => A x) continuous_const (fun _ => hAr x)).const_smul (f x)).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hb _ (hAr x) z) (norm_nonneg _)
  have hzero : ∫ z, f x • k (A x) z = 0 := by
    rw [integral_smul,hz (A x) (hAr x),smul_zero]
  have hiB := integrable_envelope_power B hB hBw hBp γ hγ hγ1
  have hiC : Integrable (fun z => ‖z‖*C z) := by
    simpa using integrable_envelope_power C hC hCw hCp 1 (by norm_num) le_rfl
  have hd (z : V) : ‖(x-r • z)-x‖ = r*‖z‖ := by
    rw [sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  calc
    _ = ‖∫ z, (f (x-r • z) • k (a z) z-f x • k (A x) z)‖ := by
      rw [integral_sub hi hi₀,hzero,sub_zero]
    _ ≤ ∫ z, ‖f (x-r • z) • k (a z) z-f x • k (A x) z‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, (H*r^γ)*(‖z‖^γ*B z)+(‖f‖*L*r)*(‖z‖*C z) := by
      apply integral_mono (hi.sub hi₀).norm ((hiB.const_mul _).add (hiC.const_mul _))
      intro z
      have hdec : f (x-r • z) • k (a z) z-f x • k (A x) z =
          (f (x-r • z)-f x) • k (a z) z+
          f x • (k (a z) z-k (A x) z) := by module
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [hdec]
      apply (norm_add_le _ _).trans
      rw [norm_smul,norm_smul]
      have hF : ‖f (x-r • z)-f x‖ ≤ H*r^γ*‖z‖^γ := by
        simpa only [hd,Real.mul_rpow hr.le (norm_nonneg _),mul_assoc] using hhold (x-r • z) x
      have hcoef : ‖k (a z) z-k (A x) z‖ ≤ C z*(L*r*‖z‖) := by
        exact (hc _ (hAr _) _ (hAr x) z).trans
          (mul_le_mul_of_nonneg_left (by simpa only [hd,mul_assoc] using hAL (x-r • z) x) (hCp z))
      calc
        _ ≤ (H*r^γ*‖z‖^γ)*B z+‖f‖*(C z*(L*r*‖z‖)) :=
          add_le_add (mul_le_mul hF (hb _ (hAr _) z) (norm_nonneg _) (by positivity))
            (mul_le_mul (f.norm_coe_le_norm x) hcoef (norm_nonneg _) (norm_nonneg _))
        _ = _ := by ring
    _ = _ := by rw [integral_add (hiB.const_mul _) (hiC.const_mul _),integral_const_mul,integral_const_mul]
end SourceFrozenCancellation

end

end OAI
