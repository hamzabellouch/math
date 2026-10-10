import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.VolterraMajorant

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma integral_Icc_factorial_tail (C : ℝ) (n : ℕ) {t : ℝ} (ht : 0≤t) :
    C*(∫ u in Icc (0:ℝ) t, (C*u)^n/(n.factorial:ℝ))=
      (C*t)^(n+1)/((n+1).factorial:ℝ) := by
  have he : (fun u : ℝ => (C*u)^n/(n.factorial:ℝ))=
      (fun u => (C^n/(n.factorial:ℝ))*u^n) := by funext u; simp only [mul_pow]; ring
  rw [he,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le ht,integral_pow]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,zero_pow (Nat.succ_ne_zero n),sub_zero,mul_pow]
  field_simp
  ring

lemma volterra_uniform_bound {α : Type*} (D C H : ℝ) (hD : 0≤D) (hC : 0≤C) :
    ∃ Z : ℝ, 0≤Z ∧ ∀ (U : ℝ), U≤H → ∀ (u : ℝ → α → ℝ),
      (∃ L : ℝ, 0≤L ∧ ∀ t∈Icc (0:ℝ) U, ∀ x, u t x≤L) →
      (∀ g : ℝ → ℝ, Continuous g →
        (∀ t∈Icc (0:ℝ) U, ∀ x, u t x≤g t) →
        ∀ t∈Icc (0:ℝ) U, ∀ x, u t x≤D+C*(∫ r in Icc (0:ℝ) t, 1+g r)) →
      ∀ t∈Icc (0:ℝ) U, ∀ x, u t x≤Z := by
  obtain ⟨z,hz,hm,hz1,hzv⟩ := exists_tame_volterra_majorant hD hC (show (0:ℝ)≤0 by rfl)
  refine ⟨z (max H 0),le_trans (by norm_num) (hz1 _ (le_max_right _ _)),?_⟩
  intro U hUH u hbound hv
  obtain ⟨L,hL,hb⟩ := hbound
  let g : ℕ → ℝ → ℝ := fun n t => z t+L*((C*t)^n/(n.factorial:ℝ))
  have hg (n : ℕ) : Continuous (g n) := by dsimp [g]; fun_prop
  have hind (n : ℕ) : ∀ t∈Icc (0:ℝ) U, ∀ x, u t x≤g n t := by
    induction n with
    | zero =>
      intro t ht x
      have hh := hz1 t ht.1
      simpa only [g,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,mul_one] using
        (hb t ht x).trans (show L≤z t+L by linarith)
    | succ n ih =>
      intro t ht x
      have hh := hv (g n) (hg n) ih t ht x
      have he : (∫ r in Icc (0:ℝ) t, 1+g n r)=
          (∫ r in Icc (0:ℝ) t, 1+z r)+L*(∫ r in Icc (0:ℝ) t, (C*r)^n/(n.factorial:ℝ)) := by
        have hfun : (fun r => 1+g n r)=(fun r => (1+z r)+L*((C*r)^n/(n.factorial:ℝ))) := by
          funext r; dsimp [g]; ring
        rw [hfun,integral_add,integral_const_mul]
        all_goals apply ContinuousOn.integrableOn_compact isCompact_Icc; fun_prop
      have hlow : D+C*(∫ r in Icc (0:ℝ) t, 1+z r)≤z t := by
        apply le_trans _ (hzv t ht.1)
        simp only [zero_add,one_mul]
        apply add_le_add_right (mul_le_mul_of_nonneg_left ?_ hC)
        apply setIntegral_mono_on _ _ measurableSet_Icc (fun r _ => by linarith)
        all_goals apply ContinuousOn.integrableOn_compact isCompact_Icc; fun_prop
      rw [he] at hh
      have hit := integral_Icc_factorial_tail C n ht.1
      dsimp [g]
      nlinarith
  intro t ht x
  have hlim : Tendsto (fun n => g n t) atTop (𝓝 (z t)) := by
    have hh := (Real.summable_pow_div_factorial (C*t)).tendsto_atTop_zero
    simpa only [g,mul_zero,add_zero] using tendsto_const_nhds.add (hh.const_mul L)
  exact (ge_of_tendsto hlim (Filter.Eventually.of_forall (fun n => hind n t ht x))).trans
    (hm (ht.2.trans (hUH.trans (le_max_left _ _))))

end RVM
end

end OAI
