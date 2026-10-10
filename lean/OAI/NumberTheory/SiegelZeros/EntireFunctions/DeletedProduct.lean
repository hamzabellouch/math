import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.SiegelZeros.Structure.Convergence

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.Workers.W01

theorem gamma_le_exp_mul_log {x : ℝ} (hx : 2 ≤ x) :
    Real.Gamma x ≤ Real.exp ((x + 1) * Real.log (x + 1)) := by
  let n : ℕ := ⌈x⌉₊
  have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
  have hnx : (n : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ x)).le
  have hx1 : 0 < x + 1 := by linarith
  have hlog : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  calc
    Real.Gamma x ≤ Real.Gamma ((n : ℝ) + 1) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn hx
        (show (2 : ℝ) ≤ (n : ℝ) + 1 by linarith)
        (show x ≤ (n : ℝ) + 1 by linarith)
    _ = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n
    _ ≤ ((n : ℝ) ^ n) := by exact_mod_cast Nat.factorial_le_pow n
    _ ≤ (x + 1) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg n) hnx n
    _ = Real.exp (Real.log (x + 1) * (n : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hx1]
    _ ≤ Real.exp ((x + 1) * Real.log (x + 1)) := by
      apply Real.exp_le_exp.mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hnx hlog

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.Workers.W01

open Filter Asymptotics Set
open scoped Topology

theorem global_exponential_envelope {f : ℝ → ℝ} {p : ℝ}
    (hf : ContinuousOn f (Ioi 0))
    (hdecay : f =O[atTop] (fun t : ℝ => Real.exp (-p * t))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → |f t| ≤ C * Real.exp (-p * t) := by
  obtain ⟨C₀, hC₀, hbound⟩ := hdecay.exists_pos
  obtain ⟨T, hT⟩ := eventually_atTop.1 hbound.bound
  have hcont : ContinuousOn (fun t => |f t| * Real.exp (p * t)) (Icc 1 (max 1 T)) := by
    apply ContinuousOn.mul
    · exact (hf.mono (fun t ht => lt_of_lt_of_le zero_lt_one ht.1)).abs
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (⟨1, le_rfl, le_max_left 1 T⟩ : (Icc 1 (max 1 T)).Nonempty) hcont
  let C := max C₀ (|f t₀| * Real.exp (p * t₀))
  refine ⟨C, lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro t ht
  by_cases hlarge : T ≤ t
  · have hb : |f t| ≤ C₀ * Real.exp (-p * t) := by
      simpa only [Real.norm_eq_abs, Real.abs_exp] using hT t hlarge
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hm : |f t| * Real.exp (p * t) ≤ C :=
      (hmax ⟨ht, (le_of_not_ge hlarge).trans (le_max_right _ _)⟩).trans (le_max_right _ _)
    have hm' := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-p * t)).le
    have he : Real.exp (p * t) * Real.exp (-p * t) = 1 := by
      rw [← Real.exp_add, show p * t + -p * t = 0 by ring, Real.exp_zero]
    simpa only [mul_assoc, he, mul_one] using hm'

theorem even_kernel_global_envelope (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |HurwitzZeta.evenKernel a t - (if a = 0 then 1 else 0)| ≤
        C * Real.exp (-p * t) := by
  classical
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub a
  exact ⟨p, hp, global_exponential_envelope
    ((HurwitzZeta.continuousOn_evenKernel a).sub continuousOn_const) hdecay⟩

theorem cos_kernel_global_envelope (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |HurwitzZeta.cosKernel a t - 1| ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_cosKernel_sub a
  exact ⟨p, hp, global_exponential_envelope
    ((HurwitzZeta.continuousOn_cosKernel a).sub continuousOn_const) hdecay⟩

theorem odd_kernel_global_envelope (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |HurwitzZeta.oddKernel a t| ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_oddKernel a
  exact ⟨p, hp, global_exponential_envelope (HurwitzZeta.continuousOn_oddKernel a) hdecay⟩

theorem sin_kernel_global_envelope (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |HurwitzZeta.sinKernel a t| ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_sinKernel a
  exact ⟨p, hp, global_exponential_envelope (HurwitzZeta.continuousOn_sinKernel a) hdecay⟩

theorem completed_eq_regularized {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    χ.completedLFunction s = ZMod.completedLFunction₀ χ s := by
  have hq : q ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  change ZMod.completedLFunction χ s = _
  rw [ZMod.completedLFunction_eq, χ.map_zero' hq, χ.sum_eq_zero_of_ne_one hχ]
  simp

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.Workers.W01

open Set MeasureTheory Filter

theorem mellin_integrand_envelope {f : ℝ → ℂ} {C p t : ℝ} (hC : 0 ≤ C)
    (ht : 1 ≤ t) (hf : ‖f t‖ ≤ C * Real.exp (-p * t)) (s : ℂ) :
    ‖(t : ℂ) ^ (s - 1) * f t‖ ≤
      C * (t ^ (‖s‖ + 1) * Real.exp (-p * t)) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  calc
    t ^ (s.re - 1) * ‖f t‖ ≤ t ^ (s.re - 1) * (C * Real.exp (-p * t)) :=
      mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg ht0.le _)
    _ ≤ t ^ (‖s‖ + 1) * (C * Real.exp (-p * t)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC (Real.exp_pos _).le)
      apply Real.rpow_le_rpow_of_exponent_le ht
      linarith [Complex.re_le_norm s]
    _ = _ := by ring

theorem mellin_tail_gamma_bound {f : ℝ → ℂ} {C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-p * t)) (s : ℂ) :
    ‖∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) * f t‖ ≤
      C * ((1 / p) ^ (‖s‖ + 2) * Real.Gamma (‖s‖ + 2)) := by
  let g : ℝ → ℝ := fun t => C * (t ^ (‖s‖ + 1) * Real.exp (-p * t))
  have hexp : IntegrableOn (fun t : ℝ => t ^ (‖s‖ + 1) * Real.exp (-p * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := ‖s‖ + 1) (p := (1 : ℝ)) (b := p)
        (by linarith [norm_nonneg s]) zero_lt_one hp)
  have hg : IntegrableOn g (Ioi 0) := hexp.const_mul C
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 :=
    Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num)
  have hnorm : ‖∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) * f t‖ ≤ ∫ t in Ioi 1, g t := by
    apply norm_integral_le_of_norm_le (hg.mono_set hsub)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mellin_integrand_envelope hC ht.le (hf t ht.le) s
  have hmono : (∫ t in Ioi 1, g t) ≤ ∫ t in Ioi 0, g t := by
    apply setIntegral_mono_set hg
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_nonneg hC (mul_nonneg (Real.rpow_pos_of_pos ht _).le (Real.exp_pos _).le)
    · exact Filter.Eventually.of_forall hsub
  calc
    _ ≤ ∫ t in Ioi 0, g t := hnorm.trans hmono
    _ = C * ((1 / p) ^ (‖s‖ + 2) * Real.Gamma (‖s‖ + 2)) := by
      rw [show g = (fun t : ℝ => C * (t ^ (‖s‖ + 1) * Real.exp (-p * t))) from rfl,
        integral_const_mul]
      congr 1
      simpa only [show ‖s‖ + 2 - 1 = ‖s‖ + 1 by ring, neg_mul] using
        Real.integral_rpow_mul_exp_neg_mul_Ioi (a := ‖s‖ + 2) (by positivity) hp

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.Workers.W01

open Set MeasureTheory

theorem mellin_tail_order_one_bound {f : ℝ → ℂ} {C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-p * t)) (s : ℂ) :
    ‖∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) * f t‖ ≤
      C * Real.exp ((‖s‖ + 2) * |Real.log (1 / p)| +
        (‖s‖ + 3) * Real.log (‖s‖ + 3)) := by
  have hn : 0 ≤ ‖s‖ + 2 := by positivity
  have hg := gamma_le_exp_mul_log (x := ‖s‖ + 2) (by linarith [norm_nonneg s])
  have hp' : 0 < (1 / p : ℝ) := one_div_pos.mpr hp
  have hpow : (1 / p) ^ (‖s‖ + 2) ≤ Real.exp ((‖s‖ + 2) * |Real.log (1 / p)|) := by
    rw [Real.rpow_def_of_pos hp']
    apply Real.exp_le_exp.mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (le_abs_self (Real.log (1 / p))) hn
  calc
    _ ≤ C * ((1 / p) ^ (‖s‖ + 2) * Real.Gamma (‖s‖ + 2)) :=
      mellin_tail_gamma_bound hC hp hf s
    _ ≤ C * (Real.exp ((‖s‖ + 2) * |Real.log (1 / p)|) *
        Real.exp ((‖s‖ + 3) * Real.log (‖s‖ + 3))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply mul_le_mul hpow
      · simpa only [show ‖s‖ + 2 + 1 = ‖s‖ + 3 by ring] using hg
      · exact Real.Gamma_nonneg_of_nonneg hn
      · exact (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.Workers.W01

open Set MeasureTheory Complex

theorem mellin_upper_indicator (f : ℝ → ℂ) (s : ℂ) :
    mellin ((Ioi (1 : ℝ)).indicator f) s =
      ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) * f t := by
  simp only [mellin, ← indicator_smul]
  rw [setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (show Ioi (1 : ℝ) ⊆ Ioi 0 from Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))]
  rfl

theorem strong_lower_mellin (P : WeakFEPair ℂ) (hP : IsStrongFEPair P) (s : ℂ) :
    mellin ((Ioo (0 : ℝ) 1).indicator P.f) s =
      P.ε • mellin ((Ioi (1 : ℝ)).indicator P.g) ((P.k : ℂ) - s) := by
  cases hP
  let u := (Ioi (1 : ℝ)).indicator P.g
  have hpoint (t : ℝ) (ht : 0 < t) :
      (Ioo (0 : ℝ) 1).indicator P.f t =
        P.ε • ((t : ℂ) ^ (-(P.k : ℂ)) • u t⁻¹) := by
    by_cases hlt : t < 1
    · have hinv : 1 < t⁻¹ := by rwa [one_lt_inv₀ ht]
      rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht, hlt⟩)]
      dsimp only [u]
      rw [indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hinv),
        ← one_div, P.h_feq' t ht]
      simp only [smul_eq_mul]
      rw [cpow_neg, ofReal_cpow ht.le]
      have hn : ((t ^ P.k : ℝ) : ℂ) ≠ 0 :=
        ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht P.k).ne'
      have hnc : (t : ℂ) ^ (P.k : ℂ) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr ht.ne'))
      field_simp [P.hε, hn, hnc]
    · have hinv : ¬ 1 < t⁻¹ := by simpa only [one_lt_inv₀ ht] using hlt
      rw [indicator_of_notMem (show t ∉ Ioo (0 : ℝ) 1 from fun h => hlt (mem_Ioo.mp h).2)]
      dsimp only [u]
      rw [indicator_of_notMem (show t⁻¹ ∉ Ioi (1 : ℝ) from hinv), smul_zero, smul_zero]
  calc
    _ = mellin (fun t : ℝ => P.ε • ((t : ℂ) ^ (-(P.k : ℂ)) • u t⁻¹)) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [hpoint t (mem_Ioi.mp ht)]
    _ = P.ε • mellin u ((P.k : ℂ) - s) := by
      rw [mellin_const_smul, mellin_cpow_smul, mellin_comp_inv]
      congr 2
      ring

theorem strong_mellin_split (P : WeakFEPair ℂ) (hP : IsStrongFEPair P) (s : ℂ) :
    P.Λ s =
      (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) * P.f t) +
      P.ε • (∫ t : ℝ in Ioi 1, (t : ℂ) ^ ((P.k : ℂ) - s - 1) * P.g t) := by
  have hi := (hP.hasMellin s).1
  have hlo : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f t) (Ioc 0 1) :=
    hi.mono_set Ioc_subset_Ioi_self
  have hup : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f t) (Ioi 1) :=
    hi.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  have hlower : (∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (s - 1) • P.f t) =
      mellin ((Ioo (0 : ℝ) 1).indicator P.f) s := by
    rw [integral_Ioc_eq_integral_Ioo]
    simp only [mellin, ← indicator_smul]
    rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self]
  rw [hP.Λ_eq, mellin, ← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) zero_le_one,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hlo hup,
    hlower, strong_lower_mellin P hP, mellin_upper_indicator]
  simp only [smul_eq_mul]
  exact add_comm _ _

theorem weak_regularized_mellin_split (P : WeakFEPair ℂ) (s : ℂ) :
    P.Λ₀ s =
      (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) * (P.f t - P.f₀)) +
      P.ε • (∫ t : ℝ in Ioi 1,
        (t : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g t - P.g₀)) := by
  have hs := strong_mellin_split P.toStrongFEPair P.isStrongFEPair_toStrongFEPair s
  rw [P.isStrongFEPair_toStrongFEPair.Λ_eq] at hs
  change P.Λ₀ s = _ at hs
  rw [hs]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hnot : t ∉ Ioo (0 : ℝ) 1 := by
      intro h
      exact (not_lt_of_ge (mem_Ioi.mp ht).le) (mem_Ioo.mp h).2
    simp only [WeakFEPair.toStrongFEPair, WeakFEPair.f_modif, Pi.add_apply,
      indicator_of_mem ht, indicator_of_notMem hnot, add_zero]
  · congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hnot : t ∉ Ioo (0 : ℝ) 1 := by
      intro h
      exact (not_lt_of_ge (mem_Ioi.mp ht).le) (mem_Ioo.mp h).2
    simp only [WeakFEPair.toStrongFEPair, WeakFEPair.f_modif, WeakFEPair.symm,
      Pi.add_apply, indicator_of_mem ht, indicator_of_notMem hnot, add_zero]

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.Workers.W01

open Set MeasureTheory Complex HurwitzZeta

noncomputable def tailGrowth (p : ℝ) (s : ℂ) : ℝ :=
  Real.exp ((‖s‖ + 2) * |Real.log (1 / p)| +
    (‖s‖ + 3) * Real.log (‖s‖ + 3))

theorem weak_regularized_growth (P : WeakFEPair ℂ)
    {p₁ p₂ C₁ C₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖P.f t - P.f₀‖ ≤ C₁ * Real.exp (-p₁ * t))
    (hg : ∀ t : ℝ, 1 ≤ t → ‖P.g t - P.g₀‖ ≤ C₂ * Real.exp (-p₂ * t)) (s : ℂ) :
    ‖P.Λ₀ s‖ ≤ C₁ * tailGrowth p₁ s + ‖P.ε‖ * (C₂ * tailGrowth p₂ ((P.k : ℂ) - s)) := by
  rw [weak_regularized_mellin_split]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact mellin_tail_order_one_bound hC₁ hp₁ hf s
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (mellin_tail_order_one_bound hC₂ hp₂ hg ((P.k : ℂ) - s)) (norm_nonneg _)

theorem strong_mellin_growth (P : WeakFEPair ℂ) (hP : IsStrongFEPair P)
    {p₁ p₂ C₁ C₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖P.f t‖ ≤ C₁ * Real.exp (-p₁ * t))
    (hg : ∀ t : ℝ, 1 ≤ t → ‖P.g t‖ ≤ C₂ * Real.exp (-p₂ * t)) (s : ℂ) :
    ‖P.Λ s‖ ≤ C₁ * tailGrowth p₁ s + ‖P.ε‖ * (C₂ * tailGrowth p₂ ((P.k : ℂ) - s)) := by
  rw [strong_mellin_split P hP]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact mellin_tail_order_one_bound hC₁ hp₁ hf s
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (mellin_tail_order_one_bound hC₂ hp₂ hg ((P.k : ℂ) - s)) (norm_nonneg _)

theorem completed_even_growth (a : UnitAddCircle) :
    ∃ p₁ > 0, ∃ p₂ > 0, ∃ C₁ > 0, ∃ C₂ > 0, ∀ s : ℂ,
      ‖completedHurwitzZetaEven₀ a s‖ ≤
        (C₁ * tailGrowth p₁ (s / 2) + C₂ * tailGrowth p₂ ((1 : ℂ) / 2 - s / 2)) / 2 := by
  classical
  obtain ⟨p₁, hp₁, C₁, hC₁, hf⟩ := even_kernel_global_envelope a
  obtain ⟨p₂, hp₂, C₂, hC₂, hg⟩ := cos_kernel_global_envelope a
  refine ⟨p₁, hp₁, p₂, hp₂, C₁, hC₁, C₂, hC₂, fun s => ?_⟩
  have hnorm (x : ℝ) : ‖(x : ℂ) - 1‖ = |x - 1| := by
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  have hf' : ∀ t : ℝ, 1 ≤ t →
      ‖(hurwitzEvenFEPair a).f t - (hurwitzEvenFEPair a).f₀‖ ≤ C₁ * Real.exp (-p₁ * t) := by
    intro t ht
    by_cases ha : a = 0
    · simpa [hurwitzEvenFEPair, ha, hnorm, norm_real, Real.norm_eq_abs] using hf t ht
    · simpa [hurwitzEvenFEPair, ha, norm_real, Real.norm_eq_abs] using hf t ht
  have hg' : ∀ t : ℝ, 1 ≤ t →
      ‖(hurwitzEvenFEPair a).g t - (hurwitzEvenFEPair a).g₀‖ ≤ C₂ * Real.exp (-p₂ * t) := by
    intro t ht
    simpa [hurwitzEvenFEPair, hnorm, norm_real, Real.norm_eq_abs] using hg t ht
  have hb := weak_regularized_growth (hurwitzEvenFEPair a)
    hp₁ hp₂ hC₁.le hC₂.le hf' hg' (s / 2)
  rw [completedHurwitzZetaEven₀, norm_div, norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  simpa [hurwitzEvenFEPair] using hb

theorem completed_odd_growth (a : UnitAddCircle) :
    ∃ p₁ > 0, ∃ p₂ > 0, ∃ C₁ > 0, ∃ C₂ > 0, ∀ s : ℂ,
      ‖completedHurwitzZetaOdd a s‖ ≤
        (C₁ * tailGrowth p₁ ((s + 1) / 2) +
          C₂ * tailGrowth p₂ ((3 : ℂ) / 2 - (s + 1) / 2)) / 2 := by
  obtain ⟨p₁, hp₁, C₁, hC₁, hf⟩ := odd_kernel_global_envelope a
  obtain ⟨p₂, hp₂, C₂, hC₂, hg⟩ := sin_kernel_global_envelope a
  refine ⟨p₁, hp₁, p₂, hp₂, C₁, hC₁, C₂, hC₂, fun s => ?_⟩
  have hf' : ∀ t : ℝ, 1 ≤ t → ‖(hurwitzOddFEPair a).f t‖ ≤ C₁ * Real.exp (-p₁ * t) := by
    intro t ht
    simpa [hurwitzOddFEPair, norm_real, Real.norm_eq_abs] using hf t ht
  have hg' : ∀ t : ℝ, 1 ≤ t → ‖(hurwitzOddFEPair a).g t‖ ≤ C₂ * Real.exp (-p₂ * t) := by
    intro t ht
    simpa [hurwitzOddFEPair, norm_real, Real.norm_eq_abs] using hg t ht
  have hb := strong_mellin_growth (hurwitzOddFEPair a)
    (isStrong_hurwitzOddFEPair a) hp₁ hp₂ hC₁.le hC₂.le hf' hg' ((s + 1) / 2)
  rw [completedHurwitzZetaOdd, norm_div, norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  simpa [hurwitzOddFEPair] using hb

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.Workers.W01

open Complex HurwitzZeta

noncomputable def radiusLog (s : ℂ) : ℝ := (‖s‖ + 5) * (1 + Real.log (‖s‖ + 5))

theorem radiusLog_ge_one (s : ℂ) : 1 ≤ radiusLog s := by
  have hn := norm_nonneg s
  have hl : 0 ≤ Real.log (‖s‖ + 5) := Real.log_nonneg (by linarith)
  dsimp [radiusLog]
  nlinarith

theorem tailGrowth_le_radiusLog (p : ℝ) {z s : ℂ} (hz : ‖z‖ ≤ ‖s‖ + 2) :
    tailGrowth p z ≤ Real.exp ((|Real.log (1 / p)| + 1) * radiusLog s) := by
  have hn := norm_nonneg s
  have hnz := norm_nonneg z
  have ha := abs_nonneg (Real.log (1 / p))
  have hlz : 0 ≤ Real.log (‖z‖ + 3) := Real.log_nonneg (by linarith)
  have hl : 0 ≤ Real.log (‖s‖ + 5) := Real.log_nonneg (by linarith)
  have hlog : Real.log (‖z‖ + 3) ≤ Real.log (‖s‖ + 5) :=
    Real.log_le_log (by positivity) (by linarith)
  have h1 := mul_le_mul_of_nonneg_right (show ‖z‖ + 2 ≤ ‖s‖ + 5 by linarith) ha
  have h2 := mul_le_mul (show ‖z‖ + 3 ≤ ‖s‖ + 5 by linarith) hlog hlz (by positivity)
  have hprod : 0 ≤ |Real.log (1 / p)| * ((‖s‖ + 5) * Real.log (‖s‖ + 5)) := by positivity
  apply Real.exp_le_exp.mpr
  dsimp [radiusLog]
  nlinarith

theorem coeff_tailGrowth_le (C p : ℝ) (hC : 0 ≤ C) {z s : ℂ}
    (hz : ‖z‖ ≤ ‖s‖ + 2) :
    C * tailGrowth p z ≤ Real.exp ((C + |Real.log (1 / p)| + 1) * radiusLog s) := by
  have hR := radiusLog_ge_one s
  have hce : C ≤ Real.exp (C * radiusLog s) := by
    have hmul : C ≤ C * radiusLog s := by nlinarith
    exact (hmul.trans (by linarith [Real.add_one_le_exp (C * radiusLog s)]))
  calc
    _ ≤ Real.exp (C * radiusLog s) * Real.exp ((|Real.log (1 / p)| + 1) * radiusLog s) :=
      mul_le_mul hce (tailGrowth_le_radiusLog p hz) (show 0 ≤ tailGrowth p z from (Real.exp_pos _).le) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem pair_tailGrowth_le (C₁ C₂ p₁ p₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    {z₁ z₂ s : ℂ} (h₁ : ‖z₁‖ ≤ ‖s‖ + 2) (h₂ : ‖z₂‖ ≤ ‖s‖ + 2) :
    (C₁ * tailGrowth p₁ z₁ + C₂ * tailGrowth p₂ z₂) / 2 ≤
      Real.exp ((C₁ + C₂ + |Real.log (1 / p₁)| + |Real.log (1 / p₂)| + 2) * radiusLog s) := by
  let A := C₁ + C₂ + |Real.log (1 / p₁)| + |Real.log (1 / p₂)| + 2
  have hR : 0 ≤ radiusLog s := (radiusLog_ge_one s).trans' zero_le_one
  have hb₁ : C₁ * tailGrowth p₁ z₁ ≤ Real.exp (A * radiusLog s) := by
    refine (coeff_tailGrowth_le C₁ p₁ hC₁ h₁).trans (Real.exp_le_exp.mpr ?_)
    apply mul_le_mul_of_nonneg_right _ hR
    dsimp [A]
    linarith [abs_nonneg (Real.log (1 / p₂))]
  have hb₂ : C₂ * tailGrowth p₂ z₂ ≤ Real.exp (A * radiusLog s) := by
    refine (coeff_tailGrowth_le C₂ p₂ hC₂ h₂).trans (Real.exp_le_exp.mpr ?_)
    apply mul_le_mul_of_nonneg_right _ hR
    dsimp [A]
    linarith [abs_nonneg (Real.log (1 / p₁))]
  change _ ≤ Real.exp (A * radiusLog s)
  linarith

theorem completed_even_radius_growth (a : UnitAddCircle) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ,
      ‖completedHurwitzZetaEven₀ a s‖ ≤ Real.exp (A * radiusLog s) := by
  obtain ⟨p₁, hp₁, p₂, hp₂, C₁, hC₁, C₂, hC₂, hb⟩ := completed_even_growth a
  refine ⟨C₁ + C₂ + |Real.log (1 / p₁)| + |Real.log (1 / p₂)| + 2, by positivity, fun s => ?_⟩
  refine (hb s).trans (pair_tailGrowth_le C₁ C₂ p₁ p₂ hC₁.le hC₂.le ?_ ?_)
  · rw [norm_div, norm_ofNat]
    linarith [norm_nonneg s]
  · calc
      ‖(1 : ℂ) / 2 - s / 2‖ ≤ ‖(1 : ℂ) / 2‖ + ‖s / 2‖ := norm_sub_le _ _
      _ ≤ ‖s‖ + 2 := by simp only [norm_div, norm_one, norm_ofNat]; linarith [norm_nonneg s]

theorem completed_odd_radius_growth (a : UnitAddCircle) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ,
      ‖completedHurwitzZetaOdd a s‖ ≤ Real.exp (A * radiusLog s) := by
  obtain ⟨p₁, hp₁, p₂, hp₂, C₁, hC₁, C₂, hC₂, hb⟩ := completed_odd_growth a
  refine ⟨C₁ + C₂ + |Real.log (1 / p₁)| + |Real.log (1 / p₂)| + 2, by positivity, fun s => ?_⟩
  have hsn : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s 1
  refine (hb s).trans (pair_tailGrowth_le C₁ C₂ p₁ p₂ hC₁.le hC₂.le ?_ ?_)
  · rw [norm_div, norm_ofNat]
    linarith [norm_nonneg s]
  · calc
      ‖(3 : ℂ) / 2 - (s + 1) / 2‖ ≤ ‖(3 : ℂ) / 2‖ + ‖(s + 1) / 2‖ := norm_sub_le _ _
      _ ≤ ‖s‖ + 2 := by simp only [norm_div, norm_ofNat]; linarith [norm_nonneg s]

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.Workers.W01

open Complex HurwitzZeta Finset

theorem completed_norm_le_common_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) {E : ℝ}
    (he : ∀ j : ZMod q, ‖completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤ E)
    (ho : ∀ j : ZMod q, ‖completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤ E) :
    ‖χ.completedLFunction s‖ ≤ 2 * (q : ℝ) * ‖(q : ℂ) ^ (-s)‖ * E := by
  have he' : ‖∑ j : ZMod q, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤ (q : ℝ) * E := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _j : ZMod q, E := by
        apply sum_le_sum
        intro j _
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (χ.norm_le_one j) (norm_nonneg _)).trans (by simpa using he j)
      _ = _ := by simp [ZMod.card, nsmul_eq_mul]
  have ho' : ‖∑ j : ZMod q, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤ (q : ℝ) * E := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _j : ZMod q, E := by
        apply sum_le_sum
        intro j _
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (χ.norm_le_one j) (norm_nonneg _)).trans (by simpa using ho j)
      _ = _ := by simp [ZMod.card, nsmul_eq_mul]
  rw [completed_eq_regularized χ hχ s, ZMod.completedLFunction₀]
  calc
    _ ≤ ‖(q : ℂ) ^ (-s)‖ * ‖∑ j : ZMod q, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ +
        ‖(q : ℂ) ^ (-s)‖ * ‖∑ j : ZMod q, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ := by
      simpa only [norm_mul] using norm_add_le
        ((q : ℂ) ^ (-s) * ∑ j : ZMod q, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s)
        ((q : ℂ) ^ (-s) * ∑ j : ZMod q, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s)
    _ ≤ ‖(q : ℂ) ^ (-s)‖ * ((q : ℝ) * E) + ‖(q : ℂ) ^ (-s)‖ * ((q : ℝ) * E) :=
      add_le_add (mul_le_mul_of_nonneg_left he' (norm_nonneg _))
        (mul_le_mul_of_nonneg_left ho' (norm_nonneg _))
    _ = _ := by ring

theorem completed_radius_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, ‖χ.completedLFunction s‖ ≤ Real.exp (A * radiusLog s) := by
  classical
  choose Ae hAe hbe using (fun j : ZMod q => completed_even_radius_growth (ZMod.toAddCircle j))
  choose Ao hAo hbo using (fun j : ZMod q => completed_odd_radius_growth (ZMod.toAddCircle j))
  let B : ℝ := (∑ j : ZMod q, Ae j) + ∑ j : ZMod q, Ao j
  have hse : 0 ≤ ∑ j : ZMod q, Ae j := sum_nonneg (fun j _ => (hAe j).le)
  have hso : 0 ≤ ∑ j : ZMod q, Ao j := sum_nonneg (fun j _ => (hAo j).le)
  have hB : 0 ≤ B := add_nonneg hse hso
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let A := B + |Real.log (q : ℝ)| + 2 * (q : ℝ) + 1
  refine ⟨A, by dsimp [A]; positivity, fun s => ?_⟩
  have hR := radiusLog_ge_one s
  have hR0 : 0 ≤ radiusLog s := le_trans zero_le_one hR
  have he : ∀ j : ZMod q, ‖completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤ Real.exp (B * radiusLog s) := by
    intro j
    refine (hbe j s).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hR0))
    exact (single_le_sum (fun i _ => (hAe i).le) (mem_univ j)).trans (le_add_of_nonneg_right hso)
  have ho : ∀ j : ZMod q, ‖completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤ Real.exp (B * radiusLog s) := by
    intro j
    refine (hbo j s).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hR0))
    exact (single_le_sum (fun i _ => (hAo i).le) (mem_univ j)).trans (le_add_of_nonneg_left hse)
  have hnormR : ‖s‖ ≤ radiusLog s := by
    have hl : 0 ≤ Real.log (‖s‖ + 5) := Real.log_nonneg (by linarith [norm_nonneg s])
    dsimp [radiusLog]
    nlinarith [norm_nonneg s]
  have hpow : ‖(q : ℂ) ^ (-s)‖ ≤ Real.exp (|Real.log (q : ℝ)| * radiusLog s) := by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hq, Real.rpow_def_of_pos hq]
    apply Real.exp_le_exp.mpr
    have hr : |(-s).re| ≤ ‖s‖ := by simpa using abs_re_le_norm (-s)
    have h1 : Real.log (q : ℝ) * (-s).re ≤ |Real.log (q : ℝ)| * |(-s).re| :=
      (le_abs_self _).trans_eq (abs_mul _ _)
    exact h1.trans (mul_le_mul_of_nonneg_left (hr.trans hnormR) (abs_nonneg _))
  have hc : 2 * (q : ℝ) ≤ Real.exp ((2 * (q : ℝ)) * radiusLog s) := by
    have hm : 2 * (q : ℝ) ≤ (2 * (q : ℝ)) * radiusLog s := by nlinarith
    linarith [Real.add_one_le_exp ((2 * (q : ℝ)) * radiusLog s)]
  calc
    _ ≤ 2 * (q : ℝ) * ‖(q : ℂ) ^ (-s)‖ * Real.exp (B * radiusLog s) :=
      completed_norm_le_common_bound χ hχ s he ho
    _ ≤ (Real.exp ((2 * (q : ℝ)) * radiusLog s) *
        Real.exp (|Real.log (q : ℝ)| * radiusLog s)) * Real.exp (B * radiusLog s) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul hc hpow (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((B + |Real.log (q : ℝ)| + 2 * (q : ℝ)) * radiusLog s) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (A * radiusLog s) := by
      apply Real.exp_le_exp.mpr
      dsimp [A]
      nlinarith

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.Workers.W01

open Complex

theorem radiusLog_le_standard (s : ℂ) :
    radiusLog s ≤ 35 * ((1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  have hn := norm_nonneg s
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hthree : Real.log 3 ≤ (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hlower : (1 / 2 : ℝ) ≤ Real.log (2 + ‖s‖) :=
    htwo.trans (Real.log_le_log (by norm_num) (by linarith))
  have hshift : Real.log (‖s‖ + 5) ≤ 2 + Real.log (2 + ‖s‖) := by
    calc
      _ ≤ Real.log (3 * (2 + ‖s‖)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 3 + Real.log (2 + ‖s‖) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ _ := by linarith
  have h1 : ‖s‖ + 5 ≤ 5 * (1 + ‖s‖) := by linarith
  have h2 : 1 + Real.log (‖s‖ + 5) ≤ 7 * Real.log (2 + ‖s‖) := by linarith
  have hpos : 0 ≤ 1 + Real.log (‖s‖ + 5) := by
    have h := Real.log_nonneg (show 1 ≤ ‖s‖ + 5 by linarith)
    linarith
  have hmul := mul_le_mul h1 h2 hpos (show 0 ≤ 5 * (1 + ‖s‖) by positivity)
  dsimp [radiusLog]
  nlinarith

theorem normalized_radius_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ,
      ‖SiegelZerosAwei.W51.normalizedCompletion χ s‖ ≤ Real.exp (A * radiusLog s) := by
  obtain ⟨A, hA, hb⟩ := completed_radius_growth χ hχ
  refine ⟨A + |Real.log (q : ℝ)|, by positivity, fun s => ?_⟩
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hnormR : ‖s‖ ≤ radiusLog s := by
    have hl : 0 ≤ Real.log (‖s‖ + 5) := Real.log_nonneg (by linarith [norm_nonneg s])
    dsimp [radiusLog]
    nlinarith [norm_nonneg s]
  have hp : ‖(q : ℂ) ^ (s / 2)‖ ≤ Real.exp (|Real.log (q : ℝ)| * radiusLog s) := by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hq, Real.rpow_def_of_pos hq]
    apply Real.exp_le_exp.mpr
    have hs : |(s / 2).re| ≤ radiusLog s := by
      refine (abs_re_le_norm (s / 2)).trans ?_
      rw [norm_div, norm_ofNat]
      linarith [norm_nonneg s]
    calc
      Real.log (q : ℝ) * (s / 2).re ≤ |Real.log (q : ℝ)| * |(s / 2).re| :=
        (le_abs_self _).trans_eq (abs_mul _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  rw [SiegelZerosAwei.W51.normalizedCompletion, norm_mul]
  calc
    _ ≤ Real.exp (|Real.log (q : ℝ)| * radiusLog s) * Real.exp (A * radiusLog s) :=
      mul_le_mul hp (hb s) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem normalizedCompletion_order_one_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖SiegelZerosAwei.W51.normalizedCompletion χ z‖ ≤
        Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨A, hA, hb⟩ := normalized_radius_growth χ hχ
  refine ⟨35 * A, by positivity, fun z => ?_⟩
  refine (hb z).trans (Real.exp_le_exp.mpr ?_)
  have h := mul_le_mul_of_nonneg_left (radiusLog_le_standard z) hA.le
  nlinarith

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.W03

theorem differentiable_indexedGenusOneProduct {ι : Type*} (ρ : ι → ℂ)
    (hρ : ∀ i, ρ i ≠ 0) (hsquare : Summable (fun i => 1 / ‖ρ i‖ ^ 2))
    (hfar : ∀ R : ℝ, ∀ᶠ i in Filter.cofinite, R ≤ ‖ρ i‖) :
    Differentiable ℂ (fun z => ∏' i, genusOneFactor (ρ i) z) := by
  classical
  intro z
  have ht := multipliableLocallyUniformlyOn_genusOne ρ hρ hsquare
    (R := ‖z‖ + 1) (by positivity) (hfar (‖z‖ + 1))
  have hfinite : ∀ t : Finset ι,
      DifferentiableOn ℂ (fun w => ∏ i ∈ t, genusOneFactor (ρ i) w)
        (Metric.ball 0 (‖z‖ + 1)) := by
    intro t
    exact (Differentiable.fun_finsetProd
      (fun i _ => differentiable_genusOneFactor (ρ i))).differentiableOn
  have hd := ht.hasProdLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall hfinite) Metric.isOpen_ball
  apply hd.differentiableAt
  apply Metric.isOpen_ball.mem_nhds
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖z‖

variable {q : ℕ} [NeZero q]

theorem actual_zero_inverse_square_summable (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) :
    Summable (fun i : W51.ZeroIndex χ => 1 / ‖W51.zeroValue χ i‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ :=
    SiegelZerosAwei.Workers.W01.normalizedCompletion_order_one_growth χ hχ
  exact actual_zero_inverse_square_summable_of_growth χ hχ hprimitive hC.le hbound

noncomputable def zeroSubproduct (χ : DirichletCharacter ℂ q)
    (S : Set (W51.ZeroIndex χ)) (z : ℂ) : ℂ :=
  ∏' i : S, genusOneFactor (W51.zeroValue χ i.val) z

theorem zeroSubfamily_inverse_square_summable (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) (S : Set (W51.ZeroIndex χ)) :
    Summable (fun i : S => 1 / ‖W51.zeroValue χ i.val‖ ^ 2) :=
  (actual_zero_inverse_square_summable χ hχ hprimitive).subtype S

theorem zeroSubfamily_cofinite_far (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (S : Set (W51.ZeroIndex χ)) (R : ℝ) :
    ∀ᶠ i : S in Filter.cofinite, R ≤ ‖W51.zeroValue χ i.val‖ :=
  (Subtype.val_injective.tendsto_cofinite).eventually
    (W51.zeroValue_cofinite_far χ hχ R)

theorem differentiable_zeroSubproduct (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) (S : Set (W51.ZeroIndex χ)) :
    Differentiable ℂ (zeroSubproduct χ S) :=
  differentiable_indexedGenusOneProduct (fun i : S => W51.zeroValue χ i.val)
    (fun i => actual_zeroValue_ne_zero χ hχ hprimitive i.val)
    (zeroSubfamily_inverse_square_summable χ hχ hprimitive S)
    (zeroSubfamily_cofinite_far χ hχ S)

theorem zeroSubproduct_ne_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) (S : Set (W51.ZeroIndex χ))
    {z : ℂ} (hz : ∀ i ∈ S, z ≠ W51.zeroValue χ i) : zeroSubproduct χ S z ≠ 0 :=
  genusOneProduct_ne_zero (fun i : S => W51.zeroValue χ i.val)
    (fun i => actual_zeroValue_ne_zero χ hχ hprimitive i.val)
    (zeroSubfamily_inverse_square_summable χ hχ hprimitive S)
    (fun i => hz i.val i.property)
    (zeroSubfamily_cofinite_far χ hχ S ‖z‖)

theorem actual_genusOneProduct_multipliable (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) (z : ℂ) :
    Multipliable (fun i : W51.ZeroIndex χ => genusOneFactor (W51.zeroValue χ i) z) := by
  have ht := multipliableLocallyUniformlyOn_genusOne (W51.zeroValue χ)
    (actual_zeroValue_ne_zero χ hχ hprimitive)
    (actual_zero_inverse_square_summable χ hχ hprimitive)
    (R := ‖z‖ + 1) (by positivity) (W51.zeroValue_cofinite_far χ hχ (‖z‖ + 1))
  exact ht.multipliable (by
    simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖z‖)

theorem multipliable_zeroSubproduct (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) (S : Set (W51.ZeroIndex χ)) (z : ℂ) :
    Multipliable (fun i : S => genusOneFactor (W51.zeroValue χ i.val) z) := by
  have ht := multipliableLocallyUniformlyOn_genusOne
    (fun i : S => W51.zeroValue χ i.val)
    (fun i => actual_zeroValue_ne_zero χ hχ hprimitive i.val)
    (zeroSubfamily_inverse_square_summable χ hχ hprimitive S)
    (R := ‖z‖ + 1) (by positivity)
    (zeroSubfamily_cofinite_far χ hχ S (‖z‖ + 1))
  exact ht.multipliable (by
    simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖z‖)

theorem deleted_root_subproduct_ne_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    (r : {z : ℂ // W51.normalizedCompletion χ z = 0}) :
    zeroSubproduct χ {i : W51.ZeroIndex χ | i.1 ≠ r} r.val ≠ 0 := by
  apply zeroSubproduct_ne_zero χ hχ hprimitive
  intro i hi heq
  apply hi
  apply Subtype.val_injective
  exact heq.symm

end SiegelZerosAwei.W03

end

end SiegelZeros

end OAI
