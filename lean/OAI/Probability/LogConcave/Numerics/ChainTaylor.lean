import Mathlib
import OAI.Probability.LogConcave.Numerics.Basis

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω}

lemma weighted_sum_sq_varying (w : I → ℝ) (f : I → Ω → E) (B : I → ℝ)
    (hm : ∀i,AEStronglyMeasurable (f i) μ)
    (hi : ∀i,Integrable (fun y => ‖f i y‖^2) μ)
    (hB : ∀i,(∫y,‖f i y‖^2 ∂μ)≤B i) :
    Integrable (fun y => ‖∑i,w i • f i y‖^2) μ ∧
      (∫y,‖∑i,w i • f i y‖^2 ∂μ)≤(∑i,|w i|)*(∑i,|w i| *B i) := by
  have hw0 : 0≤∑i,|w i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs : Integrable (fun y => (∑i,|w i|)*(∑i,|w i| *‖f i y‖^2)) μ := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  have hmeas : AEStronglyMeasurable (fun y => ‖∑i,w i • f i y‖^2) μ := by
    have h := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => (hm i).const_smul (w i))).norm.pow 2
    convert h using 1
    ext y
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]
  have ho : Integrable (fun y => ‖∑i,w i • f i y‖^2) μ :=
    hs.mono' hmeas (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs,abs_sq] using norm_weighted_sum_sq w (fun i => f i y)))
  refine ⟨ho,(integral_mono ho hs (fun y => norm_weighted_sum_sq w (fun i => f i y))).trans ?_⟩
  rw [integral_const_mul,integral_finsetSum]
  · simp only [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _))) hw0
  · exact fun i _ => (hi i).const_mul _
end LogConcaveSampling.RMSIntegral

end

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]

theorem weighted_time_seed {f : α × β → E} {w : α → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hw : AEStronglyMeasurable w μ)
    {K B : ℝ} (hB0 : 0≤B) (hK : ∀ᵐ t ∂μ,|w t|≤K)
    (hslice : ∀ᵐ t ∂μ,Integrable (fun z => ‖f (t,z)‖^2) ν)
    (hB : ∀ᵐ t ∂μ,(∫z,‖f (t,z)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∫t,w t • f (t,z) ∂μ‖^2) ν ∧
      (∫z,‖∫t,w t • f (t,z) ∂μ‖^2 ∂ν)≤(μ.real univ)^2*K^2*B := by
  have he (t : α) (z : β) : ‖w t • f (t,z)‖^2=(w t)^2*‖f (t,z)‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hs : ∀ᵐ t ∂μ,Integrable (fun z => ‖w t • f (t,z)‖^2) ν := by
    filter_upwards [hslice] with t ht
    simp only [he]
    exact ht.const_mul _
  have hb : ∀ᵐ t ∂μ,(∫z,‖w t • f (t,z)‖^2 ∂ν)≤K^2*B := by
    filter_upwards [hK,hB] with t ht hb
    simp only [he,integral_const_mul]
    have ht2 : (w t)^2≤K^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (w t)) ht 2
    exact (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans (mul_le_mul_of_nonneg_right ht2 hB0)
  simpa only [mul_assoc] using time_seed_uniform (f:=fun p => w p.1 • f p)
    (hw.comp_fst.smul hf) hs hb
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma iteratedDerivWithin_chain (J : ℕ → ℝ → E) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t) (n : ℕ) :
    EqOn (iteratedDerivWithin n (J 0) s) (J n) s := by
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro t ht
    rw [iteratedDerivWithin_succ,derivWithin_congr ih (ih ht)]
    exact (hJ n t ht).derivWithin (hs t ht)

omit [CompleteSpace E] in
lemma contDiffOn_chain (J : ℕ → ℝ → E) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t) :
    ContDiffOn ℝ (⊤:ℕ∞) (J 0) s := by
  rw [contDiffOn_infty]
  intro n
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs]
  constructor
  · intro m _
    apply (show ContinuousOn (J m) s from fun t ht => (hJ m t ht).continuousWithinAt).congr
    intro t ht
    exact iteratedDerivWithin_chain J hs hJ m ht
  · intro m _
    apply (show DifferentiableOn ℝ (J m) s from fun t ht => (hJ m t ht).differentiableWithinAt).congr
    intro t ht
    exact iteratedDerivWithin_chain J hs hJ m ht

def chainTaylor (J : ℕ → ℝ → E) (n : ℕ) (a x : ℝ) : E :=
  ∑k∈Finset.range (n+1),((k.factorial:ℝ)⁻¹*(x-a)^k) • J k a

omit [CompleteSpace E] in
lemma chainTaylor_eq {J : ℕ → ℝ → E} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t)
    (n : ℕ) {a : ℝ} (ha : a∈s) (x : ℝ) :
    taylorWithinEval (J 0) n s a x=chainTaylor J n a x := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivWithin_chain J hs hJ k ha]

lemma chainTaylor_remainder {J : ℕ → ℝ → E} {s : Set ℝ}
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t)
    {a x : ℝ} (hsub : uIcc a x⊆s) (n : ℕ) :
    J 0 x-chainTaylor J n a x=
      ∫t in a..x,((x-t)^n/(n.factorial:ℝ)) • J (n+1) t := by
  by_cases hax : a=x
  · subst x
    simp [chainTaylor, Finset.sum_range_succ']
  have hs := uniqueDiffOn_uIcc hax
  have hJ' (n : ℕ) (t : ℝ) (ht : t∈uIcc a x) :
      HasDerivWithinAt (J n) (J (n+1) t) (uIcc a x) t := (hJ n t (hsub ht)).mono hsub
  rw [←chainTaylor_eq hs hJ' n left_mem_uIcc x,
    taylor_integral_remainder ((contDiffOn_chain J hs hJ').of_le (by exact_mod_cast (show (n+1:ℕ∞)≤⊤ from le_top)))]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [iteratedDerivWithin_chain J hs hJ' _ ht]
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set

variable {β E : Type*} [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure β} [SFinite ν]

theorem chainTaylor_remainder_rms {J : ℕ → ℝ → β → E} {s : Set ℝ} {n : ℕ} {a x B : ℝ}
    (hax : a≤x) (hB0 : 0≤B) (hsub : uIcc a x⊆s)
    (hf : ∀z n t,t∈s → HasDerivWithinAt (fun t => J n t z) (J (n+1) t z) s t)
    (hm : AEStronglyMeasurable (fun p : ℝ × β => J (n+1) p.1 p.2)
      ((volume.restrict (Ioc a x)).prod ν))
    (hi : ∀t∈Ioc a x,Integrable (fun z => ‖J (n+1) t z‖^2) ν)
    (hB : ∀t∈Ioc a x,(∫z,‖J (n+1) t z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖J 0 x z-chainTaylor (fun k t => J k t z) n a x‖^2) ν ∧
      (∫z,‖J 0 x z-chainTaylor (fun k t => J k t z) n a x‖^2 ∂ν)≤
        ((x-a)^(n+1)/(n.factorial:ℝ))^2*B := by
  let μ : Measure ℝ := volume.restrict (Ioc a x)
  let w : ℝ → ℝ := fun t => (x-t)^n/(n.factorial:ℝ)
  have hw : AEStronglyMeasurable w μ := by
    apply Continuous.aestronglyMeasurable
    dsimp [w]; fun_prop
  have hk : ∀ᵐ t ∂μ,|w t|≤(x-a)^n/(n.factorial:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact taylor_kernel_bound ht.1.le ht.2 n
  have hs : ∀ᵐ t ∂μ,Integrable (fun z => ‖J (n+1) t z‖^2) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hi t ht
  have hb : ∀ᵐ t ∂μ,(∫z,‖J (n+1) t z‖^2 ∂ν)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB t ht
  have hv := RMSIntegral.weighted_time_seed hm hw hB0 hk hs hb
  have he (z : β) : J 0 x z-chainTaylor (fun k t => J k t z) n a x=
      ∫t,w t • J (n+1) t z ∂μ := by
    rw [chainTaylor_remainder (hf z) hsub,intervalIntegral.integral_of_le hax]
  have hμ : μ.real univ=x-a := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    exact Real.volume_real_Ioc_of_le hax
  simp_rw [he]
  refine ⟨hv.1,hv.2.trans_eq ?_⟩
  rw [hμ,pow_succ]
  ring
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma chainTaylor_scaled_eval (J : ℕ → ℝ → E) (n : ℕ) (a ℓ t : ℝ) :
    chainTaylor J n a (a+ℓ*t)=
      ∑k : Fin (n+1),t^(k:ℕ) •
        (((k.val.factorial:ℝ)⁻¹*ℓ^(k:ℕ)) • J k a) := by
  unfold chainTaylor
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [show a+ℓ*t-a=ℓ*t by ring,mul_pow,smul_smul]
  congr 1
  ring

omit [CompleteSpace E] in
lemma reproduces_cell_chainTaylor (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (J : ℕ → ℝ → E) (a ℓ t : ℝ) :
    interpolation u (fun i => chainTaylor J n a (a+ℓ*u i)) t=
      chainTaylor J n a (a+ℓ*t) := by
  simp_rw [chainTaylor_scaled_eval]
  exact reproduces_vector u hu (n+1) hn _ t

omit [CompleteSpace E] in
lemma interpolation_sub_unused (u : I → ℝ) (f g : I → E) (t : ℝ) :
    interpolation u (fun i => f i-g i) t=interpolation u f t-interpolation u g t := by
  simp [interpolation,smul_sub,Finset.sum_sub_distrib]

omit [CompleteSpace E] in
lemma cell_chain_error_eq (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (J : ℕ → ℝ → E) (a ℓ t : ℝ) :
    J 0 (a+ℓ*t)-interpolation u (fun i => J 0 (a+ℓ*u i)) t=
      (J 0 (a+ℓ*t)-chainTaylor J n a (a+ℓ*t))-
        interpolation u (fun i => J 0 (a+ℓ*u i)-chainTaylor J n a (a+ℓ*u i)) t := by
  rw [interpolation_sub_unused,reproduces_cell_chainTaylor u hu n hn]
  abel
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}

omit [CompleteSpace E] in
theorem cell_chain_error_rms (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (J : ℕ → ℝ → Ω → E) (a ℓ t : ℝ) {B C : ℝ}
    (hB : 0≤B) (hC : 1≤C) (hc : ∑i,|basis u i t|≤C)
    (hm : ∀s∈insert t (Set.range u),AEStronglyMeasurable
      (fun z => J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)) ν)
    (hi : ∀s∈insert t (Set.range u),Integrable
      (fun z => ‖J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)‖^2) ν)
    (hR : ∀s∈insert t (Set.range u),(∫z,
      ‖J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖J 0 (a+ℓ*t) z-interpolation u (fun i => J 0 (a+ℓ*u i) z) t‖^2) ν ∧
      (∫z,‖J 0 (a+ℓ*t) z-interpolation u (fun i => J 0 (a+ℓ*u i) z) t‖^2 ∂ν)≤4*C^2*B := by
  let R (s : ℝ) (z : Ω) := J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)
  have hmt := hm t (mem_insert t _)
  have hmn (i : I) := hm (u i) (mem_insert_of_mem t (mem_range_self i))
  have hit := hi t (mem_insert t _)
  have hin (i : I) := hi (u i) (mem_insert_of_mem t (mem_range_self i))
  have hRn (i : I) := hR (u i) (mem_insert_of_mem t (mem_range_self i))
  have hsum := RMSIntegral.weighted_sum_sq (fun i => basis u i t) (fun i => R (u i)) hmn hin hRn
  have hms : AEStronglyMeasurable (fun z => interpolation u (fun i => R (u i) z) t) ν := by
    have hs := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (hmn i).const_smul (basis u i t))
    convert hs using 1
    ext z
    simp only [interpolation,Finset.sum_apply,Pi.smul_apply,R]
  have hsb : (∫z,‖interpolation u (fun i => R (u i) z) t‖^2 ∂ν)≤C^2*B := by
    apply hsum.2.trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hc 2) hB
  have hs := RMSIntegral.sub_sq_bound hmt hms hit hsum.1 (hR t (mem_insert t _)) hsb
  have he (z : Ω) := cell_chain_error_eq u hu n hn (fun k v => J k v z) a ℓ t
  simp_rw [he]
  refine ⟨hs.1,hs.2.trans ?_⟩
  have hc2 : 1≤C^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hc2 hB]
end LogConcaveSampling.Quadrature

end

end

end

end OAI
