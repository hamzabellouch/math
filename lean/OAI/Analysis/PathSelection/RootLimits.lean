import Mathlib
import OAI.Analysis.PathSelection.ScalarRoots

namespace OAI

/-! Clock scalar limits and limits of monic roots. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma LogMonomial.trichotomy {xs : List (ℝ → ℝ)} {M : ℝ → ℝ}
    (hM : LogMonomial xs M) (hxs : ValidClocks xs) :
    M =ᶠ[atTop] 0 ∨ Tendsto M atTop atTop ∨ Tendsto M atTop atBot := by
  induction hM with
  | base p =>
    rcases lt_trichotomy (p:ℝ) 0 with hp | hp | hp
    · exact Or.inr (Or.inr ((tendsto_const_mul_atBot_of_neg hp).mpr Real.tendsto_log_atTop))
    · exact Or.inl (Eventually.of_forall (fun t => by simp [hp]))
    · exact Or.inr (Or.inl ((tendsto_const_mul_atTop_of_pos hp).mpr Real.tendsto_log_atTop))
  | @step xs M X hM β ih =>
    by_cases hβ : β=0
    · simpa [hβ] using ih hxs.1
    · have hsmall := hM.isLittleO hxs.lower_small.1 hxs.lower_small.2
      have he : (fun t => β*X t+M t) ~[atTop] (fun t => β*X t) :=
        Asymptotics.IsEquivalent.refl.add_isLittleO (hsmall.const_mul_right hβ)
      rcases lt_or_gt_of_ne hβ with hb | hb
      · exact Or.inr (Or.inr (he.symm.tendsto_atBot
          ((tendsto_const_mul_atBot_of_neg hb).mpr hxs.2.2.1)))
      · exact Or.inr (Or.inl (he.symm.tendsto_atTop
          ((tendsto_const_mul_atTop_of_pos hb).mpr hxs.2.2.1)))

lemma ClockGerm.scalar_limits {xs : List (ℝ → ℝ)} (hxs : ValidClocks xs)
    {f : ℝ → ℂ} (hf : ClockGerm xs f) :
    (∃ c : ℂ,Tendsto f atTop (𝓝 c)) ∨ Tendsto (fun t => ‖f t‖) atTop atTop := by
  rcases hf.leading_or_zero hxs with hz | hlead
  · exact Or.inl ⟨0,tendsto_const_nhds.congr' hz.symm⟩
  obtain ⟨M,hM,c,hc,ht⟩ := hlead
  have he : ∀ t,(Real.exp (M t):ℂ)*((Real.exp (-M t):ℂ)*f t)=f t := by
    intro t
    rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,add_neg_cancel]
    simp
  rcases hM.trichotomy hxs with hz | htop | hbot
  · refine Or.inl ⟨c,ht.congr' ?_⟩
    filter_upwards [hz] with t ht
    simp only [Pi.zero_apply] at ht
    simp [ht]
  · have hg := (Real.tendsto_exp_atTop.comp htop).atTop_mul_pos
      (norm_pos_iff.mpr hc) ht.norm
    refine Or.inr (hg.congr' (Eventually.of_forall (fun t => ?_)))
    dsimp only [Function.comp_apply]
    rw [←Complex.norm_of_nonneg (Real.exp_pos (M t)).le,←norm_mul,he]
  · have hg := ((Real.tendsto_exp_atBot.comp hbot).ofReal).mul ht
    simp only [Complex.ofReal_zero,zero_mul] at hg
    exact Or.inl ⟨0,hg.congr' (Eventually.of_forall he)⟩

lemma clockEvaluation_limits (xs : List (ℝ → ℝ)) [Fact (ValidClocks xs)] :
    (clockEvaluation xs).HasScalarLimits :=
  fun a => a.value_mem.scalar_limits Fact.out

 

theorem clockField_isAlgClosed (xs : List (ℝ → ℝ)) [Fact (ValidClocks xs)] :
    IsAlgClosed (ClockField xs) :=
  (clockEvaluation xs).isAlgClosed (clockEvaluation_limits xs)
    (clockEvaluation_divisible xs) (clockEvaluation_holomorphic xs)

lemma clockEvaluation_reflected (xs : List (ℝ → ℝ)) [Fact (ValidClocks xs)] :
    (clockEvaluation xs).Reflected := by
  intro a
  exact ⟨ClockField.ofFunction (fun t => star (a.value t)) a.value_mem.conj,
    ClockField.ofFunction_value _ _⟩

 

theorem clockRealField_isRealClosed (xs : List (ℝ → ℝ)) [Fact (ValidClocks xs)] :
    IsRealClosed ((clockEvaluation xs).realPart (clockEvaluation_reflected xs)) :=
  (clockEvaluation xs).realPart_isRealClosed (clockEvaluation_limits xs)
    (clockEvaluation_divisible xs) (clockEvaluation_holomorphic xs)
    (clockEvaluation_reflected xs)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped BigOperators Polynomial
namespace DegeneratingTrees.ScalarEvaluation
variable {K α : Type*} [Field K] [Algebra ℂ K] {l : Filter α}
variable (e : ScalarEvaluation K α l)

lemma tendsto_sum {ι : Type*} (s : Finset ι) {a : ι → K} {c : ι → ℂ}
    (h : ∀ i ∈ s, Tendsto (e.value (a i)) l (𝓝 (c i))) :
    Tendsto (e.value (∑ i ∈ s,a i)) l (𝓝 (∑ i ∈ s,c i)) :=
  (tendsto_finsetSum s h).congr' (e.sum s a).symm

lemma tendsto_add {a b : K} {c d : ℂ}
    (ha : Tendsto (e.value a) l (𝓝 c)) (hb : Tendsto (e.value b) l (𝓝 d)) :
    Tendsto (e.value (a+b)) l (𝓝 (c+d)) :=
  (ha.add hb).congr' (e.add a b).symm

lemma monic_root_limit [NeBot l] (hlim : e.HasScalarLimits)
    {d : ℕ} (hd : 0 < d) (a : Fin d → K)
    (ha : ∀ i,Tendsto (e.value (a i)) l (𝓝 0))
    {r : K} (hr : (monicFamily a).eval r = 0) :
    Tendsto (e.value r) l (𝓝 0) := by
  rw [monicFamily_eval] at hr
  by_cases hz : r=0
  · subst r
    exact tendsto_const_nhds.congr' e.zero.symm
  rcases hlim r with ⟨c,hc⟩ | htop
  · have hs : Tendsto (e.value (∑ i : Fin d,a i*r^(i:ℕ))) l (𝓝 0) := by
      simpa using e.tendsto_sum Finset.univ (fun i _ => e.tendsto_mul (ha i) (e.tendsto_pow hc (i:ℕ)))
    have ht := e.tendsto_add (e.tendsto_pow hc d) hs
    rw [hr] at ht
    have he : c^d=0 := by
      simpa using tendsto_nhds_unique ht (tendsto_const_nhds.congr' e.zero.symm)
    have : c=0 := (pow_eq_zero_iff (Nat.ne_of_gt hd)).mp he
    simpa [this] using hc
  · have hi := e.tendsto_inv_of_norm_atTop htop
    have hident : (1:K)+∑ i : Fin d,a i*(r⁻¹)^(d-(i:ℕ))=0 := by
      have ht := congrArg (fun x:K => x*(r⁻¹)^d) hr
      rw [add_mul,Finset.sum_mul] at ht
      have hpower : r^d*(r⁻¹)^d=(1:K) := by rw [←mul_pow]; simp [hz]
      rw [hpower,zero_mul] at ht
      convert ht using 2
      apply Finset.sum_congr rfl
      intro i _
      have hsplit : (r⁻¹)^d = (r⁻¹)^(i:ℕ)*(r⁻¹)^(d-(i:ℕ)) := by
        rw [←pow_add,Nat.add_sub_of_le i.isLt.le]
      rw [hsplit]
      have hcanc : r^(i:ℕ)*(r⁻¹)^(i:ℕ)=(1:K) := by rw [←mul_pow]; simp [hz]
      calc
        a i*(r⁻¹)^(d-(i:ℕ)) = a i*(r^(i:ℕ)*(r⁻¹)^(i:ℕ))*(r⁻¹)^(d-(i:ℕ)) := by rw [hcanc,mul_one]
        _ = _ := by ring
    have hs : Tendsto (e.value (∑ i : Fin d,a i*(r⁻¹)^(d-(i:ℕ)))) l (𝓝 0) := by
      simpa using e.tendsto_sum Finset.univ
        (fun i _ => e.tendsto_mul (ha i) (e.tendsto_pow hi (d-(i:ℕ))))
    have ht := e.tendsto_add (tendsto_const_nhds.congr' e.one.symm) hs
    rw [hident] at ht
    have he : (1:ℂ)=0 := by
      simpa using tendsto_nhds_unique ht (tendsto_const_nhds.congr' e.zero.symm)
    exact (one_ne_zero he).elim

end DegeneratingTrees.ScalarEvaluation

 

 

 

open Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem clock_monic_root_limit (xs : List (ℝ → ℝ)) [Fact (ValidClocks xs)]
    {d : ℕ} (hd : 0 < d) (a : Fin d → ClockField xs)
    (ha : ∀ i,Tendsto (a i).value atTop (𝓝 0))
    {r : ClockField xs} (hr : (monicFamily a).eval r=0) :
    Tendsto r.value atTop (𝓝 0) :=
  (clockEvaluation xs).monic_root_limit (clockEvaluation_limits xs) hd a ha hr

 

theorem clock_exists_monic_root_limit (xs : List (ℝ → ℝ)) [Fact (ValidClocks xs)]
    {d : ℕ} (hd : 0 < d) (a : Fin d → ClockField xs)
    (ha : ∀ i,Tendsto (a i).value atTop (𝓝 0)) :
    ∃ r : ClockField xs,(monicFamily a).eval r=0 ∧
      Tendsto r.value atTop (𝓝 0) := by
  let := clockField_isAlgClosed xs
  have hdeg : (monicFamily a).degree ≠ 0 := by
    intro he
    have hn := Polynomial.natDegree_eq_of_degree_eq_some he
    rw [monicFamily_natDegree] at hn
    exact Nat.ne_of_gt hd hn
  obtain ⟨r,hr⟩ := IsAlgClosed.exists_root (monicFamily a) hdeg
  exact ⟨r,hr,clock_monic_root_limit xs hd a ha hr⟩

end DegeneratingTrees.Clock
end

end OAI
