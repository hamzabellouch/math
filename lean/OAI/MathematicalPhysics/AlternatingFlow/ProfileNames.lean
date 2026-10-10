import OAI.MathematicalPhysics.AlternatingFlow.ExpNames

namespace OAI

section ProfileNamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma rat_max : Primrec₂ (fun x y : ℚ => max x y) :=
  (Primrec.ite Arithmetic.rat_le Primrec.snd Primrec.fst).of_eq (by intro z; simp [max_def])

lemma Named.inv_of_lower {A : Type*} [Primcodable A] {f : A → ℝ}
    (hf : Named f) (b : A → ℚ) (hb : Computable b) (hpos : ∀ x, 0 < b x)
    (hlower : ∀ x, (b x : ℝ) ≤ f x) : Named (fun x => (f x)⁻¹) := by
  obtain ⟨a,ha,he⟩ := hf
  let c : A × ℕ → ℚ := fun z => max (b z.1) (a z)
  have hc : Computable c := rat_max.to_comp.comp (hb.comp Computable.fst) ha
  apply Named.of_certificate _ (fun z => (c z)⁻¹)
    (fun z => (b z.1)⁻¹ ^ 2 * tolerance z.2)
    (Arithmetic.rat_inv.to_comp.comp hc)
    (Arithmetic.rat_mul.to_comp.comp
      (Arithmetic.rat_pow.to_comp.comp (Arithmetic.rat_inv.to_comp.comp (hb.comp Computable.fst))
        (Computable.const 2)) (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n
    have hb₀ : (0 : ℝ) < b x := by exact_mod_cast hpos x
    have hc₀ : (b x : ℝ) ≤ c (x,n) := by exact_mod_cast (le_max_left (b x) (a (x,n)))
    have ha₀ : (a (x,n) : ℝ) ≤ c (x,n) := by exact_mod_cast (le_max_right (b x) (a (x,n)))
    have hce : |f x - (c (x,n) : ℝ)| ≤ tolerance n := by
      rw [abs_le]
      have h := abs_le.mp (he x n)
      refine ⟨?_, by linarith⟩
      have hmax : (c (x,n) : ℝ) ≤ f x + (tolerance n : ℝ) := by
        dsimp only [c]; push_cast
        apply max_le
        · exact (hlower x).trans (le_add_of_nonneg_right (tolerance_pos n).le)
        · linarith
      linarith
    have hfx : 0 < f x := hb₀.trans_le (hlower x)
    have hcx : 0 < (c (x,n) : ℝ) := hb₀.trans_le hc₀
    push_cast
    rw [inv_sub_inv hfx.ne' hcx.ne', abs_div, abs_mul,
      abs_of_pos hfx, abs_of_pos hcx, abs_sub_comm]
    calc
      _ ≤ (tolerance n : ℝ) / ((b x : ℝ) * (b x : ℝ)) :=
        div_le_div₀ (tolerance_pos n).le hce (mul_pos hb₀ hb₀)
          (mul_le_mul (hlower x) hc₀ hb₀.le hfx.le)
      _ = _ := by ring
  · intro x
    convert tolerance_tendsto.const_mul ((b x : ℝ)⁻¹ ^ 2) using 1 <;>
      simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, inv_pow, mul_zero]

lemma Named.sum_range {A : Type*} [Primcodable A] {f : A × ℕ → ℝ}
    (hf : Named f) (N : A → ℕ) (hN : Computable N) :
    Named (fun x => ∑ i ∈ Finset.range (N x), f (x,i)) := by
  obtain ⟨a,ha,he⟩ := hf
  have hs : Computable₂ (fun z : A × ℕ => fun i : ℕ => a ((z.1,i),z.2)) :=
    ha.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst))
  apply Named.of_certificate _ (fun z => ∑ i ∈ Finset.range (N z.1), a ((z.1,i),z.2))
    (fun z => (N z.1 : ℚ) * tolerance z.2)
    ((rat_sum_range hs).comp Computable.id (hN.comp Computable.fst))
    (Arithmetic.rat_mul.to_comp.comp (Arithmetic.rat_natCast.to_comp.comp (hN.comp Computable.fst))
      (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n; push_cast; rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (N x), (tolerance n : ℝ) := Finset.sum_le_sum (fun i _ => he (x,i) n)
      _ = _ := by simp
  · intro x; push_cast
    simpa only [inv_pow, mul_zero] using tolerance_tendsto.const_mul (N x : ℝ)

lemma rho_named : Named (fun q : ℚ => expNegInvGlue (q : ℝ)) := by
  have hn := exp_named.comp (Arithmetic.rat_neg.comp Arithmetic.rat_inv |>.to_comp)
  exact (Named.ite (fun q : ℚ => q ≤ 0)
    (Arithmetic.rat_le.decide.to_comp.comp Computable.id (Computable.const 0))
    (Named.const 0) hn).congr (by intro q; simp [expNegInvGlue])

lemma transition_named : Named (fun q : ℚ => Real.smoothTransition (q : ℝ)) := by
  have h₂ := rho_named.comp (Arithmetic.rat_sub.to_comp.comp (Computable.const 1) Computable.id)
  have hd := rho_named.add h₂
  have hi := hd.inv_of_lower (fun _ => 1/9) (Computable.const _) (by intro; norm_num)
    (by intro q; simpa [Function.comp_def] using Quantitative.transition_denom_lower (q : ℝ))
  exact (rho_named.mul hi).congr (by intro q; simp [Real.smoothTransition, div_eq_mul_inv])

lemma jet_one_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (B : ℕ)
    (hB : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ B) (x y : ℝ) :
    |f x - f y| ≤ (B : ℝ) * |x-y| := by
  have h : ∀ x, ‖deriv f x‖ ≤ (B : ℝ) := by
    intro z
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] using hB z
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Set.univ) => hf.differentiable (by simp) z) (fun z _ => h z)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ y) (Set.mem_univ x)

lemma Named.transition {A : Type*} [Primcodable A] {f : A → ℝ} (hf : Named f) :
    Named (fun a => Real.smoothTransition (f a)) := by
  apply Named.apply_lipschitz (fun _ => Real.smoothTransition)
    (fun _ => (Quantitative.transitionBound 1 : ℚ)) (Computable.const _) (fun _ => by positivity)
    (fun _ x y => ?_) (transition_named.comp Computable.snd) hf
  simpa only [Rat.cast_natCast] using jet_one_lipschitz Real.smoothTransition.contDiff
    (Quantitative.transitionBound 1) (Quantitative.transition_jet_bound 1) x y

end AlternatingNS.Effective

end ProfileNamesDevelopment

end OAI
