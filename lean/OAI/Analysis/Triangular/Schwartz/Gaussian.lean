import OAI.Analysis.Triangular.Certificate.WaveIntervals

namespace OAI

noncomputable section
open scoped SchwartzMap
namespace AtomicTriangular.Analysis

lemma polynomial_gaussian_bound {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → (1+r)^m * Real.exp (-c*r^2) ≤ C := by
  let B : ℝ := 2+c⁻¹
  refine ⟨B^m*(m.factorial:ℝ)*Real.exp 1, by positivity, ?_⟩
  intro r hr
  have hc' : 0 < c⁻¹ := inv_pos.mpr hc
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h : 1+r ≤ B*(1+c*r^2) := by
    dsimp [B]
    have hsq := sq_nonneg (r-1)
    have hmul : c⁻¹*c=1 := inv_mul_cancel₀ hc.ne'
    nlinarith [sq_nonneg r, mul_nonneg hc.le (sq_nonneg r)]
  have hp : (1+c*r^2)^m ≤ (m.factorial:ℝ)*Real.exp (1+c*r^2) := by
    have hh := Real.pow_div_factorial_le_exp (1+c*r^2) (by positivity : 0 ≤ 1+c*r^2) m
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (m.factorial : ℝ))).mp hh |>.trans_eq (mul_comm _ _)
  calc
    (1+r)^m * Real.exp (-c*r^2) ≤ (B*(1+c*r^2))^m * Real.exp (-c*r^2) := by gcongr
    _ = B^m * ((1+c*r^2)^m * Real.exp (-c*r^2)) := by rw [mul_pow]; ring
    _ ≤ B^m * (((m.factorial:ℝ)*Real.exp (1+c*r^2))*Real.exp (-c*r^2)) := by gcongr
    _ = B^m*(m.factorial:ℝ)*Real.exp 1 := by
      rw [mul_assoc (m.factorial:ℝ), ← Real.exp_add]
      rw [show 1+c*r^2 + -c*r^2 = 1 by ring]
      ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gaussian_schwartz_decay {c : ℝ} (hc : 0 < c) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : E, ‖x‖^k * ‖iteratedFDeriv ℝ n (fun y : E => Real.exp (-c*‖y‖^2)) x‖ ≤ C := by
  have ht : (fun x : E => -c*‖x‖^2).HasTemperateGrowth := by fun_prop
  obtain ⟨l,B,hB,hder⟩ := ht.norm_iteratedFDeriv_le_uniform n
  obtain ⟨C,hC,hCbound⟩ := polynomial_gaussian_bound hc (k+l*n)
  refine ⟨(n.factorial:ℝ)*(B+1)^n*C, fun x => ?_⟩
  have hw : 1 ≤ (B+1)*(1+‖x‖)^l := by
    have hh : 1 ≤ (1+‖x‖)^l := one_le_pow₀ (by linarith [norm_nonneg x])
    nlinarith
  have hD (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun x : E => -c*‖x‖^2) x‖ ≤ ((B+1)*(1+‖x‖)^l)^i := by
    calc
      _ ≤ B*(1+‖x‖)^l := hder i hin x
      _ ≤ (B+1)*(1+‖x‖)^l := by gcongr; linarith
      _ ≤ ((B+1)*(1+‖x‖)^l)^i := le_self_pow₀ hw (by omega)
  have hexp (i : ℕ) (_hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i Real.exp (-c*‖x‖^2)‖ ≤ Real.exp (-c*‖x‖^2) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,Real.iter_deriv_exp]
    exact le_of_eq (Real.norm_of_nonneg (Real.exp_pos _).le)
  have hd := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) Real.contDiff_exp ht.1 (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) x hexp hD
  calc
    _ ≤ ‖x‖^k * ((n.factorial:ℝ)*Real.exp (-c*‖x‖^2)*((B+1)*(1+‖x‖)^l)^n) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ (1+‖x‖)^k * ((n.factorial:ℝ)*Real.exp (-c*‖x‖^2)*((B+1)*(1+‖x‖)^l)^n) := by gcongr; linarith
    _ = (n.factorial:ℝ)*(B+1)^n*((1+‖x‖)^(k+l*n)*Real.exp (-c*‖x‖^2)) := by
      rw [mul_pow,pow_add,pow_mul]
      ring
    _ ≤ (n.factorial:ℝ)*(B+1)^n*C := by gcongr; exact hCbound ‖x‖ (norm_nonneg _)

def gaussianSchwartz (c : ℝ) (hc : 0 < c) : 𝓢(E,ℝ) where
  toFun x := Real.exp (-c*‖x‖^2)
  smooth' := Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
  decay' := gaussian_schwartz_decay hc

@[simp] lemma gaussianSchwartz_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gaussianSchwartz c hc x = Real.exp (-c*‖x‖^2) := rfl

lemma iteratedDeriv_real_of_complex {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (f x).re) = fun x : ℝ => (iteratedDeriv n f x).re := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    exact ((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by simp) (x : ℂ)).hasDerivAt.real_of_complex.deriv

lemma entire_real_temperate {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) :
    Function.HasTemperateGrowth (fun x : ℝ => (f x).re) := by
  obtain ⟨M,hM⟩ := hstrip
  refine ⟨hf.contDiff.real_of_complex, fun n => ⟨0,(n.factorial:ℝ)*M,?_⟩⟩
  intro x
  rw [pow_zero,mul_one,norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_real_of_complex hf]
  apply (Complex.abs_re_le_norm _).trans
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := f) n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl (c := (x:ℂ)) (C := M) (fun z hz => hM z (by
      have hi := Complex.abs_im_le_norm (z-(x:ℂ))
      have he := Metric.mem_sphere.mp hz
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero,← dist_eq_norm,he] using hi))
  simpa using hh

def dampedEntireSchwartz (c : ℝ) (hc : 0 < c) (b : ℝ) (f : ℂ → ℂ)
    (_hf : Differentiable ℂ f) (_hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) : 𝓢(E,ℝ) :=
  SchwartzMap.smulLeftCLM ℝ (fun x : E => (f (b*‖x‖^2)).re) (gaussianSchwartz c hc)

lemma dampedEntireSchwartz_apply (c : ℝ) (hc : 0 < c) (b : ℝ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) (x : E) :
    dampedEntireSchwartz c hc b f hf hstrip x = Real.exp (-c*‖x‖^2)*(f (b*‖x‖^2)).re := by
  have ht := entire_real_temperate hf hstrip
  have hg : Function.HasTemperateGrowth (fun x : E => (f (b*‖x‖^2)).re) := by
    convert ht.comp (by fun_prop : Function.HasTemperateGrowth (fun x : E => b*‖x‖^2)) using 1
    funext x
    simp
  rw [dampedEntireSchwartz,SchwartzMap.smulLeftCLM_apply_apply hg,gaussianSchwartz_apply]
  simp [mul_comm]

end AtomicTriangular.Analysis
end

end OAI
