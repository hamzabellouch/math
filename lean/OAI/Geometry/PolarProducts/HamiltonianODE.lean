import OAI.Geometry.PolarProducts.PeriodicSolutions

namespace OAI

universe u116 u117 u118

section NonsqueezingInline

namespace HamiltonianODE
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
open FourierPolynomial DiagonalQuadratic
variable {κ : Type u116} [Fintype κ]

 theorem inner_I_self (z : Vector κ) : inner (𝕜 := ℝ) z (Complex.I • z) = 0 := by
  rw [real_inner_eq_complex_re, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [pow_two]

 theorem inner_I_left (z w : Vector κ) :
    inner (𝕜 := ℝ) (Complex.I • z) w = -inner (𝕜 := ℝ) z (Complex.I • w) := by
  simp only [real_inner_eq_complex_re, inner_smul_left, inner_smul_right]
  simp [Complex.mul_re]

 theorem inner_I_I (z w : Vector κ) :
    inner (𝕜 := ℝ) (Complex.I • z) (Complex.I • w) = inner (𝕜 := ℝ) z w := by
  rw [inner_I_left, smul_smul]
  simp

 theorem zero_derivative_constant {E : Type u117} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℝ → E} (hx : ∀ t, HasDerivAt x 0 t) (s t : ℝ) : x s = x t := by
  exact is_const_of_deriv_eq_zero (fun t => (hx t).differentiableAt) (fun t => (hx t).deriv) s t

 theorem energy_constant {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t) (s t : ℝ) : H (x s) = H (x t) := by
  apply zero_derivative_constant (x := H ∘ x) _ s t
  intro u
  have hh := ((hH.differentiable (by simp) (x u)).hasGradientAt.hasFDerivAt).comp_hasDerivAt u (hx u)
  simpa only [InnerProductSpace.toDual_apply_apply, inner_I_self] using hh

 theorem quadratic_constant (d : κ → ℝ) {a : ℝ → ℝ} {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • ((2*a t) • diag d (x t))) t) (s t : ℝ) :
    energy d (x s) = energy d (x t) := by
  apply zero_derivative_constant (x := energy d ∘ x) _ s t
  intro u
  have hh := (hasGradientAt_energy d (x u)).hasFDerivAt.comp_hasDerivAt u (hx u)
  simpa only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left, smul_comm Complex.I (2*a u),
    real_inner_smul_right, inner_I_self, mul_zero] using hh

 theorem linear_solution {x : ℝ → ℂ} (v : ℂ)
    (hx : ∀ t, HasDerivAt x (v*x t) t) (t : ℝ) :
    x t = Complex.exp (v*(t : ℂ))*x 0 := by
  have hd (s : ℝ) : HasDerivAt (fun u : ℝ => Complex.exp (-v*(u : ℂ))*x u) 0 s := by
    have he := ((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (-v)).cexp
    have hh := he.mul (hx s)
    apply hh.congr_deriv
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
    ring
  have hc := zero_derivative_constant hd t 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hc
  have he := congrArg (fun z : ℂ => Complex.exp (v*(t:ℂ))*z) hc
  rw [← mul_assoc, ← Complex.exp_add] at he
  have hz : v*(t:ℂ)+ -v*(t:ℂ) = 0 := by ring
  simpa only [hz, Complex.exp_zero, one_mul] using he

 theorem periodic_frequency {x : ℝ → ℂ} (a : ℝ)
    (hx : ∀ t, HasDerivAt x ((2*(a:ℂ)*Complex.I)*x t) t)
    (hp : x 1 = x 0) (hzero : x 0 ≠ 0) : ∃ m : ℤ, a = Real.pi*m := by
  have he := linear_solution (2*(a:ℂ)*Complex.I) hx 1
  rw [Complex.ofReal_one, mul_one, hp] at he
  have hh : Complex.exp (2*(a:ℂ)*Complex.I) = 1 := by
    apply mul_right_cancel₀ hzero
    simpa only [one_mul] using he.symm
  obtain ⟨m,hm⟩ := Complex.exp_eq_one_iff.mp hh
  refine ⟨m,?_⟩
  have hi := congrArg Complex.im hm
  simp [Complex.mul_im, Complex.mul_re] at hi
  linarith

 theorem slow_linear_constant {x : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (haπ : a < Real.pi)
    (hx : ∀ t, HasDerivAt x ((2*(a:ℂ)*Complex.I)*x t) t)
    (hp : x 1 = x 0) (t : ℝ) : x t = x 0 := by
  by_cases hz : x 0 = 0
  · simp only [linear_solution _ hx t, hz, mul_zero]
  obtain ⟨m,hm⟩ := periodic_frequency a hx hp hz
  have hm0 : 0 ≤ m := by
    have : 0 ≤ (m:ℝ) := (mul_nonneg_iff_of_pos_left Real.pi_pos).mp (hm ▸ ha)
    exact_mod_cast this
  have hm1 : m < 1 := by
    have : (m:ℝ) < 1 := (mul_lt_mul_iff_right₀ Real.pi_pos).mp (by simpa [mul_comm] using hm ▸ haπ)
    exact_mod_cast this
  have hmz : m = 0 := by omega
  have haz : a = 0 := by simp [hm,hmz]
  simp only [linear_solution _ hx t, haz, Complex.ofReal_zero, mul_zero, zero_mul,
    Complex.exp_zero, one_mul]

end
end HamiltonianODE

namespace HamiltonianODE
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic
variable {κ : Type u118} [Fintype κ]

omit [Fintype κ] in
 theorem diag_one (z : Vector κ) : diag (fun _ => 1) z = z := by
   ext j
   simp

 theorem energy_one (z : Vector κ) : energy (fun _ => 1) z = ‖z‖^2 := by
   simp only [energy, one_mul, EuclideanSpace.norm_sq_eq]

 theorem gradient_comp_energy (d : κ → ℝ) {f : ℝ → ℝ} {v : ℝ} (z : Vector κ)
    (hf : HasDerivAt f v (energy d z)) :
    gradient (fun w => f (energy d w)) z = (2*v) • diag d z := by
   apply HasGradientAt.gradient
   rw [hasGradientAt_iff_hasFDerivAt]
   have h := hf.comp_hasFDerivAt z (hasGradientAt_energy d z).hasFDerivAt
   apply h.congr_fderiv
   ext w
   change v * inner (𝕜 := ℝ) ((2 : ℝ) • diag d z) w =
     inner (𝕜 := ℝ) ((2*v) • diag d z) w
   simp only [real_inner_smul_left]
   ring

 theorem coordinate_derivative (d : κ → ℝ) (v : ℝ) {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • ((2*v) • diag d (x t))) t) (j : κ) (t : ℝ) :
    HasDerivAt (fun s => x s j) ((2*((v*d j : ℝ):ℂ)*Complex.I)*x t j) t := by
   have h := (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : κ => ℂ) j).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t (hx t)
   apply h.congr_deriv
   change Complex.I * ((2*v) • (d j • x t j)) = (2*((v*d j : ℝ):ℂ)*Complex.I)*x t j
   simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
   ring

 theorem slow_diagonal_constant (d : κ → ℝ) (v : ℝ)
    (hv : ∀ j, 0 ≤ v*d j) (hvπ : ∀ j, v*d j < Real.pi)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • ((2*v) • diag d (x t))) t)
    (hp : x 1 = x 0) (t : ℝ) : x t = x 0 := by
   ext j
   exact slow_linear_constant (hv j) (hvπ j) (coordinate_derivative d v hx j)
     (congrArg (fun z : Vector κ => z j) hp) t

 theorem slow_radial_constant {f v : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (v s) s)
    (hv : ∀ s, 0 ≤ v s) (hvπ : ∀ s, v s < Real.pi)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient (fun z : Vector κ => f (‖z‖^2)) (x t)) t)
    (hp : x 1 = x 0) (t : ℝ) : x t = x 0 := by
   have he (s : ℝ) : gradient (fun z : Vector κ => f (‖z‖^2)) (x s) =
       (2*v (‖x s‖^2)) • diag (fun _ => 1) (x s) := by
     simpa only [energy_one] using gradient_comp_energy (fun _ => 1) (x s) (hf (energy (fun _ => 1) (x s)))
   have hode (s : ℝ) := (hx s).congr_deriv (congrArg (fun z : Vector κ => Complex.I • z) (he s))
   have hc (s : ℝ) : ‖x s‖^2 = ‖x 0‖^2 := by
     simpa only [energy_one] using quadratic_constant (fun _ => 1) hode s 0
   apply slow_diagonal_constant (fun _ => 1) (v (‖x 0‖^2)) (by simpa only [mul_one] using fun _ : κ => hv (‖x 0‖^2))
     (by simpa only [mul_one] using fun _ : κ => hvπ (‖x 0‖^2)) _ hp t
   intro s
   simpa only [hc s] using hode s

 theorem moderate_linear_either {x : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (ha2π : a < 2*Real.pi)
    (hx : ∀ t, HasDerivAt x ((2*(a:ℂ)*Complex.I)*x t) t)
    (hp : x 1 = x 0) : a = Real.pi ∨ ∀ t, x t = x 0 := by
   by_cases hz : x 0 = 0
   · exact Or.inr (fun t => by simp only [linear_solution _ hx t,hz,mul_zero])
   obtain ⟨m,hm⟩ := periodic_frequency a hx hp hz
   have hm0 : 0 ≤ m := by
     have : 0 ≤ (m:ℝ) := (mul_nonneg_iff_of_pos_left Real.pi_pos).mp (hm ▸ ha)
     exact_mod_cast this
   have hm2 : m < 2 := by
     have : (m:ℝ) < 2 := by nlinarith [Real.pi_pos]
     exact_mod_cast this
   have he : m = 0 ∨ m = 1 := by omega
   rcases he with he | he
   · have haz : a = 0 := by simp [hm,he]
     exact Or.inr (fun t => by simp only [linear_solution _ hx t,haz,Complex.ofReal_zero,
       mul_zero,zero_mul,Complex.exp_zero,one_mul])
   · exact Or.inl (by simpa [he] using hm)

 theorem diagonal_either (j₀ : κ) (d : κ → ℝ) {v : ℝ}
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hd : ∀ j, 0 ≤ d j)
    (hdπ : ∀ j, j ≠ j₀ → d j < Real.pi) (hd2π : d j₀ < 2*Real.pi)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • ((2*v) • diag d (x t))) t)
    (hp : x 1 = x 0) : v*d j₀ = Real.pi ∨ ∀ t, x t = x 0 := by
   have hvd (j : κ) : v*d j ≤ d j := by nlinarith [hd j]
   rcases moderate_linear_either (mul_nonneg hv (hd j₀)) (lt_of_le_of_lt (hvd j₀) hd2π)
     (coordinate_derivative d v hx j₀) (congrArg (fun z : Vector κ => z j₀) hp) with he | he
   · exact Or.inl he
   · right
     intro t
     ext j
     by_cases hj : j = j₀
     · subst j; exact he t
     · exact slow_linear_constant (mul_nonneg hv (hd j)) (lt_of_le_of_lt (hvd j) (hdπ j hj))
         (coordinate_derivative d v hx j) (congrArg (fun z : Vector κ => z j) hp) t

end
end HamiltonianODE

end NonsqueezingInline

end OAI
