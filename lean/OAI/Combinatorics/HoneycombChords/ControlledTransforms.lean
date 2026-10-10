import OAI.Combinatorics.HoneycombChords.TransformSurjectivity

namespace OAI

/-! Exponential control, differentiation under the integral, and fusion identities.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real MeasureTheory Filter Topology

lemma sinh_le_mul_exp (x : ℝ) :
    Real.sinh x ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-2*x)) (Real.exp_pos x).le
  rw [← Real.exp_add, show x+(-2*x) = -x by ring] at h
  rw [Real.sinh_eq]
  nlinarith

lemma zG_norm_le (m : ℝ) {z : ℝ} (hz : 0 < z) :
    ‖zG m z‖ ≤ |m| * Real.exp (|m| * z) := by
  simp only [zG,Complex.norm_real,Real.norm_eq_abs,abs_div,Real.abs_sinh,abs_mul,abs_of_pos hz]
  apply (div_le_iff₀ hz).mpr
  have h := sinh_le_mul_exp (|m| * z)
  nlinarith

lemma power_le_one_add {z : ℝ} (hz : 0 ≤ z) {j d : ℕ} (hjd : j ≤ d) :
    z^j ≤ 1+z^d := by
  by_cases h : z ≤ 1
  · exact (pow_le_one₀ hz h).trans (by linarith [pow_nonneg hz d])
  · have hle : z^j ≤ z^d := pow_le_pow_right₀ (by linarith : 1 ≤ z) hjd
    linarith

def ControlledDensity (c : ℝ) (d : ℕ) (f : ℝ → ℂ) : Prop :=
  Measurable f ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ z, 0 < z →
    ‖f z‖ ≤ A*(1+z^d)*Real.exp (c*z)

lemma ControlledDensity.zero (c : ℝ) (d : ℕ) : ControlledDensity c d 0 := by
  refine ⟨measurable_const,0,le_rfl,?_⟩
  intros; simp
lemma ControlledDensity.add {c : ℝ} {d : ℕ} {f g : ℝ → ℂ}
    (hf : ControlledDensity c d f) (hg : ControlledDensity c d g) : ControlledDensity c d (f+g) := by
  rcases hf with ⟨hf,A,hA,hfA⟩
  rcases hg with ⟨hg,B,hB,hgB⟩
  refine ⟨hf.add hg,A+B,add_nonneg hA hB,?_⟩
  intro z hz
  have h := (norm_add_le (f z) (g z)).trans (add_le_add (hfA z hz) (hgB z hz))
  simpa only [Pi.add_apply,add_mul] using h
lemma ControlledDensity.smul {c : ℝ} {d : ℕ} {f : ℝ → ℂ}
    (hf : ControlledDensity c d f) (a : ℂ) : ControlledDensity c d (a • f) := by
  rcases hf with ⟨hf,A,hA,hfA⟩
  refine ⟨hf.const_smul a,‖a‖*A,mul_nonneg (norm_nonneg a) hA,?_⟩
  intro z hz
  simpa only [Pi.smul_apply,norm_smul,mul_assoc] using
    mul_le_mul_of_nonneg_left (hfA z hz) (norm_nonneg a)

lemma zMonomial_controlled (m : ℝ) {d j : ℕ} (hj : 2*j ≤ d) :
    ControlledDensity |m| d (zMonomial j) := by
  refine ⟨by unfold zMonomial; fun_prop,1,by norm_num,?_⟩
  intro z hz
  have hp := power_le_one_add hz.le hj
  have he : 1 ≤ Real.exp (|m| * z) := Real.one_le_exp (mul_nonneg (abs_nonneg m) hz.le)
  simp only [zMonomial,Complex.norm_real,Real.norm_eq_abs,abs_pow,abs_of_pos hz,one_mul,← pow_mul]
  exact hp.trans (le_mul_of_one_le_right (by positivity) he)

lemma zCoshJet_controlled (m : ℝ) {d j : ℕ} (hj : j ≤ d) :
    ControlledDensity |m| d (zCoshJet m j) := by
  refine ⟨by unfold zCoshJet hypJet; fun_prop,1,by norm_num,?_⟩
  intro z hz
  simp only [zCoshJet,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos hz,one_mul]
  have hh := hypJet_abs_le (j+1) (m*z)
  rw [abs_mul,abs_of_pos hz] at hh
  exact mul_le_mul (power_le_one_add hz.le hj) hh (abs_nonneg _) (by positivity)

lemma zG_controlled (m : ℝ) (d : ℕ) : ControlledDensity |m| d (zG m) := by
  refine ⟨by unfold zG; fun_prop,|m|,abs_nonneg m,?_⟩
  intro z hz
  apply (zG_norm_le m hz).trans
  exact mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right (abs_nonneg m) (by linarith [pow_nonneg hz.le d])) (Real.exp_pos _).le

lemma zDensity_controlled {m : ℝ} {N : ℕ} {f : ℝ → ℂ} (hf : f ∈ zDensity m N) :
    ControlledDensity |m| (2*N) f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ((⟨j,rfl⟩ | ⟨j,rfl⟩) | rfl)
    · exact zMonomial_controlled m (by have := j.isLt; omega)
    · exact zCoshJet_controlled m (by have := j.isLt; omega)
    · exact zG_controlled m (2*N)
  | zero => exact ControlledDensity.zero _ _
  | add f g hf hg hfi hgi => exact hfi.add hgi
  | smul a f hf hfi => exact hfi.smul a

end CriticalHoneycomb.FiniteFunctional.Analytic

end


section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real MeasureTheory Filter Topology

noncomputable def weightedJet (f : ℝ → ℂ) (j : ℕ) (u z : ℝ) : ℂ :=
  f z * ((z^j*hypJet (j+1) (u*z) : ℝ) : ℂ) * z / (Real.sinh (Real.pi*z/2) : ℂ)
noncomputable def weightedIntegral (f : ℝ → ℂ) (j : ℕ) (u : ℝ) : ℂ :=
  ∫ z in Set.Ioi (0:ℝ), weightedJet f j u z
noncomputable def jetBound (A a : ℝ) (d j : ℕ) (z : ℝ) : ℝ :=
  A*(z^(j+1)+z^(d+j+1))*Real.exp (a*z)/Real.sinh (Real.pi*z/2)

lemma weightedJet_zero (f : ℝ → ℂ) (u z : ℝ) : weightedJet f 0 u z = zKernel f u z := by
  simp only [weightedJet,zKernel,pow_zero,one_mul,Nat.zero_add,hypJet_one]
lemma weightedIntegral_zero (f : ℝ → ℂ) (u : ℝ) : weightedIntegral f 0 u = zTransform f u := by
  simp only [weightedIntegral,zTransform,weightedJet_zero]

lemma weightedJet_hasDerivAt (f : ℝ → ℂ) (j : ℕ) (u z : ℝ) :
    HasDerivAt (fun t => weightedJet f j t z) (weightedJet f (j+1) u z) u := by
  have hr := ((hypJet_hasDerivAt (j+1) (u*z)).comp u
    ((hasDerivAt_id u).mul_const z)).const_mul (z^j)
  have hd := (hr.ofReal_comp.const_mul (f z)).mul_const (z:ℂ)
  have he := hd.div_const (Real.sinh (Real.pi*z/2):ℂ)
  convert he using 1 <;> try rfl
  dsimp [weightedJet]
  push_cast
  rw [pow_succ]
  ring

lemma weightedJet_measurable {f : ℝ → ℂ} (hf : Measurable f) (j : ℕ) (u : ℝ) :
    Measurable (weightedJet f j u) := by
  unfold weightedJet hypJet
  fun_prop

lemma jetBound_integrable (A : ℝ) {a : ℝ} (ha : 0 ≤ a) (ha' : a < Real.pi/2) (d j : ℕ) :
    IntegrableOn (jetBound A a d j) (Set.Ioi 0) := by
  have hi := ((polynomial_kernel_integrable j ha ha').add
    (polynomial_kernel_integrable (d+j) ha ha')).const_mul A
  change Integrable _ _
  convert hi using 1
  ext z
  dsimp [jetBound]
  ring

lemma weightedJet_norm_le {f : ℝ → ℂ} {c A a z u : ℝ} {d : ℕ}
    (hA : 0 ≤ A) (hz : 0 < z)
    (hf : ‖f z‖ ≤ A*(1+z^d)*Real.exp (c*z)) (ha : c+|u| ≤ a) (j : ℕ) :
    ‖weightedJet f j u z‖ ≤ jetBound A a d j z := by
  have hz0 := hz.le
  have hden : 0 ≤ Real.sinh (Real.pi*z/2) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hh := hypJet_abs_le (j+1) (u*z)
  rw [abs_mul,abs_of_pos hz] at hh
  simp only [weightedJet, norm_div, norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_pow,abs_of_pos hz,abs_of_nonneg hden]
  calc
    ‖f z‖ * (z^j * |hypJet (j+1) (u*z)|) * z / Real.sinh (Real.pi*z/2)
      ≤ (A*(1+z^d)*Real.exp (c*z)) * (z^j*Real.exp (|u| * z)) * z / Real.sinh (Real.pi*z/2) := by
        gcongr
    _ = A*(z^(j+1)+z^(d+j+1))*Real.exp ((c+|u|)*z)/Real.sinh (Real.pi*z/2) := by
        simp only [add_mul,Real.exp_add,pow_add,pow_one]
        ring
    _ ≤ jetBound A a d j z := by
        dsimp [jetBound]
        gcongr

lemma weightedJet_integrable {f : ℝ → ℂ} {c : ℝ} {d : ℕ}
    (hf : ControlledDensity c d f) (hc : 0 ≤ c) {u : ℝ} (hu : c+|u| < Real.pi/2) (j : ℕ) :
    IntegrableOn (weightedJet f j u) (Set.Ioi 0) := by
  obtain ⟨A,hA,hfA⟩ := hf.2
  apply (jetBound_integrable A (add_nonneg hc (abs_nonneg u)) hu d j).mono'
  · exact (weightedJet_measurable hf.1 j u).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact weightedJet_norm_le hA hz (hfA z hz) le_rfl j

lemma weightedIntegral_hasDerivAt {f : ℝ → ℂ} {c : ℝ} {d : ℕ}
    (hf : ControlledDensity c d f) (hc : 0 ≤ c) {u : ℝ} (hu : c+|u| < Real.pi/2) (j : ℕ) :
    HasDerivAt (weightedIntegral f j) (weightedIntegral f (j+1) u) u := by
  obtain ⟨A,hA,hfA⟩ := hf.2
  let a := (Real.pi/2+(c+|u|))/2
  have ha : c+|u| < a := by dsimp [a]; linarith
  have ha0 : 0 ≤ a := (add_nonneg hc (abs_nonneg u)).trans ha.le
  have ha' : a < Real.pi/2 := by dsimp [a]; linarith
  let s := {t : ℝ | c+|t| < a}
  have hs : s ∈ 𝓝 u := (isOpen_lt (continuous_const.add continuous_abs) continuous_const).mem_nhds ha
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Filter.Eventually.of_forall (fun t => (weightedJet_measurable hf.1 j t).aestronglyMeasurable))
    (weightedJet_integrable hf hc hu j) (weightedJet_measurable hf.1 (j+1) u).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      intro t ht
      exact weightedJet_norm_le hA hz (hfA z hz) (le_of_lt ht) (j+1))
    (jetBound_integrable A ha0 ha' d (j+1))
    (ae_of_all _ (fun z t _ => weightedJet_hasDerivAt f j t z))).2

lemma weightedIntegral_iteratedDeriv {f : ℝ → ℂ} {c : ℝ} {d : ℕ}
    (hf : ControlledDensity c d f) (hc : 0 ≤ c) {u : ℝ} (hu : c+|u| < Real.pi/2) (j : ℕ) :
    iteratedDeriv j (zTransform f) u = weightedIntegral f j u := by
  induction j generalizing u with
  | zero => exact (weightedIntegral_zero f u).symm
  | succ j ih =>
    have hn : ∀ᶠ t in 𝓝 u, c+|t| < Real.pi/2 :=
      (isOpen_lt (continuous_const.add continuous_abs) continuous_const).mem_nhds hu
    have he : iteratedDeriv j (zTransform f) =ᶠ[𝓝 u] weightedIntegral f j :=
      hn.mono (fun t ht => ih ht)
    rw [iteratedDeriv_succ,he.deriv_eq]
    exact (weightedIntegral_hasDerivAt hf hc hu j).deriv

end CriticalHoneycomb.FiniteFunctional.Analytic

end


section


namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real MeasureTheory Filter Topology

noncomputable def zD (m z : ℝ) : ℂ := (2 * Real.cosh (m*z) - 1 : ℝ)

lemma zD_norm_le (m : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    ‖zD m z‖ ≤ 3 * Real.exp (|m| * z) := by
  have hh := hypJet_abs_le 1 (m*z)
  rw [hypJet_one, abs_mul, abs_of_nonneg hz] at hh
  have hcosh := Real.one_le_cosh (m*z)
  have he : 1 ≤ Real.exp (|m| * z) := Real.one_le_exp (mul_nonneg (abs_nonneg m) hz)
  simp only [zD, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith : 0 ≤ 2*Real.cosh (m*z)-1)]
  have hc : Real.cosh (m*z) ≤ Real.exp (|m| * z) := (le_abs_self _).trans hh
  linarith

lemma ControlledDensity.mul_zD {f : ℝ → ℂ} {c : ℝ} {d : ℕ}
    (hf : ControlledDensity c d f) (m : ℝ) :
    ControlledDensity (c+|m|) d (fun z => zD m z * f z) := by
  rcases hf with ⟨hf,A,hA,hfA⟩
  refine ⟨?_,3*A,by positivity,?_⟩
  · exact (by unfold zD; fun_prop : Measurable (zD m)).mul hf
  · intro z hz
    calc
      ‖zD m z * f z‖ = ‖zD m z‖ * ‖f z‖ := norm_mul _ _
      _ ≤ (3*Real.exp (|m| * z)) * (A*(1+z^d)*Real.exp (c*z)) :=
        mul_le_mul (zD_norm_le m hz.le) (hfA z hz) (norm_nonneg _) (by positivity)
      _ = (3*A)*(1+z^d)*Real.exp ((c+|m|)*z) := by
        rw [add_mul, Real.exp_add]; ring

lemma zKernel_fusion (f : ℝ → ℂ) (m u z : ℝ) :
    zKernel f (u-m) z + zKernel f (u+m) z - zKernel f u z =
      zKernel (fun z => zD m z * f z) u z := by
  simp only [zKernel,zD,sub_mul,add_mul,Real.cosh_sub,Real.cosh_add]
  push_cast
  ring

lemma zTransform_fusion {f : ℝ → ℂ} {c : ℝ} {d : ℕ}
    (hf : ControlledDensity c d f) (hc : 0 ≤ c) (m u : ℝ)
    (hu : c+|u|+|m| < Real.pi/2) :
    zTransform f (u-m) + zTransform f (u+m) - zTransform f u =
      zTransform (fun z => zD m z * f z) u := by
  have h₁ : c+|u-m| < Real.pi/2 := by linarith [abs_sub u m]
  have h₂ : c+|u+m| < Real.pi/2 := by linarith [abs_add_le u m]
  have h₃ : c+|u| < Real.pi/2 := by linarith [abs_nonneg m]
  have hi₁ := weightedJet_integrable hf hc h₁ 0
  have hi₂ := weightedJet_integrable hf hc h₂ 0
  have hi₃ := weightedJet_integrable hf hc h₃ 0
  have he (t : ℝ) : weightedJet f 0 t = zKernel f t := funext (weightedJet_zero f t)
  rw [he] at hi₁ hi₂ hi₃
  unfold zTransform
  rw [← integral_add hi₁ hi₂]
  have his : IntegrableOn (fun z => zKernel f (u-m) z + zKernel f (u+m) z) (Set.Ioi 0) := hi₁.add hi₂
  rw [← integral_sub his hi₃]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => zKernel_fusion f m u z)

noncomputable def integralInterpolant (ρ : ℂ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  4*(Real.cos (2*u):ℂ)+ρ+zTransform f u
noncomputable def integralFusion (m : ℝ) (ρ : ℂ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  4*(2*(Real.cos (2*m):ℂ)-1)*(Real.cos (2*u):ℂ)+ρ+
    zTransform (fun z => zD m z*f z) u

lemma integralInterpolant_fusion {f : ℝ → ℂ} {c : ℝ} {d : ℕ}
    (hf : ControlledDensity c d f) (hc : 0 ≤ c) (m u : ℝ) (ρ : ℂ)
    (hu : c+|u|+|m| < Real.pi/2) :
    integralInterpolant ρ f (u-m) + integralInterpolant ρ f (u+m) - integralInterpolant ρ f u =
      integralFusion m ρ f u := by
  have ht := zTransform_fusion hf hc m u hu
  dsimp [integralInterpolant,integralFusion]
  rw [show (2:ℝ)*(u-m)=2*u-2*m by ring,
      show (2:ℝ)*(u+m)=2*u+2*m by ring,Real.cos_sub, Real.cos_add]
  push_cast
  linear_combination ht

lemma integralInterpolant_fusion_eventually {f : ℝ → ℂ} {c : ℝ} {d : ℕ}
    (hf : ControlledDensity c d f) (hc : 0 ≤ c) (m u : ℝ) (ρ : ℂ)
    (hu : c+|u|+|m| < Real.pi/2) :
    (fun t => integralInterpolant ρ f (t-m)+integralInterpolant ρ f (t+m)-integralInterpolant ρ f t)
    =ᶠ[𝓝 u] integralFusion m ρ f := by
  have hn : ∀ᶠ t in 𝓝 u, c+|t|+|m| < Real.pi/2 :=
    (isOpen_lt ((continuous_const.add continuous_abs).add continuous_const) continuous_const).mem_nhds hu
  exact hn.mono (fun t ht => integralInterpolant_fusion hf hc m t ρ ht)

end CriticalHoneycomb.FiniteFunctional.Analytic

end

end OAI
