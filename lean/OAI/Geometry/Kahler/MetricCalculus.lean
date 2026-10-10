import OAI.Geometry.Kahler.Obstruction

namespace OAI

universe uKahler1607_1 uKahler1618_1

open Set Filter Topology
open scoped ContDiff
noncomputable section

namespace PinchedHartogs

open scoped Matrix.Norms.Elementwise

lemma dz_congr {f g : Ambient → ℂ} {p : Ambient} (h : f =ᶠ[𝓝 p] g) (i : Fin 3) :
    dz f p i = dz g p i := by
  simp only [dz, h.fderiv_eq]

lemma dbar_congr {f g : Ambient → ℂ} {p : Ambient} (h : f =ᶠ[𝓝 p] g) (i : Fin 3) :
    dbar f p i = dbar g p i := by
  simp only [dbar, h.fderiv_eq]

lemma dz_add {f g : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dz (fun q => f q + g q) p i = dz f p i + dz g p i := by
  have hd : fderiv ℝ (fun q => f q + g q) p = fderiv ℝ f p + fderiv ℝ g p := fderiv_add hf hg
  simp only [dz, hd, add_apply]
  ring

lemma dbar_add {f g : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dbar (fun q => f q + g q) p i = dbar f p i + dbar g p i := by
  have hd : fderiv ℝ (fun q => f q + g q) p = fderiv ℝ f p + fderiv ℝ g p := fderiv_add hf hg
  simp only [dbar, hd, add_apply]
  ring

lemma dz_mul {f g : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dz (fun q => f q * g q) p i = dz f p i * g p + f p * dz g p i := by
  have hd : fderiv ℝ (fun q => f q * g q) p = f p • fderiv ℝ g p + g p • fderiv ℝ f p := fderiv_mul hf hg
  simp only [dz, hd, add_apply,
    smul_apply, smul_eq_mul]
  ring

lemma dbar_mul {f g : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dbar (fun q => f q * g q) p i = dbar f p i * g p + f p * dbar g p i := by
  have hd : fderiv ℝ (fun q => f q * g q) p = f p • fderiv ℝ g p + g p • fderiv ℝ f p := fderiv_mul hf hg
  simp only [dbar, hd, add_apply,
    smul_apply, smul_eq_mul]
  ring

lemma fderiv_real_cast {f : Ambient → ℝ} {p : Ambient} (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun q => (f q : ℂ)) p = Complex.ofRealCLM.comp (fderiv ℝ f p) := by
  exact (Complex.ofRealCLM.hasFDerivAt.comp p hf.hasFDerivAt).fderiv

lemma dbar_eq_star_dz_real {f : Ambient → ℝ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (i : Fin 3) :
    dbar (fun q => (f q : ℂ)) p i = star (dz (fun q => (f q : ℂ)) p i) := by
  simp [dbar, dz, fderiv_real_cast hf]

lemma dz_real_comp {f : Ambient → ℝ} {p : Ambient} {ρ : ℝ → ℝ} {ρ' : ℝ}
    (hf : DifferentiableAt ℝ f p) (hρ : HasDerivAt ρ ρ' (f p)) (i : Fin 3) :
    dz (fun q => (ρ (f q) : ℂ)) p i = (ρ' : ℂ) * dz (fun q => (f q : ℂ)) p i := by
  have h := (hρ.comp_hasFDerivAt p hf.hasFDerivAt)
  have hd : fderiv ℝ (fun q => (ρ (f q) : ℂ)) p = Complex.ofRealCLM.comp (ρ' • fderiv ℝ f p) :=
    (Complex.ofRealCLM.hasFDerivAt.comp p h).fderiv
  simp only [dz, hd, fderiv_real_cast hf]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

lemma dbar_real_comp {f : Ambient → ℝ} {p : Ambient} {ρ : ℝ → ℝ} {ρ' : ℝ}
    (hf : DifferentiableAt ℝ f p) (hρ : HasDerivAt ρ ρ' (f p)) (i : Fin 3) :
    dbar (fun q => (ρ (f q) : ℂ)) p i = (ρ' : ℂ) * dbar (fun q => (f q : ℂ)) p i := by
  have h := (hρ.comp_hasFDerivAt p hf.hasFDerivAt)
  have hd : fderiv ℝ (fun q => (ρ (f q) : ℂ)) p = Complex.ofRealCLM.comp (ρ' • fderiv ℝ f p) :=
    (Complex.ofRealCLM.hasFDerivAt.comp p h).fderiv
  simp only [dbar, hd, fderiv_real_cast hf]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

lemma _root_.OAI.ContDiffAt.hartogs_dz {f : Ambient → ℂ} {p : Ambient} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hmn : m + 1 ≤ n) (i : Fin 3) :
    ContDiffAt ℝ m (fun q => dz f q i) p := by
  have hd := hf.fderiv_right hmn
  unfold PinchedHartogs.dz
  exact ((hd.clm_apply contDiffAt_const).sub
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

lemma _root_.OAI.ContDiffAt.hartogs_dbar {f : Ambient → ℂ} {p : Ambient} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hmn : m + 1 ≤ n) (i : Fin 3) :
    ContDiffAt ℝ m (fun q => dbar f q i) p := by
  have hd := hf.fderiv_right hmn
  unfold PinchedHartogs.dbar
  exact ((hd.clm_apply contDiffAt_const).add
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

lemma _root_.OAI.ContDiffAt.hartogs_real_cast {f : Ambient → ℝ} {p : Ambient} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) : ContDiffAt ℝ n (fun q => (f q : ℂ)) p :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp p hf

lemma complexHessian_real_comp {f : Ambient → ℝ} {p : Ambient}
    {ρ ρ' : ℝ → ℝ} {ρ'' : ℝ} (hf : ContDiffAt ℝ 2 f p)
    (hρ : ∀ᶠ y in 𝓝 (f p), HasDerivAt ρ (ρ' y) y)
    (hρ' : HasDerivAt ρ' ρ'' (f p)) (i j : Fin 3) :
    complexHessian (fun q => ρ (f q)) p i j =
      (ρ' (f p) : ℂ) * complexHessian f p i j +
        (ρ'' : ℂ) * dz (fun q => (f q : ℂ)) p i * dbar (fun q => (f q : ℂ)) p j := by
  have he : (fun q => dbar (fun r => (ρ (f r) : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => (ρ' (f q) : ℂ) * dbar (fun r => (f r : ℂ)) q j) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt hρ] with q hq hρq
    exact dbar_real_comp (hq.differentiableAt (by norm_num)) hρq j
  have hdφ := hf.differentiableAt (by norm_num)
  have hdρ : DifferentiableAt ℝ (fun q => (ρ' (f q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p (hρ'.differentiableAt.comp p hdφ)
  have hdb : DifferentiableAt ℝ (fun q => dbar (fun r => (f r : ℂ)) q j) p :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  unfold complexHessian
  rw [dz_congr he, dz_mul hdρ hdb, dz_real_comp hdφ hρ']
  ring

lemma dz_const_mul {f : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (c : ℂ) (i : Fin 3) :
    dz (fun q => c * f q) p i = c * dz f p i := by
  have hd : fderiv ℝ (fun q => c * f q) p = c • fderiv ℝ f p := fderiv_const_mul hf c
  simp only [dz, hd, smul_apply, smul_eq_mul]
  ring

lemma dbar_const_mul {f : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (c : ℂ) (i : Fin 3) :
    dbar (fun q => c * f q) p i = c * dbar f p i := by
  have hd : fderiv ℝ (fun q => c * f q) p = c • fderiv ℝ f p := fderiv_const_mul hf c
  simp only [dbar, hd, smul_apply, smul_eq_mul]
  ring

lemma complexHessian_add {f g : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) (i j : Fin 3) :
    complexHessian (fun q => f q + g q) p i j =
      complexHessian f p i j + complexHessian g p i j := by
  have he : (fun q => dbar (fun r => ((f r + g r : ℝ) : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => dbar (fun r => (f r : ℂ)) q j + dbar (fun r => (g r : ℂ)) q j) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with q hq hq'
    simp only [Complex.ofReal_add]
    exact dbar_add ((_root_.OAI.ContDiffAt.hartogs_real_cast hq).differentiableAt (by norm_num))
      ((_root_.OAI.ContDiffAt.hartogs_real_cast hq').differentiableAt (by norm_num)) j
  unfold complexHessian
  rw [dz_congr he]
  exact dz_add ((_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) j).differentiableAt (by norm_num))
    ((_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hg) (m := 1) (by norm_num) j).differentiableAt (by norm_num)) i

lemma complexHessian_const_mul {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (c : ℝ) (i j : Fin 3) :
    complexHessian (fun q => c * f q) p i j = (c : ℂ) * complexHessian f p i j := by
  have he : (fun q => dbar (fun r => ((c * f r : ℝ) : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => (c : ℂ) * dbar (fun r => (f r : ℂ)) q j) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    simp only [Complex.ofReal_mul]
    exact dbar_const_mul ((_root_.OAI.ContDiffAt.hartogs_real_cast hq).differentiableAt (by norm_num)) c j
  unfold complexHessian
  rw [dz_congr he]
  exact dz_const_mul ((_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) j).differentiableAt (by norm_num)) c i

lemma complexHessian_mul {f g : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) (i j : Fin 3) :
    complexHessian (fun q => f q * g q) p i j =
      (f p : ℂ) * complexHessian g p i j + (g p : ℂ) * complexHessian f p i j +
      dz (fun q => (f q : ℂ)) p i * dbar (fun q => (g q : ℂ)) p j +
      dz (fun q => (g q : ℂ)) p i * dbar (fun q => (f q : ℂ)) p j := by
  have he : (fun q => dbar (fun r => ((f r * g r : ℝ) : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => dbar (fun r => (f r : ℂ)) q j * (g q : ℂ) +
        (f q : ℂ) * dbar (fun r => (g r : ℂ)) q j) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with q hq hq'
    simp only [Complex.ofReal_mul]
    exact dbar_mul ((_root_.OAI.ContDiffAt.hartogs_real_cast hq).differentiableAt (by norm_num))
      ((_root_.OAI.ContDiffAt.hartogs_real_cast hq').differentiableAt (by norm_num)) j
  have hdf := (_root_.OAI.ContDiffAt.hartogs_real_cast hf).differentiableAt (by norm_num)
  have hdg := (_root_.OAI.ContDiffAt.hartogs_real_cast hg).differentiableAt (by norm_num)
  have hdbf := (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  have hdbg := (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hg) (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  unfold complexHessian
  rw [dz_congr he,
    dz_add (f := fun q => dbar (fun r => (f r : ℂ)) q j * (g q : ℂ))
      (g := fun q => (f q : ℂ) * dbar (fun r => (g r : ℂ)) q j)
      (hdbf.mul hdg) (hdf.mul hdbg), dz_mul hdbf hdg, dz_mul hdf hdbg]
  ring

lemma dz_conj {f : Ambient → ℂ} {p : Ambient} (hf : DifferentiableAt ℝ f p) (i : Fin 3) :
    dz (fun q => star (f q)) p i = star (dbar f p i) := by
  have hd : fderiv ℝ (fun q => star (f q)) p = Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f p) :=
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hf.hasFDerivAt).fderiv
  simp only [dz, dbar, hd]
  simp [star_add, star_mul]
  ring

lemma dbar_conj {f : Ambient → ℂ} {p : Ambient} (hf : DifferentiableAt ℝ f p) (i : Fin 3) :
    dbar (fun q => star (f q)) p i = star (dz f p i) := by
  have hd : fderiv ℝ (fun q => star (f q)) p = Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f p) :=
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hf.hasFDerivAt).fderiv
  simp only [dz, dbar, hd]
  simp [star_sub, star_mul]
  ring

lemma dz_fiber (p : Ambient) (i : Fin 3) :
    dz (fun q => q.2) p i = if i = 2 then 1 else 0 := by
  have hd : fderiv ℝ (fun q : Ambient => q.2) p = ContinuousLinearMap.snd ℝ Base ℂ :=
    (ContinuousLinearMap.snd ℝ Base ℂ).fderiv
  fin_cases i <;> simp [dz, hd, coordVector]

lemma dbar_fiber (p : Ambient) (i : Fin 3) :
    dbar (fun q => q.2) p i = 0 := by
  have hd : fderiv ℝ (fun q : Ambient => q.2) p = ContinuousLinearMap.snd ℝ Base ℂ :=
    (ContinuousLinearMap.snd ℝ Base ℂ).fderiv
  fin_cases i <;> simp [dbar, hd, coordVector]

lemma dbar_fiber_norm_sq (p : Ambient) (j : Fin 3) :
    dbar (fun q : Ambient => (‖q.2‖ ^ 2 : ℝ)) p j = p.2 * (if j = 2 then 1 else 0) := by
  have he (q : Ambient) : ((‖q.2‖ ^ 2 : ℝ) : ℂ) = q.2 * star q.2 := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj q.2).symm
  simp only [he]
  rw [dbar_mul (by fun_prop) (by fun_prop), dbar_fiber, dbar_conj (by fun_prop), dz_fiber]
  split_ifs <;> simp

lemma dz_fiber_norm_sq (p : Ambient) (j : Fin 3) :
    dz (fun q : Ambient => (‖q.2‖ ^ 2 : ℝ)) p j = star p.2 * (if j = 2 then 1 else 0) := by
  have hd : DifferentiableAt ℝ (fun q : Ambient => ‖q.2‖ ^ 2) p :=
    (contDiff_norm_sq ℂ (n := 1)).differentiable (by simp) |>.differentiableAt |>.comp p (by fun_prop)
  have h := dbar_eq_star_dz_real hd j
  rw [dbar_fiber_norm_sq] at h
  have := congrArg star h
  split_ifs at * <;> simpa using this.symm

lemma complexHessian_fiber_norm_sq (p : Ambient) (i j : Fin 3) :
    complexHessian (fun q : Ambient => ‖q.2‖ ^ 2) p i j =
      (if i = 2 then 1 else 0) * (if j = 2 then 1 else 0) := by
  unfold complexHessian
  simp only [dbar_fiber_norm_sq]
  by_cases hj : j = 2
  · simp only [hj, ite_eq_left, mul_one]
    exact dz_fiber p i
  · simp [hj, dz]

lemma complexHessian_rexp {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (i j : Fin 3) :
    complexHessian (fun q => Real.exp (f q)) p i j =
      (Real.exp (f p) : ℂ) * (complexHessian f p i j +
        dz (fun q => (f q : ℂ)) p i * dbar (fun q => (f q : ℂ)) p j) := by
  rw [complexHessian_real_comp hf (Filter.Eventually.of_forall Real.hasDerivAt_exp)
    (Real.hasDerivAt_exp (f p))]
  ring

lemma negLogOneSub_hasDerivAt {x : ℝ} (hx : 1 - x ≠ 0) :
    HasDerivAt (fun y : ℝ => -Real.log (1 - y)) ((1 - x)⁻¹) x := by
  have hh : HasDerivAt (fun y : ℝ => -Real.log (1 - y)) (-(-1 / (1-x))) x :=
    (((hasDerivAt_id x).const_sub 1).log hx).neg
  have he : -(-1 / (1-x)) = (1-x)⁻¹ := by simp [neg_div, one_div]
  rw [he] at hh
  exact hh

lemma invOneSub_hasDerivAt {x : ℝ} (hx : 1 - x ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (((1 - x) ^ 2)⁻¹) x := by
  have hh : HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (-(-1) / (1-x)^2) x :=
    ((hasDerivAt_id x).const_sub 1).inv hx
  have he : -(-1:ℝ) / (1-x)^2 = ((1-x)^2)⁻¹ := by simp [one_div]
  rw [he] at hh
  exact hh

lemma complexHessian_negLogOneSub {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hp : 1 - f p ≠ 0) (i j : Fin 3) :
    complexHessian (fun q => -Real.log (1 - f q)) p i j =
      ((1 - f p)⁻¹ : ℝ) * complexHessian f p i j +
        ((((1 - f p) ^ 2)⁻¹ : ℝ) : ℂ) * dz (fun q => (f q : ℂ)) p i *
          dbar (fun q => (f q : ℂ)) p j := by
  have hρ : ∀ᶠ y in 𝓝 (f p), HasDerivAt (fun y : ℝ => -Real.log (1-y)) ((1-y)⁻¹) y := by
    filter_upwards [((continuousAt_const.sub continuousAt_id).eventually_ne hp)] with y hy
    exact negLogOneSub_hasDerivAt hy
  exact complexHessian_real_comp (ρ := fun y : ℝ => -Real.log (1-y))
    (ρ' := fun y : ℝ => (1-y)⁻¹) hf hρ (invOneSub_hasDerivAt hp) i j

lemma psi_contDiffAt {z : Base} (hz : z ∈ ball) : ContDiffAt ℝ ∞ psi z := by
  have hp : 0 < 1 - ‖z‖ ^ 2 := by
    have h := norm_nonneg z
    change ‖z‖ < 1 at hz
    nlinarith
  exact ((contDiffAt_const.sub (contDiff_norm_sq ℂ).contDiffAt).log hp.ne').neg

lemma metricPotential_contDiffAt {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (lam : ℝ) {p : Ambient} (hp : p ∈ hartogs φ) :
    ContDiffAt ℝ ∞ (metricPotential φ lam) p := by
  have hdφ : ContDiffAt ℝ ∞ (fun q : Ambient => φ q.1) p :=
    (hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).comp p contDiffAt_fst
  have ht : ContDiffAt ℝ ∞ (fun q : Ambient => Real.exp (φ q.1) * ‖q.2‖ ^ 2) p :=
    hdφ.exp.mul ((contDiff_norm_sq ℂ).contDiffAt.comp p contDiffAt_snd)
  exact (contDiffAt_const.mul ((psi_contDiffAt hp.1).comp p contDiffAt_fst)).sub
    ((contDiffAt_const.sub ht).log (sub_pos.mpr hp.2).ne')

lemma complexHessian_contDiffAt {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ ∞ f p) : ContDiffAt ℝ ∞ (complexHessian f) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact _root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := ∞) (by simp) j) (by simp) i

lemma hartogsMetric_contDiffOn {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball) (lam : ℝ) :
    ContDiffOn ℝ ∞ (hartogsMetric φ lam) (hartogs φ) := by
  intro p hp
  exact (complexHessian_contDiffAt (metricPotential_contDiffAt hφ lam hp)).contDiffWithinAt

lemma dz_real_mul {f g : Ambient → ℝ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dz (fun q => ((f q * g q : ℝ) : ℂ)) p i =
      dz (fun q => (f q : ℂ)) p i * (g p : ℂ) + (f p : ℂ) * dz (fun q => (g q : ℂ)) p i := by
  simp only [Complex.ofReal_mul]
  exact dz_mul (Complex.ofRealCLM.differentiableAt.comp p hf)
    (Complex.ofRealCLM.differentiableAt.comp p hg) i

lemma dbar_real_mul {f g : Ambient → ℝ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dbar (fun q => ((f q * g q : ℝ) : ℂ)) p i =
      dbar (fun q => (f q : ℂ)) p i * (g p : ℂ) + (f p : ℂ) * dbar (fun q => (g q : ℂ)) p i := by
  simp only [Complex.ofReal_mul]
  exact dbar_mul (Complex.ofRealCLM.differentiableAt.comp p hf)
    (Complex.ofRealCLM.differentiableAt.comp p hg) i

lemma complexHessian_fiberPotential {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hp : Real.exp (f p) * ‖p.2‖ ^ 2 < 1) (i j : Fin 3) :
    complexHessian (fun q => -Real.log (1 - Real.exp (f q) * ‖q.2‖ ^ 2)) p i j =
      ((Real.exp (f p) * ‖p.2‖ ^ 2 / (1 - Real.exp (f p) * ‖p.2‖ ^ 2) : ℝ) : ℂ) *
        complexHessian f p i j +
      ((Real.exp (f p) / (1 - Real.exp (f p) * ‖p.2‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        ((if i = 2 then 1 else 0) + p.2 * dz (fun q => (f q : ℂ)) p i) *
        ((if j = 2 then 1 else 0) + star p.2 * dbar (fun q => (f q : ℂ)) p j) := by
  have hr : ContDiffAt ℝ 2 (fun q : Ambient => ‖q.2‖ ^ 2) p :=
    (contDiff_norm_sq ℂ).contDiffAt.comp p contDiffAt_snd
  have hef := hf.exp
  have ht := hef.mul hr
  have hdf := hf.differentiableAt (by norm_num)
  have hdr := hr.differentiableAt (by norm_num)
  have hde := hef.differentiableAt (by norm_num)
  rw [complexHessian_negLogOneSub ht (sub_pos.mpr hp).ne',
    complexHessian_mul hef hr, complexHessian_rexp hf, complexHessian_fiber_norm_sq,
    dz_real_mul hde hdr, dbar_real_mul hde hdr,
    dz_real_comp hdf (Real.hasDerivAt_exp _), dbar_real_comp hdf (Real.hasDerivAt_exp _),
    dz_fiber_norm_sq, dbar_fiber_norm_sq]
  have hn : ((‖p.2‖ ^ 2 : ℝ) : ℂ) = p.2 * star p.2 := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj p.2).symm
  have hD : (1 : ℂ) - (Real.exp (f p) : ℂ) * (p.2 * star p.2) ≠ 0 := by
    rw [← hn, ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hp).ne'
  simp only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_div] at *
  rw [hn]
  field_simp
  ring

lemma hartogsMetric_smooth_form {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (lam : ℝ) {p : Ambient} (hp : p ∈ hartogs φ) (i j : Fin 3) :
    hartogsMetric φ lam p i j =
      (lam : ℂ) * complexHessian (fun q : Ambient => psi q.1) p i j +
      ((Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) : ℝ) : ℂ) *
        complexHessian (fun q : Ambient => φ q.1) p i j +
      ((Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        ((if i = 2 then 1 else 0) + p.2 * dz (fun q : Ambient => (φ q.1 : ℂ)) p i) *
        ((if j = 2 then 1 else 0) + star p.2 * dbar (fun q : Ambient => (φ q.1 : ℂ)) p j) := by
  have hψ : ContDiffAt ℝ 2 (fun q : Ambient => psi q.1) p :=
    ((psi_contDiffAt hp.1).comp p contDiffAt_fst).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hφp : ContDiffAt ℝ 2 (fun q : Ambient => φ q.1) p :=
    ((hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).comp p contDiffAt_fst).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hr : ContDiffAt ℝ 2 (fun q : Ambient => ‖q.2‖ ^ 2) p :=
    (contDiff_norm_sq ℂ).contDiffAt.comp p contDiffAt_snd
  have hlog := ((contDiffAt_const.sub (hφp.exp.mul hr)).log (sub_pos.mpr hp.2).ne').neg
  have he : metricPotential φ lam = (fun q : Ambient =>
      lam * psi q.1 + -Real.log (1 - Real.exp (φ q.1) * ‖q.2‖ ^ 2)) := by
    funext q
    exact sub_eq_add_neg _ _
  unfold hartogsMetric
  rw [he]
  rw [complexHessian_add (contDiffAt_const.mul hψ) hlog, complexHessian_const_mul hψ,
    complexHessian_fiberPotential hφp hp.2]
  ring

private def dzFunctional (i : Fin 3) : (Ambient →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ (coordVector i) -
    Complex.I • ContinuousLinearMap.apply ℝ ℂ (Complex.I • coordVector i))

private def dbarFunctional (i : Fin 3) : (Ambient →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ (coordVector i) +
    Complex.I • ContinuousLinearMap.apply ℝ ℂ (Complex.I • coordVector i))

private lemma dzFunctional_apply (D : Ambient →L[ℝ] ℂ) (i : Fin 3) :
    dzFunctional i D = (D (coordVector i) - Complex.I * D (Complex.I • coordVector i)) / 2 := by
  simp only [dzFunctional, sub_apply, smul_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

private lemma dbarFunctional_apply (D : Ambient →L[ℝ] ℂ) (i : Fin 3) :
    dbarFunctional i D = (D (coordVector i) + Complex.I * D (Complex.I • coordVector i)) / 2 := by
  simp only [dbarFunctional, add_apply, smul_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

lemma fderiv_dz_apply {f : Ambient → ℂ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p)
    (i : Fin 3) (v : Ambient) :
    fderiv ℝ (fun q => dz f q i) p v =
      (fderiv ℝ (fderiv ℝ f) p v (coordVector i) -
        Complex.I * fderiv ℝ (fderiv ℝ f) p v (Complex.I • coordVector i)) / 2 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun q => dz f q i) = (fun q => dzFunctional i (fderiv ℝ f q)) := by
    funext q
    exact (dzFunctional_apply _ i).symm
  rw [he]
  have hh : fderiv ℝ (fun q => dzFunctional i (fderiv ℝ f q)) p =
      (dzFunctional i).comp (fderiv ℝ (fderiv ℝ f) p) :=
    ((dzFunctional i).hasFDerivAt.comp p hd.hasFDerivAt).fderiv
  rw [hh, ContinuousLinearMap.comp_apply, dzFunctional_apply]

lemma fderiv_dbar_apply {f : Ambient → ℂ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p)
    (i : Fin 3) (v : Ambient) :
    fderiv ℝ (fun q => dbar f q i) p v =
      (fderiv ℝ (fderiv ℝ f) p v (coordVector i) +
        Complex.I * fderiv ℝ (fderiv ℝ f) p v (Complex.I • coordVector i)) / 2 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun q => dbar f q i) = (fun q => dbarFunctional i (fderiv ℝ f q)) := by
    funext q
    exact (dbarFunctional_apply _ i).symm
  rw [he]
  have hh : fderiv ℝ (fun q => dbarFunctional i (fderiv ℝ f q)) p =
      (dbarFunctional i).comp (fderiv ℝ (fderiv ℝ f) p) :=
    ((dbarFunctional i).hasFDerivAt.comp p hd.hasFDerivAt).fderiv
  rw [hh, ContinuousLinearMap.comp_apply, dbarFunctional_apply]

lemma dz_dbar_comm {f : Ambient → ℂ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p)
    (i j : Fin 3) :
    dz (fun q => dbar f q j) p i = dbar (fun q => dz f q i) p j := by
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  change (fderiv ℝ (fun q => dbar f q j) p (coordVector i) -
    Complex.I * fderiv ℝ (fun q => dbar f q j) p (Complex.I • coordVector i)) / 2 =
    (fderiv ℝ (fun q => dz f q i) p (coordVector j) +
    Complex.I * fderiv ℝ (fun q => dz f q i) p (Complex.I • coordVector j)) / 2
  simp only [fderiv_dz_apply hf, fderiv_dbar_apply hf]
  conv_lhs =>
    rw [hs (coordVector i) (coordVector j), hs (coordVector i) (Complex.I • coordVector j),
      hs (Complex.I • coordVector i) (coordVector j),
      hs (Complex.I • coordVector i) (Complex.I • coordVector j)]
  ring

lemma dz_dz_comm {f : Ambient → ℂ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p)
    (i j : Fin 3) :
    dz (fun q => dz f q j) p i = dz (fun q => dz f q i) p j := by
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  change (fderiv ℝ (fun q => dz f q j) p (coordVector i) -
    Complex.I * fderiv ℝ (fun q => dz f q j) p (Complex.I • coordVector i)) / 2 =
    (fderiv ℝ (fun q => dz f q i) p (coordVector j) -
    Complex.I * fderiv ℝ (fun q => dz f q i) p (Complex.I • coordVector j)) / 2
  simp only [fderiv_dz_apply hf]
  conv_lhs =>
    rw [hs (coordVector i) (coordVector j), hs (coordVector i) (Complex.I • coordVector j),
      hs (Complex.I • coordVector i) (coordVector j),
      hs (Complex.I • coordVector i) (Complex.I • coordVector j)]
  ring

lemma complexHessian_hermitian {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (i j : Fin 3) :
    complexHessian f p i j = star (complexHessian f p j i) := by
  have hdc := (_root_.OAI.ContDiffAt.hartogs_real_cast hf)
  have he : (fun q => dbar (fun r => (f r : ℂ)) q i) =ᶠ[𝓝 p]
      (fun q => star (dz (fun r => (f r : ℂ)) q i)) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact dbar_eq_star_dz_real (hq.differentiableAt (by norm_num)) i
  unfold complexHessian
  rw [dz_congr he, dz_conj ((_root_.OAI.ContDiffAt.hartogs_dz hdc (m := 1) (by norm_num) i).differentiableAt (by norm_num)),
    star_star, dz_dbar_comm hdc]

lemma complexHessian_closed {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 3 f p) (i j k : Fin 3) :
    dz (fun q => complexHessian f q k j) p i =
      dz (fun q => complexHessian f q i j) p k := by
  exact dz_dz_comm (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 2) (by norm_num) j) i k

lemma hartogsMetric_hermitian {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (lam : ℝ) {p : Ambient} (hp : p ∈ hartogs φ) (i j : Fin 3) :
    hartogsMetric φ lam p i j = star (hartogsMetric φ lam p j i) :=
  complexHessian_hermitian ((metricPotential_contDiffAt hφ lam hp).of_le (by exact WithTop.coe_le_coe.mpr le_top)) i j

lemma hartogsMetric_closed {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (lam : ℝ) {p : Ambient} (hp : p ∈ hartogs φ) (i j k : Fin 3) :
    dz (fun q => hartogsMetric φ lam q k j) p i =
      dz (fun q => hartogsMetric φ lam q i j) p k :=
  complexHessian_closed ((metricPotential_contDiffAt hφ lam hp).of_le (by exact WithTop.coe_le_coe.mpr le_top)) i j k

def coordinateLinearEquiv : Ambient ≃ₗ[ℂ] Target where
  toFun := coordinates
  invFun t := (WithLp.toLp 2 ![t 0, t 1], t 2)
  left_inv p := by
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · rfl
  right_inv t := by
    funext i
    fin_cases i <;> rfl
  map_add' p q := by
    ext i
    fin_cases i <;> rfl
  map_smul' c p := by
    ext i
    fin_cases i <;> rfl

def coordinateEquiv : Ambient ≃L[ℂ] Target := coordinateLinearEquiv.toContinuousLinearEquiv

lemma dz_linear (L : Ambient →L[ℂ] ℂ) (p : Ambient) (i : Fin 3) :
    dz L p i = L (coordVector i) := by
  have hd : fderiv ℝ L p = L.restrictScalars ℝ := (L.restrictScalars ℝ).fderiv
  rw [dz, hd]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hI := Complex.I_sq
  linear_combination -L (coordVector i) / 2 * hI

lemma dbar_linear (L : Ambient →L[ℂ] ℂ) (p : Ambient) (i : Fin 3) :
    dbar L p i = 0 := by
  have hd : fderiv ℝ L p = L.restrictScalars ℝ := (L.restrictScalars ℝ).fderiv
  rw [dbar, hd]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hI := Complex.I_sq
  linear_combination L (coordVector i) / 2 * hI

lemma dbar_linear_norm_sq (L : Ambient →L[ℂ] ℂ) (p : Ambient) (i : Fin 3) :
    dbar (fun q => (‖L q‖ ^ 2 : ℝ)) p i = L p * star (L (coordVector i)) := by
  have he (q : Ambient) : ((‖L q‖ ^ 2 : ℝ) : ℂ) = L q * star (L q) := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj (L q)).symm
  simp only [he]
  rw [dbar_mul (L.differentiableAt.restrictScalars ℝ) (L.differentiableAt.restrictScalars ℝ).star,
      dbar_linear, dbar_conj (L.differentiableAt.restrictScalars ℝ), dz_linear]
  simp

lemma dz_linear_norm_sq (L : Ambient →L[ℂ] ℂ) (p : Ambient) (i : Fin 3) :
    dz (fun q => (‖L q‖ ^ 2 : ℝ)) p i = star (L p) * L (coordVector i) := by
  have he (q : Ambient) : ((‖L q‖ ^ 2 : ℝ) : ℂ) = L q * star (L q) := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj (L q)).symm
  simp only [he]
  rw [dz_mul (L.differentiableAt.restrictScalars ℝ) (L.differentiableAt.restrictScalars ℝ).star,
      dz_linear, dz_conj (L.differentiableAt.restrictScalars ℝ), dbar_linear]
  simp [mul_comm]

lemma complexHessian_linear_norm_sq (L : Ambient →L[ℂ] ℂ) (p : Ambient) (i j : Fin 3) :
    complexHessian (fun q => ‖L q‖ ^ 2) p i j = L (coordVector i) * star (L (coordVector j)) := by
  unfold complexHessian
  simp only [dbar_linear_norm_sq]
  rw [dz_mul (L.differentiableAt.restrictScalars ℝ) (differentiableAt_const _), dz_linear]
  simp [dz]

private def coordCLM (i : Fin 3) : Ambient →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp coordinateEquiv.toContinuousLinearMap

private lemma coordCLM_apply (i : Fin 3) (u : Ambient) : coordCLM i u = coordinates u i := rfl

private lemma coordCLM_coordVector (i j : Fin 3) :
    coordCLM i (coordVector j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [coordCLM_apply, coordinates, coordVector]

lemma base_norm_sq_coordinates (p : Ambient) :
    ‖p.1‖ ^ 2 = ‖coordCLM 0 p‖ ^ 2 + ‖coordCLM 1 p‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  rfl

lemma complexHessian_base_norm_sq (p : Ambient) (i j : Fin 3) :
    complexHessian (fun q : Ambient => ‖q.1‖ ^ 2) p i j =
      (if i = 0 then 1 else 0) * (if j = 0 then 1 else 0) +
      (if i = 1 then 1 else 0) * (if j = 1 then 1 else 0) := by
  have hC (k : Fin 3) : ContDiffAt ℝ 2 (fun q => ‖coordCLM k q‖ ^ 2) p :=
    (contDiff_norm_sq ℂ).contDiffAt.comp p ((coordCLM k).contDiff.restrict_scalars ℝ).contDiffAt
  simp only [base_norm_sq_coordinates]
  rw [complexHessian_add (hC 0) (hC 1), complexHessian_linear_norm_sq, complexHessian_linear_norm_sq]
  simp only [coordCLM_coordVector]
  fin_cases i <;> fin_cases j <;> norm_num

lemma dbar_base_norm_sq (p : Ambient) (i : Fin 3) :
    dbar (fun q : Ambient => (‖q.1‖ ^ 2 : ℝ)) p i =
      p.1 0 * (if i = 0 then 1 else 0) + p.1 1 * (if i = 1 then 1 else 0) := by
  have hd (k : Fin 3) : DifferentiableAt ℝ (fun q : Ambient => ((‖coordCLM k q‖ ^ 2 : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p (((contDiff_norm_sq ℂ (n := 1)).contDiffAt.comp p ((coordCLM k).contDiff.restrict_scalars ℝ).contDiffAt).differentiableAt (by norm_num))
  simp only [base_norm_sq_coordinates, Complex.ofReal_add]
  rw [dbar_add (hd 0) (hd 1), dbar_linear_norm_sq, dbar_linear_norm_sq]
  simp only [coordCLM_apply]
  fin_cases i <;> simp [coordinates, coordVector]

lemma dz_base_norm_sq (p : Ambient) (i : Fin 3) :
    dz (fun q : Ambient => (‖q.1‖ ^ 2 : ℝ)) p i =
      star (p.1 0) * (if i = 0 then 1 else 0) + star (p.1 1) * (if i = 1 then 1 else 0) := by
  have hd (k : Fin 3) : DifferentiableAt ℝ (fun q : Ambient => ((‖coordCLM k q‖ ^ 2 : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p (((contDiff_norm_sq ℂ (n := 1)).contDiffAt.comp p ((coordCLM k).contDiff.restrict_scalars ℝ).contDiffAt).differentiableAt (by norm_num))
  simp only [base_norm_sq_coordinates, Complex.ofReal_add]
  rw [dz_add (hd 0) (hd 1), dz_linear_norm_sq, dz_linear_norm_sq]
  simp only [coordCLM_apply]
  fin_cases i <;> simp [coordinates, coordVector]

lemma dz_lift_base {f : Base → ℂ} {p : Ambient} (hf : DifferentiableAt ℝ f p.1) (i : Fin 3) :
    dz (fun q : Ambient => f q.1) p i = ![dzBase f p.1 0, dzBase f p.1 1, 0] i := by
  have hd : fderiv ℝ (fun q : Ambient => f q.1) p =
      (fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ Base ℂ) :=
    (hf.hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ Base ℂ).hasFDerivAt).fderiv
  fin_cases i <;> simp [dz, dzBase, hd, coordVector]

lemma dbar_lift_base {f : Base → ℂ} {p : Ambient} (hf : DifferentiableAt ℝ f p.1) (i : Fin 3) :
    dbar (fun q : Ambient => f q.1) p i = ![dbarBase f p.1 0, dbarBase f p.1 1, 0] i := by
  have hd : fderiv ℝ (fun q : Ambient => f q.1) p =
      (fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ Base ℂ) :=
    (hf.hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ Base ℂ).hasFDerivAt).fderiv
  fin_cases i <;> simp [dbar, dbarBase, hd, coordVector]

lemma _root_.OAI.ContDiffAt.hartogs_dbarBase {f : Base → ℂ} {p : Base} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hmn : m + 1 ≤ n) (i : Fin 2) :
    ContDiffAt ℝ m (fun q => dbarBase f q i) p := by
  have hd := hf.fderiv_right hmn
  unfold PinchedHartogs.dbarBase
  exact ((hd.clm_apply contDiffAt_const).add
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

lemma complexHessian_lift_base {f : Base → ℝ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p.1)
    (i j : Fin 3) :
    complexHessian (fun q : Ambient => f q.1) p i j =
      !![baseHessian f p.1 0 0, baseHessian f p.1 0 1, 0;
         baseHessian f p.1 1 0, baseHessian f p.1 1 1, 0;
         0, 0, 0] i j := by
  have hfc : ContDiffAt ℝ 2 (fun z => (f z : ℂ)) p.1 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p.1 hf
  have hd (k : Fin 2) : DifferentiableAt ℝ (fun z => dbarBase (fun r => (f r : ℂ)) z k) p.1 :=
    (_root_.OAI.ContDiffAt.hartogs_dbarBase hfc (m := 1) (by norm_num) k).differentiableAt (by norm_num)
  have he : (fun q : Ambient => dbar (fun r : Ambient => (f r.1 : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q : Ambient => ![dbarBase (fun r => (f r : ℂ)) q.1 0,
        dbarBase (fun r => (f r : ℂ)) q.1 1, 0] j) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hfc.eventually (by norm_num))] with q hq
    change ContDiffAt ℝ 2 (fun z => (f z : ℂ)) q.1 at hq
    exact dbar_lift_base (hq.differentiableAt (by norm_num)) j
  unfold complexHessian
  rw [dz_congr he]
  fin_cases i <;> fin_cases j
  all_goals first
    | exact dz_lift_base (hd 0) _
    | exact dz_lift_base (hd 1) _
    | simp [dz]

lemma hermitianValue_lift_base {f : Base → ℝ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p.1)
    (u v : Ambient) :
    hermitianValue (complexHessian (fun q : Ambient => f q.1) p) u v =
      ∑ i, ∑ j, baseHessian f p.1 i j * u.1 i * star (v.1 j) := by
  simp [hermitianValue, complexHessian_lift_base hf, Fin.sum_univ_three, Fin.sum_univ_two, coordinates]

lemma hermitianValue_add (A B : CMatrix) (u v : Ambient) :
    hermitianValue (A + B) u v = hermitianValue A u v + hermitianValue B u v := by
  simp [hermitianValue, add_mul, Finset.sum_add_distrib]

lemma hermitianValue_smul (c : ℂ) (A : CMatrix) (u v : Ambient) :
    hermitianValue (c • A) u v = c * hermitianValue A u v := by
  simp [hermitianValue, Finset.mul_sum, mul_assoc]

lemma hermitianValue_rank_one (a : Fin 3 → ℂ) (u v : Ambient) :
    hermitianValue (fun i j => a i * star (a j)) u v =
      (∑ i, a i * coordinates u i) * star (∑ i, a i * coordinates v i) := by
  simp [hermitianValue, Fin.sum_univ_three, star_add, star_mul]
  ring

lemma hermitianValue_rank_one_self (a : Fin 3 → ℂ) (u : Ambient) :
    (hermitianValue (fun i j => a i * star (a j)) u u).re =
      ‖∑ i, a i * coordinates u i‖ ^ 2 := by
  rw [hermitianValue_rank_one]
  simpa only [Complex.normSq_eq_norm_sq, Complex.star_def, Complex.ofReal_re] using
    congrArg Complex.re (Complex.mul_conj (∑ i, a i * coordinates u i))

lemma hermitianValue_base_norm_sq (p u v : Ambient) :
    hermitianValue (complexHessian (fun q : Ambient => ‖q.1‖ ^ 2) p) u v =
      u.1 0 * star (v.1 0) + u.1 1 * star (v.1 1) := by
  simp [hermitianValue, complexHessian_base_norm_sq, Fin.sum_univ_three, coordinates]

lemma hermitianValue_base_norm_sq_self (p u : Ambient) :
    (hermitianValue (complexHessian (fun q : Ambient => ‖q.1‖ ^ 2) p) u u).re = ‖u.1‖ ^ 2 := by
  rw [hermitianValue_base_norm_sq, Complex.add_re, base_norm_sq_coordinates]
  simp only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, coordCLM_apply, coordinates, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma hermitianValue_psi_self {p : Ambient} (hp : p.1 ∈ ball) (u : Ambient) :
    (hermitianValue (complexHessian (fun q : Ambient => psi q.1) p) u u).re =
      (1 - ‖p.1‖ ^ 2)⁻¹ * ‖u.1‖ ^ 2 + ((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹ *
        ‖star (p.1 0) * u.1 0 + star (p.1 1) * u.1 1‖ ^ 2 := by
  have hρ : 0 < 1 - ‖p.1‖ ^ 2 := by
    have := norm_nonneg p.1
    change ‖p.1‖ < 1 at hp
    nlinarith
  have hf : ContDiffAt ℝ 2 (fun q : Ambient => ‖q.1‖ ^ 2) p :=
    (contDiff_norm_sq ℂ).contDiffAt.comp p contDiffAt_fst
  let a : Fin 3 → ℂ := ![star (p.1 0), star (p.1 1), 0]
  let R : CMatrix := fun i j => a i * star (a j)
  have hm : complexHessian (fun q : Ambient => psi q.1) p =
      ((1 - ‖p.1‖ ^ 2)⁻¹ : ℝ) • complexHessian (fun q : Ambient => ‖q.1‖ ^ 2) p +
      (((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹ : ℝ) • R := by
    ext i j
    change complexHessian (fun q : Ambient => -Real.log (1 - ‖q.1‖ ^ 2)) p i j =
      (((1 - ‖p.1‖ ^ 2)⁻¹ : ℝ) : ℂ) * complexHessian (fun q : Ambient => ‖q.1‖ ^ 2) p i j +
      ((((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) * (a i * star (a j))
    rw [complexHessian_negLogOneSub hf hρ.ne', dz_base_norm_sq, dbar_base_norm_sq]
    fin_cases i <;> fin_cases j <;> simp [a, mul_assoc]
  rw [hm, hermitianValue_add]
  have hsm (t : ℝ) (M : CMatrix) : (hermitianValue (t • M) u u).re = t * (hermitianValue M u u).re := by
    change (hermitianValue ((t : ℂ) • M) u u).re = _
    rw [hermitianValue_smul]
    simp
  rw [Complex.add_re, hsm, hsm, hermitianValue_base_norm_sq_self]
  change _ = _
  rw [show R = (fun i j => a i * star (a j)) from rfl, hermitianValue_rank_one_self]
  simp [a, Fin.sum_univ_three, coordinates]

lemma hermitianValue_real_smul (c : ℝ) (A : CMatrix) (u v : Ambient) :
    (hermitianValue (c • A) u v).re = c * (hermitianValue A u v).re := by
  change (hermitianValue ((c : ℂ) • A) u v).re = _
  rw [hermitianValue_smul]
  simp

def IsPshBase (φ : Base → ℝ) : Prop :=
  ∀ z ∈ ball, ∀ v : Base, 0 ≤ (∑ i, ∑ j, baseHessian φ z i j * v i * star (v j)).re

lemma hartogsMetric_value {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (lam : ℝ) {p : Ambient} (hp : p ∈ hartogs φ) (u : Ambient) :
    (hermitianValue (hartogsMetric φ lam p) u u).re =
      lam * (hermitianValue (complexHessian (fun q : Ambient => psi q.1) p) u u).re +
      (Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2)) *
        (∑ i, ∑ j, baseHessian φ p.1 i j * u.1 i * star (u.1 j)).re +
      (Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2) *
        ‖u.2 + p.2 * (dzBase (fun z => (φ z : ℂ)) p.1 0 * u.1 0 +
          dzBase (fun z => (φ z : ℂ)) p.1 1 * u.1 1)‖ ^ 2 := by
  have hf : ContDiffAt ℝ 2 φ p.1 :=
    (hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hdf := hf.differentiableAt (by norm_num)
  have hd : DifferentiableAt ℝ (fun q : Ambient => φ q.1) p := hdf.comp p differentiableAt_fst
  let a : Fin 3 → ℂ := fun i => (if i = 2 then 1 else 0) +
    p.2 * dz (fun q : Ambient => (φ q.1 : ℂ)) p i
  have ha (j : Fin 3) : star (a j) = (if j = 2 then 1 else 0) +
      star p.2 * dbar (fun q : Ambient => (φ q.1 : ℂ)) p j := by
    rw [dbar_eq_star_dz_real hd]
    simp [a]
  let R : CMatrix := fun i j => a i * star (a j)
  have hm : hartogsMetric φ lam p =
      lam • complexHessian (fun q : Ambient => psi q.1) p +
      (Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2)) •
        complexHessian (fun q : Ambient => φ q.1) p +
      (Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2) •
        R := by
    ext i j
    change hartogsMetric φ lam p i j =
      (lam : ℂ) * complexHessian (fun q : Ambient => psi q.1) p i j +
      ((Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) : ℝ) : ℂ) *
        complexHessian (fun q : Ambient => φ q.1) p i j +
      ((Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        (a i * star (a j))
    rw [hartogsMetric_smooth_form hφ lam hp, ha]
    simp only [a]
    ring
  rw [hm, hermitianValue_add, hermitianValue_add, Complex.add_re, Complex.add_re,
    hermitianValue_real_smul, hermitianValue_real_smul, hermitianValue_real_smul,
    hermitianValue_lift_base hf]
  rw [show R = (fun i j => a i * star (a j)) from rfl, hermitianValue_rank_one_self]
  have hdc : DifferentiableAt ℝ (fun z => (φ z : ℂ)) p.1 :=
    Complex.ofRealCLM.differentiableAt.comp p.1 hdf
  have hz (i : Fin 3) := dz_lift_base (p := p) hdc i
  have hasum : (∑ i, a i * coordinates u i) = u.2 + p.2 *
      (dzBase (fun z => (φ z : ℂ)) p.1 0 * u.1 0 +
        dzBase (fun z => (φ z : ℂ)) p.1 1 * u.1 1) := by
    simp [a, hz, Fin.sum_univ_three, coordinates]
    ring
  rw [hasum]

lemma hartogsMetric_positive {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam) {p : Ambient} (hp : p ∈ hartogs φ)
    {u : Ambient} (hu : u ≠ 0) :
    0 < (hermitianValue (hartogsMetric φ lam p) u u).re := by
  rw [hartogsMetric_value hφ lam hp, hermitianValue_psi_self hp.1]
  have hD : 0 < 1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2 := sub_pos.mpr hp.2
  have hρ : 0 < 1 - ‖p.1‖ ^ 2 := by
    have hn := norm_nonneg p.1
    have hz : ‖p.1‖ < 1 := hp.1
    nlinarith
  have hx : 0 ≤ Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) := by positivity
  have hH := hpsh p.1 hp.1 u.1
  have hB := mul_nonneg hx hH
  have hV : 0 < Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2 := by positivity
  by_cases huz : u.1 = 0
  · have huw : u.2 ≠ 0 := by
      intro h
      exact hu (Prod.ext huz h)
    simp only [huz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add,
      PiLp.zero_apply, add_zero]
    have hvpos : 0 < ‖u.2‖ ^ 2 := pow_pos (norm_pos_iff.mpr huw) _
    simpa using mul_pos hV hvpos
  · have hi : 0 < (1 - ‖p.1‖ ^ 2)⁻¹ * ‖u.1‖ ^ 2 := by positivity
    have hi2 : 0 ≤ ((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹ *
        ‖star (p.1 0) * u.1 0 + star (p.1 1) * u.1 1‖ ^ 2 := by positivity
    have hvnonneg := mul_nonneg hV.le (sq_nonneg ‖u.2 + p.2 *
      (dzBase (fun z => (φ z : ℂ)) p.1 0 * u.1 0 + dzBase (fun z => (φ z : ℂ)) p.1 1 * u.1 1)‖)
    have hh := mul_pos hlam (add_pos_of_pos_of_nonneg hi hi2)
    linarith

theorem hartogsMetric_isKahler {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam) :
    IsKahlerMetric (hartogs φ) (hartogsMetric φ lam) := by
  refine ⟨hartogsMetric_contDiffOn hφ lam, (fun p hp => hartogsMetric_hermitian hφ lam hp), ?_, (fun p hp => hartogsMetric_closed hφ lam hp)⟩
  intro p hp u hu
  exact hartogsMetric_positive hφ hpsh hlam hp hu

lemma coordinates_real_decomposition (u : Ambient) :
    u = ∑ i : Fin 3, ((coordinates u i).re • coordVector i +
      (coordinates u i).im • (Complex.I • coordVector i)) := by
  apply Prod.ext
  · ext j
    fin_cases j <;>
      simp [Fin.sum_univ_three, coordinates, coordVector, Complex.re_add_im, Complex.real_smul]
  · simp [Fin.sum_univ_three, coordinates, coordVector, Complex.re_add_im, Complex.real_smul]

private lemma wirtinger_pair_algebra (a b z : ℂ) :
    (a - Complex.I * b) / 2 * z + (a + Complex.I * b) / 2 * star z =
      (z.re : ℂ) * a + (z.im : ℂ) * b := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma fderiv_wirtinger (f : Ambient → ℂ) (p u : Ambient) :
    fderiv ℝ f p u = ∑ i : Fin 3,
      (dz f p i * coordinates u i + dbar f p i * star (coordinates u i)) := by
  conv_lhs => rw [coordinates_real_decomposition u]
  simp only [map_sum, map_add, map_smul, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro i hi
  exact (wirtinger_pair_algebra _ _ _).symm

lemma fderiv_real_wirtinger {f : Ambient → ℝ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (u : Ambient) :
    fderiv ℝ f p u = 2 * (∑ i, dz (fun q => (f q : ℂ)) p i * coordinates u i).re := by
  have h := congrArg Complex.re (fderiv_wirtinger (fun q => (f q : ℂ)) p u)
  rw [fderiv_real_cast hf] at h
  simpa [dbar_eq_star_dz_real hf, star_mul, ← star_mul, Complex.add_re,
    Finset.sum_add_distrib, ← two_mul, mul_comm, ← Finset.sum_mul] using h

lemma dz_psi {p : Ambient} (hp : p.1 ∈ ball) (i : Fin 3) :
    dz (fun q : Ambient => (psi q.1 : ℂ)) p i =
      ((1 - ‖p.1‖ ^ 2)⁻¹ : ℝ) *
        (star (p.1 0) * (if i = 0 then 1 else 0) + star (p.1 1) * (if i = 1 then 1 else 0)) := by
  have hρ : 0 < 1 - ‖p.1‖ ^ 2 := by
    have hn := norm_nonneg p.1
    change ‖p.1‖ < 1 at hp
    nlinarith
  have hf : DifferentiableAt ℝ (fun q : Ambient => ‖q.1‖ ^ 2) p :=
    ((contDiff_norm_sq ℂ (n := 1)).contDiffAt.comp p contDiffAt_fst).differentiableAt (by norm_num)
  exact (dz_real_comp hf (negLogOneSub_hasDerivAt hρ.ne') i).trans (by rw [dz_base_norm_sq])

lemma fderiv_psi {p : Ambient} (hp : p.1 ∈ ball) (u : Ambient) :
    fderiv ℝ (fun q : Ambient => psi q.1) p u =
      2 * (1 - ‖p.1‖ ^ 2)⁻¹ * (star (p.1 0) * u.1 0 + star (p.1 1) * u.1 1).re := by
  have hf : DifferentiableAt ℝ (fun q : Ambient => psi q.1) p :=
    ((psi_contDiffAt hp).comp p contDiffAt_fst).differentiableAt (by simp)
  rw [fderiv_real_wirtinger hf]
  have hs : (∑ i, dz (fun q : Ambient => (psi q.1 : ℂ)) p i * coordinates u i) =
      (((1 - ‖p.1‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        (star (p.1 0) * u.1 0 + star (p.1 1) * u.1 1) := by
    simp only [dz_psi hp, Fin.sum_univ_three]
    norm_num [coordinates, show (2 : Fin 3) ≠ 0 from by decide,
      show (2 : Fin 3) ≠ 1 from by decide]
    ring
  rw [hs, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma psi_derivative_sq_le {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam) {p : Ambient} (hp : p ∈ hartogs φ)
    (u : Ambient) :
    lam * (fderiv ℝ (fun q : Ambient => psi q.1) p u) ^ 2 ≤
      4 * (hermitianValue (hartogsMetric φ lam p) u u).re := by
  rw [fderiv_psi hp.1, hartogsMetric_value hφ lam hp, hermitianValue_psi_self hp.1]
  have hD : 0 < 1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2 := sub_pos.mpr hp.2
  have hρ : 0 < 1 - ‖p.1‖ ^ 2 := by
    have hn := norm_nonneg p.1
    have hz : ‖p.1‖ < 1 := hp.1
    nlinarith
  have hx : 0 ≤ Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) := by positivity
  have hH := mul_nonneg hx (hpsh p.1 hp.1 u.1)
  have hV : 0 ≤ Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2 *
      ‖u.2 + p.2 * (dzBase (fun z => (φ z : ℂ)) p.1 0 * u.1 0 +
        dzBase (fun z => (φ z : ℂ)) p.1 1 * u.1 1)‖ ^ 2 := by positivity
  have hN : 0 ≤ (1 - ‖p.1‖ ^ 2)⁻¹ * ‖u.1‖ ^ 2 := by positivity
  have hsq (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  have hS := mul_le_mul_of_nonneg_left (hsq (star (p.1 0) * u.1 0 + star (p.1 1) * u.1 1))
    (show 0 ≤ lam * ((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹ by positivity)
  simp only [← inv_pow] at hS ⊢
  nlinarith [mul_nonneg hlam.le hN]

def fiberParameter (φ : Base → ℝ) (p : Ambient) : ℝ := Real.exp (φ p.1) * ‖p.2‖ ^ 2

def fiberPotential (φ : Base → ℝ) (p : Ambient) : ℝ := -Real.log (1 - fiberParameter φ p)

def thetaValue (φ : Base → ℝ) (p u : Ambient) : ℂ :=
  u.2 + p.2 * (dzBase (fun z => (φ z : ℂ)) p.1 0 * u.1 0 +
    dzBase (fun z => (φ z : ℂ)) p.1 1 * u.1 1)

lemma fiberPotential_contDiffAt {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {p : Ambient} (hp : p ∈ hartogs φ) : ContDiffAt ℝ ∞ (fiberPotential φ) p := by
  have hf := (hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).comp p contDiffAt_fst
  exact ((contDiffAt_const.sub (hf.exp.mul
    ((contDiff_norm_sq ℂ).contDiffAt.comp p contDiffAt_snd))).log (sub_pos.mpr hp.2).ne').neg

lemma dz_fiberPotential {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {p : Ambient} (hp : p ∈ hartogs φ) (i : Fin 3) :
    dz (fun q => (fiberPotential φ q : ℂ)) p i =
      ((Real.exp (φ p.1) / (1 - fiberParameter φ p) : ℝ) : ℂ) * star p.2 *
        ((if i = 2 then 1 else 0) + p.2 * dz (fun q : Ambient => (φ q.1 : ℂ)) p i) := by
  have hf : DifferentiableAt ℝ (fun q : Ambient => φ q.1) p :=
    ((hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).comp p contDiffAt_fst).differentiableAt (by simp)
  have hr : DifferentiableAt ℝ (fun q : Ambient => ‖q.2‖ ^ 2) p :=
    ((contDiff_norm_sq ℂ (n := 1)).contDiffAt.comp p contDiffAt_snd).differentiableAt (by norm_num)
  have he := hf.exp
  change dz (fun q : Ambient => ((-Real.log (1 - Real.exp (φ q.1) * ‖q.2‖ ^ 2) : ℝ) : ℂ)) p i = _
  have ht : DifferentiableAt ℝ (fun q : Ambient => Real.exp (φ q.1) * ‖q.2‖ ^ 2) p := he.mul hr
  rw [dz_real_comp ht (negLogOneSub_hasDerivAt (sub_pos.mpr hp.2).ne'),
    dz_real_mul he hr, dz_real_comp hf (Real.hasDerivAt_exp _), dz_fiber_norm_sq]
  have hn : ((‖p.2‖ ^ 2 : ℝ) : ℂ) = p.2 * star p.2 := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj p.2).symm
  simp only [fiberParameter, Complex.ofReal_inv, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hn]
  ring

lemma fderiv_fiberPotential {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {p : Ambient} (hp : p ∈ hartogs φ) (u : Ambient) :
    fderiv ℝ (fiberPotential φ) p u =
      2 * (Real.exp (φ p.1) / (1 - fiberParameter φ p)) * (star p.2 * thetaValue φ p u).re := by
  rw [fderiv_real_wirtinger ((fiberPotential_contDiffAt hφ hp).differentiableAt (by simp))]
  have hdc : DifferentiableAt ℝ (fun z : Base => (φ z : ℂ)) p.1 :=
    Complex.ofRealCLM.differentiableAt.comp p.1
      ((hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).differentiableAt (by simp))
  have hs : (∑ i, dz (fun q : Ambient => (fiberPotential φ q : ℂ)) p i * coordinates u i) =
      ((Real.exp (φ p.1) / (1 - fiberParameter φ p) : ℝ) : ℂ) *
        (star p.2 * thetaValue φ p u) := by
    simp only [dz_fiberPotential hφ hp, dz_lift_base hdc, Fin.sum_univ_three]
    simp [coordinates, thetaValue, show (0 : Fin 3) ≠ 2 from by decide,
      show (1 : Fin 3) ≠ 2 from by decide, Matrix.cons_val_two]
    ring
  rw [hs, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma fiberPotential_derivative_sq_le {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam) {p : Ambient} (hp : p ∈ hartogs φ)
    (u : Ambient) :
    (fderiv ℝ (fiberPotential φ) p u) ^ 2 ≤
      4 * (hermitianValue (hartogsMetric φ lam p) u u).re := by
  have hD : 0 < 1 - fiberParameter φ p := sub_pos.mpr hp.2
  have ht : 0 ≤ fiberParameter φ p := by unfold fiberParameter; positivity
  have ht1 : fiberParameter φ p < 1 := hp.2
  have hi : 0 ≤ (hermitianValue (complexHessian (fun q : Ambient => psi q.1) p) u u).re := by
    rw [hermitianValue_psi_self hp.1]
    have hρ : 0 < 1 - ‖p.1‖ ^ 2 := by
      have hn := norm_nonneg p.1
      have hz : ‖p.1‖ < 1 := hp.1
      nlinarith
    positivity
  have hh := mul_nonneg (div_nonneg ht hD.le) (hpsh p.1 hp.1 u.1)
  have hv : 0 ≤ Real.exp (φ p.1) / (1 - fiberParameter φ p) ^ 2 * ‖thetaValue φ p u‖ ^ 2 := by positivity
  have hm : Real.exp (φ p.1) / (1 - fiberParameter φ p) ^ 2 * ‖thetaValue φ p u‖ ^ 2 ≤
      (hermitianValue (hartogsMetric φ lam p) u u).re := by
    rw [hartogsMetric_value hφ lam hp]
    change _ ≤ lam * _ + fiberParameter φ p / (1 - fiberParameter φ p) * _ +
      Real.exp (φ p.1) / (1 - fiberParameter φ p) ^ 2 * ‖thetaValue φ p u‖ ^ 2
    linarith [mul_nonneg hlam.le hi]
  have hs : (star p.2 * thetaValue φ p u).re ^ 2 ≤ ‖p.2‖ ^ 2 * ‖thetaValue φ p u‖ ^ 2 := by
    have hh := Complex.sq_norm_sub_sq_re (star p.2 * thetaValue φ p u)
    rw [norm_mul, norm_star, mul_pow] at hh
    nlinarith [sq_nonneg (star p.2 * thetaValue φ p u).im]
  rw [fderiv_fiberPotential hφ hp]
  have hs' := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (Real.exp (φ p.1) / (1 - fiberParameter φ p)) ^ 2 by positivity)
  have he : (Real.exp (φ p.1) / (1 - fiberParameter φ p)) ^ 2 *
      (‖p.2‖ ^ 2 * ‖thetaValue φ p u‖ ^ 2) = fiberParameter φ p *
        (Real.exp (φ p.1) / (1 - fiberParameter φ p) ^ 2 * ‖thetaValue φ p u‖ ^ 2) := by
    simp only [fiberParameter, div_pow]
    ring
  rw [he] at hs'
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) hv]

def hartogsCompactSet (φ : Base → ℝ) (ρ τ : ℝ) : Set Ambient :=
  {p | ‖p.1‖ ≤ ρ ∧ fiberParameter φ p ≤ τ}

lemma exp_half_sq (a : ℝ) : (Real.exp (a / 2)) ^ 2 = Real.exp a := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

lemma norm_exp_half_smul_sq (a : ℝ) (w : ℂ) :
    ‖Real.exp (a / 2) • w‖ ^ 2 = Real.exp a * ‖w‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, exp_half_sq]

lemma fiberParameter_exp_neg_half (φ : Base → ℝ) (z : Base) (w : ℂ) :
    fiberParameter φ (z, Real.exp (-φ z / 2) • w) = ‖w‖ ^ 2 := by
  unfold fiberParameter
  rw [norm_exp_half_smul_sq, ← mul_assoc, ← Real.exp_add]
  simp

lemma hartogsCompactSet_subset {φ : Base → ℝ} {ρ τ : ℝ} (hρ : ρ < 1) (hτ : τ < 1) :
    hartogsCompactSet φ ρ τ ⊆ hartogs φ := by
  intro p hp
  exact ⟨lt_of_le_of_lt hp.1 hρ, lt_of_le_of_lt hp.2 hτ⟩

lemma hartogsCompactSet_isCompact {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {ρ τ : ℝ} (hρ : ρ < 1) (hτ : 0 ≤ τ) : IsCompact (hartogsCompactSet φ ρ τ) := by
  let K : Set Ambient := Metric.closedBall (0 : Base) ρ ×ˢ Metric.closedBall (0 : ℂ) (Real.sqrt τ)
  let F : Ambient → Ambient := fun p => (p.1, Real.exp (-φ p.1 / 2) • p.2)
  have hK : IsCompact K := (isCompact_closedBall (0 : Base) ρ).prod
    (isCompact_closedBall (0 : ℂ) (Real.sqrt τ))
  have hz : ∀ p ∈ K, p.1 ∈ ball := by
    intro p hp
    exact lt_of_le_of_lt (by simpa using hp.1) hρ
  have hF : ContinuousOn F K := continuousOn_fst.prodMk
    ((Real.continuous_exp.comp_continuousOn
      (((hφ.continuousOn.comp continuousOn_fst hz).neg).div_const 2)).smul continuousOn_snd)
  have he : F '' K = hartogsCompactSet φ ρ τ := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨by simpa [F] using hq.1, ?_⟩
      change fiberParameter φ (q.1, Real.exp (-φ q.1 / 2) • q.2) ≤ τ
      rw [fiberParameter_exp_neg_half]
      have hn : ‖q.2‖ ≤ Real.sqrt τ := by simpa using hq.2
      nlinarith [Real.sq_sqrt hτ, norm_nonneg q.2]
    · intro hp
      refine ⟨(p.1, Real.exp (φ p.1 / 2) • p.2), ?_, ?_⟩
      · refine ⟨by simpa using hp.1, ?_⟩
        change dist (Real.exp (φ p.1 / 2) • p.2) 0 ≤ Real.sqrt τ
        rw [dist_zero_right]
        have hh := norm_exp_half_smul_sq (φ p.1) p.2
        have ht : Real.exp (φ p.1) * ‖p.2‖ ^ 2 ≤ τ := hp.2
        nlinarith [Real.sq_sqrt hτ, Real.sqrt_nonneg τ, norm_nonneg (Real.exp (φ p.1 / 2) • p.2)]
      · refine Prod.ext (by rfl) ?_
        change Real.exp (-φ p.1 / 2) • (Real.exp (φ p.1 / 2) • p.2) = p.2
        rw [smul_smul, ← Real.exp_add]
        have hh : -φ p.1 / 2 + φ p.1 / 2 = 0 := by ring
        rw [hh, Real.exp_zero, one_smul]
  rw [← he]
  exact hK.image_of_continuousOn hF

lemma hartogs_barrier_sublevels_compact {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (a b : ℝ) : ∃ K : Set Ambient, IsCompact K ∧ K ⊆ hartogs φ ∧
      ∀ p ∈ hartogs φ, fiberPotential φ p ≤ a → psi p.1 ≤ b → p ∈ K := by
  let τ := max 0 (1 - Real.exp (-a))
  let ρ := Real.sqrt (max 0 (1 - Real.exp (-b)))
  have hτ0 : 0 ≤ τ := le_max_left _ _
  have hτ1 : τ < 1 := max_lt (by norm_num) (by linarith [Real.exp_pos (-a)])
  have hρ1 : ρ < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    rw [one_pow]
    exact max_lt (by norm_num) (by linarith [Real.exp_pos (-b)])
  refine ⟨hartogsCompactSet φ ρ τ, hartogsCompactSet_isCompact hφ hρ1 hτ0,
    hartogsCompactSet_subset hρ1 hτ1, ?_⟩
  intro p hp ha hb
  have hD : 0 < 1 - fiberParameter φ p := sub_pos.mpr hp.2
  have hψ : 0 < 1 - ‖p.1‖ ^ 2 := by
    have hz : ‖p.1‖ < 1 := hp.1
    nlinarith [norm_nonneg p.1]
  have ha' : Real.exp (-a) ≤ 1 - fiberParameter φ p := by
    rw [← Real.exp_log hD]
    apply Real.exp_le_exp.mpr
    change -Real.log (1 - fiberParameter φ p) ≤ a at ha
    linarith
  have hb' : Real.exp (-b) ≤ 1 - ‖p.1‖ ^ 2 := by
    rw [← Real.exp_log hψ]
    apply Real.exp_le_exp.mpr
    change -Real.log (1 - ‖p.1‖ ^ 2) ≤ b at hb
    linarith
  refine ⟨?_, ?_⟩
  · have hh : ‖p.1‖ ^ 2 ≤ max 0 (1 - Real.exp (-b)) := by
      exact (by linarith : ‖p.1‖ ^ 2 ≤ 1 - Real.exp (-b)).trans (le_max_right _ _)
    have hr := Real.sq_sqrt (le_max_left 0 (1 - Real.exp (-b)))
    have hr0 := Real.sqrt_nonneg (max 0 (1 - Real.exp (-b)))
    change ‖p.1‖ ≤ Real.sqrt (max 0 (1 - Real.exp (-b)))
    nlinarith [norm_nonneg p.1]
  · exact (by linarith : fiberParameter φ p ≤ 1 - Real.exp (-a)).trans (le_max_right _ _)

lemma coordinates_equiv (u : Ambient) : coordinates u = coordinateEquiv u := rfl

@[simp] lemma coordinates_equiv_symm (v : Target) : coordinates (coordinateEquiv.symm v) = v :=
  coordinateEquiv.apply_symm_apply v

@[simp] lemma coordinates_zero : coordinates (0 : Ambient) = 0 := coordinateEquiv.map_zero

lemma coordinates_ne_zero {u : Ambient} (hu : u ≠ 0) : coordinates u ≠ 0 :=
  coordinateEquiv.map_ne_zero_iff.mpr hu

lemma matrix_isUnit_of_metric_positive {h : CMatrix}
    (hpos : ∀ u : Ambient, u ≠ 0 → 0 < (hermitianValue h u u).re) : IsUnit h := by
  have hk : ∀ v : Target, h.mulVec v = 0 → v = 0 := by
    intro v hv
    by_contra hn
    let u := coordinateEquiv.symm (star v)
    have hu : u ≠ 0 := by
      intro huu
      have hh := congrArg coordinates huu
      simp only [u, coordinates_equiv_symm, coordinates_zero] at hh
      exact hn (star_eq_zero.mp hh)
    have he : hermitianValue h u u = 0 := by
      simp only [hermitianValue, u, coordinates_equiv_symm, Pi.star_apply, star_star]
      calc
        (∑ i, ∑ j, h i j * star (v i) * v j) = ∑ i, star (v i) * (h.mulVec v) i := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          congr 1
          funext i
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = 0 := by simp [hv]
    have hh := hpos u hu
    rw [he, Complex.zero_re] at hh
    exact lt_irrefl _ hh
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  apply sub_eq_zero.mp
  apply hk
  rw [Matrix.mulVec_sub, hvw, sub_self]

lemma matrix_det_ne_zero_of_metric_positive {h : CMatrix}
    (hpos : ∀ u : Ambient, u ≠ 0 → 0 < (hermitianValue h u u).re) : h.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det h).mp (matrix_isUnit_of_metric_positive hpos)).ne_zero

lemma kahler_metric_det_ne_zero {M : Set Ambient} {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) : (g p).det ≠ 0 :=
  matrix_det_ne_zero_of_metric_positive (hg.2.2.1 p hp)

lemma matrix_contDiffAt_det {E : Type uKahler1607_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {g : E → CMatrix} {p : E} (hg : ContDiffAt ℝ n g p) :
    ContDiffAt ℝ n (fun q => (g q).det) p := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ hσ
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i hi
  exact contDiffAt_pi.mp (contDiffAt_pi.mp hg (σ i)) i

lemma matrix_contDiffAt_inv {E : Type uKahler1618_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {g : E → CMatrix} {p : E} (hg : ContDiffAt ℝ n g p)
    (hdet : (g p).det ≠ 0) : ContDiffAt ℝ n (fun q => (g q)⁻¹) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  apply ((matrix_contDiffAt_det hg).inv hdet).mul
  apply matrix_contDiffAt_det
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiffAt_const
  · simpa only [Matrix.updateRow_ne ha] using contDiffAt_pi.mp (contDiffAt_pi.mp hg a) b

def geodesicAcceleration (g : Ambient → CMatrix) (p v : Ambient) : Ambient :=
  coordinateEquiv.symm (fun k => -∑ a, ∑ c,
    christoffel g p k a c * coordinates v a * coordinates v c)

def geodesicField (g : Ambient → CMatrix) (y : Ambient × Ambient) : Ambient × Ambient :=
  (y.2, geodesicAcceleration g y.1 y.2)

lemma christoffel_contDiffAt {M : Set Ambient} (hM : IsOpen M) {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) (k a c : Fin 3) :
    ContDiffAt ℝ ∞ (fun q => christoffel g q k a c) p := by
  have hgs := hg.1.contDiffAt (hM.mem_nhds hp)
  have hinv := matrix_contDiffAt_inv hgs (kahler_metric_det_ne_zero hg hp)
  apply ContDiffAt.sum
  intro e he
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hinv e) k).mul
    (_root_.OAI.ContDiffAt.hartogs_dz (contDiffAt_pi.mp (contDiffAt_pi.mp hgs c) e) (by simp) a)

lemma geodesicField_contDiffAt {M : Set Ambient} (hM : IsOpen M) {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {y : Ambient × Ambient} (hy : y.1 ∈ M) :
    ContDiffAt ℝ ∞ (geodesicField g) y := by
  have hs : ContDiffAt ℝ ∞ (fun x : Ambient × Ambient => fun k : Fin 3 =>
      -∑ a, ∑ c, christoffel g x.1 k a c * coordinates x.2 a * coordinates x.2 c) y := by
    apply contDiffAt_pi.mpr
    intro k
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro a ha
    apply ContDiffAt.sum
    intro c hc
    exact (((christoffel_contDiffAt hM hg hy k a c).comp y contDiffAt_fst).mul
      (((coordCLM a).restrictScalars ℝ).contDiff.contDiffAt.comp y contDiffAt_snd)).mul
        (((coordCLM c).restrictScalars ℝ).contDiff.contDiffAt.comp y contDiffAt_snd)
  have ht := (coordinateEquiv.symm.contDiff.restrict_scalars ℝ).contDiffAt.comp y hs
  exact contDiffAt_snd.prodMk ht

lemma hermitianValue_conj {h : CMatrix} (hh : ∀ i j, h i j = star (h j i))
    (u v : Ambient) : hermitianValue h v u = star (hermitianValue h u v) := by
  simp only [hermitianValue, star_sum, star_mul', star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hh i j]
  simp only [star_star]
  ring

lemma christoffel_contract {g : Ambient → CMatrix} {p : Ambient}
    (hdet : (g p).det ≠ 0) (a c j : Fin 3) :
    (∑ k, g p k j * christoffel g p k a c) = dz (fun q => g q c j) p a := by
  simp only [christoffel, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ e, ∑ k, g p k j * ((g p)⁻¹ e k * dz (fun q => g q c e) p a)) =
        ∑ e, ((g p)⁻¹ * g p) e j * dz (fun q => g q c e) p a := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [Matrix.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by simp [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_apply]

def connectionCubic (g : Ambient → CMatrix) (p v : Ambient) : ℂ :=
  ∑ a, ∑ c, ∑ e, dz (fun q => g q c e) p a *
    coordinates v a * coordinates v c * star (coordinates v e)

lemma acceleration_contract {g : Ambient → CMatrix} {p : Ambient}
    (hdet : (g p).det ≠ 0) (v : Ambient) :
    hermitianValue (g p) (geodesicAcceleration g p v) v = -connectionCubic g p v := by
  have he (j : Fin 3) : (∑ i, g p i j * coordinates (geodesicAcceleration g p v) i) =
      -∑ a, ∑ c, dz (fun q => g q c j) p a * coordinates v a * coordinates v c := by
    simp only [geodesicAcceleration, coordinates_equiv_symm, mul_neg, Finset.mul_sum,
      Finset.sum_neg_distrib]
    congr 1
    calc
      (∑ i, ∑ a, ∑ c, g p i j *
          (christoffel g p i a c * coordinates v a * coordinates v c)) =
          ∑ a, ∑ c, (∑ i, g p i j * christoffel g p i a c) *
            coordinates v a * coordinates v c := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c hc
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by simp only [christoffel_contract hdet]
  simp only [hermitianValue]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, he, neg_mul, Finset.sum_neg_distrib]
  congr 1
  simp only [connectionCubic, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]

lemma metric_dbar_conj {M : Set Ambient} (hM : IsOpen M) {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) (i j a : Fin 3) :
    dbar (fun q => g q i j) p a = star (dz (fun q => g q j i) p a) := by
  have he : (fun q => g q i j) =ᶠ[𝓝 p] (fun q => star (g q j i)) := by
    filter_upwards [hM.mem_nhds hp] with q hq
    exact hg.2.1 q hq i j
  rw [dbar_congr he, dbar_conj]
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp
    (hg.1.contDiffAt (hM.mem_nhds hp)) j) i).differentiableAt (by simp)

lemma metric_derivative_contract {M : Set Ambient} (hM : IsOpen M) {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) (v : Ambient) :
    (∑ i, ∑ j, fderiv ℝ (fun q => g q i j) p v *
      coordinates v i * star (coordinates v j)) =
      connectionCubic g p v + star (connectionCubic g p v) := by
  simp only [fderiv_wirtinger, metric_dbar_conj hM hg hp,
    Finset.sum_mul, add_mul, Finset.sum_add_distrib, connectionCubic,
    star_sum, star_mul', star_star]
  congr 1
  · rw [Finset.sum_comm]
    simp only [Fin.sum_univ_three]
    ring
  · simp only [Fin.sum_univ_three]
    ring

def metricEnergy (g : Ambient → CMatrix) (y : Ambient × Ambient) : ℝ :=
  (hermitianValue (g y.1) y.2 y.2).re

lemma metric_energy_hasDerivAt_zero {M : Set Ambient} (hM : IsOpen M)
    {g : Ambient → CMatrix} (hg : IsKahlerMetric M g)
    {γ ν : ℝ → Ambient} {t : ℝ} (hp : γ t ∈ M)
    (hγ : HasDerivAt γ (ν t) t)
    (hν : HasDerivAt ν (geodesicAcceleration g (γ t) (ν t)) t) :
    HasDerivAt (fun s => (hermitianValue (g (γ s)) (ν s) (ν s)).re) 0 t := by
  let A := geodesicAcceleration g (γ t) (ν t)
  have hgij (i j : Fin 3) : DifferentiableAt ℝ (fun p => g p i j) (γ t) :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp
      (hg.1.contDiffAt (hM.mem_nhds hp)) i) j).differentiableAt (by simp)
  have hvi (i : Fin 3) : HasDerivAt (fun s => coordinates (ν s) i) (coordinates A i) t :=
    ((coordCLM i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hν
  let D : ℂ := ∑ i, ∑ j,
    ((fderiv ℝ (fun p => g p i j) (γ t) (ν t) * coordinates (ν t) i +
      g (γ t) i j * coordinates A i) * star (coordinates (ν t) j) +
      g (γ t) i j * coordinates (ν t) i * star (coordinates A j))
  have hd : HasDerivAt (fun s => hermitianValue (g (γ s)) (ν s) (ν s)) D t := by
    apply HasDerivAt.fun_sum
    intro i hi
    apply HasDerivAt.fun_sum
    intro j hj
    exact (((hgij i j).hasFDerivAt.comp_hasDerivAt t hγ).mul (hvi i)).mul (hvi j).star
  have he : D = 0 := by
    have hrewrite : D = (∑ i, ∑ j, fderiv ℝ (fun p => g p i j) (γ t) (ν t) *
        coordinates (ν t) i * star (coordinates (ν t) j)) +
        hermitianValue (g (γ t)) A (ν t) + hermitianValue (g (γ t)) (ν t) A := by
      simp only [D, hermitianValue, add_mul, Finset.sum_add_distrib]
    rw [hrewrite, hermitianValue_conj (hg.2.1 _ hp) A (ν t),
      acceleration_contract (kahler_metric_det_ne_zero hg hp),
      metric_derivative_contract hM hg hp, star_neg]
    ring
  simpa only [he, map_zero, Function.comp_def, Complex.reCLM_apply] using! (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd)

lemma geodesic_energy_hasDerivAt_zero {M : Set Ambient} (hM : IsOpen M)
    {g : Ambient → CMatrix} (hg : IsKahlerMetric M g)
    {y : ℝ → Ambient × Ambient} {t : ℝ} (hp : (y t).1 ∈ M)
    (hy : HasDerivAt y (geodesicField g (y t)) t) :
    HasDerivAt (fun s => metricEnergy g (y s)) 0 t :=
  metric_energy_hasDerivAt_zero hM hg hp hy.fst hy.snd

lemma coordinates_real_smul (c : ℝ) (v : Ambient) :
    coordinates (c • v) = c • coordinates v := by
  funext i
  fin_cases i <;> rfl

lemma hermitianValue_vector_real_smul (h : CMatrix) (c : ℝ) (v : Ambient) :
    (hermitianValue h (c • v) (c • v)).re = c ^ 2 * (hermitianValue h v v).re := by
  have he : hermitianValue h (c • v) (c • v) = (c : ℂ) ^ 2 * hermitianValue h v v := by
    simp only [hermitianValue, coordinates_real_smul, Pi.smul_apply, Complex.real_smul,
      star_mul', Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  simp [← Complex.ofReal_pow, Complex.mul_re]

lemma metricEnergy_nonneg {M : Set Ambient} {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) (v : Ambient) :
    0 ≤ metricEnergy g (p, v) := by
  by_cases hv : v = 0
  · simp [metricEnergy, hermitianValue, hv, coordinates_zero]
  · exact (hg.2.2.1 p hp v hv).le

lemma metricEnergy_continuousOn {M : Set Ambient} {g : Ambient → CMatrix}
    (hg : ContDiffOn ℝ ∞ g M) : ContinuousOn (metricEnergy g) (M ×ˢ (univ : Set Ambient)) := by
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro i hi
  apply continuousOn_finsetSum
  intro j hj
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact ((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn hg.continuousOn)).comp
          continuousOn_fst (fun _ h => h.1)
    · exact (((coordCLM i).continuous).comp continuous_snd).continuousOn
  · exact (continuous_star.comp (((coordCLM j).continuous).comp continuous_snd)).continuousOn

lemma compact_metric_coercivity {M K : Set Ambient} {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) (hK : IsCompact K) (hKM : K ⊆ M) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ K, ∀ v : Ambient,
      m * ‖v‖ ^ 2 ≤ metricEnergy g (p, v) := by
  have hs := hK.prod (isCompact_sphere (0 : Ambient) 1)
  have hc : ContinuousOn (metricEnergy g) (K ×ˢ Metric.sphere (0 : Ambient) 1) :=
    (metricEnergy_continuousOn hg.1).mono (prod_mono hKM (subset_univ _))
  obtain ⟨m, hm, hml⟩ := hs.exists_forall_le' hc (a := 0) (by
    rintro ⟨p, v⟩ ⟨hp, hv⟩
    apply hg.2.2.1 p (hKM hp) v
    intro h0
    simp [h0] at hv)
  refine ⟨m, hm, fun p hp v => ?_⟩
  by_cases hv : v = 0
  · simp [hv, metricEnergy, hermitianValue, coordinates_zero]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let u := ‖v‖⁻¹ • v
    have hu : u ∈ Metric.sphere (0 : Ambient) 1 := by
      simp [u, norm_smul, hn]
    have hu' : ‖v‖ • u = v := by simp [u, smul_smul, hn]
    have hh := mul_le_mul_of_nonneg_left (hml (p, u) ⟨hp, hu⟩) (sq_nonneg ‖v‖)
    calc
      m * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 * metricEnergy g (p, u) := by
        simpa only [mul_comm m] using hh
      _ = metricEnergy g (p, v) := by
        change ‖v‖ ^ 2 * (hermitianValue (g p) u u).re = (hermitianValue (g p) v v).re
        rw [← hermitianValue_vector_real_smul, hu']

lemma geodesic_energy_constant {M : Set Ambient} (hM : IsOpen M)
    {g : Ambient → CMatrix} (hg : IsKahlerMetric M g)
    {y : ℝ → Ambient × Ambient} {a : ℝ} (ha : 0 < a)
    (hy : ∀ t ∈ Ioo (-a) a, HasDerivAt y (geodesicField g (y t)) t ∧ (y t).1 ∈ M)
    {t : ℝ} (ht : t ∈ Ioo (-a) a) : metricEnergy g (y t) = metricEnergy g (y 0) := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (geodesic_energy_hasDerivAt_zero hM hg (hy s hs).2 (hy s hs).1).hasDerivWithinAt)
    (fun s hs => (norm_zero : ‖(0 : ℝ)‖ = 0).le)
    (convex_Ioo (-a) a) (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha⟩) ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hh

lemma hartogs_isOpen_smooth {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball) :
    IsOpen (hartogs φ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hz : ∀ᶠ q : Ambient in 𝓝 p, q.1 ∈ ball :=
    continuousAt_fst (isOpen_ball.mem_nhds hp.1)
  have hf : ContinuousAt (fiberParameter φ) p :=
    (Real.continuous_exp.continuousAt.comp
      ((hφ.continuousOn.continuousAt (isOpen_ball.mem_nhds hp.1)).comp continuousAt_fst)).mul
        (continuousAt_snd.norm.pow 2)
  have ht : ∀ᶠ q in 𝓝 p, fiberParameter φ q < 1 := hf (Iio_mem_nhds hp.2)
  exact hz.and ht

private lemma abs_le_add_one_of_sq_le {r c : ℝ} (hc : 0 ≤ c) (hr : r ^ 2 ≤ c) :
    |r| ≤ c + 1 := by
  nlinarith [sq_abs r, sq_nonneg (|r| - 1)]

lemma curve_function_bound {M : Set Ambient} {g : Ambient → CMatrix}
    {F : Ambient → ℝ} {y : ℝ → Ambient × Ambient} {a L T : ℝ}
    (ha : 0 < a) (hL : 0 ≤ L)
    (hy : ∀ s ∈ Ioo (-a) a, HasDerivAt y (geodesicField g (y s)) s ∧ (y s).1 ∈ M)
    (hF : ∀ p ∈ M, DifferentiableAt ℝ F p)
    (hbound : ∀ s ∈ Ioo (-a) a, |fderiv ℝ F (y s).1 (y s).2| ≤ L)
    {t : ℝ} (ht : t ∈ Ioo (-a) a) (htT : |t| ≤ T) :
    F (y t).1 ≤ F (y 0).1 + L * T := by
  have hd : ∀ s ∈ Ioo (-a) a, HasDerivAt (fun r => F (y r).1)
      (fderiv ℝ F (y s).1 (y s).2) s := by
    intro s hs
    exact (hF _ (hy s hs).2).hasFDerivAt.comp_hasDerivAt s (hy s hs).1.fst
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s hs)
    (convex_Ioo (-a) a) (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha⟩) ht
  simp only [Real.norm_eq_abs, sub_zero] at hb
  have hbt := (le_abs_self (F (y t).1 - F (y 0).1)).trans hb
  have := mul_le_mul_of_nonneg_left htT hL
  linarith

lemma hartogs_geodesic_compact_containment {φ : Base → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ ball) (hpsh : IsPshBase φ)
    {lam : ℝ} (hlam : 0 < lam) {p : Ambient} (hp : p ∈ hartogs φ) (v : Ambient)
    {T : ℝ} (hT : 0 < T) :
    ∃ K : Set (Ambient × Ambient), IsCompact K ∧
      K ⊆ hartogs φ ×ˢ (univ : Set Ambient) ∧
      ∀ (a : ℝ) (y : ℝ → Ambient × Ambient), 0 < a → y 0 = (p, v) →
        (∀ s ∈ Ioo (-a) a, HasDerivAt y (geodesicField (hartogsMetric φ lam) (y s)) s ∧
          (y s).1 ∈ hartogs φ) →
        ∀ t ∈ Ioo (-a) a, |t| ≤ T → y t ∈ K := by
  let g := hartogsMetric φ lam
  have hg := hartogsMetric_isKahler hφ hpsh hlam
  let E := metricEnergy g (p, v)
  have hE : 0 ≤ E := metricEnergy_nonneg hg hp v
  let Lψ := 4 * E / lam + 1
  let Lf := 4 * E + 1
  have hLψ : 0 ≤ Lψ := by dsimp [Lψ]; positivity
  have hLf : 0 ≤ Lf := by dsimp [Lf]; positivity
  obtain ⟨K, hK, hKM, hKB⟩ := hartogs_barrier_sublevels_compact hφ
    (fiberPotential φ p + Lf * T) (psi p.1 + Lψ * T)
  obtain ⟨m, hm, hml⟩ := compact_metric_coercivity hg hK hKM
  let R := E / m + T + 1
  refine ⟨K ×ˢ Metric.closedBall (0 : Ambient) R,
    hK.prod (isCompact_closedBall _ _), prod_mono hKM (subset_univ _), ?_⟩
  intro a y ha hy0 hy t ht htT
  have he (s : ℝ) (hs : s ∈ Ioo (-a) a) : metricEnergy g (y s) = E := by
    simpa only [hy0] using geodesic_energy_constant (hartogs_isOpen_smooth hφ) hg ha hy hs
  have hpos : (y t).1 ∈ K := by
    apply hKB _ (hy t ht).2
    · have hbound (s : ℝ) (hs : s ∈ Ioo (-a) a) :
          |fderiv ℝ (fiberPotential φ) (y s).1 (y s).2| ≤ Lf := by
        have hh := fiberPotential_derivative_sq_le hφ hpsh hlam (hy s hs).2 (y s).2
        change _ ≤ 4 * metricEnergy g (y s) at hh
        rw [he s hs] at hh
        exact abs_le_add_one_of_sq_le (by positivity) hh
      simpa only [hy0, Function.comp_def] using! curve_function_bound ha hLf hy
        (fun q hq => (fiberPotential_contDiffAt hφ hq).differentiableAt (by simp)) hbound ht htT
    · have hbound (s : ℝ) (hs : s ∈ Ioo (-a) a) :
          |fderiv ℝ (fun q : Ambient => psi q.1) (y s).1 (y s).2| ≤ Lψ := by
        have hh := psi_derivative_sq_le hφ hpsh hlam (hy s hs).2 (y s).2
        change _ ≤ 4 * metricEnergy g (y s) at hh
        rw [he s hs] at hh
        apply abs_le_add_one_of_sq_le (by positivity)
        exact (le_div_iff₀ hlam).mpr (by simpa only [mul_comm lam] using hh)
      simpa only [hy0, Function.comp_def] using! curve_function_bound ha hLψ hy
        (fun q hq => ((psi_contDiffAt hq.1).comp q contDiffAt_fst).differentiableAt (by simp))
        hbound ht htT
  refine ⟨hpos, ?_⟩
  have hv := hml (y t).1 hpos (y t).2
  change m * ‖(y t).2‖ ^ 2 ≤ metricEnergy g (y t) at hv
  rw [he t ht] at hv
  have hv' : ‖(y t).2‖ ^ 2 ≤ E / m :=
    (le_div_iff₀ hm).mpr (by simpa only [mul_comm m] using hv)
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖(y t).2‖ ≤ E / m + 1 := by
    simpa only [abs_norm] using abs_le_add_one_of_sq_le (by positivity) hv'
  dsimp [R]
  linarith

end PinchedHartogs

end

end OAI
