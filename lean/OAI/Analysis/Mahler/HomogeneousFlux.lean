import OAI.Analysis.Mahler.MatrixHessian

namespace OAI
open Complex
open scoped BigOperators
local notation "conj" => starRingEnd ℂ

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [normedSpaceRealE : NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

/-- The convention d^c u(v) = -D_R u(iv)/4. -/
noncomputable def dc (u : E → ℂ) (x v : E) : ℂ := -fderiv ℝ u x (I • v) / 4

omit isScalarTowerRealComplexE in
lemma dc_circle [IsScalarTower ℝ ℂ E] (u : E → ℂ) (x : E) :
    dc u x (I • x) = (dz u x x + dbar u x x) / 4 := by
  simp only [dc, dz, dbar, smul_smul, I_mul_I, neg_smul, one_smul, map_neg]
  ring

lemma dbar_real {u : E → ℂ} {x v : E} (hr : ∀ y, conj (u y) = u y)
    (hu : DifferentiableAt ℝ u x) : dbar u x v = conj (dz u x v) := by
  have h := dbar_conj (v := v) hu
  simpa only [hr] using h

omit normedSpaceRealE isScalarTowerRealComplexE in
/-- Euler's identity derived by differentiating the homogeneous scaling identity. -/
lemma homogeneous_euler [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x : E} {m : ℕ}
    (hf : DifferentiableAt ℂ f x) (hh : ∀ c : ℂ, f (c • x) = c^m * f x) :
    fderiv ℂ f x x = (m : ℂ) * f x := by
  have hl : HasDerivAt (fun c : ℂ => c • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).smul_const x
  have hfd : HasFDerivAt f (fderiv ℂ f x) ((1 : ℂ) • x) := by simpa using hf.hasFDerivAt
  have hleft := hfd.comp_hasDerivAt 1 hl
  have hright : HasDerivAt (fun c : ℂ => c^m * f x) ((m : ℂ) * f x) 1 := by
    simpa using ((hasDerivAt_id (1 : ℂ)).pow m).mul_const (f x)
  have he : (fun c : ℂ => f (c • x)) = (fun c : ℂ => c^m * f x) := funext hh
  change HasDerivAt (fun c : ℂ => f (c • x)) _ 1 at hleft
  rw [he] at hleft
  exact hleft.unique hright

variable {ι : Type*} [Fintype ι]
lemma differentiable_logTau {f : ι → E → ℂ} {x : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x) :
    DifferentiableAt ℝ (logTau f) x := by
  rw [logTau_eq]
  have hp : energy f x ∈ slitPlane := by
    rw [energy_eq_tau]
    exact Complex.ofReal_mem_slitPlane.mpr ht
  exact (((Complex.hasDerivAt_log hp).hasFDerivAt.restrictScalars ℝ).comp x
    (differentiable_energy hf).hasFDerivAt).differentiableAt

lemma dz_logTau_radial {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x)
    (hh : ∀ j (c : ℂ), f j (c • x) = c^m * f j x) :
    dz (logTau f) x x = (m : ℂ) := by
  rw [dz_logTau hf ht]
  simp_rw [homogeneous_euler (hf _) (hh _)]
  have hs : (∑ j, conj (f j x) * ((m : ℂ) * f j x)) = (m : ℂ) * energy f x := by
    simp [energy, Finset.mul_sum, mul_left_comm]
  rw [hs, energy_eq_tau]
  have hn : (tau f x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  field_simp [hn]

/-- The homogeneous sphere-flux normalization alpha(V)=m/2, V(z)=iz. -/
theorem homogeneous_dc_circle {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x)
    (hh : ∀ j (c : ℂ), f j (c • x) = c^m * f j x) :
    dc (logTau f) x (I • x) = (m : ℂ) / 2 := by
  rw [dc_circle, dbar_real (by intro y; simp [logTau]) (differentiable_logTau hf ht),
    dz_logTau_radial hf ht hh]
  simp only [map_natCast]
  ring

omit isScalarTowerRealComplexE in
lemma dc_sub [IsScalarTower ℝ ℂ E] {u q : E → ℂ} {x v : E}
    (hu : DifferentiableAt ℝ u x) (hq : DifferentiableAt ℝ q x) :
    dc (fun y => u y - q y) x v = dc u x v - dc q x v := by
  have h := hu.hasFDerivAt.sub hq.hasFDerivAt
  simp only [Pi.sub_def] at h
  rw [dc, h.fderiv]
  simp [dc]
  ring

omit isScalarTowerRealComplexE in
lemma dc_const_mul [IsScalarTower ℝ ℂ E] {u : E → ℂ} {x v : E} (r : ℂ)
    (hu : DifferentiableAt ℝ u x) :
    dc (fun y => r * u y) x v = r * dc u x v := by
  have h := (hasFDerivAt_const r x).mul hu.hasFDerivAt
  simp only [Pi.mul_def] at h
  rw [dc, h.fderiv]
  simp [dc]
  ring

/-- The beta in the homogeneous flux argument annihilates the circle direction.
The comparison map g has degree one; in particular, it can be the coordinate identity map. -/
theorem homogeneous_beta_circle {κ : Type*} [Fintype κ]
    {f : ι → E → ℂ} {g : κ → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (htf : 0 < tau f x)
    (hfg : ∀ j (c : ℂ), f j (c • x) = c^m * f j x)
    (hg : ∀ j, DifferentiableAt ℂ (g j) x) (htg : 0 < tau g x)
    (hgg : ∀ j (c : ℂ), g j (c • x) = c^1 * g j x) :
    dc (fun y => logTau f y - (m : ℂ) * logTau g y) x (I • x) = 0 := by
  rw [dc_sub (q := fun y => (m : ℂ) * logTau g y) (differentiable_logTau hf htf)
    ((differentiableAt_const (m : ℂ)).mul (differentiable_logTau hg htg)),
    dc_const_mul _ (differentiable_logTau hg htg),
    homogeneous_dc_circle hf htf hfg, homogeneous_dc_circle hg htg hgg]
  norm_num
  ring

omit normedSpaceRealE isScalarTowerRealComplexE in
/-- Scaling of the actual squared norm follows from component homogeneity. -/
lemma tau_homogeneous [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hh : ∀ j (c : ℂ), f j (c • x) = c^m * f j x) (c : ℂ) :
    tau f (c • x) = normSq c ^ m * tau f x := by
  simp [tau, hh, map_mul, map_pow, Finset.mul_sum]

/-- Circle invariance is derived from homogeneity, not assumed. -/
lemma logTau_circle_invariant {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hh : ∀ j (c : ℂ), f j (c • x) = c^m * f j x)
    {c : ℂ} (hc : normSq c = 1) : logTau f (c • x) = logTau f x := by
  simp only [logTau, tau_homogeneous hh, hc, one_pow, one_mul]

end Mahler

end OAI
