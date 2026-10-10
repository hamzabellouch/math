import Mathlib

namespace OAI

namespace RadialNilpotent

open ContinuousLinearMap

theorem exists_basis_coordinates
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {a b : F} (hdim : Module.finrank ℝ F = 2)
    (hab : LinearIndependent ℝ ![a, b]) :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] F, ∀ u v : ℝ, e (u, v) = u • a + v • b := by
  let f : (ℝ × ℝ) →L[ℝ] F := (fst ℝ ℝ ℝ).smulRight a + (snd ℝ ℝ ℝ).smulRight b
  have hf : Function.Injective f := by
    intro p q hpq
    have hzero : (p.1 - q.1) • a + (p.2 - q.2) • b = 0 := by
      change p.1 • a + p.2 • b = q.1 • a + q.2 • b at hpq
      calc
        (p.1 - q.1) • a + (p.2 - q.2) • b =
            (p.1 • a + p.2 • b) - (q.1 • a + q.2 • b) := by module
        _ = 0 := sub_eq_zero.mpr hpq
    obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.mp hab _ _ hzero
    exact Prod.ext (sub_eq_zero.mp h₁) (sub_eq_zero.mp h₂)
  have hrank : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ F := by
    simp [hdim]
  let e := (f.toLinearMap.linearEquivOfInjective hf hrank).toContinuousLinearEquiv
  exact ⟨e, fun _ _ => rfl⟩

theorem basis_coordinates_radial
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : F} (e : (ℝ × ℝ) ≃L[ℝ] F)
    (he : ∀ u v : ℝ, e (u, v) = u • a + v • b) (ρ t : ℝ) :
    e.symm (ρ • (a + t • b)) = (ρ, ρ * t) := by
  apply e.injective
  rw [e.apply_symm_apply, he]
  module

theorem induced_field_radial_value
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : F} (e : (ℝ × ℝ) ≃L[ℝ] F)
    (he : ∀ u v : ℝ, e (u, v) = u • a + v • b)
    (w : ℝ → F) {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) :
    w ((e.symm (ρ • (a + t • b))).2 / (e.symm (ρ • (a + t • b))).1) = w t := by
  rw [basis_coordinates_radial e he ρ t]
  congr 1
  exact mul_div_cancel_left₀ t hρ

theorem smulRight_square_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ell : E →L[ℝ] ℝ) (v : E) (hv : ell v = 0) :
    (ell.smulRight v).comp (ell.smulRight v) = 0 := by
  ext x
  simp [hv]

theorem angle_hasFDerivAt (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    HasFDerivAt (fun q : ℝ × ℝ => q.2 / q.1)
      (p.2 • ((-(p.1 ^ 2)⁻¹) • fst ℝ ℝ ℝ) + p.1⁻¹ • snd ℝ ℝ ℝ) p := by
  have hi := (hasDerivAt_inv hp).comp_hasFDerivAt p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  convert! (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).mul hi using 1

theorem angle_derivative_radial (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    (p.2 • ((-(p.1 ^ 2)⁻¹) • fst ℝ ℝ ℝ) + p.1⁻¹ • snd ℝ ℝ ℝ)
      (1, p.2 / p.1) = 0 := by
  change p.2 * (-(p.1 ^ 2)⁻¹ * 1) + p.1⁻¹ * (p.2 / p.1) = 0
  field_simp
  ring

theorem induced_field_square_zero
    {w : ℝ → ℝ × ℝ} {lam : ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p.1 ≠ 0)
    (hw : HasDerivAt w (lam (p.2 / p.1) • (1, p.2 / p.1)) (p.2 / p.1)) :
    (fderiv ℝ (fun q : ℝ × ℝ => w (q.2 / q.1)) p).comp
      (fderiv ℝ (fun q : ℝ × ℝ => w (q.2 / q.1)) p) = 0 := by
  let ell : (ℝ × ℝ) →L[ℝ] ℝ :=
    p.2 • ((-(p.1 ^ 2)⁻¹) • fst ℝ ℝ ℝ) + p.1⁻¹ • snd ℝ ℝ ℝ
  let v : ℝ × ℝ := lam (p.2 / p.1) • (1, p.2 / p.1)
  have hang : HasFDerivAt (fun q : ℝ × ℝ => q.2 / q.1) ell p :=
    angle_hasFDerivAt p hp
  have hder : HasFDerivAt (fun q : ℝ × ℝ => w (q.2 / q.1)) (ell.smulRight v) p := by
    convert! hw.hasFDerivAt.comp p hang using 1
  have hv : ell v = 0 := by
    dsimp only [v]
    rw [map_smul]
    have he : ell (1, p.2 / p.1) = 0 := angle_derivative_radial p hp
    rw [he, smul_zero]
  rw [hder.fderiv]
  exact smulRight_square_zero ell v hv

theorem induced_field_contDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} {w : ℝ → F} {s : Set ℝ}
    (hw : ContDiffOn ℝ n w s) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => w (p.2 / p.1))
      {p : ℝ × ℝ | p.1 ≠ 0 ∧ p.2 / p.1 ∈ s} := by
  have hang : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.2 / p.1)
      {p : ℝ × ℝ | p.1 ≠ 0 ∧ p.2 / p.1 ∈ s} := by
    exact contDiff_snd.contDiffOn.div contDiff_fst.contDiffOn (fun _ hp => hp.1)
  exact hw.comp hang (fun _ hp => hp.2)

theorem induced_field_square_zero_basis
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : (ℝ × ℝ) ≃L[ℝ] F) {w : ℝ → F} {lam : ℝ → ℝ} {z : F}
    (hz : (e.symm z).1 ≠ 0)
    (hw : HasDerivAt w
      (lam ((e.symm z).2 / (e.symm z).1) •
        e (1, (e.symm z).2 / (e.symm z).1))
      ((e.symm z).2 / (e.symm z).1)) :
    (fderiv ℝ (fun x : F => w ((e.symm x).2 / (e.symm x).1)) z).comp
      (fderiv ℝ (fun x : F => w ((e.symm x).2 / (e.symm x).1)) z) = 0 := by
  let p := e.symm z
  let ell : (ℝ × ℝ) →L[ℝ] ℝ :=
    p.2 • ((-(p.1 ^ 2)⁻¹) • fst ℝ ℝ ℝ) + p.1⁻¹ • snd ℝ ℝ ℝ
  let ellF : F →L[ℝ] ℝ := ell.comp e.symm.toContinuousLinearMap
  let v : F := lam (p.2 / p.1) • e (1, p.2 / p.1)
  have hang : HasFDerivAt (fun x : F => (e.symm x).2 / (e.symm x).1) ellF z := by
    exact (angle_hasFDerivAt p hz).comp z e.symm.hasFDerivAt
  have hder : HasFDerivAt (fun x : F => w ((e.symm x).2 / (e.symm x).1))
      (ellF.smulRight v) z := by
    convert! hw.hasFDerivAt.comp z hang using 1
  have hv : ellF v = 0 := by
    dsimp only [ellF, v]
    simp only [comp_apply, ContinuousLinearEquiv.coe_coe, map_smul,
      ContinuousLinearEquiv.symm_apply_apply]
    have he : ell (1, p.2 / p.1) = 0 := angle_derivative_radial p hz
    rw [he, smul_zero]
  rw [hder.fderiv]
  exact smulRight_square_zero ellF v hv

theorem induced_field_contDiffOn_basis
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : (ℝ × ℝ) ≃L[ℝ] F) {n : WithTop ℕ∞} {w : ℝ → F} {s : Set ℝ}
    (hw : ContDiffOn ℝ n w s) :
    ContDiffOn ℝ n (fun z : F => w ((e.symm z).2 / (e.symm z).1))
      {z : F | (e.symm z).1 ≠ 0 ∧ (e.symm z).2 / (e.symm z).1 ∈ s} := by
  exact (induced_field_contDiffOn hw).comp e.symm.contDiff.contDiffOn (fun _ hz => hz)

theorem radial_induced_field
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {a b : F} {α β : ℝ} {w : ℝ → F} {lam : ℝ → ℝ}
    (hdim : Module.finrank ℝ F = 2) (hab : LinearIndependent ℝ ![a, b])
    (hw : ContDiffOn ℝ 1 w (Set.Icc α β))
    (hder : ∀ t ∈ Set.Ioo α β, HasDerivAt w (lam t • (a + t • b)) t) :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] F,
      (∀ u v : ℝ, e (u, v) = u • a + v • b) ∧
      (∀ ρ t : ℝ, 0 < ρ →
        w ((e.symm (ρ • (a + t • b))).2 / (e.symm (ρ • (a + t • b))).1) = w t) ∧
      ContDiffOn ℝ 1 (fun z : F => w ((e.symm z).2 / (e.symm z).1))
        {z : F | 0 < (e.symm z).1 ∧ (e.symm z).2 / (e.symm z).1 ∈ Set.Ioo α β} ∧
      ∀ z : F, 0 < (e.symm z).1 →
        (e.symm z).2 / (e.symm z).1 ∈ Set.Ioo α β →
        (fderiv ℝ (fun x : F => w ((e.symm x).2 / (e.symm x).1)) z).comp
          (fderiv ℝ (fun x : F => w ((e.symm x).2 / (e.symm x).1)) z) = 0 := by
  obtain ⟨e, he⟩ := exists_basis_coordinates hdim hab
  refine ⟨e, he, ?_, ?_, ?_⟩
  · intro ρ t hρ
    exact induced_field_radial_value e he w (ne_of_gt hρ) t
  · apply (induced_field_contDiffOn_basis e (hw.mono Set.Ioo_subset_Icc_self)).mono
    intro z hz
    exact ⟨ne_of_gt hz.1, hz.2⟩
  · intro z hz hangle
    apply induced_field_square_zero_basis e (ne_of_gt hz)
    simpa only [he, one_smul] using hder _ hangle

end RadialNilpotent

end OAI
