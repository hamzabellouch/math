import OAI.Geometry.SurfaceImmersion.Primitive.InteriorVelocityPath

namespace OAI

/-! Smooth local positive averaging densities for the interior velocity path. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

/-- Circle coverage and a target in the open disk suffice for the local density construction. -/
theorem positive_density_near_of_circle_coverage
    {p : B → ℝ → Plane} {c : B → Plane}
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2)) (hc : ContDiff ℝ ∞ c)
    {b₀ : B} (hc₀ : c b₀ 0 ^ 2 + c b₀ 1 ^ 2 < 1)
    (hcover : ∀ e : Plane, e 0 ^ 2 + e 1 ^ 2 = 1 → ∃ t ∈ Ioo (0 : ℝ) 1, p b₀ t = e) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) • augment (p b t)) = augment (c b) := by
  obtain ⟨r, e, hr, hr1, he, hce⟩ := radial_representation hc₀
  choose t ht hpt using fun i : Fin 3 => hcover (triangle e i) (triangle_unit he i)
  have hcols : (fun i => augment (p b₀ (t i))) = fun i => augment (triangle e i) := by
    funext i
    rw [hpt i]
  have hM : (columnOperator (fun i => augment (p b₀ (t i)))).IsInvertible := by
    rw [hcols]
    exact triangle_invertible he
  have hbary : columnOperator (fun i => augment (p b₀ (t i))) (triangleWeights r) = augment (c b₀) := by
    rw [hcols, triangle_barycenter, ← hce]
  have hp₀ : Continuous (p b₀) := hp.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨ψ, hψ, hper, hn, _hm, ε, hε, hMψ, hw⟩ :=
    select_positive_moment_bumps hp₀ ht hM (triangleWeights_pos hr hr1) hbary
  exact exists_positive_density_near hp hc hψ hn hper hε hMψ hw

omit [FiniteDimensional ℝ B] in
lemma interiorPath_smooth {A h : B → ℝ} (hA : ContDiff ℝ ∞ A) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun z : B × ℝ => interiorPath (A z.1) (h z.1) z.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun z : B × ℝ =>
      Real.cos (h z.1 + A z.1 * Real.cos (2 * Real.pi * z.2)))
    exact ((hh.comp contDiff_fst).add ((hA.comp contDiff_fst).mul
      (contDiff_const.mul contDiff_snd).cos)).cos
  · change ContDiff ℝ ∞ (fun z : B × ℝ =>
      Real.sin (h z.1 + A z.1 * Real.cos (2 * Real.pi * z.2)))
    exact ((hh.comp contDiff_fst).add ((hA.comp contDiff_fst).mul
      (contDiff_const.mul contDiff_snd).cos)).sin

/-- The full local interior density statement has no assumed moment matrix or bump selection. -/
theorem interior_positive_density_near {A h : B → ℝ} {c : B → Plane}
    (hA : ContDiff ℝ ∞ A) (hh : ContDiff ℝ ∞ h) (hc : ContDiff ℝ ∞ c)
    {b₀ : B} (hmargin : Real.pi + |h b₀| < A b₀)
    (hc₀ : c b₀ 0 ^ 2 + c b₀ 1 ^ 2 < 1) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) • augment (interiorPath (A b) (h b) t)) = augment (c b) := by
  exact positive_density_near_of_circle_coverage (interiorPath_smooth hA hh) hc hc₀
    (fun e he => interiorPath_covers hmargin he)

end ClosedSurfaceR4.LoopDensity

end

end OAI
