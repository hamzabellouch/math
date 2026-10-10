import OAI.AlgebraicGeometry.PlaneCurves.Forms

namespace OAI

/-!
# Equivalence of projective and affine ideal-power multiplicity
-/

section

/-!
# Concrete chart evaluation and local-ring bridges
-/

noncomputable section

namespace Nagata.ProjectiveGeometry

abbrev ChartLocalRing (b : Fin 3) (p : PlanePoint) :=
  AffineMultiplicity.PointLocalRing (chartCoordinates b p)

/-- The homogeneous coordinate functions in the genuine local ring of chart
`b`; the distinguished coordinate is one. -/
def localHomogeneousCoordinates (b : Fin 3) (p : PlanePoint) :
    Fin 3 → ChartLocalRing b p :=
  fun j => if h : j = b then 1 else
    algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p)
      (MvPolynomial.X ⟨j, h⟩)

/-- A homogeneous coordinate which is nonzero at the point is a unit in the
local ring. This is the actual denominator used on projective chart overlaps. -/
theorem localHomogeneousCoordinates_isUnit (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    IsUnit (localHomogeneousCoordinates b p c) := by
  by_cases hcb : c = b
  · simp [localHomogeneousCoordinates, hcb]
  · simp only [localHomogeneousCoordinates, dite_eq_right hcb]
    apply (AffineMultiplicity.residueEval_isUnit (chartCoordinates b p) _).mpr
    simpa [chartCoordinates] using div_ne_zero hc hb

/-- The invertible denominator for the substitution from chart `c` into the
local ring of chart `b`. Its invertibility has just been proved. -/
def localChartDenominatorUnit (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) : (ChartLocalRing b p)ˣ :=
  (localHomogeneousCoordinates_isUnit b c p hb hc).unit

theorem localChartDenominatorUnit_val (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    (localChartDenominatorUnit b c p hb hc : ChartLocalRing b p) =
      localHomogeneousCoordinates b p c :=
  (localHomogeneousCoordinates_isUnit b c p hb hc).unit_spec

/-- The concrete rational substitution on an overlap of affine projective
charts, with values in the actual local ring at the target point. -/
def chartTransitionToLocalRing (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    MvPolynomial (ChartVariables c) ℂ →+* ChartLocalRing b p :=
  MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p)).comp
      MvPolynomial.C)
    (fun j => (↑((localChartDenominatorUnit b c p hb hc)⁻¹) : ChartLocalRing b p) *
      localHomogeneousCoordinates b p j.val)

theorem eval₂_dehomogenize {R : Type*} [CommSemiring R]
    (k : ℂ →+* R) (x : Fin 3 → R) (c : Fin 3) (hc : x c = 1)
    (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.eval₂ k (fun j : ChartVariables c => x j.val) (dehomogenize c F) =
      MvPolynomial.eval₂ k x F := by
  rw [dehomogenize, ← MvPolynomial.eval₂_assoc]
  congr 1
  funext j
  by_cases hj : j = c
  · subst j
    simp [hc]
  · simp [hj]

theorem eval₂_localHomogeneousCoordinates (b : Fin 3) (p : PlanePoint)
    (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.eval₂
      ((algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p)).comp
        MvPolynomial.C)
      (localHomogeneousCoordinates b p) F =
    algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p)
      (dehomogenize b F) := by
  rw [dehomogenize, MvPolynomial.eval₂_comp_left]
  congr 1
  funext j
  by_cases hj : j = b
  · simp [localHomogeneousCoordinates, hj]
  · simp [localHomogeneousCoordinates, hj]

/-- The source chart equation becomes the target chart equation multiplied
by the actual invertible denominator to degree `d`. -/
theorem chartTransition_dehomogenize {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    chartTransitionToLocalRing b c p hb hc (dehomogenize c F) =
      (↑((localChartDenominatorUnit b c p hb hc)⁻¹) : ChartLocalRing b p) ^ d *
        algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p)
          (dehomogenize b F) := by
  let u := localChartDenominatorUnit b c p hb hc
  have hu : (↑(u⁻¹) : ChartLocalRing b p) * localHomogeneousCoordinates b p c = 1 := by
    rw [← localChartDenominatorUnit_val b c p hb hc]
    exact Units.inv_mul u
  change MvPolynomial.eval₂ _
    (fun j : ChartVariables c => (↑(u⁻¹) : ChartLocalRing b p) *
      localHomogeneousCoordinates b p j.val) (dehomogenize c F) = _
  rw [eval₂_dehomogenize _
    (fun j : Fin 3 => (↑(u⁻¹) : ChartLocalRing b p) * localHomogeneousCoordinates b p j) c hu]
  rw [W16.homogeneous_eval₂_scale hF]
  rw [eval₂_localHomogeneousCoordinates]

theorem residueEval_localHomogeneousCoordinates (b : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (j : Fin 3) :
    AffineMultiplicity.residueEval (chartCoordinates b p)
      (localHomogeneousCoordinates b p j) = p.rep j / p.rep b := by
  by_cases hj : j = b
  · subst j
    simp [localHomogeneousCoordinates, hb]
  · simp [localHomogeneousCoordinates, hj, chartCoordinates]

/-- The actual rational substitution sends the target residue point to the
source chart coordinates. This discharges evaluation compatibility. -/
theorem chartTransition_residueEval (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0)
    (f : MvPolynomial (ChartVariables c) ℂ) :
    AffineMultiplicity.residueEval (chartCoordinates b p)
      (chartTransitionToLocalRing b c p hb hc f) =
        MvPolynomial.eval (chartCoordinates c p) f := by
  let ρ := AffineMultiplicity.residueEval (chartCoordinates b p)
  let e := chartTransitionToLocalRing b c p hb hc
  let u := localChartDenominatorUnit b c p hb hc
  have hu : ρ (↑u : ChartLocalRing b p) = p.rep c / p.rep b := by
    rw [localChartDenominatorUnit_val]
    exact residueEval_localHomogeneousCoordinates b p hb c
  have he : ρ.comp e = MvPolynomial.eval (chartCoordinates c p) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ, e, chartTransitionToLocalRing]
    · intro j
      simp only [RingHom.comp_apply, e, chartTransitionToLocalRing,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X]
      change ρ ((↑(u⁻¹) : ChartLocalRing b p) *
        localHomogeneousCoordinates b p j.val) = p.rep j.val / p.rep c
      rw [map_mul, map_units_inv, hu,
        residueEval_localHomogeneousCoordinates b p hb j.val]
      rw [mul_comm, ← div_eq_mul_inv, div_div_div_cancel_right₀ hb]
  exact RingHom.congr_fun he f

/-- A coordinate substitution respecting evaluation transports all ideal-power
orders into the kernel of the target evaluation homomorphism. This applies to
rational chart substitutions after mapping into an actual local ring. -/
theorem orderAtLeast_map_into_kernel {σ K R : Type*} [CommRing K] [CommRing R]
    (p : σ → K) (e : MvPolynomial σ K →+* R) (ρ : R →+* K)
    (he : ∀ f, ρ (e f) = MvPolynomial.eval p f)
    (m : ℕ) (f : MvPolynomial σ K)
    (hf : AffineMultiplicity.orderAtLeast p m f) :
    e f ∈ (RingHom.ker ρ) ^ m := by
  have hle : AffineMultiplicity.pointIdeal p ≤ Ideal.comap e (RingHom.ker ρ) := by
    intro g hg
    change ρ (e g) = 0
    rw [he]
    exact (AffineMultiplicity.pointIdeal_mem_iff p g).mp hg
  have hp : f ∈ (Ideal.comap e (RingHom.ker ρ)) ^ m :=
    Ideal.pow_right_mono hle m hf
  exact Ideal.le_comap_pow e m hp

theorem chart_order_transport_via_residue {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) (m : ℕ)
    (ρ : ChartLocalRing b p →+* ℂ)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal (ChartLocalRing b p))
    (heval : ∀ f, ρ (chartTransitionToLocalRing b c p hb hc f) =
      MvPolynomial.eval (chartCoordinates c p) f)
    (hf : AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F)) :
    AffineMultiplicity.orderAtLeast (chartCoordinates b p) m (dehomogenize b F) := by
  have hmap := orderAtLeast_map_into_kernel (chartCoordinates c p)
    (chartTransitionToLocalRing b c p hb hc) ρ heval m (dehomogenize c F) hf
  rw [hker, chartTransition_dehomogenize hF b c p hb hc] at hmap
  have hunit : IsUnit ((↑((localChartDenominatorUnit b c p hb hc)⁻¹) :
      ChartLocalRing b p) ^ d) :=
    ((localChartDenominatorUnit b c p hb hc)⁻¹).isUnit.pow d
  have hbare := (Ideal.unit_mul_mem_iff_mem
    (IsLocalRing.maximalIdeal (ChartLocalRing b p) ^ m) hunit).mp hmap
  exact (AffineMultiplicity.localOrderAtLeast_iff (chartCoordinates b p) m
    (dehomogenize b F)).mp hbare

/-- Ordinary affine ideal-power orders agree on every projective chart
overlap for a homogeneous form, at every nonnegative order. -/
theorem chart_order_transport {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) (m : ℕ)
    (hf : AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F)) :
    AffineMultiplicity.orderAtLeast (chartCoordinates b p) m (dehomogenize b F) :=
  chart_order_transport_via_residue hF b c p hb hc m
    (AffineMultiplicity.residueEval (chartCoordinates b p))
    (AffineMultiplicity.ker_residueEval (chartCoordinates b p))
    (chartTransition_residueEval b c p hb hc) hf

/-- One containing chart suffices for every multiplicity order. All residue,
localization, and homogeneous-scaling requirements have concrete witnesses. -/
theorem multiplicityAtLeast_iff_some_chart {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PlanePoint) (m : ℕ) :
    multiplicityAtLeast F p m ↔
      ∃ c : Fin 3, p.rep c ≠ 0 ∧
        AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := chart_exists p
    exact ⟨c, hc, h c hc⟩
  · rintro ⟨c, hc, hf⟩ b hb
    exact chart_order_transport hF b c p hb hc m hf

theorem multiplicityAtLeast_iff_chart {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PlanePoint) (c : Fin 3) (hc : p.rep c ≠ 0) (m : ℕ) :
    multiplicityAtLeast F p m ↔
      AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F) := by
  constructor
  · intro h
    exact h c hc
  · intro h b hb
    exact chart_order_transport hF b c p hb hc m h

/-- Nonzero scalar multiples define the same local multiplicity conditions,
including every nonreduced order. This is the equation-class descent bridge. -/
theorem multiplicityAtLeast_C_mul_iff (a : ℂ) (ha : a ≠ 0)
    (F : MvPolynomial (Fin 3) ℂ) (p : PlanePoint) (m : ℕ) :
    multiplicityAtLeast (MvPolynomial.C a * F) p m ↔ multiplicityAtLeast F p m := by
  constructor
  · intro h c hc
    have hf := h c hc
    rw [dehomogenize_mul, dehomogenize_C] at hf
    exact (AffineMultiplicity.orderAtLeast_nonvanishing_mul_iff
      (chartCoordinates c p) m (dehomogenize c F) (MvPolynomial.C a)
      (by simpa using ha)).mp hf
  · intro h c hc
    rw [dehomogenize_mul, dehomogenize_C]
    exact (AffineMultiplicity.orderAtLeast_nonvanishing_mul_iff
      (chartCoordinates c p) m (dehomogenize c F) (MvPolynomial.C a)
      (by simpa using ha)).mpr (h c hc)

theorem eval_dehomogenize (F : MvPolynomial (Fin 3) ℂ)
    (p : PlanePoint) (c : Fin 3) (hc : p.rep c ≠ 0) :
    MvPolynomial.eval (chartCoordinates c p) (dehomogenize c F) =
      MvPolynomial.eval (fun j => p.rep j / p.rep c) F := by
  exact eval₂_dehomogenize (RingHom.id ℂ) (fun j => p.rep j / p.rep c) c
    (div_self hc) F

theorem eval_dehomogenize_homogeneous {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PlanePoint) (c : Fin 3) (hc : p.rep c ≠ 0) :
    MvPolynomial.eval (chartCoordinates c p) (dehomogenize c F) =
      (p.rep c)⁻¹ ^ d * MvPolynomial.eval p.rep F := by
  rw [eval_dehomogenize F p c hc]
  simpa [div_eq_mul_inv, mul_comm] using
    W16.homogeneous_eval_scale hF p.rep ((p.rep c)⁻¹)

/-- First-order vanishing in any containing chart agrees with vanishing of
the original homogeneous form at the point's representative. -/
theorem chart_order_one_iff {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PlanePoint) (c : Fin 3) (hc : p.rep c ≠ 0) :
    AffineMultiplicity.orderAtLeast (chartCoordinates c p) 1 (dehomogenize c F) ↔
      MvPolynomial.eval p.rep F = 0 := by
  rw [AffineMultiplicity.orderAtLeast_one_iff,
    eval_dehomogenize_homogeneous hF p c hc]
  simp only [mul_eq_zero, pow_ne_zero d (inv_ne_zero hc), false_or]

theorem multiplicityAtLeast_one_iff {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PlanePoint) :
    multiplicityAtLeast F p 1 ↔ MvPolynomial.eval p.rep F = 0 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := chart_exists p
    exact (chart_order_one_iff hF p c hc).mp (h c hc)
  · intro h c hc
    exact (chart_order_one_iff hF p c hc).mpr h

/-- At order one, one containing chart suffices; this is proved from the
homogeneous scaling identity rather than assumed coordinate invariance. -/
theorem multiplicityAtLeast_one_iff_some_chart {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PlanePoint) :
    multiplicityAtLeast F p 1 ↔
      ∃ c : Fin 3, p.rep c ≠ 0 ∧
        AffineMultiplicity.orderAtLeast (chartCoordinates c p) 1 (dehomogenize c F) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := chart_exists p
    exact ⟨c, hc, h c hc⟩
  · rintro ⟨c, hc, h⟩
    exact (multiplicityAtLeast_one_iff hF p).mpr ((chart_order_one_iff hF p c hc).mp h)

theorem multiplicityAtLeast_iff_localOrder (F : MvPolynomial (Fin 3) ℂ)
    (p : PlanePoint) (m : ℕ) :
    multiplicityAtLeast F p m ↔ ∀ c : Fin 3, p.rep c ≠ 0 →
      AffineMultiplicity.localOrderAtLeast (chartCoordinates c p) m (dehomogenize c F) := by
  simp only [multiplicityAtLeast, AffineMultiplicity.localOrderAtLeast_iff]

end Nagata.ProjectiveGeometry

end
end

end OAI
