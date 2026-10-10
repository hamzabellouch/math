import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreePhysicalBasis

namespace OAI

/-! The free boundary conditions have at most one independent coefficient
vector. Nonvanishing is proved for the actual normalized H column. -/

namespace DefocusingNLS

theorem matchingColumn_kernel_line (u v : Fin 2 → ℂ) (hu : u ≠ 0)
    (hz : matchingColumnDeterminant u v = 0) (a b : ℂ × ℂ) (ha : a ≠ 0)
    (hA : a.1 • u + a.2 • v = 0) (hB : b.1 • u + b.2 • v = 0) :
    ∃ t : ℂ, b = t • a := by
  obtain ⟨k, hk⟩ := matchingColumnDeterminant_eq_zero_imp_smul u v hu hz
  have hcoeff (p : ℂ × ℂ) (hp : p.1 • u + p.2 • v = 0) : p.1 + p.2 * k = 0 := by
    apply (smul_eq_zero.mp ?_).resolve_right hu
    rw [add_smul, mul_smul, ← hk]
    exact hp
  have hAc := hcoeff a hA
  have hBc := hcoeff b hB
  have ha2 : a.2 ≠ 0 := by
    intro h
    have ha1 : a.1 = 0 := by simpa only [h, zero_mul, add_zero] using hAc
    exact ha (Prod.ext ha1 h)
  let t : ℂ := b.2 / a.2
  have ht : t * a.2 = b.2 := div_mul_cancel₀ _ ha2
  refine ⟨t, Prod.ext ?_ ?_⟩
  · change b.1 = t * a.1
    have ha1 : a.1 = -a.2 * k := by linear_combination hAc
    have hb1 : b.1 = -b.2 * k := by linear_combination hBc
    rw [ha1, hb1, ← ht]
    ring
  · exact ht.symm

theorem spectralFreePositivePhysical_core_ne_zero (ell : ℕ) (b r : ℝ)
    (z : ℂ) (hr : 0 < r) (hz : -(1/32 : ℝ) ≤ z.re) :
    spectralFreeCoreBoundary ell r (spectralFreePositivePhysical ell b z r) ≠ 0 := by
  let q := spectralQ ell 1 b z
  let x := radialFreeSlowArgument (Real.log r)
  let a := Complex.exp (((ell : ℂ) - 2 * q) * (Real.log r : ℂ)) * x ^ q
  let u := slowBoundaryColumn q (ell + 6) (-x)
  have hq : -1 < q.re := by
    dsimp only [q]
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  obtain ⟨ha, he⟩ := spectralFreeAngularPhysical_eq_boundaryColumn ell q hq r
  change a ≠ 0 at ha
  have hx : x ≠ 0 := radialFreeSlowArgument_ne_zero _
  have hxim : x.im ≠ 0 := by
    intro h
    exact hx (Complex.ext (radialFreeSlowArgument_re _) h)
  have hu : u ≠ 0 := slowBoundaryColumn_ne_zero q (ell + 6) (-x) hq
    (by simp only [Complex.neg_re, x, radialFreeSlowArgument_re, neg_zero])
    (by simpa only [Complex.neg_im, neg_ne_zero] using hxim)
  intro hzero
  have h0 := congrFun hzero 0
  have h1 := congrFun hzero 1
  simp only [spectralFreeCoreBoundary, spectralFreePositivePhysical,
    Matrix.cons_val_zero, Matrix.cons_val_one, Prod.fst_zero, Prod.snd_zero,
    Pi.zero_apply, add_zero, sub_zero] at h0 h1
  change (spectralPhysicalJet ((ell : ℂ) - 2 * q) (spectralFreeSlowJet q (ell + 6)) r).1 = 0 at h0
  change (spectralPhysicalJet ((ell : ℂ) - 2 * q) (spectralFreeSlowJet q (ell + 6)) r).2 -
    (ell : ℂ) / (r : ℂ) *
      (spectralPhysicalJet ((ell : ℂ) - 2 * q) (spectralFreeSlowJet q (ell + 6)) r).1 = 0 at h1
  rw [he] at h0 h1
  change a * u 0 = 0 at h0
  change a / (r : ℂ) * ((ell : ℂ) * u 0 - 2 * x * u 1) -
    (ell : ℂ) / (r : ℂ) * (a * u 0) = 0 at h1
  have hu0 : u 0 = 0 := (mul_eq_zero.mp h0).resolve_left ha
  have hu1 : u 1 = 0 := by
    rw [hu0] at h1
    simp only [mul_zero, zero_sub, sub_zero, mul_neg, neg_eq_zero] at h1
    have hfac : a / (r : ℂ) * (2 * x) ≠ 0 :=
      mul_ne_zero (div_ne_zero ha (Complex.ofReal_ne_zero.mpr hr.ne'))
        (mul_ne_zero (by norm_num) hx)
    exact (mul_eq_zero.mp (by simpa only [mul_assoc] using h1)).resolve_left hfac
  apply hu
  funext j
  fin_cases j
  · exact hu0
  · exact hu1

end DefocusingNLS

end OAI
