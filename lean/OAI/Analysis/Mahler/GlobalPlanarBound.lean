import OAI.Analysis.Mahler.PrimitiveEquality
import OAI.Analysis.Mahler.PlanarSymmetry

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology
open MahlerConformal

/-- The vertical integral is the radial primitive, with endpoint
continuity and every integration segment contained in the actual domain. -/
theorem planarPrimitive_eq_radial {q r₀ r : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    planarPrimitive m q (fiberHeight q r) = radialPrimitive q r₀ (m : ℝ) r := by
  have hr₁ := hr.1.trans hr.2
  have hstrip : q ∈ Ioo (-1 : ℝ) 1 := by
    have hab : |q| < 1 := by
      rw [← hq]
      exact (F_re_mem_strip (w := (r₀ : ℂ)) (by simpa [Complex.norm_real,abs_of_nonneg hr₀] using hr₁)).2
    exact ⟨by linarith [(abs_lt.mp hab).1],(abs_lt.mp hab).2⟩
  apply planarPrimitive_eq_radial_of_geometry hm hr₀ hq hr
  · exact (continuousOn_fiberHeight_basepoint hr₀ hr₁ hq).mono
      (fun s hs => ⟨hs.1,hs.2.trans_lt hr.2⟩)
  · intro s hs t ht
    have hu : (q : ℂ)+(fiberHeight q s : ℂ)*I ∈ Omega := by
      rcases hs.1.eq_or_lt with he | hlt
      · subst s
        simpa [fiberHeight_basepoint hq, verticalFiber] using zero_mem_verticalFiber hstrip
      · exact fiberHeight_mem_verticalFiber (mem_fiberDomain_of_basepoint hr₀ hq ⟨hlt,hs.2.trans_lt hr.2⟩)
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,
      Complex.add_im,Complex.mul_im,zero_add,mul_one] using vertical_segment_mem_Omega hu (t := t) (by simpa using ht)

/-- The FTC applies at every point of Omega, including the real axis. -/
theorem hasDerivAt_planarPrimitive_global (m : ℕ) {q t : ℝ}
    (hu : (q : ℂ)+(t : ℂ)*I ∈ Omega) :
    HasDerivAt (planarPrimitive m q) (planarDensity m ((q : ℂ)+(t : ℂ)*I)) t := by
  apply hasDerivAt_planarPrimitive
  intro s hs
  simpa using vertical_segment_mem_Omega hu (t := s) (by simpa using hs)

/-- Uniform bound for the vertical integral on the upper section. -/
theorem planarPrimitive_upper_bound {m : ℕ} (hm : 2 ≤ m) {q t : ℝ}
    (hu : (q : ℂ)+(t : ℂ)*I ∈ Omega) (ht : 0 ≤ t) :
    planarPrimitive m q t ≤ ‖inverseF ((q : ℂ)+(t : ℂ)*I)‖^(2*(m : ℝ) : ℝ)+planarError m := by
  rcases ht.eq_or_lt with hz | hp
  · subst t
    rw [planarPrimitive_zero]
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (planarError_nonneg _)
  have hstrip : q ∈ Ioo (-1 : ℝ) 1 := by
    have h := F_re_mem_strip (w := inverseF ((q : ℂ)+(t : ℂ)*I)) (by simpa using inverseF_mem hu)
    rw [inverseF_right hu] at h
    simpa using h
  obtain ⟨r₀,hr₀,hq⟩ := exists_radial_basepoint hstrip
  have htmem : t ∈ verticalFiber q ∩ Ioi 0 := ⟨hu,hp⟩
  rw [positive_verticalFiber_eq_image hstrip hr₀.1 hr₀.2 hq] at htmem
  obtain ⟨r,hr,rfl⟩ := htmem
  rw [planarPrimitive_eq_radial hm hr₀.1 hq hr,
    norm_inverseF_fiberHeight (mem_fiberDomain_of_basepoint hr₀.1 hq hr)]
  exact fiber_primitive_bound (by exact_mod_cast hm) hr₀.1 hq ⟨hr.1.le,hr.2⟩

/-- Uniform bound for F, inverseF and the vertical integral:
one nonnegative error tends to zero and controls every point of Omega. -/
theorem planarPrimitive_abs_bound {m : ℕ} (hm : 2 ≤ m) {u : ℂ} (hu : u ∈ Omega) :
    |planarPrimitive m u.re u.im| ≤ ‖inverseF u‖^(2*(m : ℝ) : ℝ)+planarError m := by
  have he : (u.re : ℂ)+(u.im : ℂ)*I = u := Complex.re_add_im u
  have hseg : ∀ s ∈ uIcc (0 : ℝ) u.im, (u.re : ℂ)+(s : ℂ)*I ∈ Omega :=
    fun s hs => vertical_segment_mem_Omega hu hs
  by_cases ht : 0 ≤ u.im
  · rw [abs_of_nonneg (planarPrimitive_nonneg m u.re ht)]
    have hb := planarPrimitive_upper_bound hm (q := u.re) (t := u.im) (by simpa only [Complex.re_add_im] using hu) ht
    simpa only [Complex.re_add_im] using! hb
  · have hc := Omega_conj hu
    have hcp : (u.re : ℂ)+((-u.im : ℝ) : ℂ)*I = starRingEnd ℂ u := by
      apply Complex.ext <;> simp
    have hb := planarPrimitive_upper_bound hm (hcp ▸ hc) (neg_nonneg.mpr (le_of_not_ge ht))
    rw [planarPrimitive_neg m hseg,hcp,inverseF_conj hu] at hb
    have hn : planarPrimitive m u.re u.im ≤ 0 := by
      have hp := planarPrimitive_nonneg m u.re (neg_nonneg.mpr (le_of_not_ge ht))
      rw [planarPrimitive_neg m hseg] at hp
      linarith
    simpa only [abs_of_nonpos hn,Complex.norm_conj] using hb

end SymmetricMahler

end OAI
