import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowSlitKernel
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.AnalyticMatchingColumn
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! Schwarz conjugation of the actual regularized H integral and its boundary column. -/

open MeasureTheory
namespace DefocusingNLS

theorem star_cpow_of_mem_slit (x q : ℂ) (hx : x ∈ Complex.slitPlane) :
    star (x^q)=(star x)^(star q) := by
  simpa only [Complex.star_def,Complex.conj_conj] using
    (Complex.conj_cpow x (star q) (Complex.slitPlane_arg_ne_pi hx)).symm

theorem regularizedSlowKernel_star (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : x ∈ Complex.slitPlane) (u : ℝ) (hu : 0 < u) :
    star (regularizedSlowKernel q m x u)=regularizedSlowKernel (star q) m (star x) u := by
  have hp := star_cpow_of_mem_slit (u : ℂ) (q-1) (Complex.ofReal_mem_slitPlane.mpr hu)
  have hb := star_cpow_of_mem_slit (1+(u : ℂ)/x) ((m : ℂ)-1-q)
    (one_add_real_div_mem_slitPlane_of_slit x hx hu.le)
  simp only [regularizedSlowKernel,regularizingBracket,star_mul,star_sub,star_one,hp,hb]
  simp only [star_natCast,star_one,star_add,star_div₀,Complex.star_def,
    Complex.conj_ofReal,← Complex.exp_conj,map_neg]
  ring

theorem regularizedSlowSolution_star (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : x ∈ Complex.slitPlane) :
    star (regularizedSlowSolution q m x)=regularizedSlowSolution (star q) m (star x) := by
  have hi : star (∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m x u)=
      ∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel (star q) m (star x) u := by
    rw [Complex.star_def,← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact regularizedSlowKernel_star q m x hx u hu
  simp only [regularizedSlowSolution,star_mul,star_add,star_one,star_inv₀,hi,
    star_cpow_of_mem_slit x (-q) hx,star_neg]
  rw [Complex.star_def,← Complex.Gamma_conj]
  ring

theorem slowBoundaryColumn_star (q : ℂ) (m : ℕ) (s : ℂ)
    (hs : -s ∈ Complex.slitPlane) :
    star (slowBoundaryColumn q m s)=slowBoundaryColumn (star q) m (star s) := by
  ext i
  fin_cases i
  · change star (regularizedSlowSolution q m (-s))=regularizedSlowSolution (star q) m (-star s)
    simpa only [star_neg] using regularizedSlowSolution_star q m (-s) hs
  · change star (q*regularizedSlowSolution (q+1) (m+1) (-s))=
      star q*regularizedSlowSolution (star q+1) (m+1) (-star s)
    rw [star_mul,regularizedSlowSolution_star (q+1) (m+1) (-s) hs]
    simp only [star_add,star_one,star_neg]
    ring

end DefocusingNLS

end OAI
