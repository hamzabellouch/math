import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogPhase
import OAI.NumberTheory.TwoPoint.Halasz.HalaszWeightedPrefix
import OAI.NumberTheory.TwoPoint.Halasz.HalaszCubicMaximum

namespace OAI

/-! Uniform Dirichlet block bounds in the weak Vinogradov--Korobov strip.
The harmless power of the height replaces all degree-selection constants. -/
namespace TwoPointCorrelations

open Finset Complex

theorem halasz_log_dirichlet_block : ∃ C : ℝ, 1≤C ∧ ∀ N H : ℕ,
    1≤N → H≤N → ∀ a : ℝ, a∈Set.Icc (0:ℝ) 1 → ∀ s : ℂ,
    2/3≤s.re → ∀ L lam : ℝ, 0<L → 1≤Real.log N →
    L=lam*Real.log N → 49/100≤lam →
    (N:ℝ)^(2/3:ℝ)≤(N:ℝ)/2 → |s.im|=(N:ℝ)^lam →
    ‖∑ n∈range H,(((N:ℝ)+a+n:ℝ):ℂ)^(-s)‖≤
      C*(L+1)^6*Real.exp ((10^9:ℝ)*(max (1-s.re) 0)^(3/2:ℝ)*L)+4 := by
  obtain ⟨C,hC,hphase⟩ := halasz_log_phase_bound
  refine ⟨C,hC,?_⟩
  intro N H hN hH a ha s hσ L lam hL hy hLy hlam hhalf ht
  have hNR : 1≤(N:ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N:ℝ) := by linarith
  have hx : 0<(N:ℝ)+a := by linarith [ha.1]
  have hlam0 : 0<lam := by linarith
  have hlamL : lam≤L := by nlinarith
  let δ := max (1-s.re) 0
  let η := 1/((10^15:ℝ)*lam^2)
  let A := C*(lam+1)^6*(N:ℝ)^(-η)
  have hA : 0≤A := by dsimp only [A]; positivity
  have hw := halasz_weighted_log_prefix hx s (by linarith : 0≤s.re) H
    ((N:ℝ)*A+4*(N:ℝ)^(2/3:ℝ)) (fun n hn => by
      have hh := hphase N n hN (hn.trans hH) a (-s.im) lam ha hlam hhalf
        (by simpa only [abs_neg] using ht)
      simpa only [A,η,neg_div] using hh)
  have hwbase : ((N:ℝ)+a)^(-s.re)≤(N:ℝ)^(-s.re) :=
    Real.rpow_le_rpow_of_nonpos hN0 (by linarith [ha.1]) (by linarith)
  apply hw.trans
  apply (mul_le_mul_of_nonneg_right hwbase (by positivity)).trans
  have hmain : (N:ℝ)^(-s.re)*((N:ℝ)*A)=
      C*(lam+1)^6*Real.exp ((1-s.re)*Real.log N-
        (Real.log N)^3/((10^15:ℝ)*L^2)) := by
    have hp : (N:ℝ)^(-s.re)*(N:ℝ)*(N:ℝ)^(-η)=
        (N:ℝ)^(1-s.re-η) := by
      calc
        _ = (N:ℝ)^(-s.re+1)*(N:ℝ)^(-η) := by
          rw [Real.rpow_add hN0,Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
    dsimp only [A]
    calc
      _ = C*(lam+1)^6*((N:ℝ)^(-s.re)*(N:ℝ)*(N:ℝ)^(-η)) := by ring
      _ = C*(lam+1)^6*Real.exp ((1-s.re-η)*Real.log N) := by
        rw [hp,Real.rpow_def_of_pos hN0]
        congr 2
        ring
      _ = _ := by
        congr 2
        have he := halasz_log_cubic_identity hL (show 0<Real.log N by linarith) hLy
        dsimp only [η]
        calc
          _ = (1-s.re)*Real.log N+(-1/((10^15:ℝ)*lam^2))*Real.log N := by ring
          _ = _ := by rw [he]; ring
  have htail : (N:ℝ)^(-s.re)*(N:ℝ)^(2/3:ℝ)≤1 := by
    rw [← Real.rpow_add hN0]
    apply Real.rpow_le_one_of_one_le_of_nonpos hNR
    linarith
  have hcubic : (1-s.re)*Real.log N-(Real.log N)^3/((10^15:ℝ)*L^2)≤
      (10^9:ℝ)*δ^(3/2:ℝ)*L := by
    have hh := halasz_cubic_maximum (show 0≤δ from le_max_right _ _)
      (show 0≤Real.log N by linarith) hL
    have hm := mul_le_mul_of_nonneg_right (show 1-s.re≤δ from le_max_left _ _)
      (show 0≤Real.log N by linarith)
    linarith
  have hcoef : C*(lam+1)^6≤C*(L+1)^6 := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith) (by linarith) 6) (by linarith)
  have hresult := mul_le_mul hcoef (Real.exp_le_exp.mpr hcubic)
    (Real.exp_pos _).le (by positivity : 0≤C*(L+1)^6)
  rw [mul_add,hmain]
  nlinarith only [hresult,htail]

end TwoPointCorrelations

end OAI
