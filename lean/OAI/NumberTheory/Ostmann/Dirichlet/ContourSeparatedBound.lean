import OAI.NumberTheory.Ostmann.Dirichlet.ContourZeroSet

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open scoped BigOperators

theorem exists_contour_logDerivative_of_separated :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (hchi : chi ≠ 1) (T delta : ℝ), 1 ≤ T → 0 < delta → ∀ s : ℂ,
        1/4 ≤ s.re → s.re ≤ 2 → |s.im| ≤ T+1 →
        (∀ rho ∈ contourZeros chi hchi T, delta ≤ ‖s-rho‖) →
        chi.LFunction s ≠ 0 ∧
        ‖deriv chi.LFunction s / chi.LFunction s‖ ≤
          C*q*(T+7)*(1+1/delta) := by
  classical
  obtain ⟨C,hC,hlocal⟩ := uniform_wide_local_zero_estimates
  refine ⟨C,hC,?_⟩
  intro q _ chi hchi T delta hT hdelta s hre hre2 him hsep
  have hne : chi.LFunction s ≠ 0 := by
    intro hz
    have hlt : s.re < 1 := by
      by_contra! h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) h hz
    have hs : s ∈ contourZeros chi hchi T :=
      (mem_contourZeros chi hchi T s).mpr ⟨hz,by linarith,hlt,by linarith⟩
    have h := hsep s hs
    simp only [sub_self,norm_zero] at h
    linarith
  refine ⟨hne,?_⟩
  let w : ℂ := (s-dirichletCenter s.im)/(29/10:ℂ)
  have hw : ‖w‖ ≤ 19/20 := quarterPlane_coordinate_norm s hre hre2
  have hew : wideDirichletDiskPoint s.im w = s := wideDirichletDiskPoint_coordinate s
  obtain ⟨S,hS,hmass,hb⟩ := hlocal q chi hchi s.im
  have hzero (rho : ℂ) (hr : rho ∈ S) :
      wideDirichletDiskPoint s.im rho ∈ contourZeros chi hchi T :=
    wide_zero_mem_contourZeros chi hchi him ((hS rho).mp hr).1 ((hS rho).mp hr).2
  have hterm (rho : ℂ) (hr : rho ∈ S) :
      ‖((analyticOrderAt (wideNormalizedDirichlet chi s.im) rho).toNat:ℂ)/(w-rho)‖ ≤
      ((analyticOrderAt (wideNormalizedDirichlet chi s.im) rho).toNat:ℝ)*(29/10)/delta := by
    have hd := hsep _ (hzero rho hr)
    have he : s-wideDirichletDiskPoint s.im rho = (29/10:ℂ)*(w-rho) := by
      calc
        _ = wideDirichletDiskPoint s.im w-wideDirichletDiskPoint s.im rho :=
          congrArg (fun z => z-wideDirichletDiskPoint s.im rho) hew.symm
        _ = _ := by unfold wideDirichletDiskPoint; ring
    rw [he,norm_mul] at hd
    norm_num at hd
    have hden : delta/(29/10:ℝ) ≤ ‖w-rho‖ := (div_le_iff₀ (by norm_num)).mpr (by linarith)
    rw [norm_div,Complex.norm_natCast]
    calc
      _ ≤ ((analyticOrderAt (wideNormalizedDirichlet chi s.im) rho).toNat:ℝ) /
          (delta/(29/10:ℝ)) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by ring
  have hsum : ‖∑ rho ∈ S,
      ((analyticOrderAt (wideNormalizedDirichlet chi s.im) rho).toNat:ℂ)/(w-rho)‖ ≤
      (∑ rho ∈ S, ((analyticOrderAt (wideNormalizedDirichlet chi s.im) rho).toNat:ℝ)) *
        (29/10)/delta := by
    calc
      _ ≤ ∑ rho ∈ S,
          ‖((analyticOrderAt (wideNormalizedDirichlet chi s.im) rho).toNat:ℂ)/(w-rho)‖ := norm_sum_le _ _
      _ ≤ ∑ rho ∈ S,
          ((analyticOrderAt (wideNormalizedDirichlet chi s.im) rho).toNat:ℝ)*(29/10)/delta :=
        Finset.sum_le_sum hterm
      _ = _ := by rw [← Finset.sum_div,← Finset.sum_mul]
  have hmass' : (∑ rho ∈ S,
      ((analyticOrderAt (wideNormalizedDirichlet chi s.im) rho).toNat:ℝ)) ≤ C*q*(T+7) :=
    hmass.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hsum' := hsum.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmass' (by norm_num : (0:ℝ)≤29/10)) hdelta.le)
  have hb' := hb w hw (by simpa only [hew] using hne)
  rw [hew] at hb'
  have herror := hb'.trans (mul_le_mul_of_nonneg_left
    (show |s.im|+6 ≤ T+7 by linarith) (by positivity : 0≤C*(q:ℝ)))
  have htriangle := norm_add_le
    ((29/10:ℂ)*(deriv chi.LFunction s/chi.LFunction s)-
      ∑ rho ∈ S, ((analyticOrderAt (wideNormalizedDirichlet chi s.im) rho).toNat:ℂ)/(w-rho))
    (∑ rho ∈ S, ((analyticOrderAt (wideNormalizedDirichlet chi s.im) rho).toNat:ℂ)/(w-rho))
  rw [sub_add_cancel,norm_mul] at htriangle
  norm_num at htriangle
  have hnonneg : 0 ≤ C*(q:ℝ)*(T+7) := by positivity
  rw [div_eq_mul_inv] at hsum'
  rw [norm_div]
  simp only [one_div]
  nlinarith

end Ostmann.Dirichlet

end

end OAI
