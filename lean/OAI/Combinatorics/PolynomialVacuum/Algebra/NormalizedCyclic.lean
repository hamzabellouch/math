import OAI.Combinatorics.PolynomialVacuum.Algebra.AnalyticNormalization
import OAI.Combinatorics.PolynomialVacuum.Algebra.Existence
import OAI.Combinatorics.PolynomialVacuum.Pairing.RowTranspose

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical Filter
open scoped Topology

theorem eval_frequently_ne_zero {N : ℕ} (p : MvPolynomial (Fin N) ℂ) (hp : p≠0) (X : Fin N → ℂ) :
    ∃ᶠ Y in nhds X,MvPolynomial.eval Y p≠0 := by
  by_contra hh
  have hz : (fun Y=>MvPolynomial.eval Y p)=ᶠ[nhds X] 0 := by
    change ∀ᶠ Y in nhds X,MvPolynomial.eval Y p=0
    simpa using hh
  have he := (AnalyticOnNhd.eval_mvPolynomial p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ X) hz
  apply hp
  apply MvPolynomial.funext
  intro Y
  simpa using he (Set.mem_univ Y)

namespace AnalyticVacuum

theorem normalizedVacuum_cyclic (N : ℕ) (s : Fin (N+1) → Spin) :
    zeta^charge (s 0)*normalizedVacuum (N+1) (fun _=>1) (shiftForward s)=
      normalizedVacuum (N+1) (fun _=>1) s := by
  let rot : (Fin (N+1) → ℂ) → (Fin (N+1) → ℂ):=fun X=>X ∘ (finRotate (N+1)).symm
  have hc : Continuous rot := by unfold rot; fun_prop
  have hr : rot (fun _=>1)=fun _=>1 := rfl
  have hf := normalizedVacuum_eventually_ratio (N+1) (shiftForward s)
  have hg := (hc.continuousAt (x:=(fun _=>1))).tendsto.eventually
    (normalizedVacuum_eventually_ratio (N+1) s)
  have hz := eval_frequently_ne_zero (polynomialVacuum (N+1) (fun _=>.zero))
    (polynomialVacuum_empty_ne_zero (N+1)) (fun _=>1)
  have he : ∃ᶠ X in nhds (fun _ : Fin (N+1)=>(1:ℂ)),
      zeta^charge (s 0)*normalizedVacuum (N+1) X (shiftForward s)=normalizedVacuum (N+1) (rot X) s := by
    apply (hz.and_eventually (hf.and hg)).mono
    rintro X ⟨hX,ha,hb⟩
    have hcy := polynomial_vacuum_is_vacuum.2.2.2.2.2.2.2.2.1 N s X
    have h0 := polynomial_vacuum_is_vacuum.2.2.2.2.2.2.2.2.1 N (fun _=>.zero) X
    simp only [charge,zpow_zero,one_mul,Function.comp_def] at h0
    have hs : s ∘ finRotate (N+1)=shiftForward s := by funext j; simp [shiftForward,finRotate_apply]
    rw [hs] at hcy
    rw [ha hX,hb (fun hzero => hX (h0.trans hzero))]
    change zeta^charge (s 0)*(MvPolynomial.eval X (polynomialVacuum (N+1) (shiftForward s))/
      MvPolynomial.eval X (polynomialVacuum (N+1) (fun _=>.zero)))=
      MvPolynomial.eval (rot X) (polynomialVacuum (N+1) s)/MvPolynomial.eval (rot X) (polynomialVacuum (N+1) (fun _=>.zero))
    rw [← mul_div_assoc,hcy,h0]
    rfl
  have hl := ((continuousAt_const (y:=zeta^charge (s 0))).mul (analytic_normalizedVacuum (N+1) (shiftForward s)).continuousAt).tendsto
  have ht := ((analytic_normalizedVacuum (N+1) s).continuousAt.comp (hc.continuousAt (x:=(fun _=>1)))).tendsto
  exact tendsto_nhds_unique_of_frequently_eq hl ht he

end AnalyticVacuum
end PolynomialVacuumAlgebra

end OAI
