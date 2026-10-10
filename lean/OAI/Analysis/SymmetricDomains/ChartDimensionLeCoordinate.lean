import Mathlib
import OAI.Analysis.SymmetricDomains.EtaleDerivationExtensionUnique

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Algebra

theorem trdeg_ge_of_polynomial_local_retraction {m N : ℕ}
    (V : Set (Fin N → ℂ)) (F : (Fin m → ℂ) → (Fin N → ℂ))
    (hF : AnalyticAt ℂ F 0)
    (hFV : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), F z ∈ V)
    (R : Fin m → MvPolynomial (Fin N) ℂ)
    (hR : (fun z i => MvPolynomial.eval (F z) (R i)) =ᶠ[𝓝 (0 : Fin m → ℂ)] id) :
    (m : Cardinal) ≤ Algebra.trdeg ℂ
      (MvPolynomial (Fin N) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ V) := by
  classical
  let I := MvPolynomial.vanishingIdeal ℂ V
  let Q := MvPolynomial (Fin N) ℂ ⧸ I
  let f : Fin N → (Fin m → ℂ) → ℂ := fun j z => F z j
  have hf (j : Fin N) : AnalyticAt ℂ (f j) 0 :=
    ((ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _).comp hF
  let a : Fin N → AnalyticGerm (Fin m → ℂ) := fun j => analyticGermOf _ (f j) (hf j)
  have haI : ∀ P ∈ I, MvPolynomial.aeval a P = 0 := by
    intro P hP
    apply Subtype.ext
    rw [analyticGerm_aeval f hf P]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hFV] with z hz
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hP _ hz
  let ρ : Q →ₐ[ℂ] AnalyticGerm (Fin m → ℂ) :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval a) haI
  let x : Fin m → Q := fun i => Ideal.Quotient.mkₐ ℂ I (R i)
  have he : ρ ∘ x = analyticCoordinate := by
    funext i
    change MvPolynomial.aeval a (R i) = analyticCoordinate i
    apply Subtype.ext
    rw [analyticGerm_aeval f hf (R i)]
    apply Filter.Germ.coe_eq.mpr
    exact hR.mono fun z hz => congrFun hz i
  have hx : AlgebraicIndependent ℂ x := AlgebraicIndependent.of_comp ρ
    (he.symm ▸ algebraicIndependent_analyticCoordinate)
  simpa only [Cardinal.mk_fintype,Fintype.card_fin] using hx.cardinalMk_le_trdeg

noncomputable def linearCoordinatePolynomial {m N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] (Fin m → ℂ)) (i : Fin m) : MvPolynomial (Fin N) ℂ :=
  ∑ j, MvPolynomial.C (L (Pi.single j 1) i) * MvPolynomial.X j

theorem linearCoordinatePolynomial_eval {m N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] (Fin m → ℂ)) (i : Fin m) (z : Fin N → ℂ) :
    MvPolynomial.eval z (linearCoordinatePolynomial L i) = L z i := by
  classical
  have hz : z = ∑ j : Fin N, z j • Pi.single j (1 : ℂ) := by
    ext k
    simp [Pi.single_apply]
  simp only [linearCoordinatePolynomial,map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  conv_rhs => rw [hz]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem trdeg_ge_of_analytic_immersion {m N : ℕ}
    (V : Set (Fin N → ℂ)) (F : (Fin m → ℂ) → (Fin N → ℂ))
    (hF : AnalyticAt ℂ F 0)
    (hFV : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), F z ∈ V)
    (L : (Fin N → ℂ) →L[ℂ] (Fin m → ℂ))
    (hL : L.comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ (Fin m → ℂ)) :
    (m : Cardinal) ≤ Algebra.trdeg ℂ
      (MvPolynomial (Fin N) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ V) := by
  let g : (Fin m → ℂ) → (Fin m → ℂ) := fun z => L (F z) - L (F 0)
  have hg : AnalyticAt ℂ g 0 := ((L.analyticAt _).comp hF).sub analyticAt_const
  have hg0 : g 0 = 0 := sub_self _
  have hgd : HasFDerivAt g (ContinuousLinearEquiv.refl ℂ (Fin m → ℂ) :
      (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) 0 := by
    simpa only [g,Function.comp_def,hL,ContinuousLinearEquiv.coe_refl] using
      ((L.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt).sub_const (L (F 0)))
  obtain ⟨e,he,h0,hea⟩ := analytic_local_inverse hg (ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)) hgd
  have hinv0 : e.symm 0 = 0 := by
    have hh := e.left_inv h0
    rwa [show e 0 = 0 from by rw [he]; exact hg0] at hh
  have hea0 : AnalyticAt ℂ e.symm 0 := hg0 ▸ hea
  have ht : Tendsto e.symm (𝓝 (0 : Fin m → ℂ)) (𝓝 0) := by
    simpa only [ContinuousAt,hinv0] using hea0.continuousAt
  have hF' : AnalyticAt ℂ (F ∘ e.symm) 0 :=
    (hinv0.symm ▸ hF).comp hea0
  have h0t : (0 : Fin m → ℂ) ∈ e.target := by
    have hh := e.map_source h0
    rwa [show e 0 = 0 from by rw [he]; exact hg0] at hh
  let R : Fin m → MvPolynomial (Fin N) ℂ := fun i =>
    linearCoordinatePolynomial L i - MvPolynomial.C (L (F 0) i)
  apply trdeg_ge_of_polynomial_local_retraction V (F ∘ e.symm) hF' (ht hFV) R
  filter_upwards [e.open_target.mem_nhds h0t] with z hz
  funext i
  have hh := congrFun (e.right_inv hz) i
  rw [he] at hh
  simpa only [R,Function.comp_apply,map_sub,linearCoordinatePolynomial_eval,MvPolynomial.eval_C,
    g,Pi.sub_apply,Function.id_def] using hh

theorem chart_dimension_le_coordinate_trdeg {m N : ℕ}
    (V : Set (Fin N → ℂ)) (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (F 0))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Fin m → ℂ)] id)
    (hFV : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), F z ∈ V) :
    (m : Cardinal) ≤ Algebra.trdeg ℂ
      (MvPolynomial (Fin N) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ V) := by
  apply trdeg_ge_of_analytic_immersion V F hF hFV (fderiv ℂ G (F 0))
  have hcomp := hG.differentiableAt.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt
  have hid := hcomp.congr_of_eventuallyEq hGF.symm
  exact hid.unique (hasFDerivAt_id 0)

end Release061

end

end OAI
