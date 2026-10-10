import Mathlib
import OAI.Geometry.PrescribedPotential.NormalizedPoisson
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Dimension One Potential. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical ComplexOrder
namespace MongeAmpere

lemma singleton_det_add (H K : Matrix (Fin 1) (Fin 1) ℂ) (hH : H.PosDef) :
    (H + K).det.re = H.det.re * (1 + (H⁻¹ * K).trace.re) := by
  have hr : ((H 0 0).re : ℂ) = H 0 0 :=
    Complex.conj_eq_iff_re.mp (hH.isHermitian.apply 0 0)
  have hn : (H 0 0).re ≠ 0 := ne_of_gt (Complex.pos_iff.mp hH.diag_pos).1
  simp only [Matrix.det_fin_one, Matrix.add_apply, Complex.add_re,
    Matrix.trace_fin_one, Matrix.mul_apply, Fin.sum_univ_one,
    Matrix.inv_def, Matrix.adjugate_fin_one, Matrix.det_fin_one]
  rw [← hr]
  simp [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq, Ring.inverse_eq_inv]
  field_simp

lemma singleton_posDef_of_det (H : Matrix (Fin 1) (Fin 1) ℂ)
    (hH : H.IsHermitian) (hp : 0 < H.det.re) : H.PosDef := by
  have hd : H = Matrix.diagonal (fun _ : Fin 1 => H 0 0) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hd, Matrix.posDef_diagonal_iff]
  intro i
  apply Complex.pos_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [Matrix.det_fin_one] using hp
  · exact (Complex.conj_eq_iff_im.mp (hH.apply 0 0)).symm
end MongeAmpere

namespace Anticanonical.SourceSmooth
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas 1 X}

 

theorem dimensionOne_positiveDensity (g : KaehlerMetric A) (q : SmoothRealFunction A)
    (hq : ∀ x, 0 < q.value x) :
    ∃ (φ : SmoothRealFunction A) (c : ℝ), 0 < c ∧ g.PositivePotential φ ∧
      ∀ i z, z ∈ (A.chart i).target →
        (g.matrix i z + φ.hessian i z).det.re =
          c * q.localExpression i z * g.volumeCoefficient i z := by
  let x₀ : X := Classical.arbitrary X
  obtain ⟨u,a,hn,he⟩ := normalizedPoisson 1 X A g x₀ q
  have ha : 0 < a := by
    obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty u.continuous.continuousOn
    obtain ⟨i,hi⟩ := A.covers x
    have hm := g.linearized_nonpos_at_globalMax u (fun y => hx (mem_univ y)) i hi
    have heq := he i (A.chart i x) ((A.chart i).mapsTo hi)
    have hqe : q.localExpression i (A.chart i x) = q.value x := by
      simp only [SmoothRealFunction.localExpression, Function.comp_apply, (A.chart i).left_inv hi]
    rw [hqe] at heq
    linarith [hq x]
  let φ := u.realSMul a⁻¹
  have heq (i : Fin A.count) (z : Coordinates 1) (hz : z ∈ (A.chart i).target) :
      (g.matrix i z + φ.hessian i z).det.re =
        a⁻¹ * q.localExpression i z * g.volumeCoefficient i z := by
    rw [MongeAmpere.singleton_det_add _ _ (g.positive i z hz)]
    change g.volumeCoefficient i z * (1 + g.linearizedMongeAmpere φ i z) = _
    rw [show φ = u.realSMul a⁻¹ from rfl, g.linearizedMongeAmpere_realSMul]
    have hh := he i z hz
    have hae : a ≠ 0 := ne_of_gt ha
    field_simp
    rw [add_comm a _,hh]
  refine ⟨φ,a⁻¹,inv_pos.mpr ha,?_,heq⟩
  intro i z hz
  apply MongeAmpere.singleton_posDef_of_det
  · exact (g.positive i z hz).isHermitian.add (φ.hessian_hermitian i hz)
  · rw [heq i z hz]
    exact mul_pos (mul_pos (inv_pos.mpr ha) (hq ((A.chart i).symm z)))
      (g.volumeCoefficient_pos i hz)

 

theorem prescribedPotential_dimensionOne (X : Type) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] (A : ComplexAtlas 1 X)
    (P : A.ProjectiveEmbedding) (h : SemipositiveAnticanonicalMetric A) :
    HasPrescribedVolumePotential P h := by
  let g := projectiveBackground P
  let F := prescribedForcing g h
  let q : SmoothRealFunction A := {
    value := fun x => Real.exp (F.value x)
    smooth := fun i => Real.contDiff_exp.contDiffOn.comp (F.smooth i) (fun _ _ => mem_univ _) }
  obtain ⟨φ,c,hc,hp,he⟩ := dimensionOne_positiveDensity g q (fun x => Real.exp_pos _)
  refine ⟨φ,c,hc,hp,fun i z hz => ?_⟩
  rw [he i z hz]
  change c * Real.exp (F.localExpression i z) * g.volumeCoefficient i z = _
  rw [prescribedForcing_local g h i hz, Real.exp_sub,
    Real.exp_log (g.volumeCoefficient_pos i hz)]
  field_simp [ne_of_gt (g.volumeCoefficient_pos i hz)]

end Anticanonical.SourceSmooth

end
end

end OAI
