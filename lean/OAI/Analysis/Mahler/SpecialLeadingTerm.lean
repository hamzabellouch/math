import OAI.Analysis.Mahler.ComplexStripMap
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter Finset Asymptotics
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

noncomputable def inverseLinearCoefficient : ℂ := deriv inverseF 0

lemma inverseLinearCoefficient_ne_zero : inverseLinearCoefficient ≠ 0 :=
  inverseF_deriv_ne_zero zero_mem_Omega

lemma analyticAt_inverseF_zero : AnalyticAt ℂ inverseF 0 :=
  differentiableOn_inverseF.analyticAt (isOpen_Omega.mem_nhds zero_mem_Omega)

lemma analyticAt_inverseF_dslope : AnalyticAt ℂ (dslope inverseF 0) 0 := by
  obtain ⟨p,hp⟩ := analyticAt_inverseF_zero
  exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩

lemma inverseF_factor (w : ℂ) : w*dslope inverseF 0 w = inverseF w := by
  simpa [smul_eq_mul,inverseF_zero] using sub_smul_dslope inverseF (0 : ℂ) w

/-- The exact univariate power has its asserted degree-m leading term and
an order-(m+1) remainder. The divided difference handles the origin. -/
theorem inverseF_power_leading (m : ℕ) :
    (fun w : ℂ => inverseF w^m-(inverseLinearCoefficient*w)^m) =O[𝓝 0]
      (fun w : ℂ => ‖w‖^(m+1)) := by
  have hd := (analyticAt_inverseF_dslope.pow m).differentiableAt.isBigO_sub
  have hm := (isBigO_refl (fun w : ℂ => w^m) (𝓝 0)).mul hd
  have he : ∀ w : ℂ, w^m*((dslope inverseF 0 w)^m-(dslope inverseF 0 0)^m) =
      inverseF w^m-(inverseLinearCoefficient*w)^m := by
    intro w
    rw [mul_sub,← mul_pow,inverseF_factor,dslope_same]
    simp only [inverseLinearCoefficient,mul_pow]
    ring
  simpa only [Pi.pow_apply,he,sub_zero,norm_mul,norm_pow,pow_succ] using hm.norm_right

noncomputable def specialLeadingMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Fin n → ℂ) : Fin N → ℂ := fun j => (inverseLinearCoefficient*complexRow A j z)^m

noncomputable def specialLeadingPolynomial (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (j : Fin N) : MvPolynomial (Fin n) ℂ :=
  (∑ i, MvPolynomial.C (inverseLinearCoefficient*(A j i : ℂ))*MvPolynomial.X i)^m

lemma specialLeadingPolynomial_eval (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (j : Fin N) (z : Fin n → ℂ) :
    MvPolynomial.eval z (specialLeadingPolynomial A m j) = specialLeadingMap A m z j := by
  simp [specialLeadingPolynomial,specialLeadingMap,complexRow_apply,Finset.mul_sum,mul_assoc]

lemma specialLeadingPolynomial_homogeneous (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) (j : Fin N) :
    (specialLeadingPolynomial A m j).IsHomogeneous m := by
  have h : (∑ i : Fin n, MvPolynomial.C (inverseLinearCoefficient*(A j i : ℂ))*MvPolynomial.X i).IsHomogeneous 1 := by
    exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa only [specialLeadingPolynomial,one_mul] using h.pow m

/-- The leading homogeneous map is nonzero away from zero whenever the rows
have full rank. This includes every coordinate, rather than a scalar slice. -/
theorem specialLeadingMap_eq_zero_iff (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    (z : Fin n → ℂ) : specialLeadingMap A m z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply complexRow_injective A hA
    funext j
    have hp : (inverseLinearCoefficient*complexRow A j z)^m = 0 := congrFun h j
    have hr : complexRow A j z = 0 := by
      by_contra hn
      exact (pow_ne_zero m (mul_ne_zero inverseLinearCoefficient_ne_zero hn)) hp
    simpa using hr
  · rintro rfl
    funext j
    simp [specialLeadingMap,hm.ne']

/-- The special holomorphic map has the homogeneous leading
map, with a norm-controlled order-(m+1) error in all complex variables. -/
theorem specialMap_leading_remainder (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    (fun z : Fin n → ℂ => specialMap A m z-specialLeadingMap A m z) =O[𝓝 0]
      (fun z : Fin n → ℂ => ‖z‖^(m+1)) := by
  apply isBigO_pi.mpr
  intro j
  have hrow : Tendsto (complexRow A j) (𝓝 0) (𝓝 0) := by
    simpa using (complexRow A j).continuous.tendsto (0 : Fin n → ℂ)
  have h := (inverseF_power_leading m).comp_tendsto hrow
  have hr := ((complexRow A j).isBigO_id (𝓝 (0 : Fin n → ℂ))).norm_norm.pow (m+1)
  exact h.trans hr

end SymmetricMahler

end OAI
