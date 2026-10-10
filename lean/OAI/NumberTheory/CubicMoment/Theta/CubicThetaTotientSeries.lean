import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTotientConvolution
import OAI.NumberTheory.CubicMoment.Estimates.PrincipalZetaPole
import OAI.NumberTheory.CubicMoment.Estimates.IdealDirichletInverse

namespace OAI

/-! The exact quotient of principal ideal zeta functions supplied by the
normalized residue-unit counts. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaIdealDensity (ν : EisensteinIdealExponent) : ℂ :=
  (cubicThetaIdealTotient ν:ℂ)/(idealExponentNorm ν:ℂ)

lemma cubicThetaIdealDensity_norm (ν : EisensteinIdealExponent) :
    ‖cubicThetaIdealDensity ν‖ ≤ 1 := by
  let : Finite (Residues (idealExponentGenerator ν)) :=
    finite_residues (idealExponentGenerator_ne_zero ν)
  have he := Nat.card_le_card_of_injective
    (fun u : (Residues (idealExponentGenerator ν))ˣ => (u:Residues (idealExponentGenerator ν)))
    Units.val_injective
  rw [residues_card (idealExponentGenerator_ne_zero ν)] at he
  have hN := idealExponentNorm_pos ν
  have hreal : (cubicThetaIdealTotient ν:ℝ) ≤ idealExponentNorm ν := by
    change (Nat.card (Residues (idealExponentGenerator ν))ˣ:ℝ)≤
      (normNat (idealExponentGenerator ν):ℝ)
    exact_mod_cast he
  rw [cubicThetaIdealDensity,norm_div,Complex.norm_natCast,Complex.norm_real,
    Real.norm_of_nonneg hN.le]
  exact (div_le_one hN).mpr hreal

lemma cubicThetaIdealDensity_coeff (ν : EisensteinIdealExponent) :
    cubicThetaIdealDensity ν=
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        ((MvPowerSeries.coeff p.1 idealMoebiusSeries:ℝ):ℂ)/(idealExponentNorm p.1:ℂ) := by
  have he := congrArg Complex.ofReal (cubicThetaTotient_divisor_sum ν)
  simpa only [cubicThetaIdealDensity,Complex.ofReal_div,Complex.ofReal_natCast,
    Complex.ofReal_sum] using he

lemma cubicTheta_norm_cpow_shift (ν : EisensteinIdealExponent) (s : ℂ) :
    (idealExponentNorm ν:ℂ)^(-(s+1))=
      (idealExponentNorm ν:ℂ)^(-s)/(idealExponentNorm ν:ℂ) := by
  rw [show -(s+1)=-s+(-1) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'),
    Complex.cpow_neg_one,div_eq_mul_inv]

lemma cubicThetaTotientSeries_product {s : ℂ} (hs : 1<s.re) :
    normDirichletSeries cubicThetaIdealDensity idealExponentNorm s=
      normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ))
        idealExponentNorm (s+1)*normDirichletSeries (fun _ => 1) idealExponentNorm s := by
  have hsp : 1<(s+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hmu (ν : EisensteinIdealExponent) : ‖((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)‖≤1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using idealMoebiusSeries_abs_le_one ν
  let f := fun ν : EisensteinIdealExponent =>
    ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*(idealExponentNorm ν:ℂ)^(-(s+1))
  let g := fun ν : EisensteinIdealExponent => (1:ℂ)*(idealExponentNorm ν:ℂ)^(-s)
  have hf := idealDirichlet_norm_summable _ hmu hsp
  have hg := idealDirichlet_norm_summable (fun _ => (1:ℂ)) (by simp) hs
  change (∑' ν, cubicThetaIdealDensity ν*(idealExponentNorm ν:ℂ)^(-s))=
    (∑' ν, f ν)*(∑' ν, g ν)
  rw [ideal_cauchy_product f g hf hg]
  apply tsum_congr
  intro ν
  rw [cubicThetaIdealDensity_coeff,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only [f,g]
  rw [cubicTheta_norm_cpow_shift]
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [←he,idealExponentNorm_add,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (idealExponentNorm_pos p.1).le (idealExponentNorm_pos p.2).le]
  ring

theorem cubicThetaTotientSeries_zeta_quotient {s : ℂ} (hs : 1<s.re) :
    normDirichletSeries cubicThetaIdealDensity idealExponentNorm s=
      principalIdealZeta s/principalIdealZeta (s+1) := by
  have hsp : 1<(s+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hmu := idealDirichlet_moebius_mul (fun _ => (1:ℂ)) (by simp) rfl (by simp) hsp
  have hn := idealDirichlet_ne_zero (fun _ => (1:ℂ)) (by simp) rfl (by simp) hsp
  rw [cubicThetaTotientSeries_product hs,principalIdealZeta_right hs,
    principalIdealZeta_right hsp]
  apply (eq_div_iff hn).mpr
  have hmu' : normDirichletSeries
      (fun ν => ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)) idealExponentNorm (s+1)*
        normDirichletSeries (fun _ => (1:ℂ)) idealExponentNorm (s+1)=1 := by
    simpa only [mul_one] using hmu
  calc
    _ = normDirichletSeries (fun _ => (1:ℂ)) idealExponentNorm s *
        (normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ))
          idealExponentNorm (s+1)*normDirichletSeries (fun _ => (1:ℂ)) idealExponentNorm (s+1)) := by ring
    _ = _ := by rw [hmu',mul_one]

end CubicFirstMoment

end

end OAI
