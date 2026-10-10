import OAI.NumberTheory.CubicMoment.Estimates.PrincipalIdealTheta

namespace OAI

/-! The nonzero unweighted lattice Gaussian, with its exact ideal multiplicity
and exponential decay. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace CubicFirstMoment

def cubicThetaLatticeGaussianTail (t : ℝ) : ℝ :=
  ∑' a : {a : Eisenstein // a≠0}, Real.exp (-t*norm a.val)

lemma cubicThetaLatticeGaussianTail_summable {t : ℝ} (ht : 0<t) :
    Summable (fun a : {a : Eisenstein // a≠0} => Real.exp (-t*norm a.val)) := by
  have h := (principalLatticeTheta_summable
    (mul_pos ht (residueHeckeScale_pos (q:=1) one_ne_zero))).subtype
    (fun a : Eisenstein => a≠0)
  have hA := (residueHeckeScale_pos (q:=1) one_ne_zero).ne'
  convert h.norm using 1
  ext a
  dsimp only [Function.comp_apply]
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  congr 1
  field_simp


lemma cubicThetaLatticeGaussianTail_nonneg (t : ℝ) :
    0≤cubicThetaLatticeGaussianTail t := tsum_nonneg (fun _ => (Real.exp_pos _).le)

lemma cubicThetaLatticeGaussianTail_ideal {t : ℝ} (ht : 0<t) :
    (cubicThetaLatticeGaussianTail t:ℂ)=(Nat.card (Eisensteinˣ):ℂ)*
      idealTheta (residueHeckeScale 1) (fun _ => 1) (t*residueHeckeScale 1) := by
  have hA := residueHeckeScale_pos (q:=1) one_ne_zero
  rw [cubicThetaLatticeGaussianTail,Complex.ofReal_tsum]
  convert principalIdealTheta_nonzero hA (mul_pos ht hA) using 1
  apply tsum_congr
  intro a
  congr 2
  field_simp

lemma cubicThetaLatticeGaussianTail_isBigO_exp :
    cubicThetaLatticeGaussianTail =O[atTop] (fun t : ℝ => Real.exp (-t/2)) := by
  have hA := residueHeckeScale_pos (q:=1) one_ne_zero
  let C := (Nat.card (Eisensteinˣ):ℝ)*
    ∑' ν : EisensteinIdealExponent, Real.exp (-idealExponentNorm ν/(2*residueHeckeScale 1))
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (max (1/residueHeckeScale 1) 1)] with t ht
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) ht)
  have htA : 1≤t*residueHeckeScale 1 := by
    apply (div_le_iff₀ hA).mp
    exact (le_max_left _ _).trans ht
  have h := idealTheta_norm_bound hA (fun _ => 1) (by simp) htA
  have he : -(t*residueHeckeScale 1)/(2*residueHeckeScale 1)=-t/2 := by field_simp
  rw [he] at h
  rw [Real.norm_eq_abs,abs_of_nonneg (cubicThetaLatticeGaussianTail_nonneg t)]
  have hh := congrArg (fun z : ℂ => ‖z‖) (cubicThetaLatticeGaussianTail_ideal ht0)
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (cubicThetaLatticeGaussianTail_nonneg t),
    norm_mul,Complex.norm_natCast] at hh
  rw [hh]
  simpa only [C,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_assoc] using
    mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (Nat.card (Eisensteinˣ)))

end CubicFirstMoment

end

end OAI
