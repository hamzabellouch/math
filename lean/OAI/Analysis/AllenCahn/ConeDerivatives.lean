import OAI.Analysis.AllenCahn.SechSpectrum

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff

lemma conePotential_coord {n : ℕ} (ν : Space n) (i : Fin n) (x : Space n) :
    coordDeriv (conePotential ν) i x =
      2*Real.tanh (inner ℝ ν x/Real.sqrt 2)*sech (inner ℝ ν x/Real.sqrt 2)^2 *
        (inner ℝ ν (basis n i)/Real.sqrt 2) := by
  have hI : HasFDerivAt (fun z : Space n => inner ℝ ν z/Real.sqrt 2)
      ((Real.sqrt 2)⁻¹ • innerSL ℝ ν) x := by
    simpa only [div_eq_inv_mul, innerSL_apply_apply] using ((innerSL ℝ ν).hasFDerivAt (x := x)).const_mul ((Real.sqrt 2)⁻¹)
  have H := (((tanh_hasDerivAt (inner ℝ ν x/Real.sqrt 2)).comp_hasFDerivAt x hI).pow 2).const_add (1 : ℝ)
  change HasFDerivAt (conePotential ν)
    ((2 • Real.tanh (inner ℝ ν x/Real.sqrt 2) ^ (2-1)) •
      (sech (inner ℝ ν x/Real.sqrt 2)^2 • ((Real.sqrt 2)⁻¹ • innerSL ℝ ν))) x at H
  dsimp only [coordDeriv]
  rw [H.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
    Nat.reduceSub, pow_one, two_smul]
  ring

lemma conePotential_coord_bound {n : ℕ} {ν : Space n} (hν : ‖ν‖ = 1)
    (i : Fin n) (x : Space n) : |coordDeriv (conePotential ν) i x| ≤ 2 := by
  rw [conePotential_coord]
  have hr : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hi : |inner ℝ ν (basis n i)| ≤ 1 := by
    simpa only [hν, (basis n).orthonormal.norm_eq_one i, mul_one] using abs_real_inner_le_norm ν (basis n i)
  have hs : sech (inner ℝ ν x/Real.sqrt 2)^2 ≤ 1 := by
    nlinarith [sech_sq_tanh (inner ℝ ν x/Real.sqrt 2), sq_nonneg (Real.tanh (inner ℝ ν x/Real.sqrt 2))]
  simp only [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    abs_of_nonneg (sq_nonneg (sech (inner ℝ ν x/Real.sqrt 2))),
    abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))]
  have ht := (Real.abs_tanh_lt_one (inner ℝ ν x/Real.sqrt 2)).le
  have hd : |inner ℝ ν (basis n i)| / Real.sqrt 2 ≤ 1 :=
    (div_le_one (by positivity)).mpr (hi.trans hr)
  nlinarith [sq_nonneg (sech (inner ℝ ν x/Real.sqrt 2)), abs_nonneg (Real.tanh (inner ℝ ν x/Real.sqrt 2)),
    mul_le_mul ht hs (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1),
    mul_le_mul (mul_le_mul ht hs (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1)) hd
      (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg 2)) (by norm_num : (0:ℝ) ≤ 1*1)]

lemma conePotential_extreme_separated {n : ℕ} {ν : Space n} (hν : ‖ν‖ = 1)
    {f : Space n → ℝ} (hf : f ∈ (positiveLinearCone (conePotential ν)).extremePoints ℝ) :
    ∃ (b : Space n) (F : ℝ → ℝ), inner ℝ b ν = 0 ∧
      ContDiff ℝ ∞ F ∧ (∀ y, 0 < F y) ∧ F 0 = 1 ∧
      (∀ x, f x = Real.exp (inner ℝ b x)*F (inner ℝ ν x/Real.sqrt 2)) ∧
      ∀ y, deriv (deriv F) y = (4-2*‖b‖^2-2*sech y^2)*F y := by
  let H : Submodule ℝ (Space n) := (innerSL ℝ ν).ker
  have hh : ∀ t ∈ H, ∀ x, conePotential ν (t+x) = conePotential ν x := by
    intro t ht x
    have ht' : inner ℝ ν t = 0 := ht
    dsimp [conePotential]
    rw [inner_add_right, ht', zero_add]
  obtain ⟨b, hb⟩ := positiveLinearCone_extreme_character (conePotential_smooth ν)
    (by norm_num : (0:ℝ) ≤ 2)
    (fun x => by rw [abs_of_nonneg (by linarith [(conePotential_bounds ν x).1])]; exact (conePotential_bounds ν x).2)
    (conePotential_coord_bound hν)
    (fun x => (conePotential_bounds ν x).2) hf H hh
  have hbν : inner ℝ (b : Space n) ν = 0 := by
    rw [real_inner_comm]
    exact b.property
  have hνν : inner ℝ ν ν = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
  let F := fun y : ℝ => f ((Real.sqrt 2*y) • ν)
  have hFs : ContDiff ℝ ∞ F := hf.1.1.comp ((contDiff_const.mul contDiff_id).smul contDiff_const)
  have hp := positiveLinearCone_pos (fun x => (conePotential_bounds ν x).2) hf.1
  have hrep (x) : f x = Real.exp (inner ℝ (b : Space n) x)*F (inner ℝ ν x/Real.sqrt 2) := by
    let t : H := ⟨x-(inner ℝ ν x) • ν, by
      change inner ℝ ν (x-(inner ℝ ν x) • ν) = 0
      rw [inner_sub_right, real_inner_smul_right, hνν]; ring⟩
    have H := hb t ((inner ℝ ν x) • ν)
    have ht : (t : Space n) + (inner ℝ ν x) • ν = x := sub_add_cancel x _
    rw [ht] at H
    have hib : inner ℝ b t = inner ℝ (b : Space n) x := by
      change inner ℝ (b : Space n) (x-(inner ℝ ν x) • ν) = _
      rw [inner_sub_right, real_inner_smul_right, hbν, mul_zero, sub_zero]
    rw [hib] at H
    dsimp [F]
    have hc : Real.sqrt 2 * (inner ℝ ν x/Real.sqrt 2) = inner ℝ ν x := by
      field_simp
    rw [hc]
    exact H
  refine ⟨b, F, hbν, hFs, fun y => hp _, ?_, hrep, ?_⟩
  · simpa only [F, mul_zero, zero_smul] using hf.1.2.2.2
  · intro y
    let c := (Real.sqrt 2)⁻¹ • ν
    let x := (Real.sqrt 2*y) • ν
    have hF2 : ContDiff ℝ 2 F := hFs.of_le (WithTop.coe_le_coe.mpr le_top)
    have hhrep : f = fun z => Real.exp (inner ℝ (b : Space n) z)*F (inner ℝ c z) := by
      funext z
      rw [hrep]
      dsimp [c]
      rw [real_inner_smul_left, div_eq_inv_mul]
    have hic : inner ℝ c x = y := by
      dsimp [c, x]
      rw [real_inner_smul_left, real_inner_smul_right, hνν]
      field_simp
    have hνx : inner ℝ ν x / Real.sqrt 2 = y := by
      dsimp [x]
      rw [real_inner_smul_right, hνν]
      field_simp
    have hbc : inner ℝ (b : Space n) c = 0 := by dsimp [c]; rw [real_inner_smul_right, hbν, mul_zero]
    have hbx : inner ℝ (b : Space n) x = 0 := by dsimp [x]; rw [real_inner_smul_right, hbν, mul_zero]
    have hcn : ‖c‖^2 = 1/2 := by
      dsimp [c]
      rw [norm_smul, hν, mul_one, Real.norm_eq_abs, sq_abs, inv_pow]
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    have He := hf.1.2.2.1 x
    rw [hhrep, laplacian_separated hF2, hic, hbc, hbx, hcn, Real.exp_zero] at He
    change 1 * (deriv (deriv F) y * (1/2) + 2*deriv F y*0 + F y*‖(b : Space n)‖^2) =
      conePotential ν x * (Real.exp (inner ℝ (b : Space n) x)*F (inner ℝ c x)) at He
    rw [hbx, hic, Real.exp_zero] at He
    dsimp [conePotential] at He
    rw [hνx] at He
    nlinarith [congrArg (fun t => t * F y) (sech_sq_tanh y)]

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open scoped ContDiff Polynomial

lemma coordinate_derivative_polynomial {n : ℕ} {v : Space n → ℝ}
    (hv : Differentiable ℝ v) (p : Polynomial ℝ) (i : Fin n) (x : Space n) :
    coordDeriv (fun y => p.eval (v y)) i x = p.derivative.eval (v x)*coordDeriv v i x := by
  have H := (p.hasDerivAt (v x)).comp_hasFDerivAt x (hv x).hasFDerivAt
  simp only [Function.comp_def] at H
  simp only [coordDeriv, H.fderiv, smul_apply, smul_eq_mul]

lemma polynomial_coordinate_jets {n : ℕ} {v : Space n → ℝ}
    (hv : Differentiable ℝ v) (c : Fin n → ℝ)
    (hd : ∀ i x, coordDeriv v i x = c i*(1-v x^2)) (p : Polynomial ℝ)
    (l : List (Fin n)) : ∃ q : Polynomial ℝ, ∀ x, coordinateJet (fun y => p.eval (v y)) l x = q.eval (v x) := by
  induction l with
  | nil => exact ⟨p, fun _ => rfl⟩
  | cons i l ih =>
    obtain ⟨q,hq⟩ := ih
    refine ⟨q.derivative*(Polynomial.C (c i)*(1-Polynomial.X^2)), ?_⟩
    intro x
    have he := funext hq
    change coordDeriv (coordinateJet (fun y => p.eval (v y)) l) i x = _
    rw [he, coordinate_derivative_polynomial hv, hd]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]

lemma polynomial_coordinate_jets_bounded {n : ℕ} {v : Space n → ℝ}
    (hv : Differentiable ℝ v) (hb : ∀ x, |v x| ≤ 1) (c : Fin n → ℝ)
    (hd : ∀ i x, coordDeriv v i x = c i*(1-v x^2)) (p : Polynomial ℝ)
    (l : List (Fin n)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |coordinateJet (fun y => p.eval (v y)) l x| ≤ C := by
  obtain ⟨q,hq⟩ := polynomial_coordinate_jets hv c hd p l
  obtain ⟨z,hz,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (-1:ℝ) 1).Nonempty from ⟨0, by norm_num⟩) q.continuous.abs.continuousOn
  refine ⟨|q.eval z|, abs_nonneg _, ?_⟩
  intro x
  rw [hq]
  exact hmax (abs_le.mp (hb x))

lemma conePotential_jets_bounded {n : ℕ} (ν : Space n) (l : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet (conePotential ν) l x| ≤ C := by
  let v := fun x : Space n => Real.tanh (inner ℝ ν x/Real.sqrt 2)
  have hv : ContDiff ℝ ∞ v := contDiff_tanh.comp ((innerSL ℝ ν).contDiff.div_const _)
  have hd (i : Fin n) (x : Space n) : coordDeriv v i x =
      (inner ℝ ν (basis n i)/Real.sqrt 2)*(1-v x^2) := by
    have hI : HasFDerivAt (fun z : Space n => inner ℝ ν z/Real.sqrt 2)
        ((Real.sqrt 2)⁻¹ • innerSL ℝ ν) x := by
      simpa only [div_eq_inv_mul, innerSL_apply_apply] using
        ((innerSL ℝ ν).hasFDerivAt (x := x)).const_mul ((Real.sqrt 2)⁻¹)
    have H := (tanh_hasDerivAt (inner ℝ ν x/Real.sqrt 2)).comp_hasFDerivAt x hI
    have ht : sech (inner ℝ ν x/Real.sqrt 2)^2 = 1-v x^2 := by
      dsimp [v]; linarith [sech_sq_tanh (inner ℝ ν x/Real.sqrt 2)]
    change fderiv ℝ v x (basis n i) = _
    simp only [Function.comp_def] at H
    rw [H.fderiv]
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, ht]
    ring
  have HH := polynomial_coordinate_jets_bounded (hv.differentiable (by simp))
    (fun x => (Real.abs_tanh_lt_one (inner ℝ ν x/Real.sqrt 2)).le)
    (fun i => inner ℝ ν (basis n i)/Real.sqrt 2) hd (1+Polynomial.X^2) l
  have he : (fun y => (1+Polynomial.X^2 : Polynomial ℝ).eval (v y)) = conePotential ν := by
    funext y
    simp [conePotential, v]
  rwa [he] at HH

lemma conePotential_relative_jets {n : ℕ} {ν : Space n} (hν : ‖ν‖=1)
    (l : List (Fin n)) : ∃ M : ℝ, 0 ≤ M ∧ ∀ f ∈ positiveLinearCone (conePotential ν),
      ∀ x, |coordinateJet f l x| ≤ M*f x := by
  apply positiveLinearCone_relative_jets (conePotential_smooth ν) (by norm_num : (0:ℝ) ≤ 2)
    (fun x => by rw [abs_of_nonneg (by linarith [(conePotential_bounds ν x).1] : 0 ≤ conePotential ν x)]; exact (conePotential_bounds ν x).2)
    (conePotential_coord_bound hν) (fun x => (conePotential_bounds ν x).2)
    (conePotential_jets_bounded ν) l

end DeGiorgi
end

end OAI
