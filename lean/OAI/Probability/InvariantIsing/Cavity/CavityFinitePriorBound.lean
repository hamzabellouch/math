import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCovariancePath
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCovarianceBound

namespace OAI

/-! The total ordinary covariance of the finite labeled cavity prior is
bounded independently of the number of levels. -/

noncomputable section
open MeasureTheory Set IsingPerceptron
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

variable {m d n : ℕ}

lemma cavityFiniteCovariance_eq_scalar_diagonal
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) {x : ℝ} (hx : 0 < x) :
    cavityFiniteCovariance ρ eig hρ hsum g x =
      Matrix.diagonal (fun j => cavityScalarResolvent ρ eig hρ hsum (eig (g j)) x) := by
  rw [cavityFiniteCovariance_diagonal ρ eig hρ hsum g hx]
  congr 1
  funext j
  exact (cavityScalarResolvent_pos_eq ρ eig hρ hsum (g j) le_rfl hx).symm

lemma cavityFiniteCovariance_root_eq_diagonal
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) {x : ℝ} (hx : 0 < x) :
    (1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hsum x)) •
      (cavityFiniteCovariance ρ eig hρ hsum g x *
        cavityFiniteCovariance ρ eig hρ hsum g x) =
    Matrix.diagonal (fun j => 1 /
      (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hsum x) *
        (finiteInverse ρ eig hρ hsum x - eig (g j))^2)) := by
  rw [cavityFiniteCovariance_diagonal ρ eig hρ hsum g hx, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_smul]
  congr 1
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, one_div, pow_two, mul_inv]

theorem cavity_finite_prior_covariance_bound
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) :
    ‖(cavityFiniteRootCovariance ρ eig hρ hsum g p q +
      ∑ i : Fin n, cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q i) +
      cavityFiniteCovariancePath ρ eig hρ hsum g p q n‖ ≤ ∑ a, (ρ a)⁻¹ := by
  let T := fun x => Matrix.diagonal
    (fun j : Fin d => cavityScalarResolvent ρ eig hρ hsum (eig (g j)) x)
  let x := fun i : Fin (n + 1) => deficit p (q i)
  let G := Matrix.diagonal (fun j : Fin d => 1 /
    (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hsum (x 0)) *
      (finiteInverse ρ eig hρ hsum (x 0) - eig (g j))^2))
  let C := ∑ a, (ρ a)⁻¹
  have hC (a : Fin m) : (ρ a)⁻¹ ≤ C :=
    Finset.single_le_sum (fun i _ => inv_nonneg.mpr (hρ i).le) (Finset.mem_univ a)
  have hCn : 0 ≤ C := Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hρ i).le)
  have hx (i : Fin (n + 1)) : 0 < x i :=
    finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
      (hq.monotone (Fin.le_last i))
  have hT0 : T 0 = 0 := by simp [T, cavityScalarResolvent]
  have hT : ∀ u v, 0 ≤ u → u ≤ v → ‖T v - T u‖ ≤ C * (v - u) := by
    intro u v hu huv
    rw [show T v - T u = Matrix.diagonal
      (fun j => cavityScalarResolvent ρ eig hρ hsum (eig (g j)) v -
        cavityScalarResolvent ρ eig hρ hsum (eig (g j)) u) from
        Matrix.diagonal_sub _ _, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hCn (sub_nonneg.mpr huv))).mpr
    intro j
    exact (cavityScalarResolvent_lipschitz ρ eig hρ hsum (g j) le_rfl hu huv).trans
      (mul_le_mul_of_nonneg_right (hC (g j)) (sub_nonneg.mpr huv))
  have hG : ‖G‖ ≤ C := by
    rw [show G = Matrix.diagonal _ from rfl, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hCn).mpr
    intro j
    have h := cavityScalarResolvent_derivative_bound ρ eig hρ hsum (g j) le_rfl (hx 0)
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.trans (hC (g j))
  have hb (i : Fin n) : 0 < cut i.succ.castSucc := by
    rw [← hfirst]
    exact hcut (by change 0 < i.val + 1; omega)
  have hgap (i : Fin n) : x i.castSucc - x i.succ =
      cut i.succ.castSucc * (q i.succ - q i.castSucc) := by
    have h := finite_overlap_deficit_increment p cut hcut hfirst hlast q hq hp i
      (r := q i.succ) ⟨hq.monotone (Fin.castSucc_le_succ i), le_rfl⟩
    dsimp only [x]
    linarith
  have hlastx : x (Fin.last n) = 1 - q (Fin.last n) :=
    deficit_eq_one_sub_of_ae_le p
      ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.2))
  have bound := cavity_covariance_partition_bound T G q x
    (fun i => cut i.succ.castSucc) hT0 hT hG hq.monotone
    (finite_overlap_value_mem_unit p cut hcut q hp 0).1 (fun i => (hx i).le) hb hgap hlastx
  have hpath (i : ℕ) : cavityFiniteCovariancePath ρ eig hρ hsum g p q i =
      T (x (cavityFiniteLevel n i)) :=
    cavityFiniteCovariance_eq_scalar_diagonal ρ eig hρ hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i)
  have hroot : cavityFiniteRootCovariance ρ eig hρ hsum g p q = q 0 • G := by
    dsimp only [cavityFiniteRootCovariance, cavityFiniteCovariancePath]
    rw [show cavityFiniteDeficitPath p q 0 = x 0 by simp [cavityFiniteDeficitPath, x]]
    rw [cavityFiniteCovariance_root_eq_diagonal ρ eig hρ hsum g (hx 0)]
  have he (i : Fin n) : cut ⟨i.val + 1, by omega⟩ = cut i.succ.castSucc :=
    congrArg cut (Fin.ext rfl)
  rw [hroot]
  simpa only [cavityFiniteNoiseCovariance, hpath, cavityFiniteLevel_castSucc,
    cavityFiniteLevel_succ, cavityFiniteLevel_last, chainExponent_apply cut,
    Fin.isLt, he] using bound

end InvariantIsing

end

end OAI
