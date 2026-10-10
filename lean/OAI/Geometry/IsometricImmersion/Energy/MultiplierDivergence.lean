import OAI.Geometry.IsometricImmersion.Energy.WeightedMultiplier

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def multiplierOperator (A B C u : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 (coordPartial 0 u) p + A p * coordPartial 1 (coordPartial 1 u) p +
    B p * coordPartial 0 u p + C p * coordPartial 1 u p

def multiplierTest (m n u : Coord → ℝ) (p : Coord) : ℝ :=
  m p * coordPartial 1 u p + n p * coordPartial 0 u p

def multiplierFluxT (A m n u : Coord → ℝ) (p : Coord) : ℝ :=
  m p * coordPartial 0 u p * coordPartial 1 u p +
    (1 / 2 : ℝ) * (n p * (coordPartial 0 u p) ^ 2) -
    (1 / 2 : ℝ) * (A p * n p * (coordPartial 1 u p) ^ 2)

def multiplierFluxS (A m n u : Coord → ℝ) (p : Coord) : ℝ :=
  (1 / 2 : ℝ) * (A p * m p * (coordPartial 1 u p) ^ 2) +
    A p * n p * coordPartial 0 u p * coordPartial 1 u p -
    (1 / 2 : ℝ) * (m p * (coordPartial 0 u p) ^ 2)

variable {A B C m n u : Coord → ℝ} {p : Coord} {U : Set Coord}

theorem multiplierFluxT_partial_t
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hn : DifferentiableAt ℝ n p)
    (hut : DifferentiableAt ℝ (coordPartial 0 u) p)
    (hus : DifferentiableAt ℝ (coordPartial 1 u) p) :
    coordPartial 0 (multiplierFluxT A m n u) p =
      coordPartial 0 m p * coordPartial 0 u p * coordPartial 1 u p +
      m p * coordPartial 0 (coordPartial 0 u) p * coordPartial 1 u p +
      m p * coordPartial 0 u p * coordPartial 0 (coordPartial 1 u) p +
      (coordPartial 0 n p * (coordPartial 0 u p) ^ 2 +
        2 * n p * coordPartial 0 u p * coordPartial 0 (coordPartial 0 u) p) / 2 -
      ((coordPartial 0 A p * n p + A p * coordPartial 0 n p) * (coordPartial 1 u p) ^ 2 +
        2 * A p * n p * coordPartial 1 u p * coordPartial 0 (coordPartial 1 u) p) / 2 := by
  have hd := (((hm.hasFDerivAt.fun_mul hut.hasFDerivAt).fun_mul hus.hasFDerivAt).add
    ((hn.hasFDerivAt.fun_mul (hut.hasFDerivAt.fun_mul hut.hasFDerivAt)).const_mul
      (1 / 2 : ℝ))).sub
    (((hA.hasFDerivAt.fun_mul hn.hasFDerivAt).fun_mul
      (hus.hasFDerivAt.fun_mul hus.hasFDerivAt)).const_mul (1 / 2 : ℝ))
  simp only [Pi.add_def, Pi.sub_def, coordPartial] at hd
  unfold multiplierFluxT
  simp only [pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

theorem multiplierFluxS_partial_s
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hn : DifferentiableAt ℝ n p)
    (hut : DifferentiableAt ℝ (coordPartial 0 u) p)
    (hus : DifferentiableAt ℝ (coordPartial 1 u) p) :
    coordPartial 1 (multiplierFluxS A m n u) p =
      ((coordPartial 1 A p * m p + A p * coordPartial 1 m p) * (coordPartial 1 u p) ^ 2 +
        2 * A p * m p * coordPartial 1 u p * coordPartial 1 (coordPartial 1 u) p) / 2 +
      (coordPartial 1 A p * n p + A p * coordPartial 1 n p) *
        coordPartial 0 u p * coordPartial 1 u p +
      A p * n p * coordPartial 1 (coordPartial 0 u) p * coordPartial 1 u p +
      A p * n p * coordPartial 0 u p * coordPartial 1 (coordPartial 1 u) p -
      (coordPartial 1 m p * (coordPartial 0 u p) ^ 2 +
        2 * m p * coordPartial 0 u p * coordPartial 1 (coordPartial 0 u) p) / 2 := by
  have hd := ((((hA.hasFDerivAt.fun_mul hm.hasFDerivAt).fun_mul
    (hus.hasFDerivAt.fun_mul hus.hasFDerivAt)).const_mul (1 / 2 : ℝ)).add
    (((hA.hasFDerivAt.fun_mul hn.hasFDerivAt).fun_mul hut.hasFDerivAt).fun_mul
      hus.hasFDerivAt)).sub
    ((hm.hasFDerivAt.fun_mul (hut.hasFDerivAt.fun_mul hut.hasFDerivAt)).const_mul
      (1 / 2 : ℝ))
  simp only [Pi.add_def, Pi.sub_def, coordPartial] at hd
  unfold multiplierFluxS
  simp only [pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

theorem multiplier_divergence_identity
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hn : DifferentiableAt ℝ n p) (hu : ContDiffOn ℝ ∞ u U)
    (hU : IsOpen U) (hp : p ∈ U) :
    multiplierOperator A B C u p * multiplierTest m n u p =
      coordPartial 0 (multiplierFluxT A m n u) p +
      coordPartial 1 (multiplierFluxS A m n u) p +
      multiplierT B m n p * (coordPartial 0 u p) ^ 2 +
      multiplierS A C m n p * (coordPartial 1 u p) ^ 2 +
      multiplierJ A B C m n p * coordPartial 0 u p * coordPartial 1 u p := by
  have hdu (i : Fin 2) : DifferentiableAt ℝ (coordPartial i u) p :=
    (((partial_contDiffOn hu hU i) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  rw [multiplierFluxT_partial_t hA hm hn (hdu 0) (hdu 1),
    multiplierFluxS_partial_s hA hm hn (hdu 0) (hdu 1)]
  unfold multiplierOperator multiplierTest multiplierT multiplierS multiplierJ
  rw [HessianCalculus.coordPartial_mul_at hA hm 1,
    HessianCalculus.coordPartial_mul_at hA hn 0,
    HessianCalculus.coordPartial_mul_at hA hn 1,
    coordPartial_comm hu hU hp 0 1]
  ring

theorem directed_test_factor
    (b lambda epsilon : ℝ) (I u : Coord → ℝ) (p : Coord) :
    multiplierTest (directedM b lambda I) (directedN b lambda epsilon I) u p =
      directedWeight b lambda I p *
        (-coordPartial 1 u p + epsilon * p 0 * coordPartial 0 u p) := by
  unfold multiplierTest directedM directedN
  ring

theorem directed_flux_factor
    (A u I : Coord → ℝ) (b lambda epsilon : ℝ) (p : Coord) :
    multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p =
      directedWeight b lambda I p *
        (-coordPartial 0 u p * coordPartial 1 u p +
          epsilon * p 0 * (coordPartial 0 u p) ^ 2 / 2 -
          epsilon * p 0 * A p * (coordPartial 1 u p) ^ 2 / 2) ∧
    multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p =
      directedWeight b lambda I p *
        (-A p * (coordPartial 1 u p) ^ 2 / 2 +
          epsilon * p 0 * A p * coordPartial 0 u p * coordPartial 1 u p +
          (coordPartial 0 u p) ^ 2 / 2) := by
  constructor <;> simp only [multiplierFluxT, multiplierFluxS, directedM, directedN] <;> ring

theorem directed_flux_edge_zero
    (A u I : Coord → ℝ) (b lambda epsilon : ℝ) (p : Coord) (hp : p 1 = b) :
    multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p = 0 ∧
    multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p = 0 := by
  obtain ⟨ht, hs⟩ := directed_flux_factor A u I b lambda epsilon p
  rw [directedWeight_edge_zero b lambda I p hp, zero_mul] at ht hs
  exact ⟨ht, hs⟩

end SmoothLocal.Weighted

end

end OAI
