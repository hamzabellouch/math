import OAI.Probability.InvariantIsing.Cavity.CavityValueIdentity
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteNormalizer
import OAI.Probability.InvariantIsing.Cavity.CavityScalarRoot

namespace OAI

/-! The scalar-spin and quadratic parts of the finite cavity calculation
combine to the variational trial value, with the residual Gaussian
integrated as an ordinary expectation. -/

noncomputable section
open MeasureTheory Set IsingPerceptron
open scoped Matrix BigOperators Topology

namespace InvariantIsing

theorem cavity_finite_spin_quadratic_value {m d N l : ℕ} (hN : 0 < N)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (s : Fin m → ℕ) (hs : ∀ a, s a ≤ N)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = N - s a)
    (hsrho : ∀ a, (s a : ℝ) = (N : ℝ) * rho a)
    (p : OverlapPath) (cut : Fin (l + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (l + 1)) = 1)
    (q : Fin (l + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j r, r ∈ Ioo (cut j.castSucc) (cut j.succ) → p r = q j)
    (htop : q (Fin.last l) < 1) (U : Rotation N) :
    let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B - A₀
    let H := fun j => (finiteInverse rho lam hrho hsum (deficit p (q j)) •
      (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹
    let S₀ := q 0 • ((1 / finiteSecondResolvent rho lam
      (finiteInverse rho lam hrho hsum (deficit p (q 0)))) • (H 0 * H 0))
    let Δ := (cavityFieldDiagonal rho lam hrho hsum p - h.height (Fin.last h.depth)).toNNReal
    (N : ℝ)⁻¹ * (cavityScalarCascadeMean N h.depth (chainExponent h.cut)
        (fieldCascadeVariance h) (NNReal.mk (h.height 0) (h.nonneg 0)) Δ
        (finiteR rho lam hrho hsum 0) + cavityFiniteQuadraticMean K H S₀ cut) =
      fieldValue h 0 + fieldPairing p h / 2 + spectralFunctional (finiteR rho lam hrho hsum) p := by
  dsimp only
  let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
  let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
  let A₀ := Matrix.diagonal (fun i => lam (g i))
  let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B - A₀
  let H := fun j => (finiteInverse rho lam hrho hsum (deficit p (q j)) •
    (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹
  let S₀ := q 0 • ((1 / finiteSecondResolvent rho lam
    (finiteInverse rho lam hrho hsum (deficit p (q 0)))) • (H 0 * H 0))
  have hd : h.height (Fin.last h.depth) ≤ cavityFieldDiagonal rho lam hrho hsum p :=
    cavityFieldPrimitive_mono rho lam hrho hsum p (hq0 _) htop.le
  have hspin := cavityScalarCascadeMean_diagonal N hN h
    (cavityFieldDiagonal rho lam hrho hsum p) hd (finiteR rho lam hrho hsum 0) U
  have hquad := cavity_finite_quadratic_mean rho lam hrho hsum B hB hBE hcomplete
    g s hs hcounts hsrho p cut hcut hfirst hlast q hq hp htop
  change cavityFiniteQuadraticMean K H S₀ cut = _ at hquad
  have hvalue := cavity_finite_value_identity rho lam hrho hsum p cut hcut hfirst hlast
    q hq.monotone hq0 hp
  change fieldValue h 0 + _ = _ at hvalue
  have hΔ : NNReal.mk (cavityFieldDiagonal rho lam hrho hsum p - h.height (Fin.last h.depth))
      (sub_nonneg.mpr hd) =
      (cavityFieldDiagonal rho lam hrho hsum p - h.height (Fin.last h.depth)).toNNReal := by
    exact Subtype.ext (Real.coe_toNNReal _ (sub_nonneg.mpr hd)).symm
  rw [hΔ] at hspin
  change (N : ℝ)⁻¹ * (_ + cavityFiniteQuadraticMean K H S₀ cut) =
    fieldValue h 0 + fieldPairing p h / 2 + spectralFunctional (finiteR rho lam hrho hsum) p
  rw [mul_add, hspin, hquad]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he (z : ℝ) : (N : ℝ)⁻¹ * (-((N : ℝ) / 2) * z) = -z / 2 := by
    field_simp
  rw [he]
  linarith [hvalue]

end InvariantIsing

end

end OAI
