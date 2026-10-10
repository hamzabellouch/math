import Mathlib
import OAI.Algebra.AlgebraicObstruction.AlgebraicInput
import OAI.Algebra.MarkedTensor.Holonomy

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.Holonomy

variable {R : Type*} [CommRing R]

lemma triple_mem_cube (I : Ideal R) {x y z : R}
    (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I) : x * y * z ∈ I ^ 3 := by
  have h : x * y * z ∈ (I * I) * I := Ideal.mul_mem_mul (Ideal.mul_mem_mul hx hy) hz
  simpa only [pow_succ, pow_zero, one_mul] using h

lemma cube_iSup_le_of_le_deviation {T E : Type*}
    (z : E → Matrix.SpecialLinearGroup (Fin 2) R)
    (W : T → Ideal R) (hW : ∀ t, W t ≤ deviationIdeal z)
    (r : Ideal R) (hc : deviationIdeal z ^ 3 ≤ r) : (⨆ t, W t) ^ 3 ≤ r := by
  exact (pow_le_pow_left' (iSup_le hW) 3).trans hc

lemma pow_sup_defect_le (I r : Ideal R) (q : ℕ) (h : I ^ q ≤ r) :
    (I ⊔ r) ^ q ≤ r := by
  let f : R →+* R ⧸ r := Ideal.Quotient.mk r
  have hf : RingHom.ker f = r := Ideal.mk_ker
  have hr : r.map f = ⊥ := (Ideal.map_eq_bot_iff_le_ker f).mpr (by rw [hf])
  have hI : (I ^ q).map f = ⊥ := (Ideal.map_eq_bot_iff_le_ker f).mpr (by rwa [hf])
  have hmap : ((I ⊔ r) ^ q).map f = ⊥ := by
    rw [Ideal.map_pow, Ideal.map_sup, hr, sup_bot_eq, ← Ideal.map_pow, hI]
  simpa only [hf] using ((Ideal.map_eq_bot_iff_le_ker f).mp hmap)

end BoundaryOnly.Holonomy

namespace BoundaryOnly.FormalObstruction.CoefficientRing

open MvPowerSeries FormalCorrection AlgebraicReplacement BoundaryOnly.Holonomy
open scoped Classical commutatorElement

variable {K : Type} [Field K]
variable {d : ℕ} {n : Fin d → ℕ}

lemma origin_eq_maximal {σ : Type} [Fintype σ] :
    originIdeal K σ = IsLocalRing.maximalIdeal (MvPowerSeries σ K) := by
  ext f
  rw [show originIdeal K σ = BoundaryOnly.FormalObstruction.originIdeal K σ from rfl, mem_origin_iff]
  change constantCoeff f = 0 ↔ ¬ IsUnit f
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

lemma gradientIdeal_le_origin
    (P : (i : Fin d) → MvPowerSeries (WallVar n i) K)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) K)
    (hP : ∀ i, P i ∈ (originIdeal K (WallVar n i)) ^ 3)
    (hY : ∀ c, Y c ∈ originIdeal K (GraphVar n)) :
    gradientIdeal n P Y ≤ originIdeal K (GraphVar n) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨c, rfl⟩
  apply mem_origin_iff.mpr
  have h := gradientValue_vanishes (potential n P) (potential_vanishes P hP)
    (graphCoordinates n Y) (graphCoordinates_centered Y hY) c
  exact Vanishes.one_iff.mp (h.mono (by decide : 1 ≤ 2))

variable [CharZero K] [IsAlgClosed K]

theorem no_holonomy_algebraic_input (hd : 5 ≤ d)
    (P : (i : Fin d) → MvPowerSeries (WallVar n i) K)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) K)
    (hP : ∀ i, P i ∈ (originIdeal K (WallVar n i)) ^ 3)
    (hY : ∀ c, Y c ∈ originIdeal K (GraphVar n))
    (hcomp : IsUnit (complementaryMatrix n Y).det)
    (hsquare : subst (graphCoordinates n Y) (potential n P) ∈ (gradientIdeal n P Y) ^ 2)
    (A : (i : Fin d) → AffineEtaleChart K (WallVar n i))
    (L : (i : Fin d) → Ideal (A i).LocalRing)
    (hL : ∀ i, L i ≤ IsLocalRing.maximalIdeal (A i).LocalRing)
    (hgradient : ∀ i w, pderiv (R := K) w (P i) ∈ (L i).map (A i).localExpansion.toRingHom)
    (hjets : ∀ i w, ∀ q : ℕ, 1 ≤ q → ∃ a : (A i).LocalRing,
      pderiv (R := K) w (P i) - (A i).localExpansion a ∈
        ((L i).map (A i).localExpansion.toRingHom) ^ q)
    (hYalg : ∀ c, Nonempty (LocalEtaleExpansion (Y c)))
    (z : Bool × Fin d → Matrix.SpecialLinearGroup (Fin 2) (MvPowerSeries (GraphVar n) K))
    (u : shortWords → Matrix.SpecialLinearGroup (Fin 2) (MvPowerSeries (GraphVar n) K))
    (hz : ∀ e, mat (z e) - 1 ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (GraphVar n) K)).matrix (Fin 2))
    (hu : ∀ c, mat (u c) - mat (referenceOver (MvPowerSeries (GraphVar n) K) c) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (GraphVar n) K)).matrix (Fin 2))
    (hrel : ∀ e f g a b c,
      mat ⁅u a * z e * (u a)⁻¹, ⁅u b * z f * (u b)⁻¹, u c * z g * (u c)⁻¹⁆⁆ - 1 ∈
        (gradientIdeal n P Y).matrix (Fin 2))
    (hwall : ∀ b i, Ideal.map (wallEval Y hY b i)
      ((L i).map (A i).localExpansion.toRingHom) ≤ deviationIdeal z ⊔ gradientIdeal n P Y)
    (hpositive : ∀ i, slope n i ∈ deviationIdeal z ⊔ gradientIdeal n P Y)
    (hnegative : ∀ i, negativeSlopeValue n P Y i ∈
      deviationIdeal z ⊔ gradientIdeal n P Y) : False := by
  have hr : gradientIdeal n P Y ≤
      IsLocalRing.maximalIdeal (MvPowerSeries (GraphVar n) K) := by
    rw [← origin_eq_maximal]
    exact gradientIdeal_le_origin P Y hP hY
  have hc₀ : deviationIdeal z ^ 3 ≤ gradientIdeal n P Y :=
    cubic_nilpotence_mod_ideal _ hr z u hz hu hrel
  have hc : (deviationIdeal z ⊔ gradientIdeal n P Y) ^ 3 ≤ gradientIdeal n P Y :=
    pow_sup_defect_le _ _ 3 hc₀
  have hn : deviationIdeal z ≤ originIdeal K (GraphVar n) := by
    rw [origin_eq_maximal]
    apply Ideal.span_le.mpr
    rintro x ⟨⟨e, i, j⟩, rfl⟩
    exact hz e i j
  have hnr : deviationIdeal z ⊔ gradientIdeal n P Y ≤ originIdeal K (GraphVar n) :=
    sup_le hn (gradientIdeal_le_origin P Y hP hY)
  let Q : QuadraticData (R := K) (n := n) := {
    P := P
    Y := Y
    order_three := hP
    centered := hY
    complementary := hcomp
    graph_square := hsquare
    positive_cubic := fun i j l => hc
      (triple_mem_cube _ (hpositive i) (hpositive j) (hpositive l))
    negative_cubic := fun i j l => hc
      (triple_mem_cube _ (hnegative i) (hnegative j) (hnegative l)) }
  exact no_algebraic_input hd Q A L hL hgradient hjets
    (fun b i => (hwall b i).trans hnr)
    (fun b i => (pow_le_pow_left' (hwall b i) 3).trans hc) hYalg

end BoundaryOnly.FormalObstruction.CoefficientRing

end

end OAI
