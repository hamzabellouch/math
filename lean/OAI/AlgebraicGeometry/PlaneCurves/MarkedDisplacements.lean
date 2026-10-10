import OAI.AlgebraicGeometry.PlaneCurves.ThetaSections

namespace OAI

/-!
# Nonintegral displacements in global and marked theta products; Assembly of marked smooth cubic configurations; Distinct torus configurations at a fixed period
-/

section

/-!
# Actual marked theta product and the nine-zero/q-Pi displacement list
-/
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05
open Nagata.W21
open scoped BigOperators

/-- The actual finite product of the nine actual infinite theta products. -/
def markedPi (τ : ℝ) (xi : Fin 9 → ℝ) (z : ℂ) : ℂ :=
  markedThetaProduct (τ : ℂ) (fun i => (rayPoint τ (xi i) : ℂ)) z

/-- Literal unit-valued multiplier of the degree-nine marked theta product. -/
def piMultiplier (τ : ℝ) (xi : Fin 9 → ℝ) : ℂˣ := ∏ i, -(rayPoint τ (xi i))

@[simp] theorem piMultiplier_coe (τ : ℝ) (xi : Fin 9 → ℝ) :
    (piMultiplier τ xi : ℂ) = ∏ i, -(rayPoint τ (xi i) : ℂ) := by
  simp [piMultiplier]

theorem complexPeriod_norm_lt_one {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) : ‖(τ : ℂ)‖ < 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτ1

theorem positivePeriod_free {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (k : ℤ)
    (hk : positivePeriod τ hτ ^ k = 1) : k = 0 := by
  apply Nagata.W08.unitPeriod_free (positivePeriod τ hτ) _ k hk
  exact complexPeriod_norm_lt_one hτ hτ1

/-- The scalar product is exactly the already-proved genuine holomorphic section on the cover. -/
theorem markedPi_eq_markedThetaSection {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (xi : Fin 9 → ℝ) (z : ℂˣ) :
    markedPi τ xi (z : ℂ) =
      (Nagata.W08.markedThetaSection (complexPeriod_norm_lt_one hτ hτ1)
        (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
        (fun i => (rayPoint τ (xi i) : ℂ)) (fun _ => Units.ne_zero _)).val (z : ℂ) := by
  exact (Nagata.W08.markedThetaSection_apply (complexPeriod_norm_lt_one hτ hτ1)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    (fun i => (rayPoint τ (xi i) : ℂ)) (fun _ => Units.ne_zero _) z.ne_zero).symm

theorem markedPi_zero_fixed {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (xi : Fin 9 → ℝ) (i : Fin 9) : markedPi τ xi (rayPoint τ (xi i) : ℂ) = 0 := by
  apply (markedThetaProduct_eq_zero_iff (complexPeriod_norm_lt_one hτ hτ1)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    (fun i : Fin 9 => (rayPoint τ (xi i)).ne_zero) (rayPoint τ (xi i)).ne_zero).mpr
  exact ⟨i, 0, by simp⟩

/-- Noncollision with the nine quotient points implies nonvanishing of the actual Pi. -/
theorem markedPi_ne_zero_of_torus_avoidance {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (xi : Fin 9 → ℝ) (z : ℂˣ)
    (havoid : ∀ i, torusPointMk (positivePeriod τ hτ) z ≠
      torusPointMk (positivePeriod τ hτ) (rayPoint τ (xi i))) :
    markedPi τ xi (z : ℂ) ≠ 0 := by
  intro hz
  obtain ⟨i, k, hk⟩ := (markedThetaProduct_eq_zero_iff (complexPeriod_norm_lt_one hτ hτ1)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    (fun i : Fin 9 => (rayPoint τ (xi i)).ne_zero) z.ne_zero).mp hz
  apply havoid i
  apply Eq.symm
  apply Quotient.sound
  apply (torusOrbitSetoid_iff_coe (positivePeriod τ hτ) (rayPoint τ (xi i)) z).mpr
  exact ⟨k, by simpa only [positivePeriod, Units.val_mk0, mul_comm] using hk⟩

theorem moving_avoids_fixed_of_tuple_injective {τ : ℝ} (hτ : 0 < τ)
    (x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ)) (i : Fin 9) (j : Fin q) :
    torusChart τ hτ x0 (ξ j) ≠ torusPointMk (positivePeriod τ hτ) (rayPoint τ (xi i)) := by
  intro h
  have hi : (finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)) (Sum.inr j) =
      finSumFinEquiv (Sum.inl i) := by
    apply hinj
    rw [torusTuple_right, torusTuple_left]
    exact h
  have hs := (finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).injective hi
  cases hs

theorem markedPi_ne_zero_moving {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ)) (j : Fin q) :
    markedPi τ xi (chartPoint τ x0 (ξ j) : ℂ) ≠ 0 :=
  markedPi_ne_zero_of_torus_avoidance hτ hτ1 xi (chartPoint τ x0 (ξ j))
    (fun i => moving_avoids_fixed_of_tuple_injective hτ x0 xi ξ hinj i j)

/-- The literal finite source displacement scalars: nine zeros, followed by Pi(z_j). -/
def displacementScalar (τ x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) :
    Fin (9 + q) → ℂ :=
  fun t => Sum.elim (fun _ : Fin 9 => 0)
    (fun j : Fin q => markedPi τ xi (chartPoint τ x0 (ξ j) : ℂ))
    ((finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).symm t)

@[simp] theorem displacementScalar_left (τ x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin 9) :
    displacementScalar τ x0 xi ξ (finSumFinEquiv (Sum.inl i)) = 0 := by
  simp [displacementScalar]

@[simp] theorem displacementScalar_right (τ x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin q) :
    displacementScalar τ x0 xi ξ (finSumFinEquiv (Sum.inr i)) =
      markedPi τ xi (chartPoint τ x0 (ξ i) : ℂ) := by
  simp [displacementScalar]

/-- The displacement at each actual tuple point, in the actual normal multiplier fibre D(9,L³).
L is the degree-three multiplier; the cubic/normal-bundle identification is a separate input. -/
def normalDisplacement (τ : ℝ) (hτ : 0 < τ) (L : ℂˣ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    QuotientFibre (positivePeriod τ hτ) (L ^ 3) 9 (torusTuple τ hτ x0 xi ξ t) :=
  fibreRepresentative (positivePeriod τ hτ) (L ^ 3) 9 (coverTuple τ x0 xi ξ t)
    (displacementScalar τ x0 xi ξ t)

theorem normalDisplacement_left (τ : ℝ) (hτ : 0 < τ) (L : ℂˣ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin 9) :
    (normalDisplacement τ hτ L x0 xi ξ (finSumFinEquiv (Sum.inl i))).val =
      (Quotient.mk _ (rayPoint τ (xi i), (0 : ℂ)) : MultiplierQuotient (positivePeriod τ hτ) (L ^ 3) 9) := by
  change Quotient.mk _ (coverTuple τ x0 xi ξ _, displacementScalar τ x0 xi ξ _) = _
  rw [coverTuple_left, displacementScalar_left]

theorem normalDisplacement_right (τ : ℝ) (hτ : 0 < τ) (L : ℂˣ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (j : Fin q) :
    (normalDisplacement τ hτ L x0 xi ξ (finSumFinEquiv (Sum.inr j))).val =
      (Quotient.mk _ (chartPoint τ x0 (ξ j), markedPi τ xi (chartPoint τ x0 (ξ j) : ℂ)) :
        MultiplierQuotient (positivePeriod τ hτ) (L ^ 3) 9) := by
  change Quotient.mk _ (coverTuple τ x0 xi ξ _, displacementScalar τ x0 xi ξ _) = _
  rw [coverTuple_right, displacementScalar_right]

/-- Over every selected moving lift, the actual source-fibre scalar-one vector is
sent to the actual target-fibre displacement by multiplication with the actual Pi. -/
theorem movingDisplacement_Pi_times_one {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (L : ℂˣ) (xi : Fin 9 → ℝ) (z : ℂˣ) :
    fibreScaleAtLift (positivePeriod τ hτ) (L ^ 3 / piMultiplier τ xi) (L ^ 3) 0 9
      (positivePeriod_free hτ hτ1) z (markedPi τ xi (z : ℂ))
      (fibreRepresentative (positivePeriod τ hτ) (L ^ 3 / piMultiplier τ xi) 0 z 1) =
      fibreRepresentative (positivePeriod τ hτ) (L ^ 3) 9 z (markedPi τ xi (z : ℂ)) :=
  fibreScaleAtLift_one _ _ _ _ _ _ _ _

/-- Every moving displacement is nonzero in its actual quotient fibre. -/
theorem movingDisplacement_ne_zero {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (L : ℂˣ) (x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ)) (j : Fin q) :
    fibreRepresentative (positivePeriod τ hτ) (L ^ 3) 9 (chartPoint τ x0 (ξ j))
        (markedPi τ xi (chartPoint τ x0 (ξ j) : ℂ)) ≠
      fibreRepresentative (positivePeriod τ hτ) (L ^ 3) 9 (chartPoint τ x0 (ξ j)) 0 :=
  fibreRepresentative_ne_zero _ _ _ (positivePeriod_free hτ hτ1) _ _
    (markedPi_ne_zero_moving hτ hτ1 x0 xi ξ hinj j)

end Nagata.W06.TorusConfiguration

end
end

section

/-! The finite displacement list is the image of literal scalar-one classes under
actual globally glued multiplication by Pi on the multiplier quotients. -/
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.W21 Nagata.CoefficientSpaces

/-- The genuine holomorphic marked section, typed with the literal unit multiplier Q. -/
def piSection {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (xi : Fin 9 → ℝ) :
    Nagata.W08.automorphicSections (positivePeriod τ hτ : ℂ) 9 (piMultiplier τ xi : ℂ) :=
  ⟨(Nagata.W08.markedThetaSection (complexPeriod_norm_lt_one hτ hτ1)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
      (fun i => (rayPoint τ (xi i) : ℂ)) (fun _ => Units.ne_zero _)).val,
    by simpa only [piMultiplier_coe, positivePeriod, Units.val_mk0, Fintype.card_fin,
        Nat.cast_ofNat] using
      (Nagata.W08.markedThetaSection (complexPeriod_norm_lt_one hτ hτ1)
        (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
        (fun i => (rayPoint τ (xi i) : ℂ)) (fun _ => Units.ne_zero _)).property⟩

@[simp] theorem piSection_apply {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (xi : Fin 9 → ℝ) (z : ℂˣ) : (piSection hτ hτ1 xi).val z = markedPi τ xi z := by
  exact (markedPi_eq_markedThetaSection hτ hτ1 xi z).symm

/-- Change only the parameter names of a genuine multiplier quotient. -/
def quotientParameterCast {τ γ γ' : ℂˣ} {n n' : ℤ} (hγ : γ = γ') (hn : n = n') :
    MultiplierQuotient τ γ n → MultiplierQuotient τ γ' n' := by
  subst γ'; subst n'; exact id

@[simp] theorem quotientParameterCast_mk {τ γ γ' : ℂˣ} {n n' : ℤ}
    (hγ : γ = γ') (hn : n = n') (z : ℂˣ) (c : ℂ) :
    quotientParameterCast (τ := τ) hγ hn (Quotient.mk _ (z, c)) = Quotient.mk _ (z, c) := by
  subst γ'; subst n'; rfl

def piQuotientMap {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (L : ℂˣ) (xi : Fin 9 → ℝ) :
    MultiplierQuotient (positivePeriod τ hτ) (L ^ 3 / piMultiplier τ xi) 0 →
      MultiplierQuotient (positivePeriod τ hτ) (L ^ 3) 9 :=
  quotientParameterCast (div_mul_cancel (L ^ 3) (piMultiplier τ xi)) (Int.zero_add 9) ∘
    sectionQuotientMap (positivePeriod τ hτ) (L ^ 3 / piMultiplier τ xi)
      (piMultiplier τ xi) 0 9 (piSection hτ hτ1 xi)

@[simp] theorem piQuotientMap_mk {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (L : ℂˣ) (xi : Fin 9 → ℝ) (z : ℂˣ) (c : ℂ) :
    piQuotientMap hτ hτ1 L xi (Quotient.mk _ (z, c)) =
      Quotient.mk _ (z, markedPi τ xi z * c) := by
  dsimp only [piQuotientMap, Function.comp]
  rw [sectionQuotientMap_mk, piSection_apply, quotientParameterCast_mk]

/-- The global morphism preserves the actual base point. -/
theorem piQuotientMap_projection {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (L : ℂˣ) (xi : Fin 9 → ℝ)
    (w : MultiplierQuotient (positivePeriod τ hτ) (L ^ 3 / piMultiplier τ xi) 0) :
    multiplierQuotientProjection (positivePeriod τ hτ) (L ^ 3) 9
        (piQuotientMap hτ hτ1 L xi w) =
      multiplierQuotientProjection (positivePeriod τ hτ) (L ^ 3 / piMultiplier τ xi) 0 w := by
  refine Quotient.inductionOn w ?_
  rintro ⟨z, c⟩
  rw [piQuotientMap_mk]
  rfl

/-- The complete literal zero/Pi displacement list is induced by one global map,
evaluated on scalar-one representatives at every chosen covering lift. -/
theorem normalDisplacement_eq_globalPi {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (L : ℂˣ) (x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    (normalDisplacement τ hτ L x0 xi ξ t).val =
      piQuotientMap hτ hτ1 L xi (Quotient.mk _ (coverTuple τ x0 xi ξ t, (1 : ℂ))) := by
  rw [piQuotientMap_mk, mul_one]
  change Quotient.mk _ (_, displacementScalar τ x0 xi ξ t) = _
  suffices hs : displacementScalar τ x0 xi ξ t = markedPi τ xi (coverTuple τ x0 xi ξ t) by
    rw [hs]
  obtain ⟨s, rfl⟩ := (finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).surjective t
  cases s with
  | inl i => rw [displacementScalar_left, coverTuple_left, markedPi_zero_fixed hτ hτ1]
  | inr j => rw [displacementScalar_right, coverTuple_right]

end Nagata.W06.TorusConfiguration

end
end

section

noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.W21
open Filter
open scoped Topology

/-- Explicit source exponents, one common disk, all finite collision configurations,
and nonzero actual Pi values at every moving point, uniformly for small periods. -/
theorem exists_eventual_sourceMarkedAssembly {Δ : ℝ} (hΔ : 0 < Δ) (hhalf : Δ < 1 / 2) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi / 2 ∧
      (∀ q i, Tendsto (fun n => Nagata.W20.collisionCenters q R n i) atTop (𝓝 0)) ∧
      ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ ∧ τ < 1 ∧
        ∀ (hτ : 0 < τ) (q n : ℕ),
          Function.Injective (torusTuple τ hτ (1 / 2) (markedExponent Δ)
            (Nagata.W20.collisionCenters q R n)) ∧
          ∀ j : Fin q, markedPi τ (markedExponent Δ)
            (chartPoint τ (1 / 2) (Nagata.W20.collisionCenters q R n j) : ℂ) ≠ 0 := by
  obtain ⟨R, hR, hRpi, hlim, heventual⟩ := exists_eventual_collisionConfiguration
    (markedExponent Δ) (markedExponent_injective hΔ)
    (fun i => ⟨markedExponent_pos hΔ hhalf i, markedExponent_lt_half hΔ i⟩)
  refine ⟨R, hR, hRpi, hlim, ?_⟩
  filter_upwards [heventual] with τ ht
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro hτ q n
  have hinj := ht.2.2 hτ q n
  exact ⟨hinj, fun j => markedPi_ne_zero_moving hτ ht.2.1 (1 / 2)
    (markedExponent Δ) (Nagata.W20.collisionCenters q R n) hinj j⟩

end Nagata.W06.TorusConfiguration

end
end

section

/-! The manuscript requires the marked-point construction separately for every
0<τ<1. The disk may depend on τ; no limiting restriction is imposed here. -/
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.W21

/-- Every fixed genuine period admits a disk for all finite moving configurations. -/
theorem exists_disk_for_fixed_period {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (xi : Fin 9 → ℝ) (hxi : Function.Injective xi)
    (hxi_bounds : ∀ i, 0 < xi i ∧ xi i < 1 / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ (q : ℕ) (ξ : Fin q → ℂ),
      Function.Injective ξ → (∀ j, ‖ξ j‖ < R) →
      Function.Injective (torusTuple τ hτ (1 / 2) xi ξ) ∧
        ∀ j, markedPi τ xi (chartPoint τ (1 / 2) (ξ j) : ℂ) ≠ 0 := by
  have hlogpos : 0 < |Real.log τ| := abs_pos.mpr (ne_of_lt (Real.log_neg hτ hτ1))
  have hgap : 0 < markedGap (1 / 2) xi := by
    apply markedGap_pos
    intro i
    have h := hxi_bounds i
    constructor <;> linarith
  let R := min (Real.pi / 4) (min (|Real.log τ| / 4)
    (markedGap (1 / 2) xi * |Real.log τ| / 2))
  have hR : 0 < R := lt_min (div_pos Real.pi_pos (by norm_num))
    (lt_min (div_pos hlogpos (by norm_num))
      (div_pos (mul_pos hgap hlogpos) (by norm_num)))
  have hRpi : R < Real.pi / 2 :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith [Real.pi_pos])
  have hRlog : R ≤ |Real.log τ| / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hRgap : R ≤ markedGap (1 / 2) xi * |Real.log τ| / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R, hR, ?_⟩
  intro q ξ hξ hξR
  have hinj := torusTuple_injective hτ hτ1 xi hxi hxi_bounds hR hRpi
    (by linarith) (by nlinarith [mul_pos hgap hlogpos]) ξ hξ hξR
  exact ⟨hinj, fun j => markedPi_ne_zero_moving hτ hτ1 (1 / 2) xi ξ hinj j⟩

/-- Exact source marked parameters work for every 0<τ<1, with q arbitrary. -/
theorem sourceMarkedAssembly_for_every_period {Δ τ : ℝ}
    (hΔ : 0 < Δ) (hhalf : Δ < 1 / 2) (hτ : 0 < τ) (hτ1 : τ < 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ (q : ℕ) (ξ : Fin q → ℂ),
      Function.Injective ξ → (∀ j, ‖ξ j‖ < R) →
      Function.Injective (torusTuple τ hτ (1 / 2) (markedExponent Δ) ξ) ∧
        ∀ j, markedPi τ (markedExponent Δ) (chartPoint τ (1 / 2) (ξ j) : ℂ) ≠ 0 :=
  exists_disk_for_fixed_period hτ hτ1 (markedExponent Δ) (markedExponent_injective hΔ)
    (fun i => ⟨markedExponent_pos hΔ hhalf i, markedExponent_lt_half hΔ i⟩)

end Nagata.W06.TorusConfiguration

end
end

end OAI
