import OAI.Geometry.EinsteinFour.SphericalIntegralDerivative

namespace OAI

/-! The infinitesimal rotation identity for the degree-six spherical moment.
The five factors left after differentiation determine the recurrence. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

def fiveProduct (a : Fin 5 → Fin 4) (q : FourSpace) : ℝ := ∏ r, q (a r)

def fiveOmit (a : Fin 5 → Fin 4) (q : FourSpace) (r : Fin 5) : ℝ :=
  ∏ s ∈ Finset.univ.erase r, q (a s)

def sphereRotationGenerator (i j : Fin 4) (a : Fin 5 → Fin 4) (q : FourSpace) : ℝ :=
  (delta j i * q j - q i) * fiveProduct a q + q j *
    ∑ r, (delta (a r) i * q j - delta (a r) j * q i) * fiveOmit a q r

theorem fiveProduct_eq_mul_omit (a : Fin 5 → Fin 4) (q : FourSpace) (r : Fin 5) :
    q (a r) * fiveOmit a q r = fiveProduct a q := by
  simpa only [fiveProduct, fiveOmit, mul_comm] using
    Finset.prod_erase_mul Finset.univ (fun s => q (a s)) (Finset.mem_univ r)

theorem sum_sphereRotationGenerator (i : Fin 4) (a : Fin 5 → Fin 4)
    (q : FourSpace) (hq : ∑ j, q j ^ 2 = 1) :
    (∑ j, sphereRotationGenerator i j a q) =
      (∑ r, delta (a r) i * fiveOmit a q r) - 8 * q i * fiveProduct a q := by
  have hfirst : (∑ j, (delta j i * q j - q i) * fiveProduct a q) =
      -3 * q i * fiveProduct a q := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul]
    simp [delta]
    ring
  have hterm (r : Fin 5) :
      (∑ j, q j * ((delta (a r) i * q j - delta (a r) j * q i) * fiveOmit a q r)) =
      (delta (a r) i - q i * q (a r)) * fiveOmit a q r := by
    have he (j : Fin 4) :
        q j * ((delta (a r) i * q j - delta (a r) j * q i) * fiveOmit a q r) =
        (delta (a r) i * q j ^ 2 - q i * (delta (a r) j * q j)) * fiveOmit a q r := by
      ring
    simp_rw [he]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hq]
    simp [delta]
  have hsecond :
      (∑ j, q j * ∑ r, (delta (a r) i * q j - delta (a r) j * q i) * fiveOmit a q r) =
      (∑ r, delta (a r) i * fiveOmit a q r) - 5 * q i * fiveProduct a q := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hterm, sub_mul, Finset.sum_sub_distrib]
    have he (r : Fin 5) : q i * q (a r) * fiveOmit a q r = q i * fiveProduct a q := by
      rw [mul_assoc, fiveProduct_eq_mul_omit]
    simp_rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [sphereRotationGenerator, Finset.sum_add_distrib]
  rw [hfirst, hsecond]
  ring

local instance sphericalRecurrenceNormedGroup : NormedAddCommGroup C(Directions, ℝ) :=
  ContinuousMap.instNormedAddCommGroup
local instance sphericalRecurrenceNormedSpace : NormedSpace ℝ C(Directions, ℝ) :=
  ContinuousMap.normedSpace

variable [IsProbabilityMeasure sphereMeasure]

theorem integral_sphereRotationGenerator_zero (i j : Fin 4) (a : Fin 5 → Fin 4) :
    (∫ q : Directions, sphereRotationGenerator i j a q.val ∂sphereMeasure) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [sphereRotationGenerator, delta]
  let Z (k : Fin 4) (p : ℝ × Directions) := planeRotation i j hij p.1 p.2.val k
  let V (k : Fin 4) (p : ℝ × Directions) := planeCoordinateDerivative i j p.1 p.2.val k
  have hZ (k : Fin 4) : Continuous (Z k) := continuous_planeRotation_coordinate i j hij k
  have hV (k : Fin 4) : Continuous (V k) := continuous_planeCoordinateDerivative i j k
  have hP : Continuous (fun p : ℝ × Directions => ∏ r, Z (a r) p) :=
    continuous_finsetProd Finset.univ (fun r _ => hZ (a r))
  have hD : Continuous (fun p : ℝ × Directions =>
      ∑ r, (∏ s ∈ Finset.univ.erase r, Z (a s) p) * V (a r) p) :=
    continuous_finsetSum Finset.univ (fun r _ =>
      (continuous_finsetProd (Finset.univ.erase r) (fun s _ => hZ (a s))).mul (hV (a r)))
  have hF : Continuous (fun p : ℝ × Directions => Z j p * ∏ r, Z (a r) p) :=
    (hZ j).mul hP
  have hG : Continuous (fun p : ℝ × Directions =>
      V j p * (∏ r, Z (a r) p) + Z j p *
        ∑ r, (∏ s ∈ Finset.univ.erase r, Z (a s) p) * V (a r) p) :=
    ((hV j).mul hP).add ((hZ j).mul hD)
  let F (t : ℝ) : C(Directions, ℝ) :=
    ⟨fun q => Z j (t, q) * ∏ r, Z (a r) (t, q),
      hF.comp (continuous_const.prodMk continuous_id)⟩
  let G (t : ℝ) : C(Directions, ℝ) :=
    ⟨fun q => V j (t, q) * (∏ r, Z (a r) (t, q)) + Z j (t, q) *
        ∑ r, (∏ s ∈ Finset.univ.erase r, Z (a s) (t, q)) * V (a r) (t, q),
      hG.comp (continuous_const.prodMk continuous_id)⟩
  have hpoint (t : ℝ) (q : Directions) : HasDerivAt (fun s => F s q) (G t q) t := by
    have hd (k : Fin 4) : HasDerivAt (fun s => Z k (s, q)) (V k (t, q)) t :=
      hasDerivAt_planeRotation_coordinate i j hij q.val k t
    have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun r _ => hd (a r))
    change HasDerivAt (fun s => Z j (s, q) * ∏ r, Z (a r) (s, q))
      (V j (t, q) * (∏ r, Z (a r) (t, q)) + Z j (t, q) *
        ∑ r, (∏ s ∈ Finset.univ.erase r, Z (a s) (t, q)) * V (a r) (t, q)) t
    simpa only [smul_eq_mul, Pi.mul_apply] using! (hd j).mul hp
  have hi := sphereIntegral_hasDerivAt (F := F) (G := G) hG hpoint 0
  have hconst (t : ℝ) : (∫ q, F t q ∂sphereMeasure) =
      ∫ q : Directions, q.val j * fiveProduct a q.val ∂sphereMeasure := by
    have h := sphereIntegral_isometry (directionIsometry (planeRotation i j hij t))
      (fun q : Directions => q.val j * fiveProduct a q.val)
    change (∫ q : Directions, (planeRotation i j hij t q.val) j *
      (∏ r, (planeRotation i j hij t q.val) (a r)) ∂sphereMeasure) = _ at h
    exact h
  have hfun : (fun t => ∫ q, F t q ∂sphereMeasure) =
      fun _ : ℝ => ∫ q : Directions, q.val j * fiveProduct a q.val ∂sphereMeasure :=
    funext hconst
  rw [hfun] at hi
  have hz : (∫ q, G 0 q ∂sphereMeasure) = 0 :=
    hi.unique (hasDerivAt_const 0 _)
  have hg0 (q : Directions) : G 0 q = sphereRotationGenerator i j a q.val := by
    have hz0 (k : Fin 4) : Z k (0, q) = q.val k :=
      congrArg (fun v : FourSpace => v k) (planeRotation_zero i j hij q.val)
    have hv0 (k : Fin 4) : V k (0, q) =
        delta k i * q.val j - delta k j * q.val i :=
      planeCoordinateDerivative_zero i j hij q.val k
    change V j (0, q) * (∏ r, Z (a r) (0, q)) + Z j (0, q) *
      (∑ r, (∏ s ∈ Finset.univ.erase r, Z (a s) (0, q)) * V (a r) (0, q)) = _
    simp_rw [hz0, hv0]
    simp only [show delta j j = 1 by simp [delta], one_mul]
    unfold sphereRotationGenerator fiveProduct fiveOmit
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    ring
  calc
    _ = ∫ q, G 0 q ∂sphereMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall (fun q => (hg0 q).symm))
    _ = 0 := hz

theorem spherical_sixth_recurrence (i : Fin 4) (a : Fin 5 → Fin 4) :
    8 * (∫ q : Directions, q.val i * fiveProduct a q.val ∂sphereMeasure) =
      ∑ r, delta (a r) i * (∫ q : Directions, fiveOmit a q.val r ∂sphereMeasure) := by
  have hM : Integrable (fun q : Directions => q.val i * fiveProduct a q.val) sphereMeasure :=
    sphere_continuous_integrable (by unfold fiveProduct; fun_prop)
  have hO (r : Fin 5) : Integrable (fun q : Directions => delta (a r) i *
      fiveOmit a q.val r) sphereMeasure :=
    sphere_continuous_integrable (by unfold fiveOmit; fun_prop)
  have hR (j : Fin 4) : Integrable (fun q : Directions =>
      sphereRotationGenerator i j a q.val) sphereMeasure :=
    sphere_continuous_integrable (by unfold sphereRotationGenerator fiveProduct fiveOmit; fun_prop)
  have hz : (∫ q : Directions, ∑ j, sphereRotationGenerator i j a q.val ∂sphereMeasure) = 0 := by
    rw [integral_finsetSum _ (fun j _ => hR j)]
    simp only [integral_sphereRotationGenerator_zero, Finset.sum_const_zero]
  have he : (fun q : Directions => ∑ j, sphereRotationGenerator i j a q.val) =
      fun q => (∑ r, delta (a r) i * fiveOmit a q.val r) -
        8 * (q.val i * fiveProduct a q.val) := by
    funext q
    simpa only [mul_assoc] using sum_sphereRotationGenerator i a q.val (sum_coordinate_sq q)
  rw [he, integral_sub (integrable_finsetSum _ (fun r _ => hO r)) (hM.const_mul 8),
    integral_finsetSum _ (fun r _ => hO r), integral_const_mul] at hz
  simp_rw [integral_const_mul] at hz
  linarith

omit [IsProbabilityMeasure sphereMeasure] in
theorem fiveOmit_eq_succAbove (a : Fin 5 → Fin 4) (q : FourSpace) (r : Fin 5) :
    fiveOmit a q r = ∏ s : Fin 4, q (a (r.succAbove s)) := by
  have he : (Finset.univ : Finset (Fin 5)).erase r =
      Finset.univ.map (Fin.succAboveEmb r) := by
    ext k
    simp [Finset.mem_map]
  unfold fiveOmit
  rw [he, Finset.prod_map]
  rfl

end
end PositiveEinsteinFour.Angular

end OAI
