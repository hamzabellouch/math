import OAI.Analysis.KadisonKastler.TypeIIISmallNormalizer
import OAI.Analysis.KadisonKastler.NormalizerTopology
import OAI.Analysis.KadisonKastler.BoundaryBoundedTransport

namespace OAI

/-! # Averaging close exact normalizers within the normalizer group

Separate the near-identity residual into its algebra and commutant
factors, average these separately, and take their polar unitaries inside
the respective algebras. The quadratic covariance estimate controls the
loss from separating the average of the product.
-/

namespace KadisonKastler

open scoped CStarAlgebra BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance constructedNormalizerAverageOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance constructedNormalizerAverageStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- The polar correction is taken inside the given algebra. -/
theorem constructed_exists_polar_unitary_mem_of_near_one (P : VonNeumannAlgebra H)
    (x : H →L[ℂ] H) (hx : x ∈ P) (hnear : ‖x - 1‖ < 1) :
    ∃ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ P ∧
      ‖(u : H →L[ℂ] H) - x‖ ≤ ‖star x * x - 1‖ := by
  let a : Algebra P := ⟨x, hx⟩
  obtain ⟨u, -, hn⟩ := exists_polar_unitary_close_of_near_unitary a 1 hnear
  let v := Unitary.map (StarMonoidHom.ofClass P.toStarSubalgebra.subtype) u
  exact ⟨v, (u : Algebra P).property, hn⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

local instance constructedNormalizerAverageFamilyCStar : CStarAlgebra (G →ᵇ (H →L[ℂ] H)) where

omit [Group G] in
/-- A contractive bimodule mean that preserves the two concrete algebras
replaces a close family of normalizers by a normalizer at quadratic cost. -/
theorem constructed_exists_normalizer_near_mean
    (P : VonNeumannAlgebra H) (hpub : SmallNormalizerFactorization P)
    (m : BimoduleMean (boundaryConstant (G := G) (B := H →L[ℂ] H)))
    (hpres : ∀ (Q : VonNeumannAlgebra H) (F : G →ᵇ (H →L[ℂ] H)),
      (∀ g, F g ∈ Q) → m.toCLM F ∈ Q)
    (X : unitary (G →ᵇ (H →L[ℂ] H)))
    (hX : ∀ g : G, Conjugates (unitaryFamilyEval (B := H →L[ℂ] H) X g) P P)
    (v : unitary (H →L[ℂ] H)) (hv : Conjugates v P P)
    {e : ℝ} (he : 0 ≤ e) (heSmall : 64 * e < 1)
    (hclose : ∀ g, ‖X.val g - (v : H →L[ℂ] H)‖ ≤ e) :
    ∃ w : unitary (H →L[ℂ] H), Conjugates w P P ∧
      ‖(w : H →L[ℂ] H) - m.toCLM X.val‖ ≤ 1200 * e ^ 2 := by
  let residual (g : G) := unitaryFamilyEval (B := H →L[ℂ] H) X g * star v
  have hrNorm (g : G) : ‖(residual g : H →L[ℂ] H) - 1‖ ≤ e := by
    have hid : (residual g : H →L[ℂ] H) - 1 =
        (X.val g - (v : H →L[ℂ] H)) * star (v : H →L[ℂ] H) := by
      change X.val g * star (v : H →L[ℂ] H) - 1 = _
      rw [sub_mul, Unitary.mul_star_self_of_mem v.property]
    rw [hid, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    exact hclose g
  have hr (g : G) : ∃ a b : unitary (H →L[ℂ] H),
      (a : H →L[ℂ] H) ∈ P ∧ (b : H →L[ℂ] H) ∈ P.commutant ∧
      residual g = a * b ∧
      ‖(a : H →L[ℂ] H) - 1‖ + ‖(b : H →L[ℂ] H) - 1‖ ≤ 10 * e := by
    obtain ⟨a, b, ha, hb, hab, hn⟩ := hpub (residual g)
      (hv.symm.trans (hX g)) ((hrNorm g).trans_lt (by linarith))
    exact ⟨a, b, ha, hb, hab, hn.trans (mul_le_mul_of_nonneg_left (hrNorm g) (by norm_num))⟩
  choose a b ha hb hab hn using hr
  let A := boundedUnitaryFamily a
  let B := boundedUnitaryFamily b
  have hA : ‖A.val - boundaryConstant (G := G) (1 : H →L[ℂ] H)‖ ≤ 10 * e := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro g
    have h := hn g
    change ‖(a g : H →L[ℂ] H) - 1‖ ≤ _
    linarith [norm_nonneg ((b g : H →L[ℂ] H) - 1)]
  have hB : ‖B.val - boundaryConstant (G := G) (1 : H →L[ℂ] H)‖ ≤ 10 * e := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro g
    have h := hn g
    change ‖(b g : H →L[ℂ] H) - 1‖ ≤ _
    linarith [norm_nonneg ((a g : H →L[ℂ] H) - 1)]
  have hAmem : m.toCLM A.val ∈ P := hpres P A.val ha
  have hBmem : m.toCLM B.val ∈ P.commutant := hpres P.commutant B.val hb
  have hAnear : ‖m.toCLM A.val - 1‖ < 1 := (m.norm_sub_le A.val 1 hA).trans_lt (by linarith)
  have hBnear : ‖m.toCLM B.val - 1‖ < 1 := (m.norm_sub_le B.val 1 hB).trans_lt (by linarith)
  obtain ⟨p, hp, hpn⟩ := constructed_exists_polar_unitary_mem_of_near_one P _ hAmem hAnear
  obtain ⟨q, hq, hqn⟩ := constructed_exists_polar_unitary_mem_of_near_one P.commutant _ hBmem hBnear
  have hpBound : ‖(p : H →L[ℂ] H) - m.toCLM A.val‖ ≤ 400 * e ^ 2 := by
    have h := m.norm_variance_le_four_mul_sq A 1 (by positivity : 0 ≤ 10 * e) hA
    rw [norm_sub_rev] at h
    nlinarith [hpn]
  have hqBound : ‖(q : H →L[ℂ] H) - m.toCLM B.val‖ ≤ 400 * e ^ 2 := by
    have h := m.norm_variance_le_four_mul_sq B 1 (by positivity : 0 ≤ 10 * e) hB
    rw [norm_sub_rev] at h
    nlinarith [hqn]
  have hcov : ‖m.toCLM (A.val * B.val) - m.toCLM A.val * m.toCLM B.val‖ ≤
      400 * e ^ 2 := by
    have h := m.norm_covariance_le_four_mul_sq A.val B.val (by positivity : 0 ≤ 10 * e)
      (m.norm_residual_le A.val 1 hA) (m.norm_residual_le B.val 1 hB)
    nlinarith
  have hAnorm : ‖m.toCLM A.val‖ ≤ 1 := (m.norm_le _).trans (norm_unitary_le_one A)
  have hprod : ‖(p : H →L[ℂ] H) * (q : H →L[ℂ] H) -
      m.toCLM A.val * m.toCLM B.val‖ ≤ 800 * e ^ 2 := by
    have hid : (p : H →L[ℂ] H) * (q : H →L[ℂ] H) -
        m.toCLM A.val * m.toCLM B.val =
        ((p : H →L[ℂ] H) - m.toCLM A.val) * (q : H →L[ℂ] H) +
        m.toCLM A.val * ((q : H →L[ℂ] H) - m.toCLM B.val) := by noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖((p : H →L[ℂ] H) - m.toCLM A.val) * (q : H →L[ℂ] H)‖ +
          ‖m.toCLM A.val * ((q : H →L[ℂ] H) - m.toCLM B.val)‖ := norm_add_le _ _
      _ ≤ 400 * e ^ 2 + 400 * e ^ 2 := add_le_add
        (by simpa only [CStarRing.norm_mul_coe_unitary] using hpBound)
        ((norm_mul_le _ _).trans ((mul_le_mul hAnorm hqBound (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)))
      _ = _ := by ring
  have hfield : X.val = A.val * B.val * boundaryConstant (G := G) (v : H →L[ℂ] H) := by
    apply BoundedContinuousFunction.ext
    intro g
    have h := congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H)) (hab g)
    change X.val g * star (v : H →L[ℂ] H) = (a g : H →L[ℂ] H) * (b g : H →L[ℂ] H) at h
    change X.val g = (a g : H →L[ℂ] H) * (b g : H →L[ℂ] H) * (v : H →L[ℂ] H)
    rw [← h, mul_assoc, Unitary.star_mul_self_of_mem v.property, mul_one]
  refine ⟨p * q * v, hv.trans (conjugates_self_of_separate_factors hp hq), ?_⟩
  rw [hfield, m.map_right]
  change ‖((p : H →L[ℂ] H) * (q : H →L[ℂ] H)) * (v : H →L[ℂ] H) -
    m.toCLM (A.val * B.val) * (v : H →L[ℂ] H)‖ ≤ _
  rw [← sub_mul, CStarRing.norm_mul_coe_unitary]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hprod (by simpa only [norm_sub_rev] using hcov)).trans_eq (by ring))

end

end KadisonKastler

end OAI
