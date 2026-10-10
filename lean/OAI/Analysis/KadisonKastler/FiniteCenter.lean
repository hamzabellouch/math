import OAI.Analysis.KadisonKastler.ConcreteTraceHilbert
import OAI.Analysis.KadisonKastler.BoundaryDiagonal
import OAI.Analysis.KadisonKastler.UnitaryBounds

namespace OAI

/-! # Scalar orbit averages and central projections of a nearby algebra

Least vectors in the trace Hilbert space give scalar orbit averages in a
finite factor. Operator-norm balls centred at ambient operators are retained
under this averaging, even when their centre is outside the factor.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}

/-- Trace convex hulls of uniformly bounded operators retain norm bounds
relative to an arbitrary ambient operator. -/
theorem traceHull_mem_external_ball (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hτ : FiniteVectorTrace τ)
    {s : Set (Algebra M)} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (a : H →L[ℂ] H) (hsC : ∀ x ∈ s, ‖x‖ ≤ C)
    (hsr : ∀ x ∈ s, ‖(x : H →L[ℂ] H) - a‖ ≤ r)
    {z : E} (hz : z ∈ diagonalTraceHull J s) :
    ∃ b : Algebra M, J b = z ∧ ‖(b : H →L[ℂ] H) - a‖ ≤ r := by
  have hcC : ∀ x ∈ convexHull ℝ s, ‖x‖ ≤ C := by
    have h := convexHull_min (t := Metric.closedBall (0 : Algebra M) C)
      (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hsC x hx)
      (convex_closedBall _ _)
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using h hx
  have hcr : ∀ x ∈ convexHull ℝ s, ‖(x : H →L[ℂ] H) - a‖ ≤ r := by
    have hv : Convex ℝ {x : Algebra M | ‖(x : H →L[ℂ] H) - a‖ ≤ r} := by
      have he := (convex_closedBall a r).linear_preimage
        (M.toStarSubalgebra.subtype.toLinearMap.restrictScalars ℝ)
      have heq : {x : Algebra M | ‖(x : H →L[ℂ] H) - a‖ ≤ r} =
          (fun x : Algebra M => (x : H →L[ℂ] H)) ⁻¹' Metric.closedBall a r := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
      rw [heq]
      exact he
    exact convexHull_min hsr hv
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hz
  choose x hxmem hx using hv
  have hxc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      traceTwoNorm τ (x m - x n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hvlim.cauchySeq ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [← hJ, map_sub, hx, dist_eq_norm] using hN m hm n hn
  obtain ⟨b, _, hstrong, htwo⟩ := hτ.bounded_complete x hC
    (fun n => hcC _ (hxmem n)) hxc
  have hJb : Tendsto v atTop (𝓝 (J b)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [← hx, ← map_sub, hJ] using htwo
  refine ⟨b, tendsto_nhds_unique hJb hvlim, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro ξ
  have hs := (hstrong ξ).sub (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => a ξ) atTop (𝓝 (a ξ)))
  exact le_of_tendsto hs.norm (Eventually.of_forall fun n =>
    ((x n : H →L[ℂ] H) - a).le_of_opNorm_le (hcr _ (hxmem n)) ξ)

/-- Unitary conjugates of an element, as an actual subset of the algebra. -/
def unitaryConjugacyOrbit (a : Algebra M) : Set (Algebra M) :=
  Set.range (fun u : unitary (Algebra M) => (u : Algebra M) * a * star (u : Algebra M))

/-- A bounded unitary orbit in a finite factor has a scalar in its trace
closed convex hull. -/
theorem exists_scalar_in_traceOrbit [CompleteSpace E]
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ)
    (hfactor : ∀ b : Algebra M, (∀ x : Algebra M, x * b = b * x) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (a : Algebra M) (ha : ‖a‖ ≤ 1) :
    ∃ c : ℂ, J (c • (1 : Algebra M)) ∈ diagonalTraceHull J (unitaryConjugacyOrbit a) := by
  have horbit : ∀ x ∈ unitaryConjugacyOrbit a, ‖x‖ ≤ 1 := by
    rintro _ ⟨u, rfl⟩
    simpa only [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary,
      ← Unitary.coe_star] using ha
  obtain ⟨b, hb, _⟩ := exists_unique_diagonal_least J hJ hτ
    (show (unitaryConjugacyOrbit a).Nonempty from ⟨a, ⟨1, by simp⟩⟩)
    (r := 2) (by norm_num) horbit (fun x hx => by
      have h := (norm_sub_le x 1).trans (add_le_add (horbit x hx)
        (norm_unitary_le_one (1 : unitary (Algebra M))))
      convert h using 1; norm_num)
  have hfix (u : unitary (Algebra M)) : b = (u : Algebra M) * b * star (u : Algebra M) := by
    apply diagonal_least_covariance J hJ u u
      (s := unitaryConjugacyOrbit a) (t := unitaryConjugacyOrbit a)
      ?_ ?_ hb.1 hb.1 hb.2.2.2 hb.2.2.2
    · rintro _ ⟨v, rfl⟩
      exact ⟨u * v, by simp only [Submonoid.coe_mul, star_mul, mul_assoc]⟩
    · rintro _ ⟨v, rfl⟩
      exact ⟨star u * v, by simp only [Submonoid.coe_mul, Unitary.coe_star, star_mul,
        star_star, mul_assoc]⟩
  have hcomm (u : unitary (Algebra M)) : (u : Algebra M) * b = b * u := by
    have he := congrArg (fun x : Algebra M => x * (u : Algebra M)) (hfix u)
    simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using he.symm
  let T : Algebra M →ₗ[ℂ] Algebra M := LinearMap.mulRight ℂ b - LinearMap.mulLeft ℂ b
  have hcentral (x : Algebra M) : x * b = b * x := by
    have hn := norm_le_twice_unitary_bound T (C := 0) (fun u => by
      change ‖(u : Algebra M) * b - b * u‖ ≤ 0
      rw [hcomm, sub_self, norm_zero]) x
    have hz : T x = 0 := norm_eq_zero.mp (le_antisymm (by simpa using hn) (norm_nonneg _))
    exact sub_eq_zero.mp hz
  obtain ⟨c, rfl⟩ := hfactor b hcentral
  exact ⟨c, hb.1⟩

/-- A contraction all of whose conjugates stay near an ambient operator
has a scalar near that same operator. -/
theorem exists_scalar_near_of_unitary_orbit [CompleteSpace E]
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ)
    (hfactor : ∀ b : Algebra M, (∀ x : Algebra M, x * b = b * x) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (a : Algebra M) (ha : ‖a‖ ≤ 1) (q : H →L[ℂ] H) {r : ℝ} (hr : 0 ≤ r)
    (hclose : ∀ u : unitary (Algebra M),
      ‖((u : Algebra M) * a * star (u : Algebra M) : Algebra M).val - q‖ ≤ r) :
    ∃ c : ℂ, ‖c • (1 : H →L[ℂ] H) - q‖ ≤ r := by
  obtain ⟨c, hc⟩ := exists_scalar_in_traceOrbit J hJ hτ hfactor a ha
  obtain ⟨b, hb, hbq⟩ := traceHull_mem_external_ball J hJ hτ (by norm_num : (0 : ℝ) ≤ 1)
    hr q (s := unitaryConjugacyOrbit a) (by
      rintro _ ⟨u, rfl⟩
      simpa only [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary,
        ← Unitary.coe_star] using ha) (by rintro _ ⟨u, rfl⟩; exact hclose u) hc
  have he : b = c • (1 : Algebra M) := traceHilbert_injective J hJ hb
  refine ⟨c, ?_⟩
  rw [he] at hbq
  exact hbq


/-- A projection within one half of a scalar is trivial. -/
theorem projection_eq_zero_or_one_of_near_scalar {A : Type*} [CStarAlgebra A]
    (q : A) (hq : IsStarProjection q) (c : ℂ)
    (hclose : ‖c • (1 : A) - q‖ < 1 / 2) : q = 0 ∨ q = 1 := by
  by_contra hn
  push Not at hn
  have hnq : ‖q‖ = 1 := by
    have hh := (CStarRing.norm_star_mul_self (x := q))
    rw [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq] at hh
    nlinarith [norm_pos_iff.mpr hn.1]
  have hcomp : ‖1 - q‖ = 1 := by
    have hh := (CStarRing.norm_star_mul_self (x := 1 - q))
    rw [hq.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isIdempotentElem.eq] at hh
    have hne : (1 : A) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hn.2)
    nlinarith [norm_pos_iff.mpr hne]
  have hmul : (c • (1 : A) - q) * q = (c - 1) • q := by
    simp only [sub_mul, smul_mul_assoc, one_mul, hq.isIdempotentElem.eq,
      sub_smul, one_smul]
  have hmul' : (c • (1 : A) - q) * (1 - q) = c • (1 - q) := by
    rw [sub_mul, smul_mul_assoc, one_mul, hq.mul_one_sub_self, sub_zero]
  have hc : ‖c‖ < 1 / 2 := by
    have h := norm_mul_le (c • (1 : A) - q) (1 - q)
    rw [hmul', norm_smul, hcomp, mul_one, mul_one] at h
    exact h.trans_lt hclose
  have hc1 : ‖c - 1‖ < 1 / 2 := by
    have h := norm_mul_le (c • (1 : A) - q) q
    rw [hmul, norm_smul, hnq, mul_one, mul_one] at h
    exact h.trans_lt hclose
  have htri := norm_sub_le c (c - 1)
  rw [sub_sub_cancel, norm_one] at htri
  linarith

/-- A central projection in an algebra within one tenth of a finite
factor is zero or one. The trace data are supplied separately. -/
theorem central_projection_trivial_of_near [CompleteSpace E]
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ)
    (hfactor : ∀ b : Algebra M, (∀ x : Algebra M, x * b = b * x) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    {N : VonNeumannAlgebra H} (hgap : kkDistance M N < 1 / 10)
    (q : Algebra N) (hq : IsStarProjection q)
    (hcentral : ∀ b : Algebra N, b * q = q * b) : q = 0 ∨ q = 1 := by
  have hqa : IsStarProjection (q : H →L[ℂ] H) := by
    exact ⟨congrArg Subtype.val hq.isIdempotentElem.eq,
      congrArg Subtype.val hq.isSelfAdjoint.star_eq⟩
  obtain ⟨a, ha, haq⟩ := exists_unitBall_approx (M := N) (N := M)
    ⟨q.property, hqa.norm_le⟩ (by simpa only [kkDistance_comm N M] using hgap)
  let aM : Algebra M := ⟨a, ha.1⟩
  have horbit (u : unitary (Algebra M)) :
      ‖((u : Algebra M) * aM * star (u : Algebra M) : Algebra M).val - q.val‖ ≤ 3 / 10 := by
    let U : unitary (H →L[ℂ] H) :=
      Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) u
    obtain ⟨b, hb, hub⟩ := exists_unitBall_approx (M := M) (N := N)
      ⟨u.val.property, norm_unitary_le_one U⟩ hgap
    change ‖(U : H →L[ℂ] H) - b‖ < 1 / 10 at hub
    have hbq : b * q.val = q.val * b := congrArg Subtype.val (hcentral ⟨b, hb.1⟩)
    have hdecomp : (U : H →L[ℂ] H) * q.val - q.val * U =
        ((U : H →L[ℂ] H) - b) * q.val - q.val * ((U : H →L[ℂ] H) - b) := by
      rw [sub_mul, mul_sub, hbq]
      abel
    have hcomm : ‖(U : H →L[ℂ] H) * q.val - q.val * U‖ < 2 * (1 / 10 : ℝ) := by
      calc
        _ ≤ ‖((U : H →L[ℂ] H) - b) * q.val‖ +
            ‖q.val * ((U : H →L[ℂ] H) - b)‖ := hdecomp ▸ norm_sub_le _ _
        _ ≤ ‖(U : H →L[ℂ] H) - b‖ * ‖q.val‖ +
            ‖q.val‖ * ‖(U : H →L[ℂ] H) - b‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 2 * ‖(U : H →L[ℂ] H) - b‖ := by
          nlinarith [mul_le_mul_of_nonneg_left hqa.norm_le (norm_nonneg ((U : H →L[ℂ] H) - b))]
        _ < _ := by nlinarith
    have he : (U : H →L[ℂ] H) * a * star (U : H →L[ℂ] H) - q.val =
        (U : H →L[ℂ] H) * (a - q.val) * star (U : H →L[ℂ] H) +
          ((U : H →L[ℂ] H) * q.val - q.val * U) * star (U : H →L[ℂ] H) := by
      rw [sub_mul, mul_assoc q.val, Unitary.mul_star_self_of_mem U.property, mul_one]
      noncomm_ring
    change ‖(U : H →L[ℂ] H) * a * star (U : H →L[ℂ] H) - q.val‖ ≤ _
    rw [he]
    have htri := norm_add_le ((U : H →L[ℂ] H) * (a - q.val) * star (U : H →L[ℂ] H))
      (((U : H →L[ℂ] H) * q.val - q.val * U) * star (U : H →L[ℂ] H))
    rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary] at htri
    rw [norm_sub_rev] at haq
    simp only [Unitary.coe_star] at htri
    linarith
  obtain ⟨c, hc⟩ := exists_scalar_near_of_unitary_orbit J hJ hτ hfactor aM ha.2 q.val
    (by norm_num : (0 : ℝ) ≤ 3 / 10) horbit
  have htriv := projection_eq_zero_or_one_of_near_scalar q.val hqa c (hc.trans_lt (by norm_num))
  exact htriv.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)

end

end KadisonKastler

end OAI
