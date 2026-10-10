import OAI.Analysis.KadisonSimilarity.Representation.DyadicCornerHom
import OAI.Analysis.KadisonSimilarity.FreeProduct.HaarCornerLetters
import Mathlib.Topology.Algebra.Star.Unitary

namespace OAI

/-! A Haar unitary in each corner of a diffuse finite tracial von Neumann
algebra, constructed as a norm limit of finite dyadic spectral sums. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge Filter
open scoped BigOperators Topology CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}
  (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

local instance haarAlgebra_closed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  Generator.Tracial.base_norm_closed M

def dyadicUnitaryApprox (p : AlgebraProjection M) (n : ℕ) :
    CStarCorner p.val p.property := dyadicCornerHom τ hdiff p n (dyadicPhase n)

theorem dyadicUnitaryApprox_mem (p : AlgebraProjection M) (n : ℕ) :
    dyadicUnitaryApprox τ hdiff p n ∈ unitary (CStarCorner p.val p.property) := by
  have hs : star (dyadicPhase n) * dyadicPhase n = 1 := by
    funext i
    change star (dyadicPhase n i) * dyadicPhase n i = 1
    rw [Complex.star_def, Complex.conj_mul', norm_dyadicPhase]
    norm_num
  have ht : dyadicPhase n * star (dyadicPhase n) = 1 := by
    rw [mul_comm, hs]
  apply Unitary.mem_iff.mpr
  constructor
  · simpa only [dyadicUnitaryApprox, map_mul, map_star, map_one] using
      congrArg (dyadicCornerHom τ hdiff p n) hs
  · simpa only [dyadicUnitaryApprox, map_mul, map_star, map_one] using
      congrArg (dyadicCornerHom τ hdiff p n) ht

theorem dyadicUnitaryApprox_step (p : AlgebraProjection M) (n : ℕ) :
    ‖dyadicUnitaryApprox τ hdiff p (n + 1) - dyadicUnitaryApprox τ hdiff p n‖ ≤
      Real.pi * (1 / 2 : ℝ) ^ n := by
  unfold dyadicUnitaryApprox
  rw [← dyadicCornerHom_refine τ hdiff p n, ← map_sub]
  exact norm_dyadicCornerHom_le τ hdiff p (n + 1) _ _ (by positivity)
    (dyadicPhase_refine_bound n)

theorem dyadicUnitaryApprox_cauchy (p : AlgebraProjection M) :
    CauchySeq (dyadicUnitaryApprox τ hdiff p) := by
  apply cauchySeq_of_le_geometric (1 / 2) Real.pi (by norm_num)
  intro n
  rw [dist_eq_norm, norm_sub_rev]
  exact dyadicUnitaryApprox_step τ hdiff p n

def dyadicCornerTrace (p : AlgebraProjection M) : CStarCorner p.val p.property →L[ℂ] ℂ :=
  ({ toFun := fun a => τ.trace (a : M.toStarSubalgebra)
     map_add' := fun _ _ => inner_add_right _ _ _
     map_smul' := fun _ _ => inner_smul_right _ _ _ } :
    CStarCorner p.val p.property →ₗ[ℂ] ℂ).mkContinuous 1 (fun a => by
      change ‖τ.trace (a : M.toStarSubalgebra)‖ ≤ 1 * ‖(a : M.toStarSubalgebra)‖
      rw [one_mul]
      exact (τ.norm_trace_le_norm₂ (a : M.toStarSubalgebra)).trans
        (τ.norm₂_le_norm (a : M.toStarSubalgebra)))

theorem trace_dyadicUnitaryApprox_pow (p : AlgebraProjection M) (n k : ℕ)
    (hk : 0 < k) (hkn : k < 2 ^ n) :
    dyadicCornerTrace τ p (dyadicUnitaryApprox τ hdiff p n ^ k) = 0 := by
  unfold dyadicUnitaryApprox
  rw [← map_pow]
  change τ.trace (dyadicEval τ hdiff p n (fun i => dyadicPhase n i ^ k)) = 0
  rw [dyadicEval_trace, ← Finset.sum_mul, sum_dyadicPhase_pow_eq_zero n k hk hkn,
    zero_mul]

include hdiff in
/-- The constructed corner unitary has every nonzero integer moment zero.
No Haar-unitary existence theorem is assumed. -/
theorem exists_dyadicCornerHaar (p : AlgebraProjection M) :
    ∃ z : unitary (CStarCorner p.val p.property),
      ∀ k : ℤ, k ≠ 0 → τ.trace (haarCornerPower z k) = 0 := by
  obtain ⟨a, ha, hlim⟩ := cauchySeq_tendsto_of_isComplete isClosed_unitary.isComplete
    (dyadicUnitaryApprox_mem τ hdiff p) (dyadicUnitaryApprox_cauchy τ hdiff p)
  let z : unitary (CStarCorner p.val p.property) := ⟨a, ha⟩
  have hpows (k : ℕ) (hk : 0 < k) : dyadicCornerTrace τ p (a ^ k) = 0 := by
    have hzero : ∀ᶠ n : ℕ in atTop,
        dyadicCornerTrace τ p (dyadicUnitaryApprox τ hdiff p n ^ k) = 0 := by
      filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
        (eventually_gt_atTop k)] with n hn
      exact trace_dyadicUnitaryApprox_pow τ hdiff p n k hk hn
    exact tendsto_nhds_unique ((dyadicCornerTrace τ p).continuous.tendsto _ |>.comp
      (hlim.pow k)) (tendsto_nhds_of_eventually_eq hzero)
  have hpos (k : ℕ) (hk : 0 < k) : τ.trace (haarCornerPower z (k : ℤ)) = 0 := by
    have hc := hpows k hk
    change τ.trace ((a ^ k : CStarCorner p.val p.property) : M.toStarSubalgebra) = 0 at hc
    simpa only [haarCornerPower, zpow_natCast, SubmonoidClass.coe_pow] using hc
  refine ⟨z, ?_⟩
  intro k hk
  cases k with
  | ofNat k =>
    have hk' : 0 < k := Nat.pos_of_ne_zero (fun h => hk (by simp [h]))
    exact hpos k hk'
  | negSucc k =>
    have hp : τ.trace (haarCornerPower z (k + 1 : ℕ)) = 0 := hpos (k + 1) (by omega)
    have hstar (x : M.toStarSubalgebra) : τ.trace (star x) = star (τ.trace x) := by
      change inner ℂ τ.vector (star (x : H →L[ℂ] H) τ.vector) =
        star (inner ℂ τ.vector ((x : H →L[ℂ] H) τ.vector))
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        ← inner_conj_symm]
      rfl
    rw [show Int.negSucc k = -((k + 1 : ℕ) : ℤ) by omega,
      ← star_haarCornerPower, hstar, hp, star_zero]

end KadisonSimilarity

end

end OAI
