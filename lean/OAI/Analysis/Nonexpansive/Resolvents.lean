import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Resolvents of an actual nonexpansive selfmap

The affine contraction is constructed on the norm-metric subtype of the
closed convex set. Its fixed point is supplied by the Banach contraction
theorem. The resulting resolvents are nonexpansive in their anchor, have
the exact displacement coefficient `n - 1`, and have defect at most `1/n`
when all distances in the set are at most one.
-/

noncomputable section

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X}

namespace ResolventConstruction

def step (hKconvex : Convex ℝ K) (T : K → K)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (a v : K) : K :=
  ⟨t • (a : X) + (1 - t) • (T v : X),
    hKconvex a.property (T v).property ht (sub_nonneg.mpr ht1) (by ring)⟩

theorem step_contracting (hKconvex : Convex ℝ K) (T : K → K)
    (hT : LipschitzWith 1 T) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (a : K) :
    ContractingWith (⟨1 - t, sub_nonneg.mpr ht1⟩ : NNReal)
      (step hKconvex T t ht.le ht1 a) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  · change 1 - t < 1
    linarith
  · have hTw : ‖(T v : X) - (T w : X)‖ ≤ ‖(v : X) - (w : X)‖ := by
      simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
        using hT.dist_le_mul v w
    simp only [Subtype.dist_eq, dist_eq_norm]
    change ‖(t • (a : X) + (1 - t) • (T v : X)) -
        (t • (a : X) + (1 - t) • (T w : X))‖ ≤
      (1 - t) * ‖(v : X) - (w : X)‖
    rw [show (t • (a : X) + (1 - t) • (T v : X)) -
        (t • (a : X) + (1 - t) • (T w : X)) =
        (1 - t) • ((T v : X) - (T w : X)) by module,
      norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht1)]
    exact mul_le_mul_of_nonneg_left hTw (sub_nonneg.mpr ht1)

variable [CompleteSpace X]

def atWeight (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (a : K) : K :=
  letI : CompleteSpace K := hKclosed.completeSpace_coe
  letI : Nonempty K := ⟨a⟩
  (step_contracting hKconvex T hT t ht ht1 a).fixedPoint
    (step hKconvex T t ht.le ht1 a)

theorem atWeight_equation (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (a : K) :
    (atWeight hKclosed hKconvex T hT t ht ht1 a : X) =
      t • (a : X) + (1 - t) •
        (T (atWeight hKclosed hKconvex T hT t ht ht1 a) : X) := by
  let : CompleteSpace K := hKclosed.completeSpace_coe
  let : Nonempty K := ⟨a⟩
  have hf := (step_contracting hKconvex T hT t ht ht1 a).fixedPoint_isFixedPt
  exact (congrArg Subtype.val hf).symm

theorem atWeight_unique (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (a v : K)
    (hv : (v : X) = t • (a : X) + (1 - t) • (T v : X)) :
    v = atWeight hKclosed hKconvex T hT t ht ht1 a := by
  let : CompleteSpace K := hKclosed.completeSpace_coe
  let : Nonempty K := ⟨a⟩
  apply (step_contracting hKconvex T hT t ht ht1 a).fixedPoint_unique
  apply Subtype.ext
  exact hv.symm

theorem atWeight_nonexpansive (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    LipschitzWith 1 (atWeight hKclosed hKconvex T hT t ht ht1) := by
  apply LipschitzWith.mk_one
  intro a b
  let v := atWeight hKclosed hKconvex T hT t ht ht1 a
  let w := atWeight hKclosed hKconvex T hT t ht ht1 b
  have hv := atWeight_equation hKclosed hKconvex T hT t ht ht1 a
  have hw := atWeight_equation hKclosed hKconvex T hT t ht ht1 b
  have hid : (v : X) - (w : X) =
      t • ((a : X) - (b : X)) + (1 - t) • ((T v : X) - (T w : X)) := by
    calc
      (v : X) - (w : X) =
          (t • (a : X) + (1 - t) • (T v : X)) -
            (t • (b : X) + (1 - t) • (T w : X)) := congrArg₂ (· - ·) hv hw
      _ = _ := by module
  have hTw : ‖(T v : X) - (T w : X)‖ ≤ ‖(v : X) - (w : X)‖ := by
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
      using hT.dist_le_mul v w
  have hbound : ‖(v : X) - (w : X)‖ ≤
      t * ‖(a : X) - (b : X)‖ + (1 - t) * ‖(v : X) - (w : X)‖ := by
    calc
      ‖(v : X) - (w : X)‖ =
          ‖t • ((a : X) - (b : X)) + (1 - t) • ((T v : X) - (T w : X))‖ :=
        congrArg norm hid
      _ ≤ ‖t • ((a : X) - (b : X))‖ +
          ‖(1 - t) • ((T v : X) - (T w : X))‖ := norm_add_le _ _
      _ = t * ‖(a : X) - (b : X)‖ +
          (1 - t) * ‖(T v : X) - (T w : X)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le,
          Real.norm_of_nonneg (sub_nonneg.mpr ht1)]
      _ ≤ _ := add_le_add_right
        (mul_le_mul_of_nonneg_left hTw (sub_nonneg.mpr ht1)) _
  change dist (v : X) (w : X) ≤ dist (a : X) (b : X)
  simp only [dist_eq_norm]
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith

theorem atWeight_defect_le (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (a : K) :
    ‖(T (atWeight hKclosed hKconvex T hT t ht ht1 a) : X) -
      (atWeight hKclosed hKconvex T hT t ht ht1 a : X)‖ ≤ t := by
  let v := atWeight hKclosed hKconvex T hT t ht ht1 a
  have hv := atWeight_equation hKclosed hKconvex T hT t ht ht1 a
  have hid : (T v : X) - (v : X) = t • ((T v : X) - (a : X)) := by
    calc
      (T v : X) - (v : X) =
          (T v : X) - (t • (a : X) + (1 - t) • (T v : X)) :=
        congrArg (fun z : X => (T v : X) - z) hv
      _ = _ := by module
  change ‖(T v : X) - (v : X)‖ ≤ t
  rw [hid, norm_smul, Real.norm_of_nonneg ht.le]
  exact (mul_le_mul_of_nonneg_left (hdiam (T v) a) ht.le).trans_eq (mul_one t)

theorem atWeight_displacement_le (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (a : K) :
    ‖(atWeight hKclosed hKconvex T hT t ht ht1 a : X) - (a : X)‖ ≤
      ((1 - t) / t) * ‖(T a : X) - (a : X)‖ := by
  let v := atWeight hKclosed hKconvex T hT t ht ht1 a
  have hv := atWeight_equation hKclosed hKconvex T hT t ht ht1 a
  have hid : (v : X) - (a : X) =
      (1 - t) • (((T v : X) - (T a : X)) + ((T a : X) - (a : X))) := by
    calc
      (v : X) - (a : X) =
          (t • (a : X) + (1 - t) • (T v : X)) - (a : X) :=
        congrArg (fun z : X => z - (a : X)) hv
      _ = _ := by module
  have hTa : ‖(T v : X) - (T a : X)‖ ≤ ‖(v : X) - (a : X)‖ := by
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
      using hT.dist_le_mul v a
  have hbound : ‖(v : X) - (a : X)‖ ≤
      (1 - t) * (‖(v : X) - (a : X)‖ + ‖(T a : X) - (a : X)‖) := by
    calc
      ‖(v : X) - (a : X)‖ =
          (1 - t) * ‖((T v : X) - (T a : X)) + ((T a : X) - (a : X))‖ := by
        rw [hid, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht1)]
      _ ≤ (1 - t) * (‖(T v : X) - (T a : X)‖ + ‖(T a : X) - (a : X)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (sub_nonneg.mpr ht1)
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_left hTa _)
        (sub_nonneg.mpr ht1)
  have hquot : ‖(v : X) - (a : X)‖ ≤
      ((1 - t) * ‖(T a : X) - (a : X)‖) / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  simpa only [div_mul_eq_mul_div] using hquot

theorem weight_pos (n : ℕ) (hn : 1 ≤ n) : 0 < (n : ℝ)⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact inv_pos.mpr hn'

theorem weight_le_one (n : ℕ) (hn : 1 ≤ n) : (n : ℝ)⁻¹ ≤ 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn'

end ResolventConstruction

variable [CompleteSpace X]

def resolvent (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) (n : ℕ) (hn : 1 ≤ n) : K → K :=
  ResolventConstruction.atWeight hKclosed hKconvex T hT (n : ℝ)⁻¹
    (ResolventConstruction.weight_pos n hn) (ResolventConstruction.weight_le_one n hn)

theorem resolvent_equation (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) (n : ℕ) (hn : 1 ≤ n) (a : K) :
    (resolvent hKclosed hKconvex T hT n hn a : X) =
      (n : ℝ)⁻¹ • (a : X) + (1 - (n : ℝ)⁻¹) •
        (T (resolvent hKclosed hKconvex T hT n hn a) : X) :=
  ResolventConstruction.atWeight_equation hKclosed hKconvex T hT _ _ _ a

theorem resolvent_unique (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) (n : ℕ) (hn : 1 ≤ n) (a v : K)
    (hv : (v : X) = (n : ℝ)⁻¹ • (a : X) + (1 - (n : ℝ)⁻¹) • (T v : X)) :
    v = resolvent hKclosed hKconvex T hT n hn a :=
  ResolventConstruction.atWeight_unique hKclosed hKconvex T hT _ _ _ a v hv

theorem resolvent_one (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) :
    resolvent hKclosed hKconvex T hT 1 (by decide) = id := by
  funext a
  apply Subtype.ext
  simpa using resolvent_equation hKclosed hKconvex T hT 1 (by decide) a

theorem resolvent_nonexpansive (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) (n : ℕ) (hn : 1 ≤ n) :
    LipschitzWith 1 (resolvent hKclosed hKconvex T hT n hn) :=
  ResolventConstruction.atWeight_nonexpansive hKclosed hKconvex T hT _ _ _

theorem resolvent_defect_le (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (a : K) :
    ‖(T (resolvent hKclosed hKconvex T hT n hn a) : X) -
      (resolvent hKclosed hKconvex T hT n hn a : X)‖ ≤ 1 / (n : ℝ) := by
  simpa only [resolvent, one_div] using
    ResolventConstruction.atWeight_defect_le hKclosed hKconvex T hT hdiam
      (n : ℝ)⁻¹ (ResolventConstruction.weight_pos n hn)
      (ResolventConstruction.weight_le_one n hn) a

theorem resolvent_displacement_le (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) (n : ℕ) (hn : 1 ≤ n) (a : K) :
    ‖(resolvent hKclosed hKconvex T hT n hn a : X) - (a : X)‖ ≤
      ((n : ℝ) - 1) * ‖(T a : X) - (a : X)‖ := by
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn) : (0 : ℝ) < n)
  have hcoeff : (1 - (n : ℝ)⁻¹) / (n : ℝ)⁻¹ = (n : ℝ) - 1 := by
    rw [div_inv_eq_mul, sub_mul, one_mul, inv_mul_cancel₀ hn0]
  simpa only [resolvent, hcoeff] using
    ResolventConstruction.atWeight_displacement_le hKclosed hKconvex T hT
      (n : ℝ)⁻¹ (ResolventConstruction.weight_pos n hn)
      (ResolventConstruction.weight_le_one n hn) a

end ReflexiveFixedPoints

end

end OAI
