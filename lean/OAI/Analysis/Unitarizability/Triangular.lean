import OAI.Analysis.Unitarizability.Model
import OAI.Analysis.Unitarizability.Cocycle
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.lpHolder

namespace OAI

/-! Bounded Hilbert sums and triangular representations. -/
noncomputable section
namespace Dixmier
namespace Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
abbrev Double (H : Type*) := WithLp 2 (H × H)

def inl : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H H)

def inr : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ H H)

@[simp] theorem inl_apply (x : H) : inl x = WithLp.toLp 2 (x,0) := rfl
@[simp] theorem inr_apply (x : H) : inr x = WithLp.toLp 2 (0,x) := rfl
@[simp] theorem inl_norm (x : H) : ‖inl x‖ = ‖x‖ := WithLp.norm_toLp_fst 2 H H x
@[simp] theorem inr_norm (x : H) : ‖inr x‖ = ‖x‖ := WithLp.norm_toLp_snd 2 H H x

def diagonal (U : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  inl.comp (U.comp (WithLp.fstL 2 ℂ H H)) +
    inr.comp (U.comp (WithLp.sndL 2 ℂ H H))

@[simp] theorem diagonal_fst (U : H →L[ℂ] H) (x : Double H) :
    (diagonal U x).fst = U x.fst := by simp [diagonal, inl, inr]
@[simp] theorem diagonal_snd (U : H →L[ℂ] H) (x : Double H) :
    (diagonal U x).snd = U x.snd := by simp [diagonal, inl, inr]

def operator (U D : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  diagonal U + inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H)))

@[simp] theorem operator_fst (U D : H →L[ℂ] H) (x : Double H) :
    (operator U D x).fst = U x.fst + D (U x.snd) := by simp [operator, inl]
@[simp] theorem operator_snd (U D : H →L[ℂ] H) (x : Double H) :
    (operator U D x).snd = U x.snd := by simp [operator, inl]

theorem diagonal_norm_map (U : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) (x : Double H) :
    ‖diagonal U x‖ = ‖x‖ := by
  have h : ‖diagonal U x‖^2 = ‖x‖^2 := by
    simp only [WithLp.prod_norm_sq_eq_of_L2, diagonal_fst, diagonal_snd, hU]
  nlinarith [norm_nonneg (diagonal U x), norm_nonneg x]

theorem operator_norm_le (U D : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) :
    ‖operator U D‖ ≤ 1 + ‖D‖ := by
  have hd : ‖diagonal U‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp [diagonal_norm_map U hU]
  have hn : ‖inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H)))‖ ≤ ‖D‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
    intro x
    change ‖inl (D (U x.snd))‖ ≤ ‖D‖ * ‖x‖
    rw [inl_norm]
    calc
      ‖D (U x.snd)‖ ≤ ‖D‖ * ‖U x.snd‖ := D.le_opNorm _
      _ = ‖D‖ * ‖x.snd‖ := by rw [hU]
      _ ≤ ‖D‖ * ‖x‖ := mul_le_mul_of_nonneg_left (WithLp.norm_snd_le H x) (norm_nonneg D)
  exact (norm_add_le (diagonal U) (inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H))))).trans
    (add_le_add hd hn)

@[simp] theorem inv_apply (U : G →* (H →L[ℂ] H)) (g : G) (x : H) : U g⁻¹ (U g x) = x := by
  have h : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  exact congrArg (fun T : H →L[ℂ] H => T x) h

def representation (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h)) :
    G →* (Double H →L[ℂ] Double H) where
  toFun g := operator (U g) (D g)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp [h1]
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext
    · change (operator (U (g*h)) (D (g*h)) x).fst =
        (operator (U g) (D g) (operator (U h) (D h) x)).fst
      simp only [operator_fst, operator_snd, map_mul, hD, conjugate,
        add_apply, mul_apply_eq_comp, map_add, inv_apply]
      abel
    · simp [map_mul, mul_apply_eq_comp]

theorem representation_bound (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) {κ : ℝ} (hb : ∀ g, ‖D g‖ ≤ κ) (g : G) :
    ‖representation U D h1 hD g‖ ≤ 1 + κ :=
  (operator_norm_le (U g) (D g) (hU g)).trans (add_le_add (le_refl _) (hb g))

end Triangular
end Dixmier

end

end OAI
