import OAI.Analysis.Pureness.Traces.DimensionContent
import OAI.Analysis.Pureness.Operators.ContinuousOrthogonalSeparation

namespace OAI
noncomputable section
namespace CuntzPureness
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal
variable {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]

lemma dimensionCompactCapacity_sup_disjoint (r : C(X, ℝ≥0) → ℝ≥0∞)
    (hmono : Monotone r) (hsub : ∀ f g, r (f+g) ≤ r f+r g)
    (horth : ∀ f g, f*g = 0 → r (f+g) = r f+r g)
    (K L : Compacts X) (hKL : Disjoint (K : Set X) L) :
    dimensionCompactCapacity r (K ⊔ L) = dimensionCompactCapacity r K + dimensionCompactCapacity r L := by
  apply le_antisymm (dimensionCompactCapacity_sup_le r hsub K L)
  obtain ⟨u,v,hu,hv,hu1,hv1,huv⟩ := continuous_nnreal_orthogonal_separators K.isCompact.isClosed L.isCompact.isClosed hKL
  apply le_iInf₂
  intro f hf
  have hfu : ∀ x ∈ K, 1 ≤ (f*u) x := by
    intro x hx
    simpa only [ContinuousMap.mul_apply,hu x hx,mul_one] using hf x (Or.inl hx)
  have hfv : ∀ x ∈ L, 1 ≤ (f*v) x := by
    intro x hx
    simpa only [ContinuousMap.mul_apply,hv x hx,mul_one] using hf x (Or.inr hx)
  have huv1 : u+v ≤ 1 := by
    intro x
    change u x+v x ≤ 1
    have hz : u x*v x = 0 := congrArg (fun g : C(X, ℝ≥0) => g x) huv
    rcases mul_eq_zero.mp hz with hz | hz
    · rw [hz,zero_add]
      exact hv1 x
    · rw [hz,add_zero]
      exact hu1 x
  have horth' : (f*u)*(f*v) = 0 := by
    calc
      (f*u)*(f*v) = (f*f)*(u*v) := by ring
      _ = 0 := by rw [huv,mul_zero]
  calc
    dimensionCompactCapacity r K + dimensionCompactCapacity r L ≤ r (f*u)+r (f*v) :=
      add_le_add (dimensionCompactCapacity_le r K (f*u) hfu) (dimensionCompactCapacity_le r L (f*v) hfv)
    _ = r (f*u+f*v) := (horth (f*u) (f*v) horth').symm
    _ ≤ r f := hmono (by
      intro x
      change f x*u x+f x*v x ≤ f x
      have h := mul_le_mul_of_nonneg_left (huv1 x) (show 0 ≤ f x from bot_le)
      change f x*(u x+v x) ≤ f x*1 at h
      simpa only [mul_add,mul_one] using h)

def dimensionContent (r : C(X, ℝ≥0) → ℝ≥0∞) (hfinite : r 1 ≠ ⊤)
    (hmono : Monotone r) (hsub : ∀ f g, r (f+g) ≤ r f+r g)
    (horth : ∀ f g, f*g = 0 → r (f+g) = r f+r g) : Content X where
  toFun K := (dimensionCompactCapacity r K).toNNReal
  mono' K L h := ENNReal.toNNReal_mono (dimensionCompactCapacity_ne_top r hfinite L)
    (dimensionCompactCapacity_mono r h)
  sup_disjoint' K L h _ _ := by
    rw [dimensionCompactCapacity_sup_disjoint r hmono hsub horth K L h,
      ENNReal.toNNReal_add (dimensionCompactCapacity_ne_top r hfinite K) (dimensionCompactCapacity_ne_top r hfinite L)]
  sup_le' K L := by
    rw [← ENNReal.toNNReal_add (dimensionCompactCapacity_ne_top r hfinite K) (dimensionCompactCapacity_ne_top r hfinite L)]
    exact ENNReal.toNNReal_mono (ENNReal.add_ne_top.mpr ⟨dimensionCompactCapacity_ne_top r hfinite K,
      dimensionCompactCapacity_ne_top r hfinite L⟩) (dimensionCompactCapacity_sup_le r hsub K L)

lemma dimensionContent_apply (r : C(X, ℝ≥0) → ℝ≥0∞) (hfinite : r 1 ≠ ⊤)
    (hmono : Monotone r) (hsub : ∀ f g, r (f+g) ≤ r f+r g)
    (horth : ∀ f g, f*g = 0 → r (f+g) = r f+r g) (K : Compacts X) :
    dimensionContent r hfinite hmono hsub horth K = dimensionCompactCapacity r K :=
  ENNReal.coe_toNNReal (dimensionCompactCapacity_ne_top r hfinite K)
end CuntzPureness

end

end OAI
