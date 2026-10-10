import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodGlobal

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma mesh_driver_estimate (B : Body E) (x₀ : E) (C δ : ℝ)
    (hx₀ : x₀∈B.carrier) (hδ : 0 ≤ δ) (w v : ℝ → E)
    (hc : ∀t∈Icc (0:ℝ) 1,‖v t-w t‖ ≤ δ)
    (N : ℕ) (hN : 0 < N)
    (hvw : variation (regulator B x₀ (sampledDriver w N)) N ≤ C)
    (hvv : variation (regulator B x₀ (sampledDriver v N)) N ≤ C)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    ‖mesh B x₀ v N t-mesh B x₀ w N t‖ ≤ 2*δ+Real.sqrt (8*δ*C) := by
  let p := ⌊t*(N:ℝ)⌋₊
  have hp : p ≤ N := Nat.floor_le_of_le (by nlinarith [ht.2,(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have htime (i : ℕ) (hi : i ≤ N) : (i:ℝ)/N∈Icc (0:ℝ) 1 := by
    refine ⟨by positivity,?_⟩
    rw [div_le_one hN'];exact_mod_cast hi
  have hinput : ∀i ≤ p,‖(x₀+(sampledDriver v N i-sampledDriver v N 0))-
      (x₀+(sampledDriver w N i-sampledDriver w N 0))‖ ≤ 2*δ := by
    intro i hi
    have ha := hc _ (htime i (hi.trans hp))
    have hb := hc 0 ⟨le_rfl,zero_le_one⟩
    have he : (x₀+(sampledDriver v N i-sampledDriver v N 0))-
        (x₀+(sampledDriver w N i-sampledDriver w N 0))=
        (v ((i:ℝ)/N)-w ((i:ℝ)/N))-(v 0-w 0) := by
      simp only [sampledDriver,Nat.cast_zero,zero_div];abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  have hwvar := (variation_mono (regulator B x₀ (sampledDriver w N)) hp).trans hvw
  have hvvar := (variation_mono (regulator B x₀ (sampledDriver v N)) hp).trans hvv
  have hb := walk_driver_stability B x₀ x₀ hx₀ hx₀ (sampledDriver v N) (sampledDriver w N)
    p (2*δ) (by positivity) hinput
  have hs : 2*(2*δ)*(variation (regulator B x₀ (sampledDriver v N)) p+
      variation (regulator B x₀ (sampledDriver w N)) p) ≤ 8*δ*C := by
    nlinarith [mul_le_mul_of_nonneg_left hwvar hδ,mul_le_mul_of_nonneg_left hvvar hδ]
  exact hb.trans (add_le_add le_rfl (Real.sqrt_le_sqrt hs))

end ConvexSkorokhod

end OAI
