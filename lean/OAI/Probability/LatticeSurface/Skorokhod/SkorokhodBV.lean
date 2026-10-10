import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodRegularitySupport

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma eVariation_discrete (k : ℕ → E) (N : ℕ) :
    eVariationOn k (Iic N)=ENNReal.ofReal (variation k N) := by
  have hh := eVariationOn.image_range_of_monotone k (u:=id) monotone_id N
  simp only [id_eq, Set.image_id'] at hh
  rw [hh,variation,ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [edist_dist,dist_eq_norm,norm_sub_rev]

lemma mesh_regulator_variation (B : Body E) (x₀ c : E) (r : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0 < r) (hball : Metric.closedBall c r⊆B.carrier)
    (w : ℝ → E) (hosc : ∀t∈Icc (0:ℝ) 1,‖w t-w 0‖ ≤ r/2) (N : ℕ) (hN : 0 < N) :
    eVariationOn (fun t : ℝ => regulator B x₀ (sampledDriver w N) ⌊t*N⌋₊) (Icc (0:ℝ) 1) ≤
      ENNReal.ofReal (‖x₀-c‖^2/r) := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hb := regulator_variation_bound B x₀ c r ‖x₀-c‖ hx₀ hr le_rfl hball (sampledDriver w N) N
    (by
      intro i hi
      simp only [sampledDriver,Nat.cast_zero,zero_div]
      apply hosc
      refine ⟨by positivity,?_⟩
      rw [div_le_one hN'];exact_mod_cast hi)
  have hh := eVariationOn.comp_le_of_monotoneOn (regulator B x₀ (sampledDriver w N))
    (fun t : ℝ => ⌊t*N⌋₊) (s:=Iic N) (t:=Icc (0:ℝ) 1)
    (by intro s hs t ht hst;exact Nat.floor_mono (mul_le_mul_of_nonneg_right hst hN'.le))
    (by intro t ht;apply Nat.floor_le_of_le; nlinarith [ht.2])
  exact hh.trans ((eVariation_discrete _ _).le.trans (ENNReal.ofReal_le_ofReal hb))

end ConvexSkorokhod

end OAI
