import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.StrongContractionLimit

variable {ι H G : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

variable {l : Filter ι}

lemma apply_tendsto (P : ι → H →L[ℂ] G) (Q : H →L[ℂ] G)
    (hP : ∀ i,‖P i‖≤1) (hstrong : ∀ x,Tendsto (fun i => P i x) l (𝓝 (Q x)))
    {u : ι → H} {x : H} (hu : Tendsto u l (𝓝 x)) :
    Tendsto (fun i => P i (u i)) l (𝓝 (Q x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun i => ‖u i-x‖+‖P i x-Q x‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_add] using
      ((hu.sub (tendsto_const_nhds (x := x))).norm.add
        (((hstrong x).sub (tendsto_const_nhds (x := Q x))).norm))
  apply squeeze_zero (fun i => norm_nonneg _) _ hlim
  intro i
  calc
    ‖P i (u i)-Q x‖=‖P i (u i-x)+(P i x-Q x)‖ := by rw [map_sub]; congr 1; abel
    _≤‖P i (u i-x)‖+‖P i x-Q x‖ := norm_add_le _ _
    _≤‖u i-x‖+‖P i x-Q x‖ := by
      apply add_le_add _ le_rfl
      exact ((P i).le_opNorm (u i-x)).trans (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hP i) (norm_nonneg (u i-x)))

lemma sandwich_tendsto (P : ι → H →L[ℂ] H) (hP : ∀ i,‖P i‖≤1)
    (hstrong : ∀ x,Tendsto (fun i => P i x) l (𝓝 x)) (Y : H →L[ℂ] H) (x : H) :
    Tendsto (fun i => (P i*Y*P i) x) l (𝓝 (Y x)) := by
  exact apply_tendsto P (ContinuousLinearMap.id ℂ H) hP hstrong
    (Y.continuous.tendsto x |>.comp (hstrong x))

lemma norm_le_of_strong [l.NeBot] (T : ι → H →L[ℂ] G) (Y : H →L[ℂ] G)
    (hstrong : ∀ x,Tendsto (fun i => T i x) l (𝓝 (Y x))) {C : ℝ} (hC : 0≤C)
    (hbound : ∀ᶠ i in l,‖T i‖≤C) : ‖Y‖≤C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply le_of_tendsto (hstrong x |>.norm)
  filter_upwards [hbound] with i hi
  exact ((T i).le_opNorm x).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg x))

end Kadison.StrongContractionLimit

end

end
end

end OAI
