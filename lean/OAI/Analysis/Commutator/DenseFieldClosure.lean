import Mathlib
import OAI.Analysis.Commutator.WeakOperatorAlgebra
import OAI.Analysis.Commutator.WeakOperatorLimit

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_vonNeumann_of_dense_finite_tests (Q : VonNeumannAlgebra H)
    (v : ℕ → H) (hv : DenseRange v) (T : H →L[ℂ] H) (b : ℝ) (hb : 0≤b)
    (ha : ∀ m : ℕ,∃ A : H →L[ℂ] H,A∈Q ∧ ‖A‖≤b ∧
      ∀ j : Fin m,‖A (v j)-T (v j)‖≤1/((m:ℝ)+1)) : T∈Q := by
  choose A hAQ hAb hA using ha
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le _
  obtain ⟨W,hW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω A b hb hAb
  have hWQ : W∈Q := WeakOperatorLimit.mem_vonNeumann hlim Q (Eventually.of_forall hAQ)
  have htest (j : ℕ) : W (v j)=T (v j) := by
    have hn : Tendsto (fun m => ‖A m (v j)-T (v j)‖) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
        tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop (j+1)] with m hm
      exact hA m ⟨j,by omega⟩
    have hl : Tendsto (fun m => A m (v j)) atTop (𝓝 (T (v j))) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr hn
    apply ext_inner_right ℂ
    intro y
    exact tendsto_nhds_unique (hlim (v j) y)
      (((continuous_id.inner continuous_const).tendsto (T (v j))).comp (hl.mono_left hω))
  have he : W=T := ContinuousLinearMap.ext (fun x => hv.induction_on x
    (isClosed_eq W.continuous T.continuous) htest)
  rwa [he] at hWQ

end Kadison

end

end
end

end OAI
