import Mathlib

namespace OAI

noncomputable section

namespace KKFiniteMomentNet

noncomputable section

open Filter

open scoped Topology

variable {S T : Type*}

theorem finite_moment_net (Good : S → Prop) (f : T → S → ℂ)
    (h : ∀K:Finset T, ∀ε:ℝ,0<ε → ∃s,Good s ∧ ∀t∈K,‖f t s‖<ε) :
    ∃u : (Finset T×ℕ) → S, (∀j,Good (u j)) ∧
      ∀t,Tendsto (fun j => f t (u j)) atTop (𝓝 0) := by
  classical
  have hw (j : Finset T×ℕ) : ∃s,Good s ∧ ∀t∈j.1,‖f t s‖<1/((j.2:ℝ)+1) :=
    h j.1 _ (by positivity)
  choose u hu using hw
  refine ⟨u,fun j => (hu j).1,?_⟩
  intro t
  have hsnd : Tendsto (fun j : Finset T×ℕ => j.2) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact eventually_atTop.2 ⟨(∅,n),fun _ h => h.2⟩
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd)
  exact eventually_atTop.2 ⟨({t},0),fun j hj => ((hu j).2 t (hj.1 (by simp))).le⟩

end

end KKFiniteMomentNet
end

end OAI
