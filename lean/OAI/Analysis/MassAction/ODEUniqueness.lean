import Mathlib

namespace OAI

universe uE

open Set Filter
open scoped Topology

namespace Problem326

section AutonomousODE
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : E → E} {f g : ℝ → E} {a b : ℝ}

/-- The ODE and continuity extend the derivative to the initial endpoint. -/
theorem hasDerivWithinAt_initial_of_ode
    (hv : Continuous v) (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v (f t)) t) :
    HasDerivWithinAt f (v (f a)) (Ici a) a := by
  have hc : ContinuousWithinAt f (Ioo a b) a :=
    (hf a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
  have hc' : ContinuousWithinAt f (Ioi a) a :=
    hc.mono_of_mem_nhdsWithin (Ioo_mem_nhdsGT hab)
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun t ht => (hf' t ht).differentiableAt.differentiableWithinAt)
    hc (Ioo_mem_nhdsGT hab)
  have heq : (fun t => v (f t)) =ᶠ[𝓝[>] a] deriv f := by
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    exact (hf' t ht).deriv.symm
  exact Filter.Tendsto.congr' heq (hv.continuousAt.tendsto.comp hc')

/-- Uniqueness on a closed interval only requires the ODE on its interior. -/
theorem eqOn_Icc_of_locallyLipschitz_ode
    (hv : LocallyLipschitz v) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v (f t)) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v (g t)) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    simpa only [Icc_self, eqOn_singleton] using ha
  let S := (f '' Icc a b) ∪ (g '' Icc a b)
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn hf).union
      (isCompact_Icc.image_of_continuousOn hg)
  obtain ⟨K, hK⟩ := hv.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
  have hfa := hasDerivWithinAt_initial_of_ode hv.continuous hab hf hf'
  have hga := hasDerivWithinAt_initial_of_ode hv.continuous hab hg hg'
  apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => v) (s := fun _ => S)
    (K := K) (fun _ _ => hK) hf ?_ ?_ hg ?_ ?_ ha
  · intro t ht
    by_cases hta : t = a
    · simpa only [hta] using hfa
    · exact (hf' t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2⟩).hasDerivWithinAt
  · intro t ht
    exact Or.inl (mem_image_of_mem f ⟨ht.1, ht.2.le⟩)
  · intro t ht
    by_cases hta : t = a
    · simpa only [hta] using hga
    · exact (hg' t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2⟩).hasDerivWithinAt
  · intro t ht
    exact Or.inr (mem_image_of_mem g ⟨ht.1, ht.2.le⟩)

end AutonomousODE
end Problem326

end OAI
