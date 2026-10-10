import OAI.Geometry.PeriodicTiling.ConfigurationDifferences

namespace OAI

universe uG uA uB uι

namespace PeriodicTilingThree

variable {G : Type uG} {A : Type uA} {B : Type uB}
  [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]

theorem configDiffs_eq_iterate_of_period (vs : List G) (v p : G) (f : G → A)
    (hp : Function.Periodic f p)
    (hvs : ∀ u ∈ vs, ∃ k : ℤ, u = v + k • p) :
    configDiffs vs f = (configDiff v)^[vs.length] f := by
  induction vs with
  | nil => rfl
  | cons u vs ih =>
      obtain ⟨k, hk⟩ := hvs u (List.mem_cons_self ..)
      have htail : ∀ w ∈ vs, ∃ k : ℤ, w = v + k • p := by
        intro w hw
        exact hvs w (List.mem_cons_of_mem _ hw)
      have hper := (configDiffs_preserves_period vs p f hp).zsmul k
      rw [configDiffs_cons, hk, configDiff_add_period v (k • p) _ hper,
        ih htail, List.length_cons, Function.iterate_succ_apply']

theorem configDiffs_component_zero {ι : Type uι} [Fintype ι]
    (j : ι) (vs : List G) (hvs : vs ≠ []) (f : ι → G → A) (a : A)
    (hsum : (∑ i, f i) = fun _ => a)
    (hkill : ∀ i, i ≠ j → ∃ v ∈ vs, Function.Periodic (f i) v) :
    configDiffs vs (f j) = 0 := by
  classical
  have hsum' := congrArg (configDiffs vs) hsum
  rw [configDiffs_sum, configDiffs_const hvs] at hsum'
  have hone : (∑ i, configDiffs vs (f i)) = configDiffs vs (f j) := by
    apply Finset.sum_eq_single j
    · intro i _hi hij
      obtain ⟨v, hv, hp⟩ := hkill i hij
      exact configDiffs_eq_zero_of_mem hv (f i)
        ((configDiff_eq_zero_iff v (f i)).mpr hp)
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  rw [hone] at hsum'
  exact hsum'

theorem map_configDiff (φ : A →+ B) (v : G) (f : G → A) :
    (fun x => φ (configDiff v f x)) = configDiff v (fun x => φ (f x)) := by
  ext x
  exact map_sub φ _ _

theorem map_configDiffs (φ : A →+ B) (vs : List G) (f : G → A) :
    (fun x => φ (configDiffs vs f x)) = configDiffs vs (fun x => φ (f x)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      rw [configDiffs_cons, map_configDiff, ih, configDiffs_cons]

end PeriodicTilingThree

end OAI
