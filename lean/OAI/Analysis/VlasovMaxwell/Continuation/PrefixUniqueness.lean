import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.FiniteUniqueness

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma SmoothClassicalPrefix.mono {d : Datum} {s : Solution} {T H : ℝ}
    (hs : SmoothClassicalPrefix d s H) (hTH : T ≤ H) : SmoothClassicalPrefix d s T := by
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 H := Icc_subset_Icc_right hTH
  refine ⟨hs.f_smooth.mono (fun p hp => hsub hp),hs.E_smooth.mono (fun p hp => hsub hp),
    hs.B_smooth.mono (fun p hp => hsub hp),fun t ht => hs.nonnegative t (hsub ht),?_,?_,?_,
    fun t ht htT => hs.equations t ht (htT.trans_le hTH),hs.initial_f,hs.initial_E,hs.initial_B⟩
  · obtain ⟨F,hc,he⟩ := hs.E_L2
    exact ⟨F,hc.mono hsub,fun t ht => he t (hsub ht)⟩
  · obtain ⟨F,hc,he⟩ := hs.B_L2
    exact ⟨F,hc.mono hsub,fun t ht => he t (hsub ht)⟩
  · obtain ⟨K,hK,hk⟩ := hs.compact
    exact ⟨K,hK,fun t ht => hk t (hsub ht)⟩

lemma SmoothClassicalPrefix.unique_lt {d : Datum} {s₁ s₂ : Solution} {H₁ H₂ t : ℝ}
    (h₁ : SmoothClassicalPrefix d s₁ H₁) (h₂ : SmoothClassicalPrefix d s₂ H₂)
    (ht : 0 ≤ t) (ht₁ : t < H₁) (ht₂ : t < H₂) :
    (∀ z, s₁.f (t,z)=s₂.f (t,z)) ∧ (∀ x, s₁.E (t,x)=s₂.E (t,x)) ∧
      (∀ x, s₁.B (t,x)=s₂.B (t,x)) := by
  obtain ⟨τ,htτ,hτ⟩ := exists_between (lt_min ht₁ ht₂)
  have hτ₁ := hτ.trans_le (min_le_left _ _)
  have hτ₂ := hτ.trans_le (min_le_right _ _)
  have he := classical_unique_before
    (h₁.cutoff_classical_before (ht.trans htτ.le) hτ₁)
    (h₂.cutoff_classical_before (ht.trans htτ.le) hτ₂) ht htτ.le
  have he₁ := cutoffPrefix_eq hτ₁ htτ.le s₁
  have he₂ := cutoffPrefix_eq hτ₂ htτ.le s₂
  exact ⟨fun z => (he₁.1 z).symm.trans ((he.1 z).trans (he₂.1 z)),
    fun x => (he₁.2.1 x).symm.trans ((he.2.1 x).trans (he₂.2.1 x)),
    fun x => (he₁.2.2 x).symm.trans ((he.2.2 x).trans (he₂.2.2 x))⟩

theorem SmoothClassicalPrefix.unique {d : Datum} {s₁ s₂ : Solution} {H₁ H₂ t : ℝ}
    (h₁ : SmoothClassicalPrefix d s₁ H₁) (h₂ : SmoothClassicalPrefix d s₂ H₂)
    (ht : 0 ≤ t) (ht₁ : t ≤ H₁) (ht₂ : t ≤ H₂) :
    (∀ z, s₁.f (t,z)=s₂.f (t,z)) ∧ (∀ x, s₁.E (t,x)=s₂.E (t,x)) ∧
      (∀ x, s₁.B (t,x)=s₂.B (t,x)) := by
  rcases ht.eq_or_lt with rfl | ht
  · exact ⟨fun z => (h₁.initial_f z).trans (h₂.initial_f z).symm,
      fun x => (h₁.initial_E x).trans (h₂.initial_E x).symm,
      fun x => (h₁.initial_B x).trans (h₂.initial_B x).symm⟩
  have hp : ∀ r∈Ico (0:ℝ) t,
      (∀ z, s₁.f (r,z)=s₂.f (r,z)) ∧ (∀ x, s₁.E (r,x)=s₂.E (r,x)) ∧
        (∀ x, s₁.B (r,x)=s₂.B (r,x)) :=
    fun r hr => h₁.unique_lt h₂ hr.1 (hr.2.trans_le ht₁) (hr.2.trans_le ht₂)
  have hcl : Icc (0:ℝ) t ⊆ closure (Ico 0 t) := by rw [closure_Ico ht.ne]
  have h₁r := h₁.mono ht₁
  have h₂r := h₂.mono ht₂
  refine ⟨?_,?_,?_⟩
  · intro z
    exact (Set.EqOn.of_subset_closure (fun r hr => (hp r hr).1 z)
      (h₁r.f_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      (h₂r.f_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      Ico_subset_Icc_self hcl) ⟨ht.le,le_rfl⟩
  · intro x
    exact (Set.EqOn.of_subset_closure (fun r hr => (hp r hr).2.1 x)
      (h₁r.E_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      (h₂r.E_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      Ico_subset_Icc_self hcl) ⟨ht.le,le_rfl⟩
  · intro x
    exact (Set.EqOn.of_subset_closure (fun r hr => (hp r hr).2.2 x)
      (h₁r.B_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      (h₂r.B_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      Ico_subset_Icc_self hcl) ⟨ht.le,le_rfl⟩

end RVM
end

end OAI
