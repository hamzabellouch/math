import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurationsFinite
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurationsScale

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Finset Filter
attribute [local instance] Classical.propDecidable

theorem exists_fixed_source_configuration {α : Type*} [DecidableEq α]
    (k M N : ℕ) (H : Finset α) (f : α → SourceConfiguration k)
    (hf : ∀ x ∈ H, (f x).Bounded M N) :
    ∃ c : SourceConfiguration k, ∃ H0 : Finset α,
      c.Bounded M N ∧ H0 ⊆ H ∧ (∀ x ∈ H0, f x=c) ∧
      H.card ≤ (2*M+3)^((k+1)*(N+1)+2*k)*H0.card := by
  let S := allSourceConfigurations k M N
  have hS : S.Nonempty := allSourceConfigurations_nonempty k M N
  have hcard : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
  have hmap : ∀ x ∈ H, f x ∈ S := fun x hx =>
    (mem_allSourceConfigurations k M N (f x)).mpr (hf x hx)
  have hav : S.card • ((H.card:ℝ)/(S.card:ℝ)) ≤ (H.card:ℝ) := by
    rw [nsmul_eq_mul]
    have he : (S.card:ℝ)*((H.card:ℝ)/(S.card:ℝ))=(H.card:ℝ) := by
      field_simp [ne_of_gt hcard]
    exact he.le
  obtain ⟨c,hc,hcav⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmap hS hav
  refine ⟨c,H.filter (fun x => f x=c),(mem_allSourceConfigurations k M N c).mp hc,
    filter_subset _ _,fun x hx => (mem_filter.mp hx).2,?_⟩
  have hh : H.card ≤ S.card*(H.filter (fun x => f x=c)).card := by
    have hh' := (div_le_iff₀ hcard).mp hcav
    exact_mod_cast (show (H.card:ℝ) ≤ (S.card:ℝ)*(H.filter (fun x => f x=c)).card by
      simpa only [mul_comm] using hh')
  exact hh.trans (Nat.mul_le_mul_right _ (allSourceConfigurations_card_le k M N))

theorem eventually_fixed_source_configuration (β : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ {α : Type*} [DecidableEq α] (k N : ℕ)
      (H : Finset α) (f : α → SourceConfiguration k),
      (∀ x ∈ H,(f x).Bounded ⌊Real.exp (β*L)⌋₊ N) →
      ∃ c : SourceConfiguration k, ∃ H0 : Finset α,
        c.Bounded ⌊Real.exp (β*L)⌋₊ N ∧ H0 ⊆ H ∧
        (∀ x ∈ H0,f x=c) ∧
        (H.card:ℝ) ≤ Real.exp (configurationCountCoefficient β*((k+1)*(N+1)+2*k)*L)*H0.card := by
  filter_upwards [eventually_configuration_count_bound β] with L hL
  intro α inst k N H f hf
  obtain ⟨c,H0,hc,hsub,heq,hcard⟩ := exists_fixed_source_configuration
    k ⌊Real.exp (β*L)⌋₊ N H f hf
  refine ⟨c,H0,hc,hsub,heq,?_⟩
  have hh : (H.card:ℝ) ≤ (((2*⌊Real.exp (β*L)⌋₊+3)^((k+1)*(N+1)+2*k):ℕ):ℝ)*(H0.card:ℝ) :=
    by exact_mod_cast hcard
  exact hh.trans (mul_le_mul_of_nonneg_right (hL k N) (Nat.cast_nonneg _))

end Ostmann.Characters.HigherBiasSource

end

end OAI
