import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurationsLists

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Finset
attribute [local instance] Classical.propDecidable

abbrev SourceConfiguration (k : ℕ) :=
  (Fin (2*k) → ℤ) × (Fin (k+1) → List ℤ)

def SourceConfiguration.Bounded {k : ℕ} (c : SourceConfiguration k) (M N : ℕ) : Prop :=
  (∀ i, |c.1 i| ≤ (M:ℤ)+1) ∧
    ∀ j, (c.2 j).length ≤ N ∧ ∀ x ∈ c.2 j, |x| ≤ (M:ℤ)+1

abbrev SourceConfigurationCode (k M N : ℕ) :=
  (Fin (2*k) → ↥(configurationAlphabet M)) ×
    (Fin (k+1) → ↥(boundedCellLists (configurationAlphabet M) N))

def SourceConfigurationCode.decode {k M N : ℕ} (c : SourceConfigurationCode k M N) :
    SourceConfiguration k := (fun i => (c.1 i).val, fun j => (c.2 j).val)

def allSourceConfigurations (k M N : ℕ) : Finset (SourceConfiguration k) :=
  univ.image (SourceConfigurationCode.decode (k:=k) (M:=M) (N:=N))

@[simp] theorem mem_allSourceConfigurations (k M N : ℕ) (c : SourceConfiguration k) :
    c ∈ allSourceConfigurations k M N ↔ c.Bounded M N := by
  constructor
  · intro hc
    obtain ⟨d,_,rfl⟩ := mem_image.mp hc
    constructor
    · intro i
      exact (mem_configurationAlphabet M _).mp (d.1 i).property
    · intro j
      have hh := (mem_boundedCellLists _ _ _).mp (d.2 j).property
      exact ⟨hh.1,fun x hx => (mem_configurationAlphabet M x).mp (hh.2 x hx)⟩
  · rintro ⟨ha,hl⟩
    let d : SourceConfigurationCode k M N :=
      (fun i => ⟨c.1 i,(mem_configurationAlphabet M _).mpr (ha i)⟩,
       fun j => ⟨c.2 j,(mem_boundedCellLists _ _ _).mpr
          ⟨(hl j).1,fun x hx => (mem_configurationAlphabet M x).mpr ((hl j).2 x hx)⟩⟩)
    exact mem_image.mpr ⟨d,mem_univ _,rfl⟩

theorem allSourceConfigurations_nonempty (k M N : ℕ) :
    (allSourceConfigurations k M N).Nonempty := by
  refine ⟨(fun _ => 0,fun _ => []),(mem_allSourceConfigurations _ _ _ _).mpr ?_⟩
  constructor
  · intro i
    change |(0:ℤ)| ≤ (M:ℤ)+1
    simp only [abs_zero]
    omega
  · intro j
    simp

theorem allSourceConfigurations_card_le (k M N : ℕ) :
    (allSourceConfigurations k M N).card ≤ (2*M+3)^((k+1)*(N+1)+2*k) := by
  have hl := boundedCellLists_card_add_one (configurationAlphabet M)
    (by simp) N
  rw [configurationAlphabet_card] at hl
  have hc := card_image_le (s := (univ : Finset (SourceConfigurationCode k M N)))
    (f := SourceConfigurationCode.decode)
  have he : Fintype.card (SourceConfigurationCode k M N)=
      (2*M+3)^(2*k)*(boundedCellLists (configurationAlphabet M) N).card^(k+1) := by
    simp [SourceConfigurationCode]
  rw [card_univ,he] at hc
  calc
    _ ≤ (2*M+3)^(2*k)*(boundedCellLists (configurationAlphabet M) N).card^(k+1) := hc
    _ ≤ (2*M+3)^(2*k)*((2*M+3)^(N+1))^(k+1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) (k+1))
    _ = _ := by rw [←pow_mul,←pow_add]; congr 1; ring

end Ostmann.Characters.HigherBiasSource

end

end OAI
