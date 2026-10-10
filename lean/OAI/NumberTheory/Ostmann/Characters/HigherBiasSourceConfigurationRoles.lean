import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellsBounded
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurations

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open scoped BigOperators

def configurationIndices {k : ℕ} (cfg : SourceConfiguration k) : List ℤ :=
  List.ofFn cfg.1 ++ (List.ofFn cfg.2).flatten

def configCellCount {k : ℕ} (cfg : SourceConfiguration k) : ℕ :=
  (configurationIndices cfg).length

def configCellIndices {k : ℕ} (cfg : SourceConfiguration k) : Fin (configCellCount cfg) → ℤ :=
  (configurationIndices cfg).get

@[simp] theorem configCellCount_eq {k : ℕ} (cfg : SourceConfiguration k) :
    configCellCount cfg = 2*k + ∑ j, (cfg.2 j).length := by
  simp only [configCellCount, configurationIndices, List.length_append, List.length_ofFn,
    List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def]

@[simp] theorem configurationIndices_sum {k : ℕ} (cfg : SourceConfiguration k) :
    (configurationIndices cfg).sum = (∑ i, cfg.1 i) + ∑ j, (cfg.2 j).sum := by
  simp only [configurationIndices, List.sum_append, List.sum_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem configCellIndices_sum {k : ℕ} (cfg : SourceConfiguration k) :
    (∑ i, (configCellIndices cfg i : ℝ)) =
      (∑ i, (cfg.1 i : ℝ)) + ∑ j, ((cfg.2 j).sum : ℝ) := by
  have hz : (∑ i, configCellIndices cfg i) =
      (∑ i, cfg.1 i) + ∑ j, (cfg.2 j).sum := by
    change (∑ i : Fin (configurationIndices cfg).length, (configurationIndices cfg).get i) = _
    rw [← List.sum_ofFn, List.ofFn_get]
    exact configurationIndices_sum cfg
  exact_mod_cast hz

@[simp] theorem mem_configurationIndices {k : ℕ} (cfg : SourceConfiguration k) (a : ℤ) :
    a ∈ configurationIndices cfg ↔ (∃ i, cfg.1 i = a) ∨ ∃ j, a ∈ cfg.2 j := by
  simp only [configurationIndices, List.mem_append, List.mem_ofFn, List.mem_flatten]
  constructor
  · rintro (ha | ⟨l, ⟨j,rfl⟩, hl⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨j,hl⟩
  · rintro (ha | ⟨j,hj⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨cfg.2 j,⟨j,rfl⟩,hj⟩

theorem configCellIndices_range {k : ℕ} (cfg : SourceConfiguration k) (a : ℤ) :
    (∃ i, configCellIndices cfg i = a) ↔
      (∃ i, cfg.1 i = a) ∨ ∃ j, a ∈ cfg.2 j := by
  rw [← mem_configurationIndices]
  exact List.mem_iff_get.symm

theorem configCellIndices_property {k : ℕ} (cfg : SourceConfiguration k) (P : ℤ → Prop)
    (ha : ∀ i, P (cfg.1 i)) (hl : ∀ j, ∀ a ∈ cfg.2 j, P a) :
    ∀ i, P (configCellIndices cfg i) := by
  intro i
  rcases (configCellIndices_range cfg _).mp ⟨i,rfl⟩ with ⟨a,ha'⟩ | ⟨j,hj⟩
  · simpa only [ha'] using ha a
  · exact hl j _ hj

theorem configCellIndices_anchor {k : ℕ} (cfg : SourceConfiguration k) (a : Fin (2*k)) :
    ∃ i, configCellIndices cfg i = cfg.1 a :=
  (configCellIndices_range cfg _).mpr (Or.inl ⟨a,rfl⟩)

theorem configCellIndices_list {k : ℕ} (cfg : SourceConfiguration k)
    (j : Fin (k+1)) (a : Fin (cfg.2 j).length) :
    ∃ i, configCellIndices cfg i = (cfg.2 j).get a :=
  (configCellIndices_range cfg _).mpr (Or.inr ⟨j,List.get_mem _ _⟩)

theorem configCellIndices_natAbs_le {k M N : ℕ} {cfg : SourceConfiguration k}
    (hc : cfg.Bounded M N) (i : Fin (configCellCount cfg)) :
    (configCellIndices cfg i).natAbs ≤ M+1 := by
  have hh : |configCellIndices cfg i| ≤ (M : ℤ)+1 :=
    configCellIndices_property cfg (fun a => |a| ≤ (M : ℤ)+1) hc.1
      (fun j => (hc.2 j).2) i
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  simpa only [Nat.cast_add, Nat.cast_one] using hh

theorem configCellCount_le {k : ℕ} (cfg : SourceConfiguration k)
    (hl : ∀ j, ((cfg.2 j).length : ℝ) ≤ 2 * Real.exp (2*(k : ℝ)/10000)) :
    (configCellCount cfg : ℝ) ≤ 4 * ((k : ℝ)+1) * Real.exp (2*(k : ℝ)/10000) := by
  have he : 1 ≤ Real.exp (2*(k : ℝ)/10000) := Real.one_le_exp_iff.mpr (by positivity)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hl j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hs
  rw [configCellCount_eq]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) k,
    mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α := ℝ) k)]

end Ostmann.Characters.HigherBiasSource

end

end OAI
