import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Configurations.ConfigurationLP

namespace OAI

noncomputable section

open scoped BigOperators

namespace BinPackingGap

structure PoolTemplates (I : Instance) (T U F : Type*) where
  base : T → Finset I.Item
  globalPool : U → Finset I.Item
  flagPool : F → Finset I.Item
  globalSpecies : T → U
  flagSpecies : T → F
  global_nonempty : ∀ t, (globalPool (globalSpecies t)).Nonempty
  flag_nonempty : ∀ t, (flagPool (flagSpecies t)).Nonempty
  base_global : ∀ t, Disjoint (base t) (globalPool (globalSpecies t))
  base_flag : ∀ t, Disjoint (base t) (flagPool (flagSpecies t))
  global_flag : ∀ t,
    Disjoint (globalPool (globalSpecies t)) (flagPool (flagSpecies t))
  capacity : ∀ t (u : {i // i ∈ globalPool (globalSpecies t)})
    (f : {i // i ∈ flagPool (flagSpecies t)}),
    (∑ i ∈ base t ∪ {u.val, f.val}, I.size i) ≤ 1

namespace PoolTemplates

variable {I : Instance} {T U F : Type*} [Fintype T]

variable (D : PoolTemplates I T U F)

abbrev Globals (t : T) := {i // i ∈ D.globalPool (D.globalSpecies t)}
abbrev Flags (t : T) := {i // i ∈ D.flagPool (D.flagSpecies t)}
abbrev Sample := (t : T) × (D.Globals t × D.Flags t)

def column (t : T) (u : D.Globals t) (f : D.Flags t) : IndividualConfiguration I :=
  ⟨D.base t ∪ {u.val, f.val}, D.capacity t u f⟩

def sampleColumn (s : D.Sample) : IndividualConfiguration I :=
  D.column s.1 s.2.1 s.2.2

def templateMass (t : T) : ℝ :=
  1 / (2 * ((D.globalPool (D.globalSpecies t)).card : ℝ) *
    ((D.flagPool (D.flagSpecies t)).card : ℝ))

def sampleMass (s : D.Sample) : ℝ := D.templateMass s.1

def weights : IndividualConfiguration I → ℝ :=
  FractionalCover.pushforward D.sampleColumn D.sampleMass

omit [Fintype T] in
theorem templateMass_nonneg (t : T) : 0 ≤ D.templateMass t := by
  unfold templateMass
  positivity

omit [Fintype T] in
theorem global_card_ne_zero (t : T) :
    ((D.globalPool (D.globalSpecies t)).card : ℝ) ≠ 0 := by
  exact_mod_cast (Finset.card_pos.mpr (D.global_nonempty t)).ne'

omit [Fintype T] in
theorem flag_card_ne_zero (t : T) :
    ((D.flagPool (D.flagSpecies t)).card : ℝ) ≠ 0 := by
  exact_mod_cast (Finset.card_pos.mpr (D.flag_nonempty t)).ne'

omit [Fintype T] in
theorem sum_templateMass (t : T) :
    (∑ _u : D.Globals t, ∑ _f : D.Flags t, D.templateMass t) = (1 / 2 : ℝ) := by
  have hu := D.global_card_ne_zero t
  have hf := D.flag_card_ne_zero t
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  unfold templateMass
  field_simp [hu, hf]

theorem objective_weights :
    FractionalCover.objective D.weights = (Fintype.card T : ℝ) / 2 := by
  rw [weights, FractionalCover.objective_pushforward]
  unfold FractionalCover.objective sampleMass
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, sum_templateMass]
  simp [div_eq_mul_inv]

theorem sum_pool_eq (S : Finset I.Item) (i : I.Item) (a : ℝ) :
    (∑ u : {j // j ∈ S}, if i = u.val then a else 0) =
      if i ∈ S then a else 0 := by
  classical
  by_cases hi : i ∈ S
  · have he : ∀ u : {j // j ∈ S}, i = u.val ↔ u = ⟨i, hi⟩ := by
      intro u
      constructor
      · intro h
        exact Subtype.ext h.symm
      · intro h
        exact (congrArg Subtype.val h).symm
    simp only [he]
    simp [hi]
  · have he : ∀ u : {j // j ∈ S}, i ≠ u.val := by
      intro u h
      exact hi (h.symm ▸ u.property)
    simp [he, hi]

omit [Fintype T] in
theorem template_coverage (t : T) (i : I.Item) :
    (∑ u : D.Globals t, ∑ f : D.Flags t,
      (if i ∈ (D.column t u f).val then (1 : ℝ) else 0) * D.templateMass t) =
    (if i ∈ D.base t then (1 / 2 : ℝ) else 0) +
    (if i ∈ D.globalPool (D.globalSpecies t) then
      1 / (2 * ((D.globalPool (D.globalSpecies t)).card : ℝ)) else 0) +
    (if i ∈ D.flagPool (D.flagSpecies t) then
      1 / (2 * ((D.flagPool (D.flagSpecies t)).card : ℝ)) else 0) := by
  classical
  have hu := D.global_card_ne_zero t
  have hf := D.flag_card_ne_zero t
  by_cases hb : i ∈ D.base t
  · have hgu : i ∉ D.globalPool (D.globalSpecies t) :=
      fun h => Finset.disjoint_left.mp (D.base_global t) hb h
    have hfl : i ∉ D.flagPool (D.flagSpecies t) :=
      fun h => Finset.disjoint_left.mp (D.base_flag t) hb h
    simpa [column, hb, hgu, hfl] using D.sum_templateMass t
  · by_cases hg : i ∈ D.globalPool (D.globalSpecies t)
    · have hfl : i ∉ D.flagPool (D.flagSpecies t) :=
        fun h => Finset.disjoint_left.mp (D.global_flag t) hg h
      have hcol : ∀ u : D.Globals t, ∀ f : D.Flags t,
          i ∈ (D.column t u f).val ↔ i = u.val := by
        intro u f
        have hn : i ≠ f.val := fun h => hfl (h.symm ▸ f.property)
        simp [column, hb, hn]
      simp only [hcol, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm]
      simp_rw [sum_pool_eq]
      simp only [hb, hg, hfl, ite_false, ite_true, zero_add, add_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      unfold templateMass
      field_simp [hu, hf]
    · by_cases hfl : i ∈ D.flagPool (D.flagSpecies t)
      · have hcol : ∀ u : D.Globals t, ∀ f : D.Flags t,
            i ∈ (D.column t u f).val ↔ i = f.val := by
          intro u f
          have hn : i ≠ u.val := fun h => hg (h.symm ▸ u.property)
          simp [column, hb, hn]
        simp only [hcol, ite_mul, one_mul, zero_mul]
        simp_rw [sum_pool_eq]
        simp only [hb, hg, hfl, ite_false, ite_true, zero_add,
          Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        unfold templateMass
        field_simp [hu, hf]
      · have hcol : ∀ u : D.Globals t, ∀ f : D.Flags t,
            i ∉ (D.column t u f).val := by
          intro u f
          have hnu : i ≠ u.val := fun h => hg (h.symm ▸ u.property)
          have hnf : i ≠ f.val := fun h => hfl (h.symm ▸ f.property)
          simp [column, hb, hnu, hnf]
        simp [hcol, hb, hg, hfl]

theorem sum_by_species {S : Type*} [Fintype S] [DecidableEq S]
    (species : T → S) (a : S → ℝ) :
    (∑ t, a (species t)) =
      ∑ s, ((Finset.univ.filter (fun t => species t = s)).card : ℝ) * a s := by
  classical
  calc
    (∑ t, a (species t)) = ∑ t, ∑ s, if species t = s then a s else 0 := by simp
    _ = ∑ s, ∑ t, if species t = s then a s else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter]
      simp

theorem sum_pool_demands {S : Type*} [Fintype S] [DecidableEq S]
    (species : T → S) (pool : S → Finset I.Item)
    (hdemand : ∀ s, (Finset.univ.filter (fun t => species t = s)).card =
      2 * (pool s).card) (i : I.Item) :
    (∑ t, if i ∈ pool (species t) then
      1 / (2 * ((pool (species t)).card : ℝ)) else 0) =
    ∑ s, if i ∈ pool s then (1 : ℝ) else 0 := by
  classical
  rw [sum_by_species species (fun s =>
    if i ∈ pool s then 1 / (2 * ((pool s).card : ℝ)) else 0)]
  apply Finset.sum_congr rfl
  intro s _
  rw [hdemand s]
  by_cases hi : i ∈ pool s
  · have hs : ((pool s).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨i, hi⟩).ne'
    simp only [hi, ite_true, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hs]
  · simp [hi]

variable [Fintype U] [Fintype F] [DecidableEq U] [DecidableEq F]

theorem weights_feasible
    (labeled : Finset I.Item)
    (hbase : ∀ i, (Finset.univ.filter (fun t => i ∈ D.base t)).card =
      if i ∈ labeled then 2 else 0)
    (hglobal : ∀ u, (Finset.univ.filter (fun t => D.globalSpecies t = u)).card =
      2 * (D.globalPool u).card)
    (hflag : ∀ f, (Finset.univ.filter (fun t => D.flagSpecies t = f)).card =
      2 * (D.flagPool f).card)
    (hpartition : ∀ i,
      (if i ∈ labeled then (1 : ℝ) else 0) +
      (∑ u, if i ∈ D.globalPool u then (1 : ℝ) else 0) +
      (∑ f, if i ∈ D.flagPool f then (1 : ℝ) else 0) = 1) :
    IndividualFeasible I D.weights := by
  classical
  refine ⟨FractionalCover.pushforward_nonneg D.sampleColumn
    (fun s => D.templateMass_nonneg s.1), ?_⟩
  intro i
  change 1 ≤ ∑ H, individualMatrix I H i * D.weights H
  rw [weights, FractionalCover.coverage_pushforward]
  change 1 ≤ ∑ s : D.Sample,
    (if i ∈ (D.column s.1 s.2.1 s.2.2).val then (1 : ℝ) else 0) * D.templateMass s.1
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, template_coverage, Finset.sum_add_distrib]
  rw [sum_pool_demands D.globalSpecies D.globalPool hglobal,
    sum_pool_demands D.flagSpecies D.flagPool hflag]
  have hb : (∑ t, if i ∈ D.base t then (1 / 2 : ℝ) else 0) =
      if i ∈ labeled then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, hbase]
    split_ifs <;> norm_num
  simpa only [hb, hpartition i] using (le_refl (1 : ℝ))

end PoolTemplates

end BinPackingGap

end

end OAI
