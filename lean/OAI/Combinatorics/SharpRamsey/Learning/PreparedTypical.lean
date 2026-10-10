import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.TestRowPencils

namespace OAI

section
namespace SharpLogRamsey.PreparedTypical
open Finset PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {A : Type*}

lemma outside_count (S O : Finset A) (hO : O⊆S) (x : A) (R : A→Prop) :
    (((S\(O∪{x})).filter R).card:ℝ) ≤ (S.filter R).card-(O.filter R).card ∧
    (S.filter R).card-(O.filter R).card-1 ≤ (((S\(O∪{x})).filter R).card:ℝ) := by
  have he : (S\(O∪{x})).filter R = ((S.filter R)\(O.filter R)).erase x := by
    ext y
    simp only [mem_filter,mem_sdiff,mem_union,mem_singleton,mem_erase]
    aesop
  have ho : O.filter R⊆S.filter R := filter_subset_filter R hO
  have hk := card_sdiff_add_card_eq_card ho
  have hn : (((S.filter R)\(O.filter R)).erase x).card ≤ ((S.filter R)\(O.filter R)).card :=
    card_le_card (erase_subset _ _)
  have hl : ((S.filter R)\(O.filter R)).card ≤ (((S.filter R)\(O.filter R)).erase x).card+1 := by
    by_cases hx : x∈((S.filter R)\(O.filter R))
    · rw [card_erase_of_mem hx]; omega
    · rw [erase_eq_of_notMem hx]; omega
  rw [he]
  have hk' : (((S.filter R)\(O.filter R)).card:ℝ)+(O.filter R).card=(S.filter R).card := by exact_mod_cast hk
  have hn' : ((((S.filter R)\(O.filter R)).erase x).card:ℝ)≤((S.filter R)\(O.filter R)).card := by exact_mod_cast hn
  have hl' : (((S.filter R)\(O.filter R)).card:ℝ)≤(((S.filter R)\(O.filter R)).erase x).card+1 := by exact_mod_cast hl
  constructor <;> linarith

lemma outside_scalar (c f l o r : ℝ) (_hc : 0≤c) (hc1 : c≤1/100)
    (hf0 : 0≤f) (hf : f≤1/25)
    (hl : |l-1|≤1/10) (ho : |o-f|≤1/50)
    (hr₁ : r≤l-o) (hr₂ : l-o-c≤r) :
    3/4≤r ∧ r≤2 ∧ |r-(1-f)|≤13/100 := by
  rw [abs_le] at hl ho ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma outside_square (c f l o r : ℝ) (hc : 0≤c)
    (hr₁ : r≤l-o) (hr₂ : l-o-c≤r) :
    (r-(1-f))^2≤3*((l-1)^2+(o-f)^2+c^2) := by
  have he₁ : 0≤l-o-r := by linarith
  have he₂ : l-o-r≤c := by linarith
  have hes : (l-o-r)^2≤c^2 := by nlinarith
  nlinarith [sq_nonneg ((l-1)+(o-f)),sq_nonneg ((l-1)+(l-o-r)),
    sq_nonneg ((o-f)-(l-o-r))]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedTypical_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPreparedTypical_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

def mass (S : Finset (Projectivization K V)) (c : ℝ≥0)
    (H : Projectivization K (Module.Dual K V)) : ℝ :=
  (c:ℝ)*((S.filter (fun y => y.submodule≤LinearMap.ker H.rep)).card:ℝ)

omit [Finite K] [FiniteDimensional K V] in
lemma outside_mass_between (S O : Finset (Projectivization K V)) (hO : O⊆S)
    (x : Projectivization K V) (c : ℝ≥0) (H : Projectivization K (Module.Dual K V)) :
    outsideMass S O x c H≤ mass S c H-mass O c H ∧
    mass S c H-mass O c H-c≤ outsideMass S O x c H := by
  have he : (S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule≤LinearMap.ker H.rep) =
      (S\(O∪{x})).filter (fun y => y.submodule≤LinearMap.ker H.rep) := by
    ext y
    simp only [mem_filter,mem_sdiff,mem_union,mem_singleton]
    aesop
  have hh := outside_count S O hO x (fun y => y.submodule≤LinearMap.ker H.rep)
  simp only [outsideMass,he,mass]
  constructor
  · have ht := mul_le_mul_of_nonneg_left hh.1 c.coe_nonneg
    linarith
  · have ht := mul_le_mul_of_nonneg_left hh.2 c.coe_nonneg
    linarith

omit [Finite K] [FiniteDimensional K V] in
theorem typical_point (S O : Finset (Projectivization K V)) (hO : O⊆S)
    (x : Projectivization K V) (c : ℝ≥0) (H : Projectivization K (Module.Dual K V))
    (f : ℝ) (hc : (c:ℝ)≤1/100) (hf0 : 0≤f) (hf : f≤1/25)
    (hl : |mass S c H-1|≤1/10) (ho : |mass O c H-f|≤1/50) :
    3/4≤ outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-f)|≤13/100 := by
  have hh := outside_mass_between S O hO x c H
  exact outside_scalar c f _ _ _ c.coe_nonneg hc hf0 hf hl ho hh.1 hh.2

theorem typical_squares (S O : Finset (Projectivization K V)) (hO : O⊆S)
    (x : Projectivization K V) (c : ℝ≥0)
    (T : Finset (Projectivization K (Module.Dual K V))) (hT : T⊆pencil x)
    (f U W : ℝ)
    (hl : ∀ H∈T,|mass S c H-1|≤1/10)
    (ho : ∀ H∈T,|mass O c H-f|≤1/50)
    (hU : (∑ H∈pencil x,min 1 ((mass S c H-1)^2))≤U)
    (hW : (∑ H∈pencil x,min 1 ((mass O c H-f)^2))≤W) :
    (∑ H∈T,(outsideMass S O x c H-(1-f))^2)≤
      3*(U+W+(T.card:ℝ)*(c:ℝ)^2) := by
  have hl' : (∑ H∈T,(mass S c H-1)^2)≤U := by
    calc
      _ = ∑ H∈T,min 1 ((mass S c H-1)^2) := by
        apply sum_congr rfl
        intro H hH
        have ht := hl H hH
        rw [min_eq_right]
        have hs := mul_self_le_mul_self (abs_nonneg (mass S c H-1)) ht
        nlinarith [sq_abs (mass S c H-1)]
      _ ≤ ∑ H∈pencil x,min 1 ((mass S c H-1)^2) :=
        sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => le_min (by norm_num) (sq_nonneg _))
      _ ≤ U := hU
  have ho' : (∑ H∈T,(mass O c H-f)^2)≤W := by
    calc
      _ = ∑ H∈T,min 1 ((mass O c H-f)^2) := by
        apply sum_congr rfl
        intro H hH
        have ht := ho H hH
        rw [min_eq_right]
        have hs := mul_self_le_mul_self (abs_nonneg (mass O c H-f)) ht
        nlinarith [sq_abs (mass O c H-f)]
      _ ≤ ∑ H∈pencil x,min 1 ((mass O c H-f)^2) :=
        sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => le_min (by norm_num) (sq_nonneg _))
      _ ≤ W := hW
  calc
    _ ≤ ∑ H∈T,3*((mass S c H-1)^2+(mass O c H-f)^2+(c:ℝ)^2) := by
      apply sum_le_sum
      intro H _
      have hh := outside_mass_between S O hO x c H
      exact outside_square c f _ _ _ c.coe_nonneg hh.1 hh.2
    _ = 3*((∑ H∈T,(mass S c H-1)^2)+(∑ H∈T,(mass O c H-f)^2)+(T.card:ℝ)*(c:ℝ)^2) := by
      simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul]
    _ ≤ _ := by linarith

end
end SharpLogRamsey.PreparedTypical

end

end OAI
