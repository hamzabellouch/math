import OAI.Analysis.MarkovType.OrbitDisplacement
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

def LatticeCube (J : Type*) (R : ℕ) :=
  J → Set.Icc (-(R : ℤ)) (R : ℤ)

instance {J : Type*} [Fintype J] (R : ℕ) : Fintype (LatticeCube J R) := by
  classical
  unfold LatticeCube
  infer_instance

def latticeCubeVal {J : Type*} {R : ℕ} (a : LatticeCube J R) : J → ℤ :=
  fun j => (a j).val

theorem latticeCubeVal_injective {J : Type*} {R : ℕ} :
    Function.Injective (@latticeCubeVal J R) := by
  intro a b hab
  funext j
  exact Subtype.ext (congrFun hab j)

def latticeCubeZero (J : Type*) (R : ℕ) : LatticeCube J R :=
  fun _ => ⟨0, by constructor <;> omega⟩

instance {J : Type*} (R : ℕ) : Nonempty (LatticeCube J R) :=
  ⟨latticeCubeZero J R⟩

@[simp] theorem latticeCubeVal_zero (J : Type*) (R : ℕ) :
    latticeCubeVal (latticeCubeZero J R) = 0 := rfl

theorem latticeCube_coordinate_bounds {J : Type*} {R : ℕ}
    (a : LatticeCube J R) (j : J) :
    -(R : ℤ) ≤ latticeCubeVal a j ∧ latticeCubeVal a j ≤ R :=
  (a j).property

theorem latticeCube_card {J : Type*} [Fintype J] (R : ℕ) :
    Fintype.card (LatticeCube J R) = (2 * R + 1) ^ Fintype.card J := by
  classical
  have hinterval : Fintype.card (Set.Icc (-(R : ℤ)) (R : ℤ)) = 2 * R + 1 := by
    rw [Fintype.card_Icc, Int.card_Icc]
    omega
  simp [LatticeCube, Fintype.card_pi, hinterval]

theorem latticeCube_card_pos {J : Type*} [Fintype J] (R : ℕ) :
    0 < Fintype.card (LatticeCube J R) := Fintype.card_pos

theorem latticeCube_card_real_pos {J : Type*} [Fintype J] (R : ℕ) :
    0 < (Fintype.card (LatticeCube J R) : ℝ) := by
  exact_mod_cast latticeCube_card_pos (J := J) R

def LatticeCentral {J : Type*} {R : ℕ} (n : ℕ) (a : LatticeCube J R) : Prop :=
  ∀ j, -((R - n : ℕ) : ℤ) ≤ latticeCubeVal a j ∧
    latticeCubeVal a j ≤ ((R - n : ℕ) : ℤ)

def latticeCubeInclusion {J : Type*} {R Q : ℕ} (hQR : Q ≤ R)
    (a : LatticeCube J Q) : LatticeCube J R := fun j =>
  ⟨(a j).val, by
    rcases (a j).property with ⟨hl, hu⟩
    constructor <;> omega⟩

@[simp] theorem latticeCubeVal_inclusion {J : Type*} {R Q : ℕ} (hQR : Q ≤ R)
    (a : LatticeCube J Q) :
    latticeCubeVal (latticeCubeInclusion hQR a) = latticeCubeVal a := rfl

def latticeCentralEquiv {J : Type*} (n R : ℕ) :
    LatticeCube J (R - n) ≃ {a : LatticeCube J R // LatticeCentral n a} where
  toFun a := ⟨latticeCubeInclusion (Nat.sub_le R n) a, fun j => (a j).property⟩
  invFun a := fun j => ⟨latticeCubeVal a.val j, a.property j⟩
  left_inv a := by
    funext j
    rfl
  right_inv a := by
    apply Subtype.ext
    funext j
    rfl

theorem latticeCentral_card {J : Type*} [Fintype J] (n R : ℕ) :
    Fintype.card {a : LatticeCube J R // LatticeCentral n a} =
      (2 * (R - n) + 1) ^ Fintype.card J := by
  classical
  rw [← Fintype.card_congr (latticeCentralEquiv (J := J) n R), latticeCube_card]

def latticeDensity (J : Type*) [Fintype J] (n R : ℕ) : ℝ :=
  (Fintype.card (LatticeCube J (R - n)) : ℝ) /
    (Fintype.card (LatticeCube J R) : ℝ)

theorem latticeDensity_formula {J : Type*} [Fintype J] (n R : ℕ) :
    latticeDensity J n R =
      (((2 * (R - n) + 1 : ℕ) : ℝ) / ((2 * R + 1 : ℕ) : ℝ)) ^
        Fintype.card J := by
  simp only [latticeDensity, latticeCube_card, Nat.cast_pow, div_pow]

theorem latticeDensity_pos {J : Type*} [Fintype J] (n R : ℕ) :
    0 < latticeDensity J n R :=
  div_pos (latticeCube_card_real_pos (J := J) (R - n))
    (latticeCube_card_real_pos (J := J) R)

theorem latticeDensity_tendsto_one {J : Type*} [Fintype J] (n : ℕ) :
    Tendsto (fun m : ℕ => latticeDensity J n (m + n + 1)) atTop (𝓝 1) := by
  have hden : Tendsto (fun m : ℕ => 2 * (m + n + 1) + 1) atTop atTop :=
    tendsto_atTop_mono (fun m => by change m ≤ 2 * (m + n + 1) + 1; omega) tendsto_id
  have hsmall : Tendsto
      (fun m : ℕ => (2 * (n : ℝ)) / ((2 * (m + n + 1) + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * (n : ℝ))).comp hden
  have hbase : Tendsto
      (fun m : ℕ => (((2 * ((m + n + 1) - n) + 1 : ℕ) : ℝ) /
        ((2 * (m + n + 1) + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
    have heq : (fun m : ℕ => (((2 * ((m + n + 1) - n) + 1 : ℕ) : ℝ) /
        ((2 * (m + n + 1) + 1 : ℕ) : ℝ))) =
        (fun m : ℕ => 1 - (2 * (n : ℝ)) /
          ((2 * (m + n + 1) + 1 : ℕ) : ℝ)) := by
      funext m
      have hsub : m + n + 1 - n = m + 1 := by omega
      have hne : ((2 * (m + n + 1) + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [hsub]
      field_simp
      push_cast
      ring
    rw [heq]
    simpa using tendsto_const_nhds.sub hsmall
  have hp := hbase.pow (Fintype.card J)
  simpa only [latticeDensity_formula, one_pow] using hp

end MarkovSuperreflexivity

end

end OAI
