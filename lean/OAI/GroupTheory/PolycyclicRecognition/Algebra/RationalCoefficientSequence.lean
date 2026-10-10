import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationColimit
import Mathlib.Data.Nat.Factorial.BigOperators

namespace OAI

/-! # The factorial coefficient system with colimit the rational numbers -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear

def factorialMultiplier (i j : ℕ) : ℤ := ∏ k ∈ Finset.Ico i j, (k + 1 : ℤ)

theorem factorialMultiplier_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    factorialMultiplier i j * factorialMultiplier j k = factorialMultiplier i k :=
  Finset.prod_Ico_consecutive (fun n : ℕ => (n + 1 : ℤ)) hij hjk

@[simp]
theorem factorialMultiplier_self (i : ℕ) : factorialMultiplier i i = 1 := by
  simp [factorialMultiplier]

theorem factorialMultiplier_zero (j : ℕ) : factorialMultiplier 0 j = j.factorial := by
  simp only [factorialMultiplier, Nat.Ico_zero_eq_range, Nat.factorial_eq_prod_range_add_one,
    Nat.cast_prod, Nat.cast_add, Nat.cast_one]

theorem factorialMultiplier_factorial (i j : ℕ) (hij : i ≤ j) :
    (i.factorial : ℤ) * factorialMultiplier i j = j.factorial := by
  rw [← factorialMultiplier_zero i, ← factorialMultiplier_zero j]
  exact factorialMultiplier_comp 0 i j (Nat.zero_le i) hij

def rationalCoefficientDiagram (G : Type) [Group G] : SequentialRepresentationDiagram G where
  obj _ := trivialIntegral G
  map i j _ := factorialMultiplier i j • 𝟙 _
  map_id i := by rw [factorialMultiplier_self, one_smul]
  map_comp i j k hij hjk := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, smul_smul,
      factorialMultiplier_comp i j k hij hjk]

def rationalCoefficientInclusion (G : Type) [Group G] (i : ℕ) :
    trivialIntegral G ⟶ Rep.trivial ℤ G ℚ :=
  Rep.ofHom ⟨{ toFun := fun z => (z : ℚ) / (i.factorial : ℚ)
               map_add' := fun x y => by simp [add_div]
               map_smul' := fun r z => by simp [mul_div_assoc] },
    fun g => by rfl⟩

@[simp]
theorem rationalCoefficientInclusion_apply (G : Type) [Group G] (i : ℕ) (z : ℤ) :
    (rationalCoefficientInclusion G i).hom z = (z : ℚ) / (i.factorial : ℚ) := rfl

def rationalCoefficientColimit (G : Type) [Group G] :
    (rationalCoefficientDiagram G).ColimitCocone (Rep.trivial ℤ G ℚ) where
  ι := rationalCoefficientInclusion G
  comm i j hij := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change ℤ at z
    change ((factorialMultiplier i j * (z : ℤ) : ℤ) : ℚ) / (j.factorial : ℚ) =
      ((z : ℤ) : ℚ) / (i.factorial : ℚ)
    have he : (i.factorial : ℚ) * (factorialMultiplier i j : ℚ) = (j.factorial : ℚ) := by
      exact_mod_cast factorialMultiplier_factorial i j hij
    have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    push_cast
    field_simp
    calc
      (factorialMultiplier i j : ℚ) * (z : ℚ) * (i.factorial : ℚ) =
          (z : ℚ) * ((i.factorial : ℚ) * (factorialMultiplier i j : ℚ)) := by ring
      _ = (z : ℚ) * (j.factorial : ℚ) := congrArg (fun t : ℚ => (z : ℚ) * t) he
  surj q := by
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Rat.den_pos q) (le_refl q.den)
    refine ⟨q.den, q.num * (k : ℤ), ?_⟩
    change ((q.num * (k : ℤ) : ℤ) : ℚ) / (q.den.factorial : ℚ) = q
    rw [hk]
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast (Rat.den_pos q).ne'
    have hk0 : (k : ℚ) ≠ 0 := by
      have hkn : k ≠ 0 := by intro h; simp only [h, mul_zero] at hk; exact Nat.factorial_ne_zero q.den hk
      exact_mod_cast hkn
    push_cast
    rw [mul_div_mul_right _ _ hk0]
    exact Rat.num_div_den q
  zero_exact i z hz := by
    change ℤ at z
    refine ⟨i, le_rfl, ?_⟩
    have hz' : ((z : ℤ) : ℚ) / (i.factorial : ℚ) = 0 := hz
    have hfac : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have h0 : z = 0 := by exact_mod_cast (div_eq_zero_iff.mp hz').resolve_right hfac
    subst z
    simp [rationalCoefficientDiagram]
    rfl

end PolycyclicRecognition

end

end OAI
