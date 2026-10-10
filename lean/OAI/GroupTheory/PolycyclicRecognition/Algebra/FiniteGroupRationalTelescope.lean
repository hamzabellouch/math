import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SequentialProjectiveTelescope
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationSteps
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalCoefficientSequence
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteGroupProjectiveNorm

namespace OAI

/-! # A projective telescope for rational trivial coefficients of a finite group

Consecutive free modules map by augmentation followed by the norm section,
scaled by the next positive integer. The actual colimit is the rational
trivial representation. Thus it has integral projective dimension at most one.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G] [Fintype G]

abbrev finiteGroupRationalStage := normalizedFreeRepresentation (trivialIntegral G)

def finiteGroupNormSection : trivialIntegral G ⟶ finiteGroupRationalStage G :=
  Rep.ofHom
    ⟨{ toFun := fun z => z • ((Rep.norm (finiteGroupRationalStage G)).hom
         (normalizedFreeGenerator (trivialIntegral G) 1))
       map_add' := fun x y => add_smul x y _
       map_smul' := fun r z => by
         simp only [RingHom.id_apply, smul_eq_mul]
         exact mul_smul r z _ },
    fun g => by
      apply LinearMap.ext
      intro z
      change z • _ = (finiteGroupRationalStage G).ρ g (z • _)
      rw [map_smul]
      congr 1
      exact (Representation.self_norm_apply (finiteGroupRationalStage G).ρ g _).symm⟩

theorem finiteGroupNormSection_augmentation :
    finiteGroupNormSection G ≫ normalizedFreeAugmentation (trivialIntegral G) =
      (Fintype.card G : ℤ) • 𝟙 (trivialIntegral G) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change (normalizedFreeAugmentation (trivialIntegral G)).hom
    (z • (Rep.norm (finiteGroupRationalStage G)).hom
      (normalizedFreeGenerator (trivialIntegral G) 1)) = (Fintype.card G : ℤ) • z
  rw [map_smul]
  have hn := ConcreteCategory.congr_hom
    (Rep.norm_comm (normalizedFreeAugmentation (trivialIntegral G)))
      (normalizedFreeGenerator (trivialIntegral G) 1)
  change (Rep.norm (trivialIntegral G)).hom
    ((normalizedFreeAugmentation (trivialIntegral G)).hom
      (normalizedFreeGenerator (trivialIntegral G) 1)) =
    (normalizedFreeAugmentation (trivialIntegral G)).hom
      ((Rep.norm (finiteGroupRationalStage G)).hom
        (normalizedFreeGenerator (trivialIntegral G) 1)) at hn
  rw [← hn, normalizedFreeAugmentation_generator]
  simp [Rep.norm, Representation.norm, trivialIntegral, mul_comm]

def finiteGroupRationalStep (i : ℕ) :
    finiteGroupRationalStage G ⟶ finiteGroupRationalStage G :=
  ((i + 1 : ℕ) : ℤ) •
    (normalizedFreeAugmentation (trivialIntegral G) ≫ finiteGroupNormSection G)

def finiteGroupRationalDiagram : SequentialRepresentationDiagram G :=
  .ofConsecutive (fun _ => finiteGroupRationalStage G) (finiteGroupRationalStep G)

def finiteGroupRationalDenominator (i : ℕ) : ℕ := Fintype.card G ^ i * i.factorial

theorem finiteGroupRationalDenominator_ne_zero (i : ℕ) :
    finiteGroupRationalDenominator G i ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ Fintype.card_ne_zero) (Nat.factorial_ne_zero i)

omit [Group G] in
theorem finiteGroupRationalDenominator_succ (i : ℕ) :
    finiteGroupRationalDenominator G (i + 1) =
      finiteGroupRationalDenominator G i * Fintype.card G * (i + 1) := by
  simp only [finiteGroupRationalDenominator, pow_succ, Nat.factorial_succ]
  ring

def integralRationalDivision (d : ℕ) : trivialIntegral G ⟶ Rep.trivial ℤ G ℚ :=
  Rep.ofHom ⟨{ toFun := fun z => (z : ℚ) / (d : ℚ)
               map_add' := fun x y => by simp [add_div]
               map_smul' := fun r z => by simp [mul_div_assoc] }, fun _ => by rfl⟩

def finiteGroupRationalInclusion (i : ℕ) :
    finiteGroupRationalStage G ⟶ Rep.trivial ℤ G ℚ :=
  normalizedFreeAugmentation (trivialIntegral G) ≫
    integralRationalDivision G (finiteGroupRationalDenominator G i)

theorem finiteGroupRationalStep_inclusion (i : ℕ) :
    finiteGroupRationalStep G i ≫ finiteGroupRationalInclusion G (i + 1) =
      finiteGroupRationalInclusion G i := by
  unfold finiteGroupRationalStep finiteGroupRationalInclusion
  rw [Preadditive.zsmul_comp, Category.assoc, ← Category.assoc (finiteGroupNormSection G),
    finiteGroupNormSection_augmentation]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  let z : ℤ := (normalizedFreeAugmentation (trivialIntegral G)).hom x
  change (i + 1 : ℤ) • ((((Fintype.card G : ℤ) * z : ℤ) : ℚ) /
      (finiteGroupRationalDenominator G (i + 1) : ℚ)) =
    (z : ℚ) / (finiteGroupRationalDenominator G i : ℚ)
  rw [finiteGroupRationalDenominator_succ]
  have hd : (finiteGroupRationalDenominator G i : ℚ) ≠ 0 := by
    exact_mod_cast finiteGroupRationalDenominator_ne_zero G i
  have hc : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := G)
  have hi : (i + 1 : ℚ) ≠ 0 := by positivity
  simp only [zsmul_eq_mul]
  push_cast
  field_simp


def finiteGroupRationalColimit :
    (finiteGroupRationalDiagram G).ColimitCocone (Rep.trivial ℤ G ℚ) where
  ι := finiteGroupRationalInclusion G
  comm := SequentialRepresentationDiagram.ofConsecutive_comm _ _ _ _
    (finiteGroupRationalStep_inclusion G)
  surj q := by
    change ℚ at q
    have hdvd : q.den ∣ finiteGroupRationalDenominator G q.den := by
      apply (Nat.dvd_factorial (Rat.den_pos q) le_rfl).trans
      exact ⟨Fintype.card G ^ q.den, by simp [finiteGroupRationalDenominator, mul_comm]⟩
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨q.den, normalizedFreeGenerator (trivialIntegral G) (q.num * (k : ℤ)), ?_⟩
    change (((normalizedFreeAugmentation (trivialIntegral G)).hom
      (normalizedFreeGenerator (trivialIntegral G) (q.num * (k : ℤ))) : ℤ) : ℚ) /
        (finiteGroupRationalDenominator G q.den : ℚ) = q
    rw [normalizedFreeAugmentation_generator, hk]
    have hk0 : (k : ℚ) ≠ 0 := by
      have hkn : k ≠ 0 := by
        intro h
        simp only [h, mul_zero] at hk
        exact finiteGroupRationalDenominator_ne_zero G q.den hk
      exact_mod_cast hkn
    push_cast
    rw [mul_div_mul_right _ _ hk0]
    exact Rat.num_div_den q
  zero_exact i x hx := by
    change finiteGroupRationalStage G at x
    refine ⟨i + 1, Nat.le_succ i, ?_⟩
    have hz : (normalizedFreeAugmentation (trivialIntegral G)).hom x = 0 := by
      have hq : (((normalizedFreeAugmentation (trivialIntegral G)).hom x : ℤ) : ℚ) /
          (finiteGroupRationalDenominator G i : ℚ) = 0 := hx
      have hd : (finiteGroupRationalDenominator G i : ℚ) ≠ 0 := by
        exact_mod_cast finiteGroupRationalDenominator_ne_zero G i
      exact_mod_cast (div_eq_zero_iff.mp hq).resolve_right hd
    change ((SequentialRepresentationDiagram.ofConsecutive
      (fun _ => finiteGroupRationalStage G) (finiteGroupRationalStep G)).map
        i (i + 1) (Nat.le_succ i)).hom x = 0
    rw [SequentialRepresentationDiagram.ofConsecutive_map_step]
    change (i + 1 : ℤ) • ((finiteGroupNormSection G).hom
      ((normalizedFreeAugmentation (trivialIntegral G)).hom x)) = 0
    rw [hz, map_zero]
    exact smul_zero _

theorem finiteGroup_rational_projectiveDimension_le_one :
    HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) 1 := by
  let : ∀ i, Projective ((finiteGroupRationalDiagram G).obj i) := fun i => by
    change Projective (finiteGroupRationalStage G)
    infer_instance
  exact (finiteGroupRationalColimit G).projectiveDimension_le_one

end PolycyclicRecognition

end

end OAI
