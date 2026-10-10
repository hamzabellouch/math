import OAI.Combinatorics.Progressions.Estimates.RelativeRetainedCubeSource
import OAI.Combinatorics.Progressions.Lattices.CoefficientResidueMixture
import OAI.Combinatorics.Progressions.Lattices.CubeResidueMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def rawCubeBlockSource {b g q : ℕ}
    (t : Fin b → Fin g → FiniteCubeSlice q)
    (w : Fin b → Fin g → (Option (Fin q) → ℤ) → ℝ)
    (hw : ∀ a j z, 0 ≤ w a j z) (htotal : ∀ a j, 0 < ∑ x : (t a j).Domain, w a j ((t a j).coordinates x)) :
    FiniteProbabilityWeights (∀ a j, (t a j).Domain) :=
  FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi (fun j =>
    FiniteProbabilityWeights.ofPositiveWeights (fun x => w a j ((t a j).coordinates x))
      (fun x => hw a j ((t a j).coordinates x)) (htotal a j)))

noncomputable def rawCubeBlockSum {b g q : ℕ} (t : Fin b → Fin g → FiniteCubeSlice q)
    (J : Finset (Finset (Fin q))) (center : J → ℤ) (x : ∀ a j, (t a j).Domain) : J → ℤ :=
  center + ∑ a, fun Z : J => integerBooleanBlockJet (fun j => (t a j).coordinates (x a j)) Z

noncomputable def rawModerateBlockSource {b g q : ℕ} (c : Fin b → FiniteCoefficientSlice)
    (t : Fin b → Fin g → FiniteCubeSlice q) (v : Fin b → ℤ → ℝ)
    (w : Fin b → Fin g → (Option (Fin q) → ℤ) → ℝ)
    (hv : ∀ a z, 0 ≤ v a z) (hw : ∀ a j z, 0 ≤ w a j z)
    (vtotal : ∀ a, 0 < ∑ x : (c a).Domain, v a ((c a).value x))
    (htotal : ∀ a j, 0 < ∑ x : (t a j).Domain, w a j ((t a j).coordinates x)) :
    FiniteProbabilityWeights (∀ a, (c a).Domain × (∀ j, (t a j).Domain)) :=
  FiniteProbabilityWeights.pi (fun a =>
    (FiniteProbabilityWeights.ofPositiveWeights (fun x => v a ((c a).value x))
      (fun x => hv a ((c a).value x)) (vtotal a)).prod
      (FiniteProbabilityWeights.pi (fun j => FiniteProbabilityWeights.ofPositiveWeights
        (fun x => w a j ((t a j).coordinates x)) (fun x => hw a j ((t a j).coordinates x)) (htotal a j))))

noncomputable def rawModerateBlockSum {b g q : ℕ} (c : Fin b → FiniteCoefficientSlice)
    (t : Fin b → Fin g → FiniteCubeSlice q) (J : Finset (Finset (Fin q))) (center : J → ℤ)
    (x : ∀ a, (c a).Domain × (∀ j, (t a j).Domain)) : J → ℤ :=
  center + ∑ a, fun Z : J => (c a).value (x a).1 *
    integerBooleanBlockJet (fun j => (t a j).coordinates ((x a).2 j)) Z

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace RetainedCubeSlice

theorem total_pos_of_finiteSlice_eq {q M : ℕ} {B T η : ℝ≥0}
    (s : RetainedCubeSlice q M B T η) (hη : 0 < η) (t : FiniteCubeSlice q)
    (ht : s.finiteSlice = t) (w : (Option (Fin q) → ℤ) → ℝ)
    (hw : ∀ x : s.Domain, s.sliceWeight x = w (s.finiteSlice.coordinates x)) :
    0 < ∑ y : t.Domain, w (t.coordinates y) := by
  have he : (∑ x : s.Domain, s.sliceWeight x) = ∑ y : t.Domain, w (t.coordinates y) := by
    apply Fintype.sum_equiv (FiniteCubeSlice.domainEquiv ht)
    intro x
    simpa only [FiniteCubeSlice.coordinates_domainEquiv] using hw x
  rw [← he]
  exact s.total_pos hη

theorem law_complexMean_of_finiteSlice_eq {q M : ℕ} {B T η : ℝ≥0}
    (s : RetainedCubeSlice q M B T η) (hη : 0 < η) (t : FiniteCubeSlice q)
    (ht : s.finiteSlice = t) (w : (Option (Fin q) → ℤ) → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hs : ∀ x : s.Domain, s.sliceWeight x = w (s.finiteSlice.coordinates x))
    (htotal : 0 < ∑ y : t.Domain, w (t.coordinates y)) (f : (Option (Fin q) → ℤ) → ℂ) :
    (s.law hη).complexMean (fun x => f (s.finiteSlice.coordinates x)) =
      (FiniteProbabilityWeights.ofPositiveWeights (fun y : t.Domain => w (t.coordinates y))
        (fun y => hw (t.coordinates y)) htotal).complexMean (fun y => f (t.coordinates y)) := by
  apply FiniteProbabilityWeights.ofPositiveWeights_complexMean_equiv (FiniteCubeSlice.domainEquiv ht)
  · intro x
    simpa only [FiniteCubeSlice.coordinates_domainEquiv] using hs x
  · intro x
    rw [FiniteCubeSlice.coordinates_domainEquiv]

end RetainedCubeSlice

namespace RetainedCoefficientSlice

theorem total_pos_of_finiteSlice_eq {M : ℕ} {B T η : ℝ≥0}
    (s : RetainedCoefficientSlice M B T η) (hη : 0 < η) (offset stride : ℤ)
    (t : FiniteCoefficientSlice) (ht : s.finiteSlice offset stride = t) (w : ℤ → ℝ)
    (hw : ∀ x : s.Domain, s.sliceWeight x = w ((s.finiteSlice offset stride).value x)) :
    0 < ∑ y : t.Domain, w (t.value y) := by
  have he : (∑ x : s.Domain, s.sliceWeight x) = ∑ y : t.Domain, w (t.value y) := by
    apply Fintype.sum_equiv (FiniteCoefficientSlice.domainEquiv ht)
    intro x
    simpa only [FiniteCoefficientSlice.value_domainEquiv] using hw x
  rw [← he]
  exact s.total_pos hη

theorem law_complexMean_of_finiteSlice_eq {M : ℕ} {B T η : ℝ≥0}
    (s : RetainedCoefficientSlice M B T η) (hη : 0 < η) (offset stride : ℤ)
    (t : FiniteCoefficientSlice) (ht : s.finiteSlice offset stride = t)
    (w : ℤ → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hs : ∀ x : s.Domain, s.sliceWeight x = w ((s.finiteSlice offset stride).value x))
    (htotal : 0 < ∑ y : t.Domain, w (t.value y)) (f : ℤ → ℂ) :
    (s.law hη).complexMean (fun x => f ((s.finiteSlice offset stride).value x)) =
      (FiniteProbabilityWeights.ofPositiveWeights (fun y : t.Domain => w (t.value y))
        (fun y => hw (t.value y)) htotal).complexMean (fun y => f (t.value y)) := by
  apply FiniteProbabilityWeights.ofPositiveWeights_complexMean_equiv (FiniteCoefficientSlice.domainEquiv ht)
  · intro x
    simpa only [FiniteCoefficientSlice.value_domainEquiv] using hs x
  · intro x
    rw [FiniteCoefficientSlice.value_domainEquiv]

end RetainedCoefficientSlice

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

abbrev RetainedCubeBlockDomain {b g q M : ℕ} {B T η : ℝ≥0}
    (s : Fin b → Fin g → RetainedCubeSlice q M B T η) := ∀ a j, (s a j).Domain

noncomputable def retainedCubeBlockSource {b g q M : ℕ} {B T η : ℝ≥0}
    (s : Fin b → Fin g → RetainedCubeSlice q M B T η)
    (hη : 0 < η) : FiniteProbabilityWeights (RetainedCubeBlockDomain s) :=
  FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi (fun j => (s a j).law hη))

noncomputable def retainedCubeBlockSum {b g q M : ℕ} {B T η : ℝ≥0}
    (s : Fin b → Fin g → RetainedCubeSlice q M B T η) (J : Finset (Finset (Fin q)))
    (center : J → ℤ) (x : RetainedCubeBlockDomain s) : J → ℤ :=
  center + ∑ a, fun Z : J => integerBooleanBlockJet (fun j => (s a j).finiteSlice.coordinates (x a j)) Z

theorem retainedCubeBlockSource_normalized {b g q M : ℕ} {B T η : ℝ≥0}
    (s : Fin b → Fin g → RetainedCubeSlice q M B T η)
    (hη : 0 < η) (hB : 0 < B)
    (hlong : ∀ a j, (q + 1) * M ≤ (s a j).length) :
    weightedSliceIntegerSource (fun a j => (s a j).normalized hB hη (hlong a j))
      (fun a j => (s a j).root) = retainedCubeBlockSource s hη := by
  unfold weightedSliceIntegerSource retainedCubeBlockSource
  congr 1
  funext a
  congr 1
  funext j
  exact (s a j).normalized_sliceWeights hB hη (hlong a j)

theorem retainedCubeBlockSum_normalized {b g q M : ℕ} {B T η : ℝ≥0}
    (s : Fin b → Fin g → RetainedCubeSlice q M B T η) (hB : 0 < B) (hη : 0 < η)
    (hlong : ∀ a j, (q + 1) * M ≤ (s a j).length)
    (J : Finset (Finset (Fin q))) :
    weightedSliceIntegerSum (fun a j => (s a j).normalized hB hη (hlong a j))
      (fun a j => (s a j).root) J = retainedCubeBlockSum s J := rfl

theorem retainedCubeBlockSum_support {b g q M K : ℕ} {B T η : ℝ≥0}
    (s : Fin b → Fin g → RetainedCubeSlice q M B T η) {O F : ℝ} (hO : 0 ≤ O)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g)
    (center : J → ℤ) (x : RetainedCubeBlockDomain s) (Z : J) :
    |(retainedCubeBlockSum s J center x Z : ℝ) - center Z| ≤
      (affineTorusRadius q g b (O + 1) F : ℝ) * K := by
  let fs := fun a j => (s a j).finiteSlice
  let coeff := fun (_ : Unit) (_ : Fin b) => (1 : ℤ)
  have hradius (a : Fin b) (j : Fin g) :
      ((fs a j).radius : ℝ) ≤ (((q + 1 : ℕ) : ℝ) * (O + 1)) * (fs a j).length := by
    apply ((s a j).finiteSlice.radius_relative (hroot a j)).trans
    have hq : (1 : ℝ) ≤ (q + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le q))
    have h := mul_le_mul_of_nonneg_right hq
      (show 0 ≤ (O + 1) * (fs a j).length by positivity)
    simpa only [one_mul, mul_assoc] using h
  have hbound := cubeSliceBlockSum_bound fs coeff J center ((), x) Z
  have hscale := cubeSliceBlockBound_le_scale fs coeff () (fun _ => 1)
    (show 0 ≤ ((q + 1 : ℕ) : ℝ) * (O + 1) by positivity)
    (fun _ => by norm_num [coeff]) hradius
    (fun a => by simpa only [one_mul, fs, RetainedCubeSlice.finiteSlice] using hupper a)
    Z (hJ Z Z.property)
  have hraw : |(retainedCubeBlockSum s J center x Z : ℝ) - center Z| ≤
      (cubeSliceBlockBound fs coeff () Z : ℝ) := by
    exact_mod_cast (show |retainedCubeBlockSum s J center x Z - center Z| ≤
      cubeSliceBlockBound fs coeff () Z from by
        simpa only [cubeSliceBlockSum, coeff, one_mul, retainedCubeBlockSum, fs] using hbound)
  exact (hraw.trans hscale).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg K))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {b g q M : ℕ} {B T η : ℝ≥0}
    (s : Fin b → Fin g → RetainedCubeSlice q M B T η) (hη : 0 < η)
    (t : Fin b → Fin g → FiniteCubeSlice q) (ht : ∀ a j, (s a j).finiteSlice = t a j)
    (w : Fin b → Fin g → (Option (Fin q) → ℤ) → ℝ) (hw : ∀ a j z, 0 ≤ w a j z)
    (hs : ∀ a j x, (s a j).sliceWeight x = w a j ((s a j).finiteSlice.coordinates x))
    (htotal : ∀ a j, 0 < ∑ x : (t a j).Domain, w a j ((t a j).coordinates x))

include ht hs

theorem retainedCubeBlockSource_raw_complexMean (f : (Fin b → Fin g → Option (Fin q) → ℤ) → ℂ) :
    (retainedCubeBlockSource s hη).complexMean
      (fun x => f (fun a j => (s a j).finiteSlice.coordinates (x a j))) =
    (rawCubeBlockSource t w hw htotal).complexMean
      (fun x => f (fun a j => (t a j).coordinates (x a j))) := by
  apply FiniteProbabilityWeights.complexMean_pi_transport
    (fun a => FiniteProbabilityWeights.pi (fun j => (s a j).law hη))
    (fun a => FiniteProbabilityWeights.pi (fun j => FiniteProbabilityWeights.ofPositiveWeights
      (fun x => w a j ((t a j).coordinates x)) (fun x => hw a j _) (htotal a j)))
    (fun a x j => (s a j).finiteSlice.coordinates (x j)) (fun a x j => (t a j).coordinates (x j)) _ f
  intro a test
  exact FiniteProbabilityWeights.complexMean_pi_transport
    (fun j => (s a j).law hη)
    (fun j => FiniteProbabilityWeights.ofPositiveWeights (fun x => w a j ((t a j).coordinates x))
      (fun x => hw a j _) (htotal a j))
    (fun j x => (s a j).finiteSlice.coordinates x) (fun j x => (t a j).coordinates x)
    (fun j v => (s a j).law_complexMean_of_finiteSlice_eq hη (t a j) (ht a j)
      (w a j) (hw a j) (hs a j) (htotal a j) v) test

theorem retainedCubeBlockSum_raw_complexMean (J : Finset (Finset (Fin q))) (center : J → ℤ)
    (f : (J → ℤ) → ℂ) :
    (retainedCubeBlockSource s hη).complexMean (fun x => f (retainedCubeBlockSum s J center x)) =
      (rawCubeBlockSource t w hw htotal).complexMean (fun x => f (rawCubeBlockSum t J center x)) :=
  retainedCubeBlockSource_raw_complexMean s hη t ht w hw hs htotal
    (fun z => f (center + ∑ a, fun Z : J => integerBooleanBlockJet (z a) Z))

theorem retainedCubeBlockSum_raw_imageMass (J : Finset (Finset (Fin q))) (center z : J → ℤ) :
    finiteImageMass (retainedCubeBlockSource s hη) (retainedCubeBlockSum s J center) z =
      finiteImageMass (rawCubeBlockSource t w hw htotal) (rawCubeBlockSum t J center) z :=
  finiteImageMass_eq_of_complexMean _ _ _ _
    (retainedCubeBlockSum_raw_complexMean s hη t ht w hw hs htotal J center) z

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

abbrev RetainedModerateBlockDomain {b g q M : ℕ} {B T η : ℝ≥0}
    (c : Fin b → RetainedCoefficientSlice M B T η) (s : Fin b → Fin g → RetainedCubeSlice q M B T η) :=
  ∀ a, (c a).Domain × (∀ j, (s a j).Domain)

noncomputable def retainedModerateBlockSource {b g q M : ℕ} {B T η : ℝ≥0}
    (c : Fin b → RetainedCoefficientSlice M B T η) (s : Fin b → Fin g → RetainedCubeSlice q M B T η)
    (hη : 0 < η) :
    FiniteProbabilityWeights (RetainedModerateBlockDomain c s) :=
  FiniteProbabilityWeights.pi (fun a => ((c a).law hη).prod
    (FiniteProbabilityWeights.pi (fun j => (s a j).law hη)))

noncomputable def retainedModerateBlockSum {b g q M : ℕ} {B T η : ℝ≥0}
    (c : Fin b → RetainedCoefficientSlice M B T η) (s : Fin b → Fin g → RetainedCubeSlice q M B T η)
    (offset : Fin b → ℤ) (stride : Fin b → ℕ) (J : Finset (Finset (Fin q)))
    (center : J → ℤ) (x : RetainedModerateBlockDomain c s) : J → ℤ :=
  center + ∑ a, fun Z : J => (offset a + (stride a : ℤ) * (x a).1.val) *
    integerBooleanBlockJet (fun j => (s a j).finiteSlice.coordinates ((x a).2 j)) Z

theorem retainedModerateBlockSource_normalized {b g q M : ℕ} {B T η : ℝ≥0}
    (c : Fin b → RetainedCoefficientSlice M B T η) (s : Fin b → Fin g → RetainedCubeSlice q M B T η)
    (hη : 0 < η)
    (hB : 0 < B) (hclong : ∀ a, M ≤ (c a).length)
    (hlong : ∀ a j, (q + 1) * M ≤ (s a j).length) :
    moderateSliceIntegerSource (fun a => (c a).normalized hB hη (hclong a))
      (fun a j => (s a j).normalized hB hη (hlong a j)) (fun a j => (s a j).root) =
        retainedModerateBlockSource c s hη := by
  unfold moderateSliceIntegerSource retainedModerateBlockSource
  congr 1
  funext a
  unfold moderateSliceWeights
  apply congrArg₂ FiniteProbabilityWeights.prod
  · exact (c a).normalized_coefficientWeights hB hη (hclong a)
  · congr 1
    funext j
    exact (s a j).normalized_sliceWeights hB hη (hlong a j)

theorem retainedModerateBlockSum_normalized {b g q M : ℕ} {B T η : ℝ≥0}
    (c : Fin b → RetainedCoefficientSlice M B T η) (s : Fin b → Fin g → RetainedCubeSlice q M B T η)
    (hB : 0 < B) (hη : 0 < η) (hclong : ∀ a, M ≤ (c a).length)
    (hlong : ∀ a j, (q + 1) * M ≤ (s a j).length)
    (offset : Fin b → ℤ) (stride : Fin b → ℕ) (J : Finset (Finset (Fin q))) :
    moderateSliceIntegerSum (fun a => (c a).normalized hB hη (hclong a))
      (fun a j => (s a j).normalized hB hη (hlong a j)) offset stride (fun a j => (s a j).root) J =
        retainedModerateBlockSum c s offset stride J := rfl

theorem retainedModerateBlockSum_support {b g q M K : ℕ} {B T η : ℝ≥0}
    (c : Fin b → RetainedCoefficientSlice M B T η) (s : Fin b → Fin g → RetainedCubeSlice q M B T η)
    (offset : Fin b → ℤ) (stride : Fin b → ℕ) {O F : ℝ} (hO : 0 ≤ O)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (|(offset a : ℝ)| + (stride a : ℝ) * (c a).length) *
      (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g)
    (center : J → ℤ) (x : RetainedModerateBlockDomain c s) (Z : J) :
    |(retainedModerateBlockSum c s offset stride J center x Z : ℝ) - center Z| ≤
      (affineTorusRadius q g b (O + 1) F : ℝ) * K := by
  let fs := fun a j => (s a j).finiteSlice
  let coeff := fun (z : ∀ a, (c a).Domain) a => offset a + (stride a : ℤ) * (z a).val
  let z := fun a => (x a).1
  let y := fun a j => (x a).2 j
  let H := fun a => |(offset a : ℝ)| + (stride a : ℝ) * (c a).length
  have hradius (a : Fin b) (j : Fin g) :
      ((fs a j).radius : ℝ) ≤ (((q + 1 : ℕ) : ℝ) * (O + 1)) * (fs a j).length := by
    apply ((s a j).finiteSlice.radius_relative (hroot a j)).trans
    have hq : (1 : ℝ) ≤ (q + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le q))
    have h := mul_le_mul_of_nonneg_right hq
      (show 0 ≤ (O + 1) * (fs a j).length by positivity)
    simpa only [one_mul, mul_assoc] using h
  have hbound := cubeSliceBlockSum_bound fs coeff J center (z, y) Z
  have hscale := cubeSliceBlockBound_le_scale fs coeff z H
    (show 0 ≤ ((q + 1 : ℕ) : ℝ) * (O + 1) by positivity)
    (fun a => (c a).affine_abs_le (offset a) (stride a) (z a)) hradius
    (fun a => by simpa only [H, fs, RetainedCubeSlice.finiteSlice] using hupper a)
    Z (hJ Z Z.property)
  have hraw : |(retainedModerateBlockSum c s offset stride J center x Z : ℝ) - center Z| ≤
      (cubeSliceBlockBound fs coeff z Z : ℝ) := by
    exact_mod_cast (show |retainedModerateBlockSum c s offset stride J center x Z - center Z| ≤
      cubeSliceBlockBound fs coeff z Z from by
        simpa only [cubeSliceBlockSum, coeff, retainedModerateBlockSum, fs, z, y] using hbound)
  exact (hraw.trans hscale).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg K))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem FiniteProbabilityWeights.complexMean_prod_transport
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (p₁ : FiniteProbabilityWeights X₁) (p₂ : FiniteProbabilityWeights X₂)
    (q₁ : FiniteProbabilityWeights Y₁) (q₂ : FiniteProbabilityWeights Y₂)
    (F₁ : X₁ → Z₁) (F₂ : X₂ → Z₂) (G₁ : Y₁ → Z₁) (G₂ : Y₂ → Z₂)
    (h₁ : ∀ f : Z₁ → ℂ, p₁.complexMean (fun x => f (F₁ x)) = q₁.complexMean (fun y => f (G₁ y)))
    (h₂ : ∀ f : Z₂ → ℂ, p₂.complexMean (fun x => f (F₂ x)) = q₂.complexMean (fun y => f (G₂ y)))
    (f : Z₁ × Z₂ → ℂ) :
    (p₁.prod p₂).complexMean (fun x => f (F₁ x.1, F₂ x.2)) =
      (q₁.prod q₂).complexMean (fun y => f (G₁ y.1, G₂ y.2)) := by
  rw [FiniteProbabilityWeights.complexMean_prod, FiniteProbabilityWeights.complexMean_prod]
  calc
    _ = p₁.complexMean (fun x => q₂.complexMean (fun y => f (F₁ x, G₂ y))) := by
      congr 1
      funext x
      exact h₂ (fun z => f (F₁ x, z))
    _ = _ := h₁ (fun z => q₂.complexMean (fun y => f (z, G₂ y)))

variable {b g q M : ℕ} {B T η : ℝ≥0}
    (c : Fin b → RetainedCoefficientSlice M B T η)
    (s : Fin b → Fin g → RetainedCubeSlice q M B T η) (hη : 0 < η)
    (offset : Fin b → ℤ) (stride : Fin b → ℕ)
    (d : Fin b → FiniteCoefficientSlice) (t : Fin b → Fin g → FiniteCubeSlice q)
    (hd : ∀ a, (c a).finiteSlice (offset a) (stride a) = d a)
    (ht : ∀ a j, (s a j).finiteSlice = t a j)
    (v : Fin b → ℤ → ℝ) (w : Fin b → Fin g → (Option (Fin q) → ℤ) → ℝ)
    (hv : ∀ a z, 0 ≤ v a z) (hw : ∀ a j z, 0 ≤ w a j z)
    (hc : ∀ a x, (c a).sliceWeight x = v a (((c a).finiteSlice (offset a) (stride a)).value x))
    (hs : ∀ a j x, (s a j).sliceWeight x = w a j ((s a j).finiteSlice.coordinates x))
    (vtotal : ∀ a, 0 < ∑ x : (d a).Domain, v a ((d a).value x))
    (htotal : ∀ a j, 0 < ∑ x : (t a j).Domain, w a j ((t a j).coordinates x))

include hd ht hc hs

theorem retainedModerateBlockSource_raw_complexMean
    (f : (Fin b → ℤ × (Fin g → Option (Fin q) → ℤ)) → ℂ) :
    (retainedModerateBlockSource c s hη).complexMean
      (fun x => f (fun a => (((c a).finiteSlice (offset a) (stride a)).value (x a).1,
        fun j => (s a j).finiteSlice.coordinates ((x a).2 j)))) =
    (rawModerateBlockSource d t v w hv hw vtotal htotal).complexMean
      (fun x => f (fun a => ((d a).value (x a).1, fun j => (t a j).coordinates ((x a).2 j)))) := by
  apply FiniteProbabilityWeights.complexMean_pi_transport
    (fun a => ((c a).law hη).prod (FiniteProbabilityWeights.pi (fun j => (s a j).law hη)))
    (fun a => (FiniteProbabilityWeights.ofPositiveWeights (fun x => v a ((d a).value x))
      (fun x => hv a _) (vtotal a)).prod (FiniteProbabilityWeights.pi (fun j =>
        FiniteProbabilityWeights.ofPositiveWeights (fun x => w a j ((t a j).coordinates x))
          (fun x => hw a j _) (htotal a j))))
    (fun a x => (((c a).finiteSlice (offset a) (stride a)).value x.1,
      fun j => (s a j).finiteSlice.coordinates (x.2 j)))
    (fun a x => ((d a).value x.1, fun j => (t a j).coordinates (x.2 j))) _ f
  intro a test
  apply FiniteProbabilityWeights.complexMean_prod_transport
    ((c a).law hη) (FiniteProbabilityWeights.pi (fun j => (s a j).law hη))
    (FiniteProbabilityWeights.ofPositiveWeights (fun x => v a ((d a).value x)) (fun x => hv a _) (vtotal a))
    (FiniteProbabilityWeights.pi (fun j => FiniteProbabilityWeights.ofPositiveWeights
      (fun x => w a j ((t a j).coordinates x)) (fun x => hw a j _) (htotal a j)))
    (((c a).finiteSlice (offset a) (stride a)).value)
    (fun x j => (s a j).finiteSlice.coordinates (x j))
    ((d a).value) (fun x j => (t a j).coordinates (x j)) _ _ test
  · intro f
    exact (c a).law_complexMean_of_finiteSlice_eq hη (offset a) (stride a) (d a) (hd a)
      (v a) (hv a) (hc a) (vtotal a) f
  · intro f
    exact FiniteProbabilityWeights.complexMean_pi_transport
      (fun j => (s a j).law hη)
      (fun j => FiniteProbabilityWeights.ofPositiveWeights (fun x => w a j ((t a j).coordinates x))
        (fun x => hw a j _) (htotal a j))
      (fun j x => (s a j).finiteSlice.coordinates x) (fun j x => (t a j).coordinates x)
      (fun j f => (s a j).law_complexMean_of_finiteSlice_eq hη (t a j) (ht a j)
        (w a j) (hw a j) (hs a j) (htotal a j) f) f

theorem retainedModerateBlockSum_raw_complexMean (J : Finset (Finset (Fin q))) (center : J → ℤ)
    (f : (J → ℤ) → ℂ) :
    (retainedModerateBlockSource c s hη).complexMean
      (fun x => f (retainedModerateBlockSum c s offset stride J center x)) =
      (rawModerateBlockSource d t v w hv hw vtotal htotal).complexMean
        (fun x => f (rawModerateBlockSum d t J center x)) :=
  retainedModerateBlockSource_raw_complexMean c s hη offset stride d t hd ht v w hv hw hc hs vtotal htotal
    (fun z => f (center + ∑ a, fun Z : J => (z a).1 * integerBooleanBlockJet (z a).2 Z))

theorem retainedModerateBlockSum_raw_imageMass (J : Finset (Finset (Fin q))) (center z : J → ℤ) :
    finiteImageMass (retainedModerateBlockSource c s hη) (retainedModerateBlockSum c s offset stride J center) z =
      finiteImageMass (rawModerateBlockSource d t v w hv hw vtotal htotal) (rawModerateBlockSum d t J center) z :=
  finiteImageMass_eq_of_complexMean _ _ _ _
    (retainedModerateBlockSum_raw_complexMean c s hη offset stride d t hd ht v w hv hw hc hs vtotal htotal J center) z

end Erdos3

end

section

namespace Erdos3.RelativeProgression

open scoped BigOperators NNReal Classical

theorem retainedCubeSource_complexMean {δ : ℝ} (P : RelativeProgression δ)
    (q R : ℕ) (hδ : 0 < δ) (hR : 0 < R) (r : P.CubeResidueLabel q R)
    (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w) (hη : 0 < η)
    (hr : r ∉ (P.cubeReference q hδ).lowWeightFibers
      ((P.cubeSlice q).residueLabelMap (fun _ => P.canonicalStep * R))
      (fun x => translatedCubeWeight P.parentLength 0 w ((P.cubeSlice q).coordinates x)) η)
    (f : (Option (Fin q) → ℤ) → ℂ) :
    let _ := P.cubeSlice_nonempty q hδ
    let s := P.retainedCubeSource q R hδ hR r w B T η hw hLip hr
    (s.law hη).complexMean (fun x => f (s.finiteSlice.coordinates x)) =
      ((P.cubeSlice q).retainedRefinementLaw (fun _ => P.canonicalStep * R)
        (fun _ => ⟨R, rfl⟩) (translatedCubeWeight P.parentLength 0 w) (fun _ => (hw _).1)
        (show (0 : ℝ) < η from hη) r hr).complexMean
          (fun x => f (((P.cubeSlice q).refineResidues (fun _ => P.canonicalStep * R) r).coordinates x)) := by
  let := P.cubeSlice_nonempty q hδ
  dsimp only
  exact (P.retainedCubeSource q R hδ hR r w B T η hw hLip hr).law_complexMean_of_finiteSlice_eq hη
    ((P.cubeSlice q).refineResidues (fun _ => P.canonicalStep * R) r)
    (P.retainedCubeSource_finiteSlice q R hδ hR r w B T η hw hLip hr)
    (translatedCubeWeight P.parentLength 0 w) (fun _ => (hw _).1)
    (P.retainedCubeSource_sliceWeight q R hδ hR r w B T η hw hLip hr)
    ((P.cubeSlice q).retained_refineResidues_total_pos (fun _ => P.canonicalStep * R)
      (fun _ => ⟨R, rfl⟩) r (translatedCubeWeight P.parentLength 0 w) (show (0 : ℝ) < η from hη) hr) f

theorem retainedCoefficientSource_complexMean {δ : ℝ} (P : RelativeProgression δ)
    (R : ℕ) (hδ : 0 < δ) (hR : 0 < R) (r : P.CoefficientResidueLabel R)
    (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w) (hη : 0 < η)
    (hr : r ∉ (P.coefficientReference hδ).lowWeightFibers (P.coefficientSlice.residueLabelMap R)
      (fun x => w (fun _ => ((P.coefficientSlice.value x : ℤ) : ℝ) / P.parentLength)) η)
    (f : ℤ → ℂ) :
    let _ := P.coefficientSlice_nonempty hδ
    let s := P.retainedCoefficientSource R hδ hR r w B T η hw hLip hr
    (s.law hη).complexMean (fun x => f ((s.finiteSlice P.root P.canonicalStep).value x)) =
      (P.coefficientSlice.retainedRefinementLaw R (one_dvd R)
        (fun z => w (fun _ => (z : ℝ) / P.parentLength)) (fun _ => (hw _).1)
        (show (0 : ℝ) < η from hη) r hr).complexMean
          (fun x => f ((P.coefficientSlice.refineResidues R r).value x)) := by
  let := P.coefficientSlice_nonempty hδ
  dsimp only
  exact (P.retainedCoefficientSource R hδ hR r w B T η hw hLip hr).law_complexMean_of_finiteSlice_eq hη
    P.root P.canonicalStep (P.coefficientSlice.refineResidues R r)
    (P.retainedCoefficientSource_finiteSlice R hδ hR r w B T η hw hLip hr)
    (fun z => w (fun _ => (z : ℝ) / P.parentLength)) (fun _ => (hw _).1)
    (P.retainedCoefficientSource_sliceWeight R hδ hR r w B T η hw hLip hr)
    (P.coefficientSlice.retained_refineResidues_total_pos R (one_dvd R) r
      (fun z => w (fun _ => (z : ℝ) / P.parentLength)) (show (0 : ℝ) < η from hη) hr) f

end Erdos3.RelativeProgression

end

end OAI
