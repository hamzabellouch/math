import OAI.Analysis.CStarAlgebra.PureInfiniteness.ChoicePairs

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance fourChoicesPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance fourChoicesStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem finite_four_choices {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hp : ∀ z : A, 0 ≤ z → z ∈ fourHer X → ProperlyInfinite z)
    (E : Finset A) {η : ℝ} (hη : 0 < η) :
    ∃ T : Fin 4 → A,
      (∀ i, ‖T i‖ ≤ 1) ∧ (∀ i, T i ∈ fourHer X) ∧
      T 0 * star (T 0) = ramp (firstSandwich (firstU X (B 0)) (firstV X) η E) η (2*η) ∧
      T 1 * star (T 1) = T 0 * star (T 0) ∧ T 0 * star (T 1) = 0 ∧
      star (T 0) * T 0 ∈ Her (firstV X) ∧ star (T 1) * T 1 ∈ Her (firstV X) ∧
      star (T 2) * T 3 = 0 ∧ star (T 2) * T 2 = star (T 3) * T 3 ∧
      T 2 * star (T 2) ∈ Her (cut (lastR X (B 0) (B 2)) η) ∧
      T 3 * star (T 3) ∈ Her (cut (lastR X (B 0) (B 2)) η) ∧
      (∀ {D : Type*} [NonUnitalCStarAlgebra D] (π : A →⋆ₙₐ[ℂ] D),
        4*η ≤ ‖π (lastR X (B 0) (B 2))‖ → ‖π (T 2)‖ = 1) := by
  let U := firstU X (B 0)
  let V := firstV X
  let R := lastR X (B 0) (B 2)
  let D₀ := firstSandwich U V η E
  have hV : 0 ≤ V := cut_nonneg X _
  have hVk : V ∈ fourHer X := firstV_mem hX
  have hDk : D₀ ∈ fourHer X := Her_mono_of_mem (firstU_mem hX (B 0))
    (Her_mono_of_mem (cut_mem_Her (firstU_nonneg X (B 0)) η) (firstSandwich_mem U V η E))
  obtain ⟨T₀, hT₀norm, hT₀mem, hT₀mod, hT₀outer⟩ :=
    first_pair_choice (firstSandwich_nonneg hV η E) hV
      (firstSandwich_two_cuntzLE (hp V hV hVk) η E) hDk hVk hη
  obtain ⟨T₂, hT₂norm, hT₂mem, hT₂mod, hT₂outer, hT₂rep⟩ :=
    last_pair_choice (lastR_nonneg X (B 0) (B 2)) (lastR_mem hX _ _) hη
      (hp (cut R η) (cut_nonneg R η)
        (Her_mono_of_mem (lastR_mem hX _ _) (cut_mem_Her (lastR_nonneg X (B 0) (B 2)) η)))
  refine ⟨![T₀ 0, T₀ 1, T₂ 0, T₂ 1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> first | exact hT₀norm _ | exact hT₂norm _
  · intro i; fin_cases i <;> first | exact hT₀mem _ | exact hT₂mem _
  · simpa using hT₀mod 0 0
  · simpa using (hT₀mod 1 1).trans (hT₀mod 0 0).symm
  · simpa using hT₀mod 0 1
  · exact hT₀outer 0 0
  · exact hT₀outer 1 1
  · simpa using hT₂mod 0 1
  · simpa using (hT₂mod 0 0).trans (hT₂mod 1 1).symm
  · exact hT₂outer 0 0
  · exact hT₂outer 1 1
  · intro D _ π hR
    exact hT₂rep π hR 0

end MainGap

namespace MainGap
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
local instance fourChoicesMapDomainOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance fourChoicesMapDomainStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance fourChoicesMapCodomainOrder : PartialOrder D := CStarAlgebra.spectralOrder D
local instance fourChoicesMapCodomainStarOrder : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
variable (π : A →⋆ₐ[ℂ] D)

lemma map_cut_sa {a : A} (ha : IsSelfAdjoint a) {l : ℝ} (hl : 0 ≤ l) :
    π (cut a l) = cut (π a) l :=
  π.toNonUnitalStarAlgHom.map_cfcₙ (fun t : ℝ => max (t-l) 0) a
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [max_eq_right (neg_nonpos.mpr hl)]) (map_continuous π) ha (ha.map π)

lemma map_ramp_sa {a : A} (ha : IsSelfAdjoint a) {l u : ℝ} (hl : 0 ≤ l) :
    π (ramp a l u) = ramp (π a) l u :=
  π.toNonUnitalStarAlgHom.map_cfcₙ (rampFn l u) a
    (continuous_rampFn l u).continuousOn (rampFn_zero hl)
    (map_continuous π) ha (ha.map π)

lemma map_deficiency {d : A} (hd : IsSelfAdjoint d) :
    π (deficiency d) = deficiency (π d) :=
  π.map_cfc (fun t : ℝ => max (1/2-t) 0) d
    ((continuous_const.sub continuous_id).max continuous_const).continuousOn
    (map_continuous π) hd (hd.map π)

lemma map_sqrt {a : A} (ha : 0 ≤ a) : π (CFC.sqrt a) = CFC.sqrt (π a) :=
  π.toNonUnitalStarAlgHom.map_cfcₙ NNReal.sqrt a (by fun_prop) (by simp)
    (map_continuous π) ha (map_nonneg π ha)

lemma map_firstX {X : A} (hX : IsSelfAdjoint X) : π (firstX X) = firstX (π X) :=
  map_cut_sa π hX (by norm_num)
lemma map_firstV {X : A} (hX : IsSelfAdjoint X) : π (firstV X) = firstV (π X) :=
  map_cut_sa π hX (by norm_num)
lemma map_firstH {X : A} (hX : IsSelfAdjoint X) : π (firstH X) = firstH (π X) :=
  map_ramp_sa π hX (by norm_num)
lemma map_firstK {X : A} (hX : IsSelfAdjoint X) : π (firstK X) = firstK (π X) :=
  map_ramp_sa π hX (by norm_num)

lemma map_firstU {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (firstU X B) = firstU (π X) (π B) := by
  simp only [firstU, map_mul, map_firstX π hX,
    map_deficiency π (.mul_star_self B), map_star]

lemma map_firstR {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (firstR X B) = firstR (π X) (π B) := by
  change π ((Real.sqrt 2) • (star B * firstH X)) = _
  calc
    π ((Real.sqrt 2) • (star B * firstH X)) = (Real.sqrt 2) • π (star B * firstH X) :=
      π.toAlgHom.map_smul_of_tower _ _
    _ = firstR (π X) (π B) := by simp only [firstR, map_mul, map_star, map_firstH π hX]

lemma map_scalingComplement {H : A} (hH : IsSelfAdjoint H) (hn : ‖H‖ ≤ 1) :
    π (scalingComplement H) = scalingComplement (π H) := by
  simp only [scalingComplement, map_sqrt π (complement_nonneg hH hn), map_sub, map_one, map_mul]

lemma map_scalingDefect {H : A} (hH : IsSelfAdjoint H) (hn : ‖H‖ ≤ 1) (r : A) :
    π (scalingDefect H r) = scalingDefect (π H) (π r) := by
  simp only [scalingDefect, scalingIsometry, map_sub, map_mul, map_star, map_one, map_add,
    map_scalingComplement π hH hn]

lemma scalingDefect_selfAdjoint (H r : A) : IsSelfAdjoint (scalingDefect H r) :=
  (IsSelfAdjoint.one A).sub (.mul_star_self _)

lemma prospective_input_selfAdjoint (X B : A) :
    IsSelfAdjoint (firstK X * scalingDefect (firstH X) (firstR X B) * firstK X) := by
  have hK : IsSelfAdjoint (firstK X) := .of_nonneg (ramp_nonneg X (by norm_num))
  rw [isSelfAdjoint_iff]
  simp only [star_mul, hK.star_eq, scalingDefect_selfAdjoint _ _ |>.star_eq, mul_assoc]

lemma map_prospectiveDefect {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (prospectiveDefect X B) = prospectiveDefect (π X) (π B) := by
  have hH : IsSelfAdjoint (firstH X) := .of_nonneg (ramp_nonneg X (by norm_num))
  have hn : ‖firstH X‖ ≤ 1 := norm_ramp_le_one _ (by norm_num)
  simp only [prospectiveDefect, map_ramp_sa π (prospective_input_selfAdjoint X B) le_rfl,
    map_mul, map_firstK π hX, map_scalingDefect π hH hn, map_firstH π hX,
    map_firstR π hX]

lemma map_lastX {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (lastX X B) = lastX (π X) (π B) := by
  have hp : IsSelfAdjoint (prospectiveDefect X B) := .of_nonneg (ramp_nonneg _ (by norm_num))
  rw [lastX, map_cut_sa π hp (by norm_num), map_prospectiveDefect π hX]
  rfl

lemma map_lastR {X : A} (hX : IsSelfAdjoint X) (B C : A) :
    π (lastR X B C) = lastR (π X) (π B) (π C) := by
  simp only [lastR, map_mul, map_lastX π hX,
    map_deficiency π (.mul_star_self C), map_star]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance fourChoiceStructureOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance fourChoiceStructureStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

universe v

structure FourChoice (X : A) (B : Fin 4 → A) (E : Finset A) (η : ℝ) where
  T : Fin 4 → A
  contractive : ∀ i, ‖T i‖ ≤ 1
  mem : ∀ i, T i ∈ fourHer X
  first_mod : T 0 * star (T 0) = ramp (firstSandwich (firstU X (B 0)) (firstV X) η E) η (2*η)
  first_equal : T 1 * star (T 1) = T 0 * star (T 0)
  first_cross : T 0 * star (T 1) = 0
  outer₀ : star (T 0) * T 0 ∈ Her (firstV X)
  outer₁ : star (T 1) * T 1 ∈ Her (firstV X)
  last_cross : star (T 2) * T 3 = 0
  last_equal : star (T 2) * T 2 = star (T 3) * T 3
  outer₂ : T 2 * star (T 2) ∈ Her (cut (lastR X (B 0) (B 2)) η)
  outer₃ : T 3 * star (T 3) ∈ Her (cut (lastR X (B 0) (B 2)) η)
  last_norm : ∀ {D : Type v} [NonUnitalCStarAlgebra D] (π : A →⋆ₙₐ[ℂ] D),
    4*η ≤ ‖π (lastR X (B 0) (B 2))‖ → ‖π (T 2)‖ = 1

theorem fourChoice_nonempty {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hp : ∀ z : A, 0 ≤ z → z ∈ fourHer X → ProperlyInfinite z)
    (E : Finset A) {η : ℝ} (hη : 0 < η) : Nonempty (FourChoice.{v, _} X B E η) := by
  obtain ⟨T, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ :=
    finite_four_choices hX B hp E hη
  exact ⟨⟨T, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩⟩

lemma firstH_fixes_V {X : A} (hX : 0 ≤ X) : firstH X * firstV X = firstV X :=
  ramp_mul_cut hX (by norm_num) (by norm_num) le_rfl

namespace FourChoice
variable {X : A} {B : Fin 4 → A} {E : Finset A} {η : ℝ} (F : FourChoice.{v, _} X B E η)

lemma first_mem (hη : 0 < η) :
    F.T 0 * star (F.T 0) ∈ Her (cut (firstU X (B 0)) η) := by
  rw [F.first_mod]
  exact Her_mono_of_mem (firstSandwich_mem _ _ η E)
    (Her_mono_of_mem (cut_mem_Her (firstSandwich_nonneg (cut_nonneg X _) η E) η)
      (ramp_mem_Her_cut (firstSandwich_nonneg (cut_nonneg X _) η E) hη.le))

lemma first_support₀ (hX : 0 ≤ X) : firstH X * star (F.T 0) = star (F.T 0) := by
  apply fixed_left_of_modulus
  simp only [star_star]
  exact Her_fixed_left (firstH_fixes_V hX) F.outer₀

lemma first_support₁ (hX : 0 ≤ X) : firstH X * star (F.T 1) = star (F.T 1) := by
  apply fixed_left_of_modulus
  simp only [star_star]
  exact Her_fixed_left (firstH_fixes_V hX) F.outer₁

lemma last_support : ramp (prospectiveDefect X (B 0)) 0 (1/2) * F.T 3 = F.T 3 := by
  apply fixed_left_of_modulus
  apply Her_fixed_left (ramp_mul_cut (prospectiveDefect_nonneg X _)
    le_rfl (by norm_num : (0:ℝ) < 1/2) le_rfl)
  exact Her_mono_of_mem (squareSandwich_mem (.of_nonneg (lastX_nonneg X _)) _)
    (Her_mono_of_mem (cut_mem_Her (lastR_nonneg X _ _) η) F.outer₃)

variable {D : Type v} [CStarAlgebra D]
local instance fourChoiceRepresentationOrder : PartialOrder D := CStarAlgebra.spectralOrder D
local instance fourChoiceRepresentationStarOrder : StarOrderedRing D :=
  CStarAlgebra.spectralOrderedRing D
variable (π : A →⋆ₐ[ℂ] D) (hX : 0 ≤ X) (hη : 0 < η)
  (hmatch : ∀ i, π (F.T i) = π (B i))

include F hX hη hmatch in
lemma first_bound : π (B 0) * star (π (B 0)) ≤ (1/2 : ℝ) • (1 : D) := by
  have hm := Her_map π.toNonUnitalStarAlgHom (F.first_mem hη)
  change π (F.T 0 * star (F.T 0)) ∈ Her (π (cut (firstU X (B 0)) η)) at hm
  simp only [map_mul, map_star, hmatch] at hm
  rw [map_cut_sa π (.of_nonneg (firstU_nonneg X (B 0))) hη.le,
    map_firstU π (.of_nonneg hX)] at hm
  exact selfConsistent_cutoff_bound (cut_nonneg (π X) _)
    (mul_star_self_nonneg _) hη (by norm_num) hm

include F hX hη hmatch in
lemma last_bound : π (B 2) * star (π (B 2)) ≤ (1/2 : ℝ) • (1 : D) := by
  have hm := Her_map π.toNonUnitalStarAlgHom F.outer₂
  change π (F.T 2 * star (F.T 2)) ∈ Her (π (cut (lastR X (B 0) (B 2)) η)) at hm
  simp only [map_mul, map_star, hmatch] at hm
  rw [map_cut_sa π (.of_nonneg (lastR_nonneg X (B 0) (B 2))) hη.le,
    map_lastR π (.of_nonneg hX)] at hm
  exact selfConsistent_cutoff_bound (lastX_nonneg (π X) _)
    (mul_star_self_nonneg _) hη (by norm_num) hm

include F hX hη hmatch in
lemma first_norm : ‖π (firstSandwich (firstU X (B 0)) (firstV X) η E)‖ < 2*η := by
  have hpos : 0 ≤ firstSandwich (firstU X (B 0)) (firstV X) η E :=
    firstSandwich_nonneg (cut_nonneg X _) η E
  have hmod := congrArg π F.first_mod
  rw [map_mul, map_star, hmatch, map_ramp_sa π (.of_nonneg hpos) hη.le] at hmod
  apply norm_ramp_bound (map_nonneg π hpos)
    hη (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  rw [← hmod]
  exact F.first_bound π hX hη hmatch

include F hX hη hmatch in
lemma last_norm_lt : ‖π (lastR X (B 0) (B 2))‖ < 4*η := by
  by_contra! hn
  have hone : ‖π (B 2)‖ = 1 := by
    have ht : ‖π (F.T 2)‖ = 1 := F.last_norm π.toNonUnitalStarAlgHom hn
    rwa [hmatch] at ht
  have hle : ‖π (B 2) * star (π (B 2))‖ ≤ 1/2 := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (by norm_num : (0:ℝ) ≤ 1/2)
      (mul_star_self_nonneg _)).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using F.last_bound π hX hη hmatch
  rw [CStarRing.norm_self_mul_star, hone] at hle
  norm_num at hle

end FourChoice
end MainGap

end

end OAI
