import OAI.NumberTheory.CubicMoment.Estimates.RamifiedIdealParts
import OAI.NumberTheory.CubicMoment.Estimates.IdealMoebiusBounds

namespace OAI

/-! The actual small-prime partition of squarefree cubic moduli. Its
parts divide the small modulus, so their number has a proved subpower bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def supportedIdealPart (v : Eisenstein) (ν : EisensteinIdealExponent) : EisensteinIdealExponent :=
  ν.filter (fun p => p ∈ (idealExponentOf v).support)

def outsideIdealPart (v : Eisenstein) (ν : EisensteinIdealExponent) : EisensteinIdealExponent :=
  ν.filter (fun p => p ∉ (idealExponentOf v).support)

lemma supported_add_outside (v : Eisenstein) (ν : EisensteinIdealExponent) :
    supportedIdealPart v ν+outsideIdealPart v ν = ν := Finsupp.filter_add_filter_not _ _

lemma supportedIdealPart_le (v : Eisenstein) (ν : EisensteinIdealExponent) :
    supportedIdealPart v ν ≤ ν := by
  intro p
  simp only [supportedIdealPart,Finsupp.filter_apply]
  split <;> simp

lemma outsideIdealPart_le (v : Eisenstein) (ν : EisensteinIdealExponent) :
    outsideIdealPart v ν ≤ ν := by
  intro p
  simp only [outsideIdealPart,Finsupp.filter_apply]
  split <;> simp

def primarySmallPart (v a : Eisenstein) : Eisenstein :=
  idealPrimaryGenerator (supportedIdealPart v (idealExponentOf a))

def primaryOutsidePart (v a : Eisenstein) : Eisenstein :=
  idealPrimaryGenerator (outsideIdealPart v (idealExponentOf a))

lemma primarySmallPart_primary (v : Eisenstein) {a : Eisenstein} (ha : primary a) :
    primary (primarySmallPart v a) := idealPrimaryGenerator_primary ha (supportedIdealPart_le v _)

lemma primaryOutsidePart_primary (v : Eisenstein) {a : Eisenstein} (ha : primary a) :
    primary (primaryOutsidePart v a) := idealPrimaryGenerator_primary ha (outsideIdealPart_le v _)

lemma primary_small_outside_mul (v : Eisenstein) {a : Eisenstein} (ha : primary a) :
    primarySmallPart v a*primaryOutsidePart v a = a := by
  have hle : supportedIdealPart v (idealExponentOf a)+outsideIdealPart v (idealExponentOf a) ≤
      idealExponentOf a := by rw [supported_add_outside]
  rw [primarySmallPart,primaryOutsidePart,← idealPrimaryGenerator_add ha hle,
    supported_add_outside,idealPrimaryGenerator_at_element ha]

lemma primarySmallPart_dvd {a v : Eisenstein} (ha : Squarefree a) (hv : v ≠ 0) :
    primarySmallPart v a ∣ v := by
  have hle : supportedIdealPart v (idealExponentOf a) ≤ idealExponentOf v := by
    intro p
    simp only [supportedIdealPart,Finsupp.filter_apply]
    split_ifs with hp
    · exact ((idealExponentOf_squarefree_iff ha.ne_zero).mpr ha p).trans
        (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp))
    · exact Nat.zero_le _
  exact (primaryNormalize_associated _).symm.dvd.trans
    ((idealExponentGenerator_dvd_of_le hle).trans (idealExponentOf_associated hv).dvd)

lemma primaryOutsidePart_coprime {a v : Eisenstein} (ha : primary a) (hv : v ≠ 0) :
    IsCoprime (primaryOutsidePart v a) v := by
  rw [isCoprime_iff_idealExponent_disjoint
    (primary_ne_zero (primaryOutsidePart_primary v ha)) hv]
  change ∀ p, idealExponentOf (idealPrimaryGenerator (outsideIdealPart v (idealExponentOf a))) p = 0 ∨
    idealExponentOf v p = 0
  rw [idealExponentOf_primaryGenerator]
  intro p
  by_cases hp : p ∈ (idealExponentOf v).support
  · left
    have hne := Finsupp.mem_support_iff.mp hp
    simp [outsideIdealPart,hne]
  · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

lemma primarySmallPart_squarefree (v : Eisenstein) {a : Eisenstein}
    (ha : primary a) (hsa : Squarefree a) : Squarefree (primarySmallPart v a) := by
  have hs : Squarefree (primarySmallPart v a*primaryOutsidePart v a) := by
    rw [primary_small_outside_mul v ha]
    exact hsa
  exact hs.of_mul_left

lemma primaryOutsidePart_squarefree (v : Eisenstein) {a : Eisenstein}
    (ha : primary a) (hsa : Squarefree a) : Squarefree (primaryOutsidePart v a) := by
  have hs : Squarefree (primarySmallPart v a*primaryOutsidePart v a) := by
    rw [primary_small_outside_mul v ha]
    exact hsa
  exact hs.of_mul_right

theorem smallPrimeParts_card {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (v : Eisenstein), v ≠ 0 →
      (∀ a ∈ P, primary a ∧ Squarefree a) →
      ((P.image (primarySmallPart v)).card:ℝ) ≤ C*norm v^ε := by
  obtain ⟨C,hC,hbound⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro P v hv hP
  let T := P.image (primarySmallPart v)
  have hprim (x : Eisenstein) (hx : x ∈ T) : primary x := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact primarySmallPart_primary v (hP a ha).1
  have hdiv (x : Eisenstein) (hx : x ∈ T) : x ∣ v := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact primarySmallPart_dvd (hP a ha).2 hv
  have he : T.filter (fun x => x ∣ v) = T := Finset.filter_eq_self.mpr hdiv
  have h := hbound T hprim v hv
  rwa [he] at h

end CubicFirstMoment

end

end OAI
