import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Entropy.Pairs

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def outsideAt (S O : Finset (ℙ K V)) :
    Finset {y : ℙ K V // x ≠ y} := (S \ O).subtype (fun y => x ≠ y)

noncomputable def radialWeight (X : Finset {y : ℙ K V // x ≠ y})
    (δ : ℝ≥0) (l : RadialLine x) : ℝ≥0 :=
  δ * (RadialLine.trainingOnLine X l).card

noncomputable def pencilLines (F : Finset (ℙ K (Module.Dual K V)))
    (H : F) : Finset (RadialLine x) := RadialLine.inFlat (LinearMap.ker H.val.rep)

lemma mass_inFlat (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (W : Submodule K V) (hx : x.submodule ≤ W) :
    PoissonScore.mass (radialWeight x X δ) (RadialLine.inFlat W) =
      (δ:ℝ) * (X.filter fun y => y.val.submodule ≤ W).card := by
  unfold PoissonScore.mass radialWeight
  simp only [NNReal.coe_mul, NNReal.coe_natCast, ← Finset.mul_sum, ← Nat.cast_sum]
  rw [RadialLine.sum_trainingOnLine X W hx]

lemma mass_pencil (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H) =
      (δ:ℝ) * (X.filter fun y => Incident y.val H.val).card :=
  mass_inFlat x X δ _ (hF H.val H.property)

lemma mass_overlap (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') =
      (δ:ℝ) * (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
  unfold pencilLines
  rw [RadialLine.inFlat_inf, mass_inFlat x X δ _ (le_inf (hF H.val H.property)
    (hF H'.val H'.property))]
  simp only [Incident, le_inf_iff]
  rfl

omit [FiniteDimensional K V] [Fintype (RadialLine x)] in
lemma weight_pos_lower (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (l : RadialLine x) (h : 0 < radialWeight x X δ l) :
    δ ≤ radialWeight x X δ l := by
  have hc : 0 < (RadialLine.trainingOnLine X l).card := by
    by_contra hn
    have := Nat.eq_zero_of_not_pos hn
    simp [radialWeight,this] at h
  have hcast : (1:ℝ≥0) ≤ (RadialLine.trainingOnLine X l).card := by exact_mod_cast hc
  exact (mul_one δ).symm.trans_le (mul_le_mul_of_nonneg_left hcast (zero_le))

lemma overlap_pos_lower (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F)
    (h : 0 < PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')) :
    (δ:ℝ) ≤ PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') := by
  rw [mass_overlap x X δ F hF] at h ⊢
  have hc : 0 < (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
    by_contra hn
    have := Nat.eq_zero_of_not_pos hn
    simp [this] at h
  have hcast : (1:ℝ) ≤ (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
    exact_mod_cast hc
  exact (mul_one (δ:ℝ)).symm.trans_le (mul_le_mul_of_nonneg_left hcast δ.coe_nonneg)

variable [Finite K]

lemma one_anchor_count (F : Finset (ℙ K (Module.Dual K V))) (l : RadialLine x) :
    (Finset.univ.filter (fun H : F => l ∈ pencilLines x F H)).card ≤
      ∑ i ∈ Finset.range (finrank K V-2), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : {H : F // l ∈ pencilLines x F H} →
      {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} := fun H =>
    ⟨H.val.val, (Finset.mem_filter.mp H.property).2⟩
  have hf : Function.Injective f := by
    intro H H' he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun b : {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} => b.val) he
  have hc := Nat.card_le_card_of_injective f hf
  rw [RadialLine.card_hyperplanes l, Nat.card_eq_fintype_card] at hc
  simpa only [Fintype.card_subtype] using hc

lemma two_anchor_count (F : Finset (ℙ K (Module.Dual K V)))
    (l m : RadialLine x) (hlm : l ≠ m) :
    (Finset.univ.filter (fun H : F => l ∈ pencilLines x F H ∧ m ∈ pencilLines x F H)).card ≤
      ∑ i ∈ Finset.range (finrank K V-3), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : {H : F // l ∈ pencilLines x F H ∧ m ∈ pencilLines x F H} →
      {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep} :=
    fun H => ⟨H.val.val, (Finset.mem_filter.mp H.property.1).2,
      (Finset.mem_filter.mp H.property.2).2⟩
  have hf : Function.Injective f := by
    intro H H' he
    exact Subtype.ext (Subtype.ext (congrArg (fun b : {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep} => b.val) he))
  have hc := Nat.card_le_card_of_injective f hf
  rw [RadialLine.card_hyperplanes_pair hlm, Nat.card_eq_fintype_card] at hc
  simpa only [Fintype.card_subtype] using hc

omit [Fintype (RadialLine x)] in
lemma pencil_size (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) :
    F.card ≤ ∑ i ∈ Finset.range (finrank K V-1), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : F → {b : ℙ K (Module.Dual K V) // Incident x b} := fun H => ⟨H.val,hF H.val H.property⟩
  have hf : Function.Injective f := by
    intro H H' he
    exact Subtype.ext (congrArg (fun b : {b : ℙ K (Module.Dual K V) // Incident x b} => b.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [card_hyperplanes_through_point, Nat.card_eq_fintype_card, Fintype.card_coe] using hc

end
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma submodule_eq_ker_annihilator (b : ℙ K (Module.Dual K V)) :
    b.submodule = (LinearMap.ker b.rep).dualAnnihilator := by
  have hle : b.submodule ≤ (LinearMap.ker b.rep).dualAnnihilator := by
    rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem,Submodule.mem_dualAnnihilator]
    intro v hv
    exact hv
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.ker b.rep)
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  rw [Projectivization.finrank_submodule]
  omega

lemma kernel_injective : Function.Injective (fun b : ℙ K (Module.Dual K V) => LinearMap.ker b.rep) := by
  intro b c h
  apply Projectivization.submodule_injective
  simp only [submodule_eq_ker_annihilator,h]

variable (x : ℙ K V) [Fintype (RadialLine x)]

lemma mass_pairPoints (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') =
      (δ:ℝ)*(ActualOverlap.pairPoints x X (LinearMap.ker H.val.rep)
        (LinearMap.ker H'.val.rep)).card := by
  rw [mass_overlap x X δ F hF]
  simp only [ActualOverlap.pairPoints, NondominantOverlap.onPlane, Incident, le_inf_iff]
  rfl

lemma distinctPairs_ext {H : Type*} {p q : WeightedPrograms.DistinctPairs H}
    (h₁ : p.1=q.1) (h₂ : p.2.val=q.2.val) : p=q := by
  rcases p with ⟨p,p',hp⟩
  rcases q with ⟨q,q',hq⟩
  cases h₁
  cases h₂
  rfl

lemma pair_strength_count_le (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (a : ℝ) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a ≤ WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)).card ≤
    (WeightedOverlap.pairs x X (F.image fun b => LinearMap.ker b.rep) δ a).card := by
  let E := Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a ≤ WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)
  let G := WeightedOverlap.pairs x X (F.image fun b => LinearMap.ker b.rep) δ a
  let f (p : E) : G := ⟨(LinearMap.ker p.val.1.val.rep,LinearMap.ker p.val.2.val.val.rep),by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,p.val.1.property,rfl⟩,
      Finset.mem_image.mpr ⟨_,p.val.2.val.property,rfl⟩⟩,?_,?_⟩
    · intro h
      exact p.val.2.property (Subtype.ext (kernel_injective h).symm)
    · have hp := (Finset.mem_filter.mp p.property).2
      change a ≤ PoissonScore.mass (radialWeight x X δ)
        (pencilLines x F p.val.1 ∩ pencilLines x F p.val.2.val) at hp
      rwa [mass_pairPoints x X δ F hF] at hp⟩
  have hi : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply distinctPairs_ext
    · apply Subtype.ext
      apply kernel_injective
      exact congrArg (fun z : G => z.val.1) he
    · apply Subtype.ext
      apply kernel_injective
      exact congrArg (fun z : G => z.val.2) he
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

variable [Finite K]

theorem score_pair_count_four (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (a : ℝ) (ha : 0≤a) :
    ((Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a ≤ WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)).card:ℝ)*a^2 ≤
      (ActualOverlap.richRadials x X ⊤ ⌈a/(2*(δ:ℝ))⌉₊).card *
        ((Nat.card K:ℝ)^2+Nat.card K+1)^2*a^2 +
      2*(δ:ℝ)^2*X.card^2*((Nat.card K:ℝ)+1)^2 := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdimG (A : Submodule K V) (hA : A ∈ G) : finrank K A = 4 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A : Submodule K V) (hA : A ∈ G) : x.submodule ≤ A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  have hc : ((Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a ≤ WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)).card:ℝ) ≤
      (WeightedOverlap.pairs x X G δ a).card := by
    exact_mod_cast pair_strength_count_le x X δ F hF a
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg a)).trans
    (WeightedOverlap.pair_count_four x hdim X G hdimG hxG (by exact_mod_cast hδ) ha)

end SharpRamseyFive.ScoreGeometry

end OAI
