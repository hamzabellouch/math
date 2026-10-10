import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Entropy.DegreeCountFour
import OAI.Combinatorics.RamseyFive.Geometry.Outside

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (x : ℙ K V) [Fintype (RadialLine x)]

lemma degree_strength_count_le (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (H : F) (a : ℝ) :
    (Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card ≤
    (WeightedOverlap.neighbors x X (F.image fun b => LinearMap.ker b.rep)
      (LinearMap.ker H.val.rep) δ a).card := by
  let E := Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))
  let G := WeightedOverlap.neighbors x X (F.image fun b => LinearMap.ker b.rep)
      (LinearMap.ker H.val.rep) δ a
  let f (p : E) : G := ⟨LinearMap.ker p.val.val.rep,by
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_,p.val.property,rfl⟩,?_,?_⟩
    · intro h
      exact (Finset.mem_filter.mp p.property).2.1 (Subtype.ext (kernel_injective h))
    · have hp := (Finset.mem_filter.mp p.property).2.2
      rwa [mass_pairPoints x X δ F hF] at hp⟩
  have hi : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply Subtype.ext
    exact kernel_injective (congrArg (fun z : G => z.val) he)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

variable [Finite K]

theorem score_degree_four (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (H : F) (a : ℝ) (ha : 0≤a) :
    ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ)*a^2 ≤
      2*PoissonScore.mass (radialWeight x X δ) (pencilLines x F H)*
        ((Nat.card K:ℝ)^2+Nat.card K+1)*a +
      2*(PoissonScore.mass (radialWeight x X δ) (pencilLines x F H))^2*((Nat.card K:ℝ)+1) := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdG (A) (hA : A ∈ G) : finrank K A = 4 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A) (hA : A ∈ G) : x.submodule ≤ A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  have hdH : finrank K (LinearMap.ker H.val.rep) = 4 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero H.val.rep_nonzero
    omega
  have hc : ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ) ≤
      (WeightedOverlap.neighbors x X G (LinearMap.ker H.val.rep) δ a).card := by
    exact_mod_cast degree_strength_count_le x X δ F hF H a
  have hh := (mul_le_mul_of_nonneg_right hc (sq_nonneg a)).trans
    (WeightedOverlap.degree_count_four x hdim X G hdG hxG _ hdH
      (hF H.val H.property) (by exact_mod_cast hδ) ha)
  have hm : PoissonScore.mass (radialWeight x X δ) (pencilLines x F H) =
      (δ:ℝ)*(NondominantOverlap.onPlane x X (LinearMap.ker H.val.rep)).card := by
    rw [mass_pencil x X δ F hF]
    rfl
  rw [hm]
  nlinarith [hh]

theorem score_degree_truncated (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (H : F) (a : ℝ) (ha : 0≤a)
    (hline : ∀ l : RadialLine x, (radialWeight x X δ l:ℝ) < a/2) :
    ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ)*a^2 ≤
      2*(PoissonScore.mass (radialWeight x X δ) (pencilLines x F H))^2*((Nat.card K:ℝ)+1) := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdG (A) (hA : A ∈ G) : finrank K A = 4 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A) (hA : A ∈ G) : x.submodule ≤ A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  have hdH : finrank K (LinearMap.ker H.val.rep) = 4 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero H.val.rep_nonzero
    omega
  have hc : ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ) ≤
      (WeightedOverlap.neighbors x X G (LinearMap.ker H.val.rep) δ a).card := by
    exact_mod_cast degree_strength_count_le x X δ F hF H a
  have hh := (mul_le_mul_of_nonneg_right hc (sq_nonneg a)).trans
    (WeightedOverlap.nondominant_weighted_degree x hdim X G hdG hxG _ hdH
      (hF H.val H.property) (by exact_mod_cast hδ) ha (by
        intro l
        simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast] using hline l))
  have hm : PoissonScore.mass (radialWeight x X δ) (pencilLines x F H) =
      (δ:ℝ)*(NondominantOverlap.onPlane x X (LinearMap.ker H.val.rep)).card := by
    rw [mass_pencil x X δ F hF]
    rfl
  rw [hm]
  nlinarith [hh]

end SharpRamseyFive.ScoreGeometry

end OAI
