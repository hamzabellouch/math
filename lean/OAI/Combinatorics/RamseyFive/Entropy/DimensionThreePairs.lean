import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.DegreeStrengthCount
import OAI.Combinatorics.RamseyFive.Geometry.LocalLines

namespace OAI

namespace SharpRamseyFive.WeightedOverlap
open Module ProjectiveIncidence RichPlaneGeometry HyperplaneOverlap NondominantOverlap ActualOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem pair_count_three (hdim : finrank K V = 4)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (hxF : ∀ A ∈ F, x.submodule ≤ A) {δ a : ℝ} (hδ : 0<δ) :
    (pairs x X F δ a).card ≤
      (richRadials x X ⊤ ⌈a/δ⌉₊).card*(Nat.card K+1)^2 := by
  have hh := dominant_pair_count x (d := 3) hdim X F hF
    (pairs x X F δ a) (Finset.filter_subset _ _) ⌈a/δ⌉₊ (by
      intro p hp
      obtain ⟨hp,hne,hs⟩ := Finset.mem_filter.mp hp
      obtain ⟨hA,hB⟩ := Finset.mem_product.mp hp
      obtain ⟨l,hl,hX⟩ := intersection_radial_three x hdim p.1 p.2 (hF _ hA) (hF _ hB)
        (hxF _ hA) (hxF _ hB) hne X
      refine ⟨l,hl.le,?_⟩
      rw [hX]
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hδ).mpr
      simpa only [mul_comm] using hs)
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,zero_add,add_comm] using hh

theorem degree_count_three (hdim : finrank K V = 4)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H=3) (hxH : x.submodule≤H)
    {δ a : ℝ} (hδ : 0<δ) :
    ((neighbors x X F H δ a).card:ℝ)*a ≤
      δ*(onPlane x X H).card*(Nat.card K+1) := by
  have hh := dominant_degree_count x (d := 3) hdim X F hF H hxH
    (neighbors x X F H δ a) (Finset.filter_subset _ _) ⌈a/δ⌉₊ (by
      intro A hA
      obtain ⟨hA,hne,hs⟩ := Finset.mem_filter.mp hA
      obtain ⟨l,hl,hX⟩ := intersection_radial_three x hdim H A hH (hF _ hA)
        hxH (hxF _ hA) hne X
      refine ⟨l,hl.le,?_⟩
      rw [hX]
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hδ).mpr
      simpa only [mul_comm] using hs)
  have hc : ((neighbors x X F H δ a).card:ℝ)*⌈a/δ⌉₊ ≤
      (onPlane x X H).card*((Nat.card K:ℝ)+1) := by
    have he : (∑i∈Finset.range (3-1),Nat.card K^i)=Nat.card K+1 := by
      norm_num [Finset.sum_range_succ,Nat.add_comm]
    rw [he] at hh
    exact_mod_cast hh
  have hceil : a≤δ*(⌈a/δ⌉₊:ℝ) :=
    ((div_le_iff₀ hδ).mp (Nat.le_ceil (a/δ))).trans_eq (mul_comm _ _)
  calc
    _ ≤ (neighbors x X F H δ a).card*(δ*(⌈a/δ⌉₊:ℝ)) := mul_le_mul_of_nonneg_left hceil (by positivity)
    _ = δ*((neighbors x X F H δ a).card*(⌈a/δ⌉₊:ℝ)) := by ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc hδ.le

omit [Finite K] [Fintype (RadialLine x)] in

theorem no_neighbors_three (hdim : finrank K V = 4)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H=3) (hxH : x.submodule≤H)
    (δ a : ℝ) (hline : ∀ l : RadialLine x, δ*(RadialLine.trainingOnLine X l).card<a) :
    neighbors x X F H δ a=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A hA
  obtain ⟨hA,hne,hs⟩ := Finset.mem_filter.mp hA
  obtain ⟨l,_,hX⟩ := intersection_radial_three x hdim H A hH (hF _ hA)
    hxH (hxF _ hA) hne X
  have hl := hline l
  rw [hX] at hl
  exact (not_le_of_gt hl) hs

end SharpRamseyFive.WeightedOverlap
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pair_count_three (hdim : finrank K V=4)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H∈F,Incident x H) (a : ℝ) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a≤WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)).card ≤
      (ActualOverlap.richRadials x X ⊤ ⌈a/(δ:ℝ)⌉₊).card*(Nat.card K+1)^2 := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdimG (A : Submodule K V) (hA : A∈G) : finrank K A=3 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A : Submodule K V) (hA : A∈G) : x.submodule≤A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  exact (pair_strength_count_le x X δ F hF a).trans
    (WeightedOverlap.pair_count_three x hdim X G hdimG hxG (by exact_mod_cast hδ))

theorem score_degree_three (hdim : finrank K V=4)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H∈F,Incident x H)
    (H : F) (a : ℝ) (ha : 0≤a) :
    ((Finset.univ.filter (fun H' : F => H≠H' ∧ a≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ)*a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H)*(Nat.card K+1) := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdG (A) (hA : A∈G) : finrank K A=3 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A) (hA : A∈G) : x.submodule≤A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  have hdH : finrank K (LinearMap.ker H.val.rep)=3 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero H.val.rep_nonzero
    omega
  have hc : ((Finset.univ.filter (fun H' : F => H≠H' ∧ a≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ) ≤
      (WeightedOverlap.neighbors x X G (LinearMap.ker H.val.rep) δ a).card := by
    exact_mod_cast degree_strength_count_le x X δ F hF H a
  have hh := (mul_le_mul_of_nonneg_right hc ha).trans
    (WeightedOverlap.degree_count_three x hdim X G hdG hxG _ hdH
      (hF H.val H.property) (by exact_mod_cast hδ))
  have hm : PoissonScore.mass (radialWeight x X δ) (pencilLines x F H)=
      (δ:ℝ)*(NondominantOverlap.onPlane x X (LinearMap.ker H.val.rep)).card := by
    rw [mass_pencil x X δ F hF]
    rfl
  rwa [hm]

omit [Finite K] in

theorem score_no_neighbors_three (hdim : finrank K V=4)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H∈F,Incident x H)
    (H : F) (a : ℝ) (hline : ∀ l : RadialLine x,(radialWeight x X δ l:ℝ)<a) :
    (Finset.univ.filter (fun H' : F => H≠H' ∧ a≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')))=∅ := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdG (A) (hA : A∈G) : finrank K A=3 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A) (hA : A∈G) : x.submodule≤A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  have hdH : finrank K (LinearMap.ker H.val.rep)=3 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero H.val.rep_nonzero
    omega
  have he := WeightedOverlap.no_neighbors_three x hdim X G hdG hxG (LinearMap.ker H.val.rep)
    hdH (hF H.val H.property) δ a (by
      intro l
      simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast] using hline l)
  apply Finset.card_eq_zero.mp
  have hc := degree_strength_count_le x X δ F hF H a
  rw [he,Finset.card_empty] at hc
  omega

end
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pairs_three_off_radial (hdim : finrank K V = 4)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (a D : ℝ) (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ a Lines Q D) :
    ((Finset.univ.filter (fun p : DistinctPairs F  =>  a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ) ≤
      D*((Nat.card K:ℝ)+1)^2 := by
  have hlocal : ((localLines S O δ a Lines x).card:ℝ) < D := by
    by_contra hn
    exact hgood (Finset.mem_filter.mpr ⟨hx,le_of_not_gt hn⟩)
  have hh := score_pair_count_three x hdim (outsideAt x S (O x)) δ hδ F hF a
  have hr := richRadials_le_localLines x S O δ a (by exact_mod_cast hδ) Lines hLines
  have hc : ((Finset.univ.filter (fun p : DistinctPairs F  =>  a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ) ≤
      (localLines S O δ a Lines x).card*((Nat.card K:ℝ)+1)^2 := by
    exact_mod_cast hh.trans (Nat.mul_le_mul_right _ hr)
  exact hc.trans (mul_le_mul_of_nonneg_right hlocal.le (sq_nonneg _))

theorem score_pair_three_normalized (hdim : finrank K V = 4)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (n a χ : ℝ) (hn : 0 < n) (ha : 0 < a) (ha2 : a ≤ 2)
    (hχ : (4*2^100:ℝ) ≤ Real.exp χ)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ a Lines Q ((Nat.card K:ℝ)^4/n^2*Real.exp χ/a^100)) :
    ((Finset.univ.filter (fun p : DistinctPairs F  =>  a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^3/n)^2*Real.exp (2*χ) := by
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hq2 : ((Nat.card K:ℝ)+1)^2 ≤ 4*(Nat.card K:ℝ)^2 := by nlinarith
  have hh := score_pairs_three_off_radial x hdim S O δ hδ F hF a _ Lines hLines Q hx hgood
  have hp : a^100 ≤ (2:ℝ)^100 := pow_le_pow_left₀ ha.le ha2 _
  calc
    _  ≤  ((Nat.card K:ℝ)^4/n^2*Real.exp χ/a^100)*((Nat.card K:ℝ)+1)^2*a^200 :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _  ≤  ((Nat.card K:ℝ)^4/n^2*Real.exp χ/a^100)*(4*(Nat.card K:ℝ)^2)*a^200 := by gcongr
    _  =  ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*(4*a^100) := by field_simp
    _  ≤  ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*(4*2^100) := by gcongr
    _  ≤  ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*Real.exp χ := by gcongr
    _  =  _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring

end SharpRamseyFive.ScoreGeometry

end OAI
