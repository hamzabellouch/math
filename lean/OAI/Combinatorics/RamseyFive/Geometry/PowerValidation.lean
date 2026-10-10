import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Entropy.LowMomentBudget
import OAI.Combinatorics.RamseyFive.Geometry.DyadCount
import OAI.Combinatorics.RamseyFive.Geometry.RadialAlternatives
import OAI.Combinatorics.RamseyFive.Entropy.DimensionThreePairs

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma power_tail_mul {T : Type*} [Fintype T] (f : T→ℝ) (hf : ∀z,0 ≤ f z)
    (k : ℕ) (t M : ℝ) (ht : 0 < t) (hM : (∑z,f z^k) ≤ M) :
    ((Finset.univ.filter fun z => t ≤ f z).card:ℝ)*t^k ≤ M := by
  exact (le_div_iff₀ (pow_pos ht k)).mp (power_tail_card f hf k t M ht hM)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] in
lemma validation_pairs_from_power (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (k : ℕ) (M : ℝ)
    (hM : (∑z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k) ≤ M)
    (t : ℝ) (ht : 0 < t) :
    ((Finset.univ.filter fun z : {z : F×F // z.1 ≠ z.2} => t ≤
      mass (radialWeight x X δ) (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card:ℝ)*t^k ≤ M := by
  let f : {z : F×F // z.1 ≠ z.2}→DistinctPairs F := fun z => ⟨z.val.1,⟨z.val.2,z.property.symm⟩⟩
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    exact congrArg (fun z : DistinctPairs F => (z.1,z.2.val)) he
  have hc : (Finset.univ.filter fun z : {z : F×F // z.1 ≠ z.2} => t ≤
      mass (radialWeight x X δ) (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card ≤
      (Finset.univ.filter fun z : DistinctPairs F => t ≤
      strength (pencilLines x F) (radialWeight x X δ) z).card := by
    apply Finset.card_le_card_of_injOn f
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩
    · exact hf.injOn
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (pow_nonneg ht.le _)).trans
    (power_tail_mul _ (strength_nonneg _ _) k t M ht hM)

end

section

open Filter ParameterHierarchy
open scoped Topology

theorem eventually_dyad_power_payment {η : ℝ} (hη : 0 < η) (hη' : η < 1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D R χ : ℝ) (m : ℕ),Range η σ D R →
      χ ≤ P η σ D R/200 → (m:ℝ) ≤ Real.exp (3*σ) →
      2^200*((Nat.clog 2 m:ℝ)+1)*Real.exp (2*χ) ≤ Real.exp (P η σ D R/50) := by
  have he := eventually_power_absorption hη hη' (8*2^200) 1 (1/100)
    (by positivity) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),he] with σ hσ he
  intro D R χ m hr hχ hm
  have hh : (8*2^200:ℝ)*σ ≤ Real.exp (P η σ D R/100) := by
    simpa only [Real.rpow_one,one_mul,one_div,div_eq_mul_inv,mul_comm (100⁻¹:ℝ)] using he D R hr
  calc
    _ ≤ ((8*2^200:ℝ)*σ)*Real.exp (2*χ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      nlinarith only [dyad_count_le hσ hm]
    _ ≤ Real.exp (P η σ D R/100)*Real.exp (P η σ D R/100) :=
      mul_le_mul hh (Real.exp_le_exp.mpr (by linarith only [hχ])) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add];congr 1;ring

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pair_three_half_normalized (hdim : finrank K V = 4)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (n a χ : ℝ) (hn : 0<n) (ha : 0<a) (ha2 : a ≤ 2)
    (hχ : (4*2^200:ℝ) ≤ Real.exp χ)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ (a/2) Lines Q ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(a/2)^100)) :
    ((Finset.univ.filter (fun p : DistinctPairs F => a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^3/n)^2*Real.exp (2*χ) := by
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hq2 : ((Nat.card K:ℝ)+1)^2 ≤ 4*(Nat.card K:ℝ)^2 := by nlinarith
  have hc : ((Finset.univ.filter (fun p : DistinctPairs F => a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ) ≤
      ((Finset.univ.filter (fun p : DistinctPairs F => a/2 ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith only [ha,(Finset.mem_filter.mp hp).2]⟩
  have hh := hc.trans (score_pairs_three_off_radial x hdim S O δ hδ F hF (a/2) _ Lines hLines Q hx hgood)
  have hp : a^100 ≤ (2:ℝ)^100 := pow_le_pow_left₀ ha.le ha2 _
  calc
    _  ≤  ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(a/2)^100)*((Nat.card K:ℝ)+1)^2*a^200 :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _  ≤  ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(a/2)^100)*(4*(Nat.card K:ℝ)^2)*a^200 := by gcongr
    _ = ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*(4*2^100*a^100) := by field_simp
    _  ≤  ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*(4*2^100*2^100) := by gcongr
    _ = ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*(4*2^200) := by ring
    _  ≤  ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*Real.exp χ := by gcongr
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring

theorem score_pair_three_moment (hdim : finrank K V=4)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (n χ : ℝ) (hn : 0<n) (hχ : (4*2^200:ℝ) ≤ Real.exp χ)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hm : ∀H:F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
    (hgood : x∉radialExceptions S O δ Lines Q (Nat.card K) n χ)
    (R : ℕ) (hR : 200 ≤ R) :
    (∑z : DistinctPairs F,strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) z^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^3/n)^2*Real.exp (2*χ)) := by
  apply score_higher_power x _ δ hδ F hF _ (by positivity) 200 R (by norm_num) hR hm
  intro i hi
  exact score_pair_three_half_normalized x hdim S O δ hδ F hF n _ χ hn (by positivity)
    (Finset.mem_filter.mp hi).2 hχ Lines hLines Q hx
    (off_radialExceptions S O δ Lines Q (Nat.card K) n χ x hgood i hi)

theorem score_degree_three_normalized (hdim : finrank K V=4)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) (H : F)
    (n a χ : ℝ) (hn : 0<n) (ha : 0<a) (ha2 : a ≤ 2)
    (hm : mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hcap : n ≤ 10*(Nat.card K:ℝ)^2) (hχ : (40*2^199:ℝ) ≤ Real.exp (2*χ)) :
    ((Finset.univ.filter fun H':F => H≠H' ∧ a ≤ mass
      (radialWeight x X δ) (pencilLines x F H∩pencilLines x F H')).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^3/n)*Real.exp (2*χ) := by
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hq0 : (0:ℝ)<Nat.card K := by linarith only [hq]
  have hh := score_degree_three x hdim X δ hδ F hF H a ha.le
  have hp : a^199 ≤ (2:ℝ)^199 := pow_le_pow_left₀ ha.le ha2 _
  have hnq : (Nat.card K:ℝ) ≤ 10*((Nat.card K:ℝ)^3/n) := by
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hn).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hcap hq0.le]
  calc
    _ = (((Finset.univ.filter fun H':F => H≠H' ∧ a ≤ mass
      (radialWeight x X δ) (pencilLines x F H∩pencilLines x F H')).card:ℝ)*a)*a^199 := by ring
    _  ≤  (mass (radialWeight x X δ) (pencilLines x F H)*((Nat.card K:ℝ)+1))*a^199 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (by positivity)
    _  ≤  (2*(2*(Nat.card K:ℝ)))*2^199 := by gcongr; linarith only [hq]
    _  ≤  (4*(10*((Nat.card K:ℝ)^3/n)))*2^199 := by
      calc
        (2*(2*(Nat.card K:ℝ)))*2^199 = (4*(Nat.card K:ℝ))*2^199 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnq (by norm_num)) (by positivity)
    _ = ((Nat.card K:ℝ)^3/n)*(40*2^199) := by ring
    _  ≤  _ := mul_le_mul_of_nonneg_left hχ (by positivity)

end SharpRamseyFive.ScoreGeometry

end OAI
