import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.MomentPolynomialTail
import OAI.Combinatorics.RamseyFive.Probability.PencilFactor
import OAI.Combinatorics.RamseyFive.Probability.QB

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_degree_low_normalized (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F)
    (n a χ : ℝ) (hn : 0<n) (ha : 0≤a) (ha2 : a≤2)
    (hm : mass (radialWeight x X δ) (pencilLines x F H)≤2)
    (hcap : n≤(Nat.card K:ℝ)^3) (hlow : n≤(Nat.card K:ℝ)^2*Real.exp χ)
    (hchi : (10*2^200:ℝ)≤Real.exp χ) :
    ((Finset.univ.filter fun H' : F => H≠H' ∧ a≤
      mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/n)*Real.exp (2*χ) := by
  have hq : (1:ℝ)≤Nat.card K := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.card_pos : 0<Nat.card K)
  apply ScoreScalars.normalized_degree_low hq hn ha ha2 hcap hlow hchi
  exact ScoreScalars.degree_power_two_hundred hq (mass_nonneg _ _) hm ha
    (score_degree_four x hdim X δ hδ F hF H a ha)

omit [Finite K] in
lemma offRow_bounded_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H)≤ m) (H H' : F)
    (hp : 0<offRow x X δ F H H') :
    ∃ i∈boundedOverlapDyads x X δ m,(δ:ℝ)*2^i≤offRow x X δ F H H' ∧
      offRow x X δ F H H'≤2*((δ:ℝ)*2^i) := by
  have hn : H≠H' := by intro he; simp only [offRow,ite_eq_left he] at hp; linarith
  have hp' : 0<strength (pencilLines x F) (radialWeight x X δ) ⟨H,⟨H',Ne.symm hn⟩⟩ := by
    simpa only [offRow,ite_eq_right hn,strength,mass] using hp
  simpa only [offRow,ite_eq_right hn,strength,mass] using
    bounded_overlap_cover x X δ hδ F hF m hm ⟨H,⟨H',Ne.symm hn⟩⟩ hp'

theorem score_row_low_moment (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F)
    (n χ : ℝ) (hn : 0<n) (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H)≤2)
    (hcap : n≤(Nat.card K:ℝ)^3) (hlow : n≤(Nat.card K:ℝ)^2*Real.exp χ)
    (hchi : (10*2^200:ℝ)≤Real.exp χ) :
    (∑ H',offRow x X δ F H H'^200) ≤
      2^200*(Nat.clog 2 X.card+1)*(((Nat.card K:ℝ)^4/n)*Real.exp (2*χ)) := by
  apply (moment_polynomial_tail _ (fun i : ℕ => (δ:ℝ)*2^i)
    (boundedOverlapDyads x X δ 2) 200 (by norm_num)
    (((Nat.card K:ℝ)^4/n)*Real.exp (2*χ)) (offRow_nonneg x X δ F H)
    (by intro i _; positivity) (offRow_bounded_cover x X δ hδ F hF 2 hm H) ?_).trans
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast boundedOverlapDyads_card x X δ 2) (by positivity)) (by positivity)
  intro i hi
  have ha : 0<(δ:ℝ)*2^i := by positivity
  have he : (Finset.univ.filter (fun H' : F => (δ:ℝ)*2^i ≤ offRow x X δ F H H'))=
      Finset.univ.filter (fun H' : F => H≠H' ∧ (δ:ℝ)*2^i ≤
        mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')) := by
    apply Finset.filter_congr
    intro H' _
    by_cases h : H=H'
    · simp [offRow,h,not_le.mpr ha]
    · simp [offRow,h]
  rw [he]
  exact score_degree_low_normalized x hdim X δ hδ F hF H n _ χ hn ha.le
    (Finset.mem_filter.mp hi).2 (hm H) hcap hlow hchi

omit [FiniteDimensional K V] [Finite K] in

theorem shift_row_from_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H : F) (p k : ℕ) (hk : k≠0)
    (A : ℝ) (hA : (∑ H',offRow x X δ F H H'^k)≤A) :
    (∑ H',SingletonEnumeration.shiftKernel (radialWeight x X δ) (pencilLines x F) p k H' H)≤
      1+(p:ℝ)^k*A := by
  have hs : (∑ H' : F,if H=H' then (1:ℝ) else 0)=1 := by simp
  calc
    _ ≤ ∑ H' : F,((if H=H' then (1:ℝ) else 0)+((p:ℝ)*offRow x X δ F H H')^k) := by
      apply Finset.sum_le_sum
      intro H' _
      by_cases he : H=H'
      · simp only [ite_eq_left he,offRow,mul_zero,zero_pow hk,add_zero]
        exact (SingletonEnumeration.shiftKernel_range _ _ p k H' H).2
      · simp only [ite_eq_right he,offRow,zero_add]
        unfold SingletonEnumeration.shiftKernel
        rw [Finset.inter_comm]
        exact min_le_right _ _
    _ = 1+(p:ℝ)^k*(∑ H',offRow x X δ F H H'^k) := by
      rw [Finset.sum_add_distrib,hs]
      simp only [mul_pow,Finset.mul_sum]
    _ ≤ 1+(p:ℝ)^k*A := add_le_add_right
      (mul_le_mul_of_nonneg_left hA (pow_nonneg (Nat.cast_nonneg p) k)) 1

omit [FiniteDimensional K V] [Finite K] in

theorem shift_pair_from_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (p k : ℕ) (A : ℝ)
    (hA : (∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k)≤A) :
    (∑ H : F,∑ H' : F,SingletonEnumeration.shiftKernel (radialWeight x X δ)
      (pencilLines x F) p k H H') ≤ F.card+(p:ℝ)^k*A := by
  rw [SingletonEnumeration.sum_pairs_split_diagonal]
  apply add_le_add
  · have hh:=Finset.sum_le_sum (fun H (_ : H∈(Finset.univ : Finset F)) =>
      (SingletonEnumeration.shiftKernel_range (radialWeight x X δ) (pencilLines x F) p k H H).2)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_coe] using hh
  · calc
      _ ≤ ∑ z : DistinctPairs F,((p:ℝ)*strength (pencilLines x F) (radialWeight x X δ) z)^k :=
        Finset.sum_le_sum (fun z _ => min_le_right _ _)
      _ = (p:ℝ)^k*∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k := by
        simp only [mul_pow,Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)

omit [FiniteDimensional K V] [Finite K] in

theorem certificate_pair_eq_power (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (R k : ℕ) :
    WeightedPrograms.pairMoment (B := Fin R) (pencilLines x F)
      (fun l => L*radialWeight x X δ l) k=
      ((R:ℝ)*(L:ℝ))^k*∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k := by
  unfold WeightedPrograms.pairMoment
  change _ = _ * ∑ z : (Σ h : F, {h' : F // h' ≠ h}), _
  rw [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H' _
  simp only [Fintype.card_fin,NNReal.coe_mul,←Finset.mul_sum,WeightedPrograms.strength]
  rw [←mul_assoc,mul_pow]

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def certificateMajorant (Q M B b L : ℝ) (p R k N₁ N₂ : ℕ) : ℝ :=
  B*(1+(((p:ℝ)*(Q*p)/B)/b^8+
    (p:ℝ)^2*(N₁*p)*((k:ℝ)*p+R*(2*L))/B+
    ((p:ℝ)^3*(N₂*p)*((k:ℝ)*p+R*(2*L))^2/B)*b+
    (p:ℝ)^2*((p:ℝ)^2*((R*L)^k*M+Q*(R*(2*L))^k))/B^2))

lemma certificateMajorant_nonneg (Q M B b L : ℝ) (p R k N₁ N₂ : ℕ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hB : 0 ≤ B) (hb : 0 ≤ b) (hL : 0 ≤ L) :
    0 ≤ certificateMajorant Q M B b L p R k N₁ N₂ := by
  unfold certificateMajorant
  positivity

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] in

theorem score_certificate_majorant (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (p R k N₁ N₂ : ℕ) (Q M B b : ℝ)
    (hB : 0 < B) (_hb : 0 ≤ b) (hQ : (F.card:ℝ) ≤ Q) (_hM : 0 ≤ M)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hPow : (∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k) ≤ M) :
    B*(1+branchingBound (V := Fin p) (B := Fin R)
      (fun z : F × Fin p => pencilLines x F z.1) (fun l => L*radialWeight x X δ l)
      B b (2*(L:ℝ)) k (N₁*p) (N₂*p) true) ≤
      certificateMajorant Q M B b L p R k N₁ N₂ := by
  have hmass (H : F) : (∑ l∈pencilLines x F H,((L*radialWeight x X δ l:ℝ≥0):ℝ)) ≤ 2*(L:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hm H) L.coe_nonneg
    simpa only [mass,NNReal.coe_mul,Finset.mul_sum,mul_comm (L:ℝ) 2] using hh
  have hQ0 : 0 ≤ Q := (Nat.cast_nonneg F.card).trans hQ
  have hpair := SingletonEnumeration.pairMoment_labelled_le (V := Fin p) (B := Fin R)
    (pencilLines x F) (fun l => L*radialWeight x X δ l) k (2*(L:ℝ)) (by positivity) hmass
  simp only [Fintype.card_fin,Fintype.card_coe] at hpair
  rw [certificate_pair_eq_power] at hpair
  have hpair' : pairMoment (B := Fin R) (fun z : F × Fin p => pencilLines x F z.1)
      (fun l => L*radialWeight x X δ l) k ≤
      (p:ℝ)^2*(((R:ℝ)*(L:ℝ))^k*M+Q*((R:ℝ)*(2*(L:ℝ)))^k) := by
    apply hpair.trans
    gcongr
  unfold certificateMajorant
  apply mul_le_mul_of_nonneg_left _ hB.le
  apply add_le_add_right
  unfold branchingBound uniformAnchorBudget
  simp only [reduceIte,Fintype.card_fin,Fintype.card_prod,Fintype.card_coe,
    Nat.cast_mul]
  gcongr

end SharpRamseyFive.ScoreGeometry

end OAI
