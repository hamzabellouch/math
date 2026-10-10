import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.RadialOffException
import OAI.Combinatorics.RamseyFive.Geometry.TrainingLineCard

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def highMomentBudget (Q M A B b L : ℝ) (p R N₂ : ℕ) : ℝ :=
  highCertificateMajorant Q M B b L p R 200 N₂ +
    (1+(p:ℝ)^200*A)+B+(Q/B+(p:ℝ)^200*(M/B))

lemma highMomentBudget_bounds (Q M A B b L : ℝ) (p R N₂ : ℕ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 < B)
    (hb : 0 ≤ b) (hL : 0 ≤ L) :
    0 ≤ highMomentBudget Q M A B b L p R N₂ ∧
    highCertificateMajorant Q M B b L p R 200 N₂ ≤ highMomentBudget Q M A B b L p R N₂ ∧
    1+(p:ℝ)^200*A ≤ highMomentBudget Q M A B b L p R N₂ ∧
    Q+(p:ℝ)^200*M ≤ (highMomentBudget Q M A B b L p R N₂)^2 := by
  have hc := highCertificateMajorant_nonneg Q M B b L p R 200 N₂ hQ hM hB.le hb hL
  have hrow : 0 ≤ 1+(p:ℝ)^200*A := by positivity
  have hx : 0 ≤ Q/B+(p:ℝ)^200*(M/B) := by positivity
  have hCB : B ≤ highMomentBudget Q M A B b L p R N₂ := by
    unfold highMomentBudget; linarith
  have hCx : Q/B+(p:ℝ)^200*(M/B) ≤ highMomentBudget Q M A B b L p R N₂ := by
    unfold highMomentBudget; linarith
  have hC := hB.le.trans hCB
  refine ⟨hC,?_,?_,?_⟩
  · unfold highMomentBudget; linarith
  · unfold highMomentBudget; linarith
  · calc
      _ = B*(Q/B+(p:ℝ)^200*(M/B)) := by field_simp
      _ ≤ highMomentBudget Q M A B b L p R N₂ *
          highMomentBudget Q M A B b L p R N₂ := mul_le_mul hCB hCx hx hC
      _ = _ := (sq _).symm

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def pencilHighBudget (q m : ℕ) (n χ b L : ℝ) (p R : ℕ) : ℝ :=
  highMomentBudget (pencilAlphabet q 4) (dyadFactor m χ*(geometryScale q n)^2)
    (dyadFactor m χ*geometryScale q n) (geometryScale q n) b L p R
      (pencilAlphabet q 2)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem projective_high_moment_from_pairs (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ L : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (n χ b base D₀ : ℝ) (hn : 0 < n) (hb : 1 ≤ b) (hD : 0 ≤ D₀)
    (hL : 10000 ≤ (L:ℝ)) (hbase : (23/25:ℝ) ≤ base)
    (hcap : n ≤ (Nat.card K:ℝ)^3)
    (hscaleDensity : n*(δ:ℝ) ≤ 4*Nat.card K)
    (hchi : (208*2^198:ℝ) ≤ Real.exp (2*χ))
    (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
    (hlower : ∀ H : F,(3/4:ℝ) ≤ mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))
    (hdelta : ∀ H : F,|mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H)-base| ≤ 17/100)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hPow : (∑ z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) δ) z^200) ≤
      dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) n)^2)
    {p : ℕ} (hp : 0 < p) (R h : ℕ) (hKR : 200 ≤ R/2) (hh : 0 < h)
    (hsize : h ≤ (R/2-5000)/(2*200)) (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1) < 1/2)
    (own : F→Fin R→Bool)
    (hDsum : (∑ H : F,SingletonEnumeration.independentWeight
      (radialWeight x (outsideAt x S (O x)) δ) (fun d => L*radialWeight x (outsideAt x S (O x)) δ d)
      (pencilLines x F) R 5000 base H) ≤ D₀)
    (hcost : D₀+2*((p+1:ℝ)*pencilHighBudget (Nat.card K) (outsideAt x S (O x)).card n χ b L p R) ≤
      geometryScale (Nat.card K) n*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2 ≤ Real.exp (((L:ℝ)*R)/10))
    (hA : 2 ≤ geometryScale (Nat.card K) n*Real.exp (-((L:ℝ)*R)))
    (hscale : 16*((Nat.card K:ℝ)+1) ≤
      (geometryScale (Nat.card K) n*Real.exp (-((L:ℝ)*R)))*(1/(100*(p:ℝ)))^2)
    (hstrong : x∉badCenters S O δ ((1/(100*(p:ℝ)))/2) Lines Q 1)
    (hpairScalar : (pencilAlphabet (Nat.card K) 4:ℝ)+
      (dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) n)^2)/(1/(100*(p:ℝ)))^200 ≤
      (geometryScale (Nat.card K) n)^2*Real.exp (((L:ℝ)*R)/10)) :
    (∫ ω, HighMoment.allTrunc R 5000 ω*(∑ H : F,scoreTerm (pencilLines x F H) (Real.exp (-(L:ℝ)*base)) (own H)
      (fun r d => ω (r,d)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S (O x)) δ i.2)) ≤
      (geometryScale (Nat.card K) n)^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  let X := outsideAt x S (O x)
  let q := Nat.card K
  let B := geometryScale q n
  let M := dyadFactor X.card χ*B^2
  let A := dyadFactor X.card χ*B
  let C := pencilHighBudget q X.card n χ b L p R
  have hq : 0 < q := Nat.card_pos
  have hB : 0 < B := by dsimp [B,geometryScale]; positivity
  have hM : 0 ≤ M := by dsimp [M,dyadFactor]; positivity
  have hRow : 0 ≤ A := by dsimp [A,dyadFactor]; positivity
  have hQ : 0 ≤ (pencilAlphabet q 4:ℝ) := Nat.cast_nonneg _
  have hC := highMomentBudget_bounds (pencilAlphabet q 4) M A B b L p R
    (pencilAlphabet q 2) hQ hM hRow hB (zero_le_one.trans hb) L.coe_nonneg
  have hrows (H : F) : (∑ H',offRow x X δ F H H'^200) ≤ A := by
    simpa only [A,B,dyadFactor,geometryScale,mul_assoc,mul_left_comm,mul_comm] using
      score_row_uniform_moment x hdim X δ hδ F hF H n χ hn hm hcap hscaleDensity hchi
  have hQsize : (F.card:ℝ) ≤ (pencilAlphabet q 4:ℝ) := by
    exact_mod_cast (by simpa only [hdim,Nat.reduceSub,pencilAlphabet] using pencil_size x F hF)
  have hN₁ (d : RadialLine x) : (Finset.univ.filter fun H : F => d∈pencilLines x F H).card ≤ pencilAlphabet q 3 := by
    simpa only [hdim,Nat.reduceSub,pencilAlphabet] using one_anchor_count x F d
  have hN₂ (d e : RadialLine x) (hde : d≠e) :
      (Finset.univ.filter fun H : F => d∈pencilLines x F H ∧ e∈pencilLines x F H).card ≤ pencilAlphabet q 2 := by
    simpa only [hdim,Nat.reduceSub,pencilAlphabet] using two_anchor_count x F d e hde
  have hmassL (H : F) : (∑ d∈pencilLines x F H,((L*radialWeight x X δ d:ℝ≥0):ℝ)) ≤ 2*(L:ℝ) := by
    simpa only [mass,NNReal.coe_mul,Finset.mul_sum,mul_comm (L:ℝ) 2] using
      mul_le_mul_of_nonneg_left (hm H) L.coe_nonneg
  have ht : 0 < 1/(100*(p:ℝ)) := by positivity
  let Δ := ⌊B*Real.exp (-((L:ℝ)*R))⌋₊
  have hΔ (H : F) : Fintype.card {H' : F // AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))) H H'} ≤ Δ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    exact ambient_degree_off_exception x hdim S O δ hδ F hF hm _ _ ht hA hscale Lines hLines Q hx hstrong H
  have hdeg : (Δ:ℝ) ≤ B*Real.exp (-((L:ℝ)*R)) := Nat.floor_le (by positivity)
  have hRelPairs : (Fintype.card (ComponentEnumeration.RelatedPair (AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))))):ℝ) ≤ B^2*Real.exp (((L:ℝ)*R)/10) := by
    apply (strong_pairs_le x X δ F _).trans
    apply le_trans (add_le_add hQsize (power_tail_card _ (fun z => by unfold strength; positivity) 200 _ M ht hPow))
    exact hpairScalar
  apply AmbientEnumeration.ambient_refined_truncated_moment (radialWeight x X δ) (pencilLines x F)
    hp R own L B b (2*(L:ℝ)) C D₀ base B hL hbase hlower hdelta hB hb (by positivity)
    hC.1 hD hB.le hmassL 200 5000 h (pencilAlphabet q 3) (pencilAlphabet q 2) (by norm_num)
    hKR hh false hsize herr hN₁ hN₂ ?_ ?_ ?_ hDsum hcost hp2 Δ hΔ hdeg hRelPairs
  · exact (score_high_certificate_majorant x X δ L F p R 200 _ _ M B b hB (zero_le_one.trans hb) hQsize hM hm hPow).trans hC.2.1
  · intro H
    exact (shift_row_from_power x X δ F H p 200 (by norm_num) A (hrows H)).trans hC.2.2.1
  · exact (shift_pair_from_power x X δ F p 200 M hPow).trans
      ((add_le_add hQsize (le_refl _)).trans hC.2.2.2)

end SharpRamseyFive.ScoreGeometry

end OAI
