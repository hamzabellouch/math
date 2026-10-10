import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.ScorePairCapturedNormalized
import OAI.Combinatorics.RamseyFive.Entropy.HighMomentBudget

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem projective_high_captured_moment (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (T : Finset I) (hT : T.Nonempty)
    (P : I → Submodule K V) (J₀ : ℕ)
    (X₀ : Finset (ℙ K V))
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ L : ℝ≥0) (hδ : 0 < δ)
    (hS : S ⊆ X₀ \ remaining T hT (fun i => flatPoints (P i)) X₀ J₀)
    (hO : ownCell T hT (fun i => flatPoints (P i)) X₀ J₀ x ⊆ O x)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (χ b base D₀ : ℝ) (hn : 0 < (X₀.card:ℝ)) (hb : 1 ≤ b) (hD : 0 ≤ D₀)
    (hL : 10000 ≤ (L:ℝ)) (hbase : (23/25:ℝ) ≤ base)
    (hcap : (X₀.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscaleDensity : (X₀.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2 ≤ X₀.card)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
    (hlower : ∀ H : F,(3/4:ℝ) ≤ mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))
    (hdelta : ∀ H : F,|mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H)-base| ≤ 17/100)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/X₀.card^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (hcaptured : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      2097152*(Nat.card K:ℝ)^2 ≤ X₀.card*((δ:ℝ)*2^i)^2 →
      x∉highExceptions T hT P X₀ Planes J₀ ((δ:ℝ)*2^i) χ Q)
    {p : ℕ} (hp : 0 < p) (R h : ℕ) (hKR : 200 ≤ R/2) (hh : 0 < h)
    (hsize : h ≤ (R/2-5000)/(2*200)) (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1) < 1/2)
    (own : F→Fin R→Bool)
    (hDsum : (∑ H : F,SingletonEnumeration.independentWeight
      (radialWeight x (outsideAt x S (O x)) δ) (fun d => L*radialWeight x (outsideAt x S (O x)) δ d)
      (pencilLines x F) R 5000 base H) ≤ D₀)
    (hcost : D₀+2*((p+1:ℝ)*pencilHighBudget (Nat.card K) (outsideAt x S (O x)).card (X₀.card:ℝ) χ b L p R) ≤
      geometryScale (Nat.card K) (X₀.card:ℝ)*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2 ≤ Real.exp (((L:ℝ)*R)/10))
    (hA : 2 ≤ geometryScale (Nat.card K) (X₀.card:ℝ)*Real.exp (-((L:ℝ)*R)))
    (hscale : 16*((Nat.card K:ℝ)+1) ≤
      (geometryScale (Nat.card K) (X₀.card:ℝ)*Real.exp (-((L:ℝ)*R)))*(1/(100*(p:ℝ)))^2)
    (hstrong : x∉badCenters S O δ ((1/(100*(p:ℝ)))/2) Lines Q 1)
    (hpairScalar : (pencilAlphabet (Nat.card K) 4:ℝ)+
      (dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) (X₀.card:ℝ))^2)/(1/(100*(p:ℝ)))^200 ≤
      (geometryScale (Nat.card K) (X₀.card:ℝ))^2*Real.exp (((L:ℝ)*R)/10)) :
    (∫ ω, HighMoment.allTrunc R 5000 ω*(∑ H : F,scoreTerm (pencilLines x F H) (Real.exp (-(L:ℝ)*base)) (own H)
      (fun r d => ω (r,d)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S (O x)) δ i.2)) ≤
      (geometryScale (Nat.card K) (X₀.card:ℝ))^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  have hn' : 0 < X₀.card := by exact_mod_cast hn
  have hχ : 0 ≤ χ := Real.one_le_exp_iff.mp (le_trans (by norm_num) hchi)
  have hrowchi : (208*2^198:ℝ) ≤ Real.exp (2*χ) :=
    le_trans (le_trans (by norm_num) hchi) (Real.exp_le_exp.mpr (by linarith))
  apply projective_high_moment_from_pairs x hdim S O δ L hδ F hF X₀.card χ b base D₀
    hn hb hD hL hbase hcap hscaleDensity hrowchi hm hlower hdelta Lines hLines Q hx
    ?_ hp R h hKR hh hsize herr own hDsum hcost hp2 hA hscale hstrong hpairScalar
  simpa only [dyadFactor,geometryScale,mul_assoc,mul_left_comm,mul_comm] using
    score_pair_captured_moment x hdim T hT P X₀ S O J₀ hS hO δ hδ F hF
      Planes hPlanes hcomplete χ Q hx hn' hcap hscaleDensity hhigh hchi hmass
      Lines hLines hm hgood hcaptured 200 le_rfl

theorem projective_high_residual_moment (hdim : finrank K V=5)
    (X₀ : Finset (ℙ K V))
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ L : ℝ≥0) (hδ : 0 < δ)
    (hS : S ⊆ X₀)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (χ b base D₀ : ℝ) (hn : 0 < (X₀.card:ℝ)) (hb : 1 ≤ b) (hD : 0 ≤ D₀)
    (hL : 10000 ≤ (L:ℝ)) (hbase : (23/25:ℝ) ≤ base)
    (hcap : (X₀.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscaleDensity : (X₀.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2 ≤ X₀.card)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
    (hlower : ∀ H : F,(3/4:ℝ) ≤ mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))
    (hdelta : ∀ H : F,|mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H)-base| ≤ 17/100)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/X₀.card^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (hresidual : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      2097152*(Nat.card K:ℝ)^2 ≤ X₀.card*((δ:ℝ)*2^i)^2 →
      x∉residualExceptions Planes X₀ Q ((δ:ℝ)*2^i) χ)
    {p : ℕ} (hp : 0 < p) (R h : ℕ) (hKR : 200 ≤ R/2) (hh : 0 < h)
    (hsize : h ≤ (R/2-5000)/(2*200)) (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1) < 1/2)
    (own : F→Fin R→Bool)
    (hDsum : (∑ H : F,SingletonEnumeration.independentWeight
      (radialWeight x (outsideAt x S (O x)) δ) (fun d => L*radialWeight x (outsideAt x S (O x)) δ d)
      (pencilLines x F) R 5000 base H) ≤ D₀)
    (hcost : D₀+2*((p+1:ℝ)*pencilHighBudget (Nat.card K) (outsideAt x S (O x)).card (X₀.card:ℝ) χ b L p R) ≤
      geometryScale (Nat.card K) (X₀.card:ℝ)*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2 ≤ Real.exp (((L:ℝ)*R)/10))
    (hA : 2 ≤ geometryScale (Nat.card K) (X₀.card:ℝ)*Real.exp (-((L:ℝ)*R)))
    (hscale : 16*((Nat.card K:ℝ)+1) ≤
      (geometryScale (Nat.card K) (X₀.card:ℝ)*Real.exp (-((L:ℝ)*R)))*(1/(100*(p:ℝ)))^2)
    (hstrong : x∉badCenters S O δ ((1/(100*(p:ℝ)))/2) Lines Q 1)
    (hpairScalar : (pencilAlphabet (Nat.card K) 4:ℝ)+
      (dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) (X₀.card:ℝ))^2)/(1/(100*(p:ℝ)))^200 ≤
      (geometryScale (Nat.card K) (X₀.card:ℝ))^2*Real.exp (((L:ℝ)*R)/10)) :
    (∫ ω, HighMoment.allTrunc R 5000 ω*(∑ H : F,scoreTerm (pencilLines x F H) (Real.exp (-(L:ℝ)*base)) (own H)
      (fun r d => ω (r,d)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S (O x)) δ i.2)) ≤
      (geometryScale (Nat.card K) (X₀.card:ℝ))^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  have hn' : 0 < X₀.card := by exact_mod_cast hn
  have hχ : 0 ≤ χ := Real.one_le_exp_iff.mp (le_trans (by norm_num) hchi)
  have hrowchi : (208*2^198:ℝ) ≤ Real.exp (2*χ) :=
    le_trans (le_trans (by norm_num) hchi) (Real.exp_le_exp.mpr (by linarith))
  apply projective_high_moment_from_pairs x hdim S O δ L hδ F hF X₀.card χ b base D₀
    hn hb hD hL hbase hcap hscaleDensity hrowchi hm hlower hdelta Lines hLines Q hx
    ?_ hp R h hKR hh hsize herr own hDsum hcost hp2 hA hscale hstrong hpairScalar
  simpa only [dyadFactor,geometryScale,mul_assoc,mul_left_comm,mul_comm] using
    score_pair_residual_moment x hdim X₀ S O hS δ hδ F hF
      Planes hPlanes hcomplete χ Q hx hn' hcap hscaleDensity hhigh hchi hmass
      Lines hLines hm hgood hresidual 200 le_rfl

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

lemma radial_tail_off_exception (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a D : ℝ) (Lines : Finset (Submodule K V))
    (hLines : ∀ l : RadialLine x,l.val∈Lines) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ a Lines Q D) :
    ((Finset.univ.filter fun l : RadialLine x =>
      a ≤ (radialWeight x (outsideAt x S (O x)) δ l:ℝ)).card:ℝ) < D := by
  let A := Finset.univ.filter fun l : RadialLine x =>
      a ≤ (radialWeight x (outsideAt x S (O x)) δ l:ℝ)
  let E := localLines S O δ a Lines x
  let f (l : A) : E := ⟨l.val.val,by
    refine Finset.mem_filter.mpr ⟨hLines l.val,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.val.property.2
    · have hr := (Finset.mem_filter.mp l.property).2
      change a ≤ (δ:ℝ)*(((outsideAt x S (O x)).filter fun y => y.val.submodule ≤ l.val.val).card:ℝ) at hr
      rwa [outsideAt_filter_card] at hr⟩
  have hi : Function.Injective f := by
    intro l m he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : E => z.val) he))
  have hc : A.card ≤ E.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi
  have he : (E.card:ℝ) < D := by
    by_contra hn
    exact hgood (Finset.mem_filter.mpr ⟨hx,le_of_not_gt hn⟩)
  exact lt_of_le_of_lt (by exact_mod_cast hc) he

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma radial_bounded_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (M : ℝ) (hmax : ∀ l : RadialLine x,(radialWeight x X δ l:ℝ) ≤ M)
    (l : RadialLine x) (hp : 0 < (radialWeight x X δ l:ℝ)) :
    ∃ i∈boundedOverlapDyads x X δ M,
      (δ:ℝ)*2^i ≤ (radialWeight x X δ l:ℝ) ∧
      (radialWeight x X δ l:ℝ) ≤ 2*((δ:ℝ)*2^i) := by
  have hc : 0 < (RadialLine.trainingOnLine X l).card := by
    by_contra hn
    have hz : (RadialLine.trainingOnLine X l).card=0 := by omega
    simp [radialWeight,hz] at hp
  have hfloor : (δ:ℝ) ≤ (radialWeight x X δ l:ℝ) := by
    have hh : (1:ℝ) ≤ (RadialLine.trainingOnLine X l).card := by exact_mod_cast hc
    simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast,mul_one] using
      mul_le_mul_of_nonneg_left hh δ.coe_nonneg
  have hbound : (radialWeight x X δ l:ℝ) ≤ (δ:ℝ)*2^Nat.clog 2 X.card := by
    have hh : (RadialLine.trainingOnLine X l).card ≤ 2^Nat.clog 2 X.card :=
      (Finset.card_filter_le _ _).trans (Nat.le_pow_clog (by norm_num) X.card)
    change (δ:ℝ)*((RadialLine.trainingOnLine X l).card:ℝ) ≤ (δ:ℝ)*(2:ℝ)^Nat.clog 2 X.card
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hh) δ.coe_nonneg
  obtain ⟨i,hi,hlo,hhi⟩ := dyadic_cover δ _ δ.coe_nonneg hfloor _ hbound
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,hlo.trans (hmax l)⟩,hlo,hhi⟩

theorem radial_high_moment (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (hδ : 0 < δ) (n χ : ℝ) (hn : 0 < n)
    (hmax : (δ:ℝ)*((Nat.card K:ℝ)+1) ≤ 2)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (J : ℕ) (hJ : 100 ≤ J) :
    (∑ l : RadialLine x,(radialWeight x (outsideAt x S (O x)) δ l:ℝ)^J) ≤
      ((δ:ℝ)*((Nat.card K:ℝ)+1))^(J-100)*
        (2^200*(Nat.clog 2 (outsideAt x S (O x)).card+1)*((Nat.card K:ℝ)^4/n^2*Real.exp χ)) := by
  let X := outsideAt x S (O x)
  let A := (Nat.card K:ℝ)^4/n^2*Real.exp χ
  have hm (l : RadialLine x) : (radialWeight x X δ l:ℝ) ≤ (δ:ℝ)*((Nat.card K:ℝ)+1) := by
    have hh : ((RadialLine.trainingOnLine X l).card:ℝ) ≤ (Nat.card K:ℝ)+1 := by
      exact_mod_cast training_line_card x X l
    exact mul_le_mul_of_nonneg_left hh δ.coe_nonneg
  have hpoly : (∑ l : RadialLine x,(radialWeight x X δ l:ℝ)^100) ≤
      2^200*(Nat.clog 2 X.card+1)*A := by
    have hh := moment_polynomial_tail (fun l : RadialLine x => (radialWeight x X δ l:ℝ))
      (fun i : ℕ => (δ:ℝ)*2^i) (boundedOverlapDyads x X δ 2) 100 (by norm_num) (2^100*A)
      (fun l => NNReal.coe_nonneg _) (by intro i _; positivity)
      (radial_bounded_cover x X δ 2 (fun l => (hm l).trans hmax)) ?_
    · apply hh.trans
      have hc : ((boundedOverlapDyads x X δ 2).card:ℝ) ≤ Nat.clog 2 X.card+1 := by
        exact_mod_cast boundedOverlapDyads_card x X δ 2
      have hA : 0 ≤ A := by dsimp [A]; positivity
      calc
        _ ≤ (2:ℝ)^100*(Nat.clog 2 X.card+1)*(2^100*A) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (pow_nonneg (by norm_num) 100)) (mul_nonneg (pow_nonneg (by norm_num) 100) hA)
        _ = _ := by ring
    · intro i hi
      let a : ℝ := (δ:ℝ)*2^i
      have ha : 0 < a := by dsimp [a]; positivity
      have ht := radial_tail_off_exception x S O δ (a/2) (A/(a/2)^100) Lines hLines Q hx (hgood i hi)
      have hcard : ((Finset.univ.filter fun l : RadialLine x => a ≤ (radialWeight x X δ l:ℝ)).card:ℝ) ≤
          ((Finset.univ.filter fun l : RadialLine x => a/2 ≤ (radialWeight x X δ l:ℝ)).card:ℝ) := by
        apply Nat.cast_le.mpr
        apply Finset.card_le_card
        intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(by linarith : a/2 ≤ a).trans (Finset.mem_filter.mp hl).2⟩
      calc
        _ ≤ (A/(a/2)^100)*a^100 := mul_le_mul_of_nonneg_right (hcard.trans ht.le) (pow_nonneg ha.le _)
        _ = 2^100*A := by field_simp
  exact pow_sum_from_lower _ _ _ 100 J (by positivity) hJ (fun l => NNReal.coe_nonneg _) hm hpoly

end SharpRamseyFive.ScoreGeometry

end OAI
