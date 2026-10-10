import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.OutsideCard
import OAI.Combinatorics.RamseyFive.Geometry.OutsidePairCard
import OAI.Combinatorics.RamseyFive.Probability.NormalizedPairHigh
import OAI.Combinatorics.RamseyFive.Probability.HighOrSmall

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pair_captured_normalized (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X S O : Finset (ℙ K V))
    (J : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (hO : ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V)))
    (hG : ∀ H∈G,Incident x H)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (a χ : ℝ) (Y : Finset (ℙ K V)) (hxY : x∈Y)
    (hn : 0 < X.card) (ha : 0 < a) (ha2 : a ≤ 2)
    (hcap : (X.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hhigh : 2097152*(Nat.card K:ℝ)^2 ≤ X.card*a^2)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hx : x∉highExceptions F hF P X Planes J a χ Y) :
    ((Finset.univ.filter fun z : DistinctPairs G => a ≤ strength (pencilLines x G)
      (radialWeight x (outsideAt x S O) δ) z).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/X.card)^2*Real.exp (2*χ) := by
  have hn' : (0:ℝ) < X.card := by exact_mod_cast hn
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.card_pos : 0 < Nat.card K))
  apply ScoreScalars.normalized_pair_high hq hn' ha ha2 hcap hchi
  have hh := score_high_captured_pairs_of_le x hdim F hF P X S O J hS hO δ hδ G hG
    Planes hPlanes hcomplete a a χ Y hxY hn ha ha2 hhigh
    (high_threshold_scale (K := K) δ X.card a hn' ha.le hscale) hx
  have hh' : ((Finset.univ.filter fun z : DistinctPairs G => a ≤ strength (pencilLines x G)
      (radialWeight x (outsideAt x S O) δ) z).card:ℝ) ≤
      (2*HighParameters.degree (Nat.card K) X.card a χ*(Nat.card K+1)^2:ℕ) := Nat.cast_le.mpr hh
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hh'

theorem score_pair_residual_normalized (hdim : finrank K V=5)
    (X S O : Finset (ℙ K V)) (hS : S ⊆ X)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V)))
    (hG : ∀ H∈G,Incident x H)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (a χ : ℝ) (Y : Finset (ℙ K V)) (hxY : x∈Y)
    (hn : 0 < X.card) (ha : 0 < a) (ha2 : a ≤ 2)
    (hcap : (X.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hx : x∉residualExceptions Planes X Y a χ) :
    ((Finset.univ.filter fun z : DistinctPairs G => a ≤ strength (pencilLines x G)
      (radialWeight x (outsideAt x S O) δ) z).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/X.card)^2*Real.exp (2*χ) := by
  have hn' : (0:ℝ) < X.card := by exact_mod_cast hn
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.card_pos : 0 < Nat.card K))
  apply ScoreScalars.normalized_pair_high hq hn' ha ha2 hcap hchi
  have ht := high_threshold_scale (K := K) δ X.card a hn' ha.le hscale
  have ht' : (δ:ℝ)*HighParameters.threshold (Nat.card K) X.card a ≤ a := by
    have h0 : 0 ≤ (δ:ℝ)*(HighParameters.threshold (Nat.card K) X.card a:ℝ) := by positivity
    linarith
  have hh := score_high_residual_pairs x hdim X S O hS δ hδ G hG Planes hPlanes hcomplete
    a a χ Y hxY ht' hx
  have hh' : ((Finset.univ.filter fun z : DistinctPairs G => a ≤ strength (pencilLines x G)
    (radialWeight x (outsideAt x S O) δ) z).card:ℝ) ≤
    (HighParameters.degree (Nat.card K) X.card a χ*(Nat.card K+1)^2:ℕ) := Nat.cast_le.mpr hh
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] at hh'
  apply hh'.trans
  have h0 : 0 ≤ (HighParameters.degree (Nat.card K) X.card a χ:ℝ)*(Nat.card K+1)^2 := by positivity
  nlinarith

theorem score_pair_captured_moment (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (J : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (hO : ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O x)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (χ : ℝ) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hn : 0 < X.card) (hcap : (X.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2 ≤ X.card)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (hm : ∀ H : G,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x G H) ≤ 2)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/X.card^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (hcaptured : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      2097152*(Nat.card K:ℝ)^2 ≤ X.card*((δ:ℝ)*2^i)^2 →
      x∉highExceptions F hF P X Planes J ((δ:ℝ)*2^i) χ Q)
    (R : ℕ) (hR : 200 ≤ R) :
    (∑ z : DistinctPairs G,strength (pencilLines x G) (radialWeight x (outsideAt x S (O x)) δ) z^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/X.card)^2*Real.exp (2*χ)) := by
  have hn' : (0:ℝ) < X.card := by exact_mod_cast hn
  apply score_higher_power x _ δ hδ G hG _ (by positivity) 200 R (by norm_num) hR hm
  intro i hi
  have ha : 0 < (δ:ℝ)*2^i := by positivity
  have ha2 := (Finset.mem_filter.mp hi).2
  rcases ScoreScalars.high_or_small (q := (Nat.card K:ℝ)) (n := X.card)
      (by positivity) hn' ha.le hhigh with hlarge|hsmall
  · exact score_pair_captured_normalized x hdim F hF P X S (O x) J hS hO δ hδ G hG
      Planes hPlanes hcomplete _ χ Q hx hn ha ha2 hcap hscale hlarge hchi (hcaptured i hi hlarge)
  · exact score_pair_small_normalized x hdim S O δ hδ G hG X.card _ χ hn' ha ha2 hmass hsmall
      (le_trans (by norm_num) hchi) Lines hLines Q hx (hgood i hi)

theorem score_pair_residual_moment (hdim : finrank K V=5)
    (X S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (hS : S ⊆ X)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (χ : ℝ) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hn : 0 < X.card) (hcap : (X.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2 ≤ X.card)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (hm : ∀ H : G,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x G H) ≤ 2)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/X.card^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (hresidual : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      2097152*(Nat.card K:ℝ)^2 ≤ X.card*((δ:ℝ)*2^i)^2 →
      x∉residualExceptions Planes X Q ((δ:ℝ)*2^i) χ)
    (R : ℕ) (hR : 200 ≤ R) :
    (∑ z : DistinctPairs G,strength (pencilLines x G) (radialWeight x (outsideAt x S (O x)) δ) z^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/X.card)^2*Real.exp (2*χ)) := by
  have hn' : (0:ℝ) < X.card := by exact_mod_cast hn
  apply score_higher_power x _ δ hδ G hG _ (by positivity) 200 R (by norm_num) hR hm
  intro i hi
  have ha : 0 < (δ:ℝ)*2^i := by positivity
  have ha2 := (Finset.mem_filter.mp hi).2
  rcases ScoreScalars.high_or_small (q := (Nat.card K:ℝ)) (n := X.card)
      (by positivity) hn' ha.le hhigh with hlarge|hsmall
  · exact score_pair_residual_normalized x hdim X S (O x) hS δ hδ G hG
      Planes hPlanes hcomplete _ χ Q hx hn ha ha2 hcap hscale hchi (hresidual i hi hlarge)
  · exact score_pair_small_normalized x hdim S O δ hδ G hG X.card _ χ hn' ha ha2 hmass hsmall
      (le_trans (by norm_num) hchi) Lines hLines Q hx (hgood i hi)

end SharpRamseyFive.ScoreGeometry

end OAI
