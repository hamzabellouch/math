import OAI.NumberTheory.TwoPoint.Halasz.HalaszSelectedWeights
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDegreeSaving

namespace OAI

/-! Fixed and rounded Taylor degrees cover the bounded height/length ratios. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_medium_degree_saving {lam k d : ℝ}
    (hlo : 9/10≤lam) (hhi : lam≤48) (hk0 : 0≤k) (hk : k≤3*lam+6)
    (hdlo : 3*lam/2≤d) (hdhi : d≤3*lam/2+1) :
    (1:ℝ)/32+k^2/1024≤min (d/3) (min (d-lam) (lam-d/3)) := by
  have hm := halasz_medium_degree_margin hlo hhi
  have hk2 : k^2≤(3*lam+6)^2 := by nlinarith
  apply le_min
  · nlinarith
  · apply le_min <;> nlinarith

noncomputable def halaszMediumDegree (lam : ℝ) : ℕ := 3*⌈lam⌉₊+3
noncomputable def halaszMediumActive (lam : ℝ) : ℕ := ⌈3*lam/2⌉₊

lemma halasz_medium_degree_bounds {lam : ℝ} (hlo : 9/10≤lam) :
    2≤halaszMediumDegree lam ∧ 1≤halaszMediumActive lam ∧
    halaszMediumActive lam≤halaszMediumDegree lam ∧
    3*lam+3≤(halaszMediumDegree lam:ℝ) ∧
    (halaszMediumDegree lam:ℝ)≤3*lam+6 ∧
    3*lam/2≤(halaszMediumActive lam:ℝ) ∧
    (halaszMediumActive lam:ℝ)≤3*lam/2+1 := by
  have hc := Nat.le_ceil lam
  have hc' := Nat.ceil_lt_add_one (by linarith : 0≤lam)
  have hd := Nat.le_ceil (3*lam/2)
  have hd' := Nat.ceil_lt_add_one (by linarith : 0≤3*lam/2)
  have hklo : 3*lam+3≤(halaszMediumDegree lam:ℝ) := by
    dsimp only [halaszMediumDegree]
    push_cast
    linarith
  have hkhi : (halaszMediumDegree lam:ℝ)≤3*lam+6 := by
    dsimp only [halaszMediumDegree]
    push_cast
    linarith
  have hdlo : 3*lam/2≤(halaszMediumActive lam:ℝ) := hd
  have hdhi : (halaszMediumActive lam:ℝ)≤3*lam/2+1 := hd'.le
  refine ⟨?_,?_,?_,hklo,hkhi,hdlo,hdhi⟩
  · unfold halaszMediumDegree
    omega
  · exact_mod_cast (show (1:ℝ)≤halaszMediumActive lam by linarith)
  · exact_mod_cast (show (halaszMediumActive lam:ℝ)≤halaszMediumDegree lam by linarith)

lemma halasz_single_degree_weight_product {k r M d : ℕ} (hr : 1≤r) (hM : 1≤M)
    (hd0 : 1≤d) (hdk : d≤k) {t z N lam η : ℝ} (hN : 1≤N)
    (hz : N≤z) (hzhi : z≤2*N) (ht : |t|=N^lam)
    (hscale : N^(1/3:ℝ)≤2*(M:ℝ))
    (h₁ : η≤(d:ℝ)/3) (h₂ : η≤(d:ℝ)-lam) (h₃ : η≤lam-(d:ℝ)/3) :
    (∏ j : Fin k,halaszNormalizedWeight r M (halaszLogCoefficient t z) j)≤
      (halaszLogWeightCost k r)^k*N^(-η) := by
  let j : Fin k := ⟨d-1,by omega⟩
  have hj : (j.val:ℝ)+1=d := by
    dsimp only [j]
    rw [Nat.cast_sub hd0,Nat.cast_one]
    ring
  have hh := halasz_log_selected_weight_product hr hM hN hz hzhi ht hscale {j}
    (η := η)
    (fun i hi => by have hi' := mem_singleton.mp hi; subst i; rw [hj]; linarith)
    (fun i hi => by have hi' := mem_singleton.mp hi; subst i; rw [hj]; exact h₂)
    (fun i hi => by have hi' := mem_singleton.mp hi; subst i; rw [hj]; linarith)
  simpa using hh

end TwoPointCorrelations

end OAI
