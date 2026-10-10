import OAI.NumberTheory.Ostmann.Characters.CharacterMaximum

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters

theorem correlationBound_sq_le_quadratic_higher {p:ℕ} [Fact p.Prime]
    (S:Finset (ZMod p)) (hp:p≠2)
    (hlo:1/4≤Supply.density S) (hhi:Supply.density S≤3/4) :
    ((FiniteField.correlationBound (Supply.additiveTransform S):ℝ))^2 ≤
      48*(((maxTranslatedBias S (quadraticCharacter p):ℝ))^2+
        ((higherBias S:ℝ))^2+(p:ℝ)⁻¹) := by
  have h := correlationBound_le_quadratic_add_higher S hp hlo hhi
  let q : ℝ := maxTranslatedBias S (quadraticCharacter p)
  let a : ℝ := higherBias S
  let r : ℝ := 1/Real.sqrt p
  have hq : 0≤q := NNReal.coe_nonneg _
  have ha : 0≤a := NNReal.coe_nonneg _
  have hr : 0≤r := by positivity
  have hc : 0≤(FiniteField.correlationBound (Supply.additiveTransform S):ℝ) :=
    NNReal.coe_nonneg _
  have he : r^2=(p:ℝ)⁻¹ := by
    simp only [r,one_div,inv_pow,Real.sq_sqrt (Nat.cast_nonneg p)]
  have hh : (FiniteField.correlationBound (Supply.additiveTransform S):ℝ)≤4*(q+a+r) := by
    calc
      _ ≤ 4*(q+a)+4/Real.sqrt p := h
      _ = _ := by dsimp [r]; ring
  have hs := (sq_le_sq₀ hc (by positivity : 0≤4*(q+a+r))).mpr hh
  change _≤48*(q^2+a^2+(p:ℝ)⁻¹)
  rw [← he]
  nlinarith [sq_nonneg (q-a),sq_nonneg (q-r),sq_nonneg (a-r)]

theorem weighted_mixed_bad_bound {ι:Type*} [Fintype ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime] (S:∀i,Finset (ZMod (p i)))
    (w:ι→ℝ) (hw:∀i,0≤w i) (δ:ℝ) (hδ:0<δ)
    (hp:∀i,p i≠2) (hlo:∀i,1/4≤Supply.density (S i))
    (hhi:∀i,Supply.density (S i)≤3/4) :
    δ^2*(∑i:ι with δ≤(FiniteField.correlationBound (Supply.additiveTransform (S i)):ℝ),w i) ≤
      48*(∑i:ι,w i*(((maxTranslatedBias (S i) (quadraticCharacter (p i)):ℝ))^2+
        ((higherBias (S i):ℝ))^2+(p i:ℝ)⁻¹)) := by
  classical
  let bad : Finset ι := Finset.univ.filter
    (fun i=>δ≤(FiniteField.correlationBound (Supply.additiveTransform (S i)):ℝ))
  change δ^2*(∑i∈bad,w i)≤_
  calc
    _ = ∑i∈bad,w i*δ^2 := by rw [Finset.mul_sum]; congr 1; ext i; ring
    _ ≤ ∑i∈bad,w i*48*
        (((maxTranslatedBias (S i) (quadraticCharacter (p i)):ℝ))^2+
        ((higherBias (S i):ℝ))^2+(p i:ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      have hbad := (Finset.mem_filter.mp hi).2
      have hsq : δ^2≤((FiniteField.correlationBound (Supply.additiveTransform (S i)):ℝ))^2 :=
        (sq_le_sq₀ hδ.le (NNReal.coe_nonneg _)).mpr hbad
      have hi' := hsq.trans (correlationBound_sq_le_quadratic_higher (S i) (hp i) (hlo i) (hhi i))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi' (hw i)
    _ ≤ ∑i:ι,w i*48*
        (((maxTranslatedBias (S i) (quadraticCharacter (p i)):ℝ))^2+
        ((higherBias (S i):ℝ))^2+(p i:ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i hi hnot
      have hwi := hw i
      positivity
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring

end Ostmann.Characters

end

end OAI
