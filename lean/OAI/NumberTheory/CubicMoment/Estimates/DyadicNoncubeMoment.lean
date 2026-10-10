import OAI.NumberTheory.CubicMoment.Estimates.FullNoncubeMoment
import OAI.NumberTheory.CubicMoment.Estimates.ExceptionalBenchmark

namespace OAI

/-! Fixed norm dyads in the actual noncube estimate. Their factor of two
is absorbed by a strictly smaller exponent neighborhood. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma shifted_distance_bound (p q b c : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    |p-b|+|q-c| ≤ |p+a-b|+|q+a-c|+2*a := by
  have hb : |p-b| ≤ |p+a-b|+a := by
    calc
      _ = |(p+a-b)+(-a)| := by congr 1; ring
      _ ≤ |p+a-b|+|-a| := abs_add_le _ _
      _ = _ := by rw [abs_neg,abs_of_nonneg ha]
  have hc : |q-c| ≤ |q+a-c|+a := by
    calc
      _ = |(q+a-c)+(-a)| := by congr 1; ring
      _ ≤ |q+a-c|+|-a| := abs_add_le _ _
      _ = _ := by rw [abs_neg,abs_of_nonneg ha]
  linarith

lemma noncube_dyadic_shift_absorption {B C ν a : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (p q : ℝ) (ha : a ≤ ν/2) :
    C*B^2*(B^(p+a)*(B^(q+a))^2)^(1/3:ℝ)*B^(-ν) ≤
      C*B^2*(B^p*(B^q)^2)^(1/3:ℝ)*B^(-ν/2) := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have heq : (B^(p+a)*(B^(q+a))^2)^(1/3:ℝ) = (B^p*(B^q)^2)^(1/3:ℝ)*B^a := by
    rw [conductor_rpow_identity hBp,conductor_rpow_identity hBp,← Real.rpow_add hBp]
    congr 1
    ring
  rw [heq]
  calc
    _ = (C*B^2*(B^p*(B^q)^2)^(1/3:ℝ))*(B^a*B^(-ν)) := by ring
    _ = (C*B^2*(B^p*(B^q)^2)^(1/3:ℝ))*B^(a-ν) := by
      rw [← Real.rpow_add hBp]
      congr 2
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB (by linarith)) (by positivity)

theorem dyadic_full_noncube (hHuxley : HuxleyAdditiveLargeSieve)
    {κ δ R : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hR : 1 ≤ R) :
    ∃ η C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (p q : ℝ) (v e : Eisenstein) (u : ℝ)
      (Ram S T J H : Finset Eisenstein), T₀ ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η → κ ≤ p+2*q →
      δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      (∀ s ∈ S, gramDyad ((L r)^p) s) → (∀ t ∈ T, gramDyad ((L r)^q) t) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨η,C,ν,hη,hηhi,hC,hν,hraw⟩ := full_logarithmic_noncube (γ := γ) (ι := ι)
    hHuxley hκ (show 0 < δ/2 by positivity) hR
  let a := min η (min ν δ)/12
  have ha : 0 < a := div_pos (lt_min hη (lt_min hν hδ)) (by norm_num)
  have haη : 3*a ≤ η/2 := by dsimp [a]; linarith [min_le_left η (min ν δ)]
  have haν : a ≤ ν/2 := by dsimp [a]; linarith [(min_le_right η (min ν δ)).trans (min_le_left ν δ)]
  have haδ : 2*a ≤ δ/2 := by dsimp [a]; linarith [(min_le_right η (min ν δ)).trans (min_le_right ν δ)]
  refine ⟨η/2,C,ν/2,by positivity,by linarith,hC,by positivity,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₁,hbound⟩ := hraw L W hL hW hlo hhi
  obtain ⟨T₂,htwo⟩ := eventually_atTop.mp ((tendsto_rpow_atTop ha).eventually_ge_atTop (2:ℝ))
  refine ⟨max T₁ T₂,?_⟩
  intro r X p q v e u Ram S T J H hT₀ hX hprod hp hq hsize hlarge hfirst hbalanced hS hT hH
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have h2 : 2 ≤ (L r)^a := htwo (L r) ((le_max_right _ _).trans hT₀)
  have hn (z t : ℝ) (hz : z < 2*(L r)^t) : z ≤ (L r)^(t+a) := by
    apply hz.le.trans
    rw [Real.rpow_add hLp]
    nlinarith [mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLp.le t)]
  have hS' : ∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ (L r)^(p+a) :=
    fun s hs => ⟨(hS s hs).1,(hS s hs).2.1,hn _ _ (hS s hs).2.2.2⟩
  have hT' : ∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ (L r)^(q+a) :=
    fun t ht => ⟨(hT t ht).1,(hT t ht).2.1,hn _ _ (hT t ht).2.2.2⟩
  have hf : δ/2 ≤ |p+a-1|+|q+a| := by
    have hh := shifted_distance_bound p q 1 0 ha.le
    simp only [sub_zero] at hh
    linarith
  have hb : δ/2 ≤ |p+a-1/3|+|q+a-1/3| := by
    have hh := shifted_distance_bound p q (1/3) (1/3) ha.le
    linarith
  have hm := hbound r X (p+a) (q+a) v e u Ram S T J H ((le_max_left _ _).trans hT₀)
    hX hprod (by linarith) (by linarith) (by linarith) (by linarith) hf hb hS' hT' hH
  apply hm.trans
  have hh := noncube_dyadic_shift_absorption (hL r)
    (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg Ram.card)) (Nat.cast_nonneg J.card)) p q haν
  simpa only [mul_assoc,neg_div] using hh

end CubicFirstMoment

end

end OAI
