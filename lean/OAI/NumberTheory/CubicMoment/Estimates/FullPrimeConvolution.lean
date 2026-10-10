import OAI.NumberTheory.CubicMoment.Estimates.StructuredSupportBounds

namespace OAI

/-! A finite realization of the literal prime convolution: each coordinate
contains every primary prime on which its independent weight is nonzero. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullPrimeSupport (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (i : ι) : Finset Eisenstein :=
  ((primaryElementBall (R*X i)).filter (fun n => W i (norm n/X i) ≠ 0)).filter Prime

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_mem_iff {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hhi : ∀ i x, R < x → W i x = 0) (i : ι) (p : Eisenstein) :
    p ∈ fullPrimeSupport R W X i ↔ primaryPrime p ∧ W i (norm p/X i) ≠ 0 := by
  simp only [fullPrimeSupport,Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨⟨hp,_⟩,hw⟩,hq⟩
    exact ⟨⟨hp,hq⟩,hw⟩
  · rintro ⟨⟨hp,hq⟩,hw⟩
    have hn : norm p/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
    exact ⟨⟨⟨hp,(div_le_iff₀ (hX i)).mp hn⟩,hw⟩,hq⟩

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_eq_coordinate {R Z : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hhi : ∀ i x, R < x → W i x = 0)
    (hZ : ∀ i, R*X i ≤ 2*Z) : fullPrimeSupport R W X = coordinatePrimeSupport W X Z := by
  funext i
  ext p
  rw [fullPrimeSupport_mem_iff W X hX hhi]
  simp only [coordinatePrimeSupport,coordinateSupport,Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨hp,hq⟩,hw⟩
    have hn : norm p/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
    exact ⟨⟨⟨hp,((div_le_iff₀ (hX i)).mp hn).trans (hZ i)⟩,hw⟩,hq⟩
  · rintro ⟨⟨⟨hp,_⟩,hw⟩,hq⟩
    exact ⟨⟨hp,hq⟩,hw⟩

def fullPrimeCoefficient (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (z : Eisenstein) : ℂ :=
  squarefreeConvolution (fullPrimeSupport R W X) (fun i n => W i (norm n/X i)) z

def fullStructuredPrimeSum (R : ℝ) (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun z => IsCoprime z e),
    fullPrimeCoefficient R W X z*mellinPhase u (norm z)*cubicSymbol z (v*a*b^2)

lemma fullStructuredPrimeSum_eq {R Z : ℝ} (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hhi : ∀ i x, R < x → W i x = 0) (hZ : ∀ i, R*X i ≤ 2*Z) :
    fullStructuredPrimeSum R a b v e u W X = structuredPrimeSum a b v e u W X Z := by
  unfold fullStructuredPrimeSum fullPrimeCoefficient structuredPrimeSum primeMomentCoefficient
  rw [fullPrimeSupport_eq_coordinate W X hX hhi hZ]

lemma coordinate_le_product (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i) (i : ι) :
    X i ≤ ∏ j, X j := by
  rw [← Finset.mul_prod_erase _ X (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (by linarith [hX i]) (Finset.one_le_prod₀ (fun j _ => hX j))

lemma fullStructuredPrimeSum_partition_cutoff {R : ℝ} (hR : 1 ≤ R)
    (J : ℕ) (hJ : 2*R^(Fintype.card ι) ≤ (4/3:ℝ)^J)
    (a b v e : Eisenstein) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 1 ≤ X i) (hhi : ∀ i x, R < x → W i x = 0) :
    fullStructuredPrimeSum R a b v e u W X =
      structuredPrimeSum a b v e u W X (((4/3:ℝ)^J/2)*(∏ i, X i)) := by
  apply fullStructuredPrimeSum_eq a b v e u W X (fun i => by linarith [hX i]) hhi
  intro i
  have hi := coordinate_le_product X hX i
  have hprod : 0 ≤ ∏ i, X i := Finset.prod_nonneg (fun i _ => by linarith [hX i])
  have hk : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hRk : R ≤ R^(Fintype.card ι) := by
    exact le_self_pow₀ hR (Nat.ne_of_gt hk)
  have hRR : R ≤ (4/3:ℝ)^J := by linarith [hRk,show (0:ℝ) ≤ R^Fintype.card ι by positivity]
  nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ R by linarith),
    mul_le_mul_of_nonneg_right hRR hprod]

end CubicFirstMoment

end

end OAI
