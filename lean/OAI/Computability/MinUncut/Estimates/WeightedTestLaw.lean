import Mathlib
import OAI.Computability.MinUncut.Search.FiniteAverageBounds
import OAI.Computability.MinUncut.Estimates.LiteralTestQueries
import OAI.Computability.MinUncut.Analysis.RationalRowNoise

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I : Type*} [Fintype I] {m n : ℕ}

abbrev LocalSample (A : Type*) {V : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] (m n : ℕ) (g : GridData) :=
  FaceArray A m n × FaceArray A m n × Code m n × (TestCoordinates m n → Fin g.L)

def noiseWeight {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (a : ℚ) (B C : FaceArray A m n) : Test → ℚ
  | .second => RowNoise.rationalDensity a B C
  | _ => 1

def localWeight {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (g : GridData) (a b : ℚ) (j : Test) (p : LocalSample A m n g) : ℚ :=
  (Fintype.card (FaceArray A m n):ℚ)⁻¹ * (Fintype.card (FaceArray A m n):ℚ)⁻¹ *
  (Fintype.card (Code m n):ℚ)⁻¹ * gridWeight g p.2.2.2 * noiseWeight a p.1 p.2.1 j / b

lemma sum_invcard_mul {X : Type*} [Fintype X] (f : X → ℝ) :
    (∑ x, (Fintype.card X:ℝ)⁻¹*f x)=𝔼 x, f x := by
  rw [← Finset.mul_sum,Fintype.expect_eq_sum_div_card,mul_comm,div_eq_mul_inv]

lemma localWeight_nonneg {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (g : GridData) (hT : 0<g.T) (hL : 0<g.L) {a b : ℚ} (ha : 0≤a) (ha1 : a≤1)
    (hb : 0<b) (j : Test) (p : LocalSample A m n g) : 0≤localWeight g a b j p := by
  have hg := (gridWeight_pos g hT hL p.2.2.2).le
  have hn : 0≤noiseWeight a p.1 p.2.1 j := by
    cases j with
    | second => exact RowNoise.rationalDensity_nonneg ha ha1 _ _
    | first => exact zero_le_one
    | third => exact zero_le_one
    | fourth => exact zero_le_one
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg _)))
    (inv_nonneg.mpr (Nat.cast_nonneg _))) hg) hn) hb.le

lemma localWeight_sum {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (g : GridData) (a b : ℚ) (j : Test) (F : LocalSample A m n g → ℝ) :
    (∑ p, (localWeight g a b j p:ℝ)*F p)=
      (𝔼 B, 𝔼 C, 𝔼 z, ∑ q : TestCoordinates m n → Fin g.L,
        (gridWeight g q:ℝ)*(noiseWeight a B C j:ℝ)*F (B,C,z,q))/(b:ℝ) := by
  simp only [localWeight,Rat.cast_div,Rat.cast_mul,Rat.cast_inv,Rat.cast_natCast,
    Fintype.sum_prod_type,Fintype.expect_eq_sum_div_card]
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma noiseWeight_cast (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (a : ℚ) (B C : FaceArray (SecondAlphabet (secondQuestion U h pos)) m n) :
    (noiseWeight a B C .second:ℝ)=RowNoise.density a B C :=
  RowNoise.rationalDensity_cast a B C

lemma localTest_mean (f : ProofFamily Name I) (U : I → Equation Name) (h : I → Bool)
    (pos : I → Fin 3) (g : GridData) (a σ η : ℚ) (j : Test) :
    (𝔼 B, 𝔼 C, 𝔼 z, ∑ q : TestCoordinates m n → Fin g.L,
      (gridWeight g q:ℝ)*(noiseWeight a B C j:ℝ)*
        testFunctional f U h pos B C z (rationalScoreTable σ η (fun i => midpoint g.T g.L (q i))) j)=
    match j with
    | .first => finiteFirst (m := m) (n := n) g (f.second (secondQuestion U h pos)) σ η
    | .second => finiteSecond (m := m) (n := n) g (f.second (secondQuestion U h pos)) a σ η
    | .third => finiteThird (m := m) (n := n) g (f.second (secondQuestion U h pos)) σ η
    | .fourth => finiteFourth (m := m) (n := n) g (projection U h pos)
        (f.first U) (f.second (secondQuestion U h pos)) σ η := by
  cases j
  · simp only [noiseWeight,Rat.cast_one,mul_one,testFunctional,Fintype.expect_const,
      finiteFirst,tableAverage]
  · simp only [noiseWeight,RowNoise.rationalDensity_cast,testFunctional,Fintype.expect_const,
      finiteSecond,tableAverage]
    congr 1
    funext B
    congr 1
    funext C
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  · simp only [noiseWeight,Rat.cast_one,mul_one,testFunctional,Fintype.expect_const,
      finiteThird,tableAverage]
  · simp only [noiseWeight,Rat.cast_one,mul_one,testFunctional,Fintype.expect_const,
      finiteFourth,tableAverage]
end MinUncut.Outer

namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n k : ℕ}

instance localSampleFintype {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (m n : ℕ) (g : GridData) : Fintype (LocalSample A m n g) := by
  unfold LocalSample
  infer_instance

abbrev OuterSample (I S : Type*) [Fintype I] (k : ℕ) :=
  FixedSets I k × (I → S) × (I → Fin 3)

def sampleFirst (equations : S → Equation Name) (o : OuterSample I S k) : I → Equation Name :=
  fun i => equations (o.2.1 i)
def sampleHidden (o : OuterSample I S k) : I → Bool := hiddenSet o.1.val

abbrev sampleSecond (equations : S → Equation Name) (o : OuterSample I S k) : I → SecondQuestion Name :=
  secondQuestion (sampleFirst equations o) (sampleHidden o) o.2.2

abbrev Elementary (equations : S → Equation Name) (k m n : ℕ) (g : GridData) :=
  Σ o : OuterSample I S k, LocalSample (SecondAlphabet (sampleSecond equations o)) m n g

instance elementaryFintype (equations : S → Equation Name) (k m n : ℕ) (g : GridData) :
    Fintype (Elementary (I := I) equations k m n g) := by
  unfold Elementary
  infer_instance

def elementaryWeight (equations : S → Equation Name) (g : GridData) (a b : ℚ) (j : Test)
    (e : Elementary (I := I) equations k m n g) : ℚ :=
  (Fintype.card (OuterSample I S k):ℚ)⁻¹*localWeight g a b j e.2

def elementaryQuery (equations : S → Equation Name) (g : GridData) (σ η : ℚ) (j : Test)
    (e : Elementary (I := I) equations k m n g) : QueryDemand (A := FamilyAlphabet (Name := Name) (I := I)) :=
  testQuery (sampleFirst equations e.1) (sampleHidden e.1) e.1.2.2 e.2.1 e.2.2.1 e.2.2.2.1
    (rationalScoreTable σ η (fun i => midpoint g.T g.L (e.2.2.2.2 i))) j

lemma elementaryWeight_nonneg (equations : S → Equation Name) (g : GridData)
    (hT : 0<g.T) (hL : 0<g.L) {a b : ℚ} (ha : 0≤a) (ha1 : a≤1) (hb : 0<b)
    (j : Test) (e : Elementary (I := I) equations k m n g) :
    0≤elementaryWeight equations g a b j e :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (localWeight_nonneg g hT hL ha ha1 hb j e.2)

lemma expect_prod_type {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    (𝔼 p, f p)=𝔼 x, 𝔼 y, f (x,y) := by
  simp only [Fintype.expect_eq_sum_div_card,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    Finset.sum_div,div_div]
  rw [mul_comm (Fintype.card X:ℝ)]

lemma outer_weight_sum (equations : S → Equation Name) (F : EdgeStatistic Name I) :
    (∑ o : OuterSample I S k, (Fintype.card (OuterSample I S k):ℝ)⁻¹*
      F (sampleFirst equations o) (sampleHidden o) o.2.2)=edgeMean equations k F := by
  rw [sum_invcard_mul,expect_prod_type]
  simp only [expect_prod_type,edgeMean,sampleHidden]
  rfl

lemma elementary_weighted_sum (equations : S → Equation Name) (g : GridData) (a b σ η : ℚ)
    (j : Test) (f : ProofFamily Name I) :
    (∑ e : Elementary (I := I) equations k m n g,
      (elementaryWeight equations g a b j e:ℝ)*((elementaryQuery equations g σ η j e).failure f.queryAnswer:ℝ))=
    edgeMean equations k (fun U h pos =>
      (match j with
      | .first => finiteFirst (m := m) (n := n) g (f.second (secondQuestion U h pos)) σ η
      | .second => finiteSecond (m := m) (n := n) g (f.second (secondQuestion U h pos)) a σ η
      | .third => finiteThird (m := m) (n := n) g (f.second (secondQuestion U h pos)) σ η
      | .fourth => finiteFourth (m := m) (n := n) g (projection U h pos)
          (f.first U) (f.second (secondQuestion U h pos)) σ η)/(b:ℝ)) := by
  change (∑ e : Sigma _, _) = _
  rw [Fintype.sum_sigma]
  simp only [elementaryWeight,Rat.cast_mul,Rat.cast_inv,Rat.cast_natCast,mul_assoc,← Finset.mul_sum]
  trans ∑ o : OuterSample I S k, (Fintype.card (OuterSample I S k):ℝ)⁻¹*
    ((𝔼 B, 𝔼 C, 𝔼 z, ∑ q : TestCoordinates m n → Fin g.L,
       (gridWeight g q:ℝ)*(noiseWeight a B C j:ℝ)*testFunctional f
        (sampleFirst equations o) (sampleHidden o) o.2.2 B C z
        (rationalScoreTable σ η (fun i => midpoint g.T g.L (q i))) j)/(b:ℝ))
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    congr 1
    rw [localWeight_sum]
    simp only [elementaryQuery]
    simp_rw [testQuery_failure]
  · simp_rw [localTest_mean]
    rw [sum_invcard_mul,expect_prod_type]
    simp only [expect_prod_type,edgeMean,sampleHidden]
    cases j <;> rfl
end MinUncut.Outer

end

end OAI
