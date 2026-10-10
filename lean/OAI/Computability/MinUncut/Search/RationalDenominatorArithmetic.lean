import Mathlib
import OAI.Computability.MinUncut.Estimates.WeightedTestLaw
import OAI.Computability.MinUncut.Machines.FiniteAlphabetBounds

namespace OAI

section
open scoped BigOperators
namespace MinUncut.RationalDenominator
lemma mul_dvd {a b : ℚ} {A B : ℕ} (ha : a.den∣A) (hb : b.den∣B) : (a*b).den∣A*B :=
  (Rat.mul_den_dvd a b).trans (Nat.mul_dvd_mul ha hb)

lemma add_dvd {a b : ℚ} {D : ℕ} (ha : a.den∣D) (hb : b.den∣D) : (a+b).den∣D :=
  (Rat.add_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)

lemma sub_dvd {a b : ℚ} {D : ℕ} (ha : a.den∣D) (hb : b.den∣D) : (a-b).den∣D :=
  (Rat.sub_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)

lemma prod_dvd {X : Type*} (s : Finset X) (f : X → ℚ) (D : X → ℕ)
    (h : ∀ x∈s, (f x).den∣D x) : (∏ x∈s, f x).den∣∏ x∈s, D x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx,Finset.prod_insert hx]
    exact mul_dvd (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

lemma inv_nat {N : ℕ} (hN : 0<N) : ((N:ℚ)⁻¹).den=N := Rat.inv_natCast_den_of_pos hN

lemma mul_nat_dvd (a : ℚ) (N : ℕ) : (a*N).den∣a.den := by
  simpa only [Rat.den_natCast,mul_one] using Rat.mul_den_dvd a (N:ℚ)

lemma denominatorProduct_pos {X : Type*} [Fintype X] (f : X → ℚ) : 0<∏ x, (f x).den :=
  Finset.prod_pos (fun x _ => Rat.den_pos (f x))

lemma denominator_dvd_product {X : Type*} [Fintype X] (f : X → ℚ) (x : X) :
    (f x).den∣∏ x, (f x).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ x)
end MinUncut.RationalDenominator

end
section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof RationalDenominator OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n k : ℕ}

lemma rationalRowDensity_den {W : Type*} [Fintype W] [DecidableEq W] (a : ℚ) (b c : W) :
    (RowNoise.rationalRowDensity a b c).den∣a.den := by
  unfold RowNoise.rationalRowDensity
  apply add_dvd _ (dvd_refl _)
  split_ifs
  · exact (mul_nat_dvd (1-a) _).trans (sub_dvd (by simp) (dvd_refl _))
  · simp

lemma rationalDensity_den {R W : Type*} [Fintype R] [Fintype W] [DecidableEq W]
    (a : ℚ) (B C : R → W) : (RowNoise.rationalDensity a B C).den∣a.den^Fintype.card R := by
  have hh := prod_dvd (Finset.univ : Finset R) (fun r => RowNoise.rationalRowDensity a (B r) (C r))
    (fun _ => a.den) (fun r _ => rationalRowDensity_den a (B r) (C r))
  simpa only [RowNoise.rationalDensity,Finset.prod_const,Finset.card_univ] using hh

lemma noiseWeight_den {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (a : ℚ) (B C : FaceArray A m n) (j : Test) :
    (noiseWeight a B C j).den∣a.den^Fintype.card (Row m n) := by
  cases j with
  | second => exact rationalDensity_den a B C
  | first => exact one_dvd _
  | third => exact one_dvd _
  | fourth => exact one_dvd _

def gridDenominator (m n : ℕ) (g : GridData) : ℕ :=
  ∏ q : TestCoordinates m n → Fin g.L, (gridWeight g q).den

def budgetDenominator (b : Test → ℚ) : ℕ := ∏ j, (b j)⁻¹.den

def innerDenominator (t m n : ℕ) (g : GridData) (a : ℚ) (b : Test → ℚ) : ℕ :=
  (faceCardBound t m n).factorial*(faceCardBound t m n).factorial*
  Fintype.card (Code m n)*gridDenominator m n g*a.den^Fintype.card (Row m n)*budgetDenominator b

def samplerDenominator (I S : Type*) [Fintype I] [Fintype S] (k m n : ℕ)
    (g : GridData) (a : ℚ) (b : Test → ℚ) : ℕ :=
  Fintype.card (OuterSample I S k)*innerDenominator (Fintype.card I) m n g a b

lemma innerDenominator_pos (t m n : ℕ) (g : GridData) (a : ℚ) (b : Test → ℚ) :
    0 < innerDenominator t m n g a b := by
  have hC := Fintype.card_pos (α := Code m n)
  have hg : 0<gridDenominator m n g := denominatorProduct_pos _
  have hb : 0<budgetDenominator b := denominatorProduct_pos _
  unfold innerDenominator
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (Nat.factorial_pos _)
    (Nat.factorial_pos _)) hC) hg) (pow_pos (Rat.den_pos a) _)) hb

lemma localWeight_den (Q : I → SecondQuestion Name) (g : GridData) (a : ℚ) (b : Test → ℚ)
    (j : Test) (p : LocalSample (SecondAlphabet Q) m n g) :
    (localWeight g a (b j) j p).den∣innerDenominator (Fintype.card I) m n g a b := by
  have hf : ((Fintype.card (FaceArray (SecondAlphabet Q) m n):ℚ)⁻¹).den ∣
      (faceCardBound (Fintype.card I) m n).factorial := by
    rw [inv_nat Fintype.card_pos]
    exact Nat.dvd_factorial Fintype.card_pos (faceArray_card_le Q m n)
  unfold localWeight innerDenominator
  rw [div_eq_mul_inv]
  exact mul_dvd (mul_dvd (mul_dvd (mul_dvd (mul_dvd hf hf)
    (by rw [inv_nat Fintype.card_pos])) (denominator_dvd_product _ p.2.2.2))
    (noiseWeight_den a p.1 p.2.1 j)) (denominator_dvd_product _ j)

variable [Nonempty S]
lemma samplerDenominator_pos (hk : k≤Fintype.card I) (g : GridData) (a : ℚ) (b : Test → ℚ) :
    0<samplerDenominator I S k m n g a b := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  exact mul_pos Fintype.card_pos (innerDenominator_pos _ _ _ _ _ _)

lemma elementaryWeight_den (equations : S → Equation Name) (hk : k≤Fintype.card I)
    (g : GridData) (a : ℚ) (b : Test → ℚ) (j : Test) (e : Elementary (I := I) equations k m n g) :
    (elementaryWeight equations g a (b j) j e).den∣samplerDenominator I S k m n g a b := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  exact mul_dvd (by rw [inv_nat Fintype.card_pos]) (localWeight_den _ g a b j e.2)

omit [Nonempty S] in
lemma samplerDenominator_polynomial (g : GridData) (a : ℚ) (b : Test → ℚ) :
    samplerDenominator I S k m n g a b=
      (Fintype.card (FixedSets I k)*3^Fintype.card I*innerDenominator (Fintype.card I) m n g a b)*
        Fintype.card S^Fintype.card I := by
  simp only [samplerDenominator,OuterSample,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  ring
end MinUncut.Outer

end
end

end OAI
