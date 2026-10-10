import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.RationalCounts
import OAI.Combinatorics.MatchingCount.Algorithm.SortedList
import OAI.Combinatorics.MatchingCount.Machines.TreeSlotWeight
import OAI.Combinatorics.MatchingCount.Arithmetic.OnlineFractionParam

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

abbrev SigmaInput := (ℕ×ℕ)×Fraction

def sigma (x : SigmaInput) : Fraction :=
  TreeFraction.minimum
    (TreeFraction.div ((1,100000),(100*x.1.1,1)),TreeFraction.div (x.2,(1000*x.1.2,1)))
def sigmaRealizer : Realizer sigma :=
  (composition (pair
    (composition (pair (constant (1,100000)) (pair ((constant 100).mulNat first.fst) (constant 1))) divRealizer)
    (composition (pair second (pair ((constant 1000).mulNat first.snd) (constant 1))) divRealizer)) minimumRealizer).congr (fun _=>rfl)
lemma polynomial_sigma : PolynomialTime sigmaRealizer := by
  unfold sigmaRealizer Realizer.fst Realizer.snd; apply polynomial_congr
  have := polynomial_div
  have := TreeFraction.polynomial_minimum
  simp only [Realizer.mulNat]
  tree_cost
lemma sigma_repr (D K : ℕ) (e : ℚ) (he : 0≤e) :
    sigma ((D,K),TreeFraction.repr e)=TreeFraction.repr (Counting.sigma D K e) := by
  unfold sigma
  rw [←repr_nat (100*D),←repr_nat (1000*K),
    show ((1,100000) : Fraction)=TreeFraction.repr ((1:ℚ)/100000) from by norm_num [TreeFraction.repr],
    div_repr (by positivity) (by positivity), div_repr he (by positivity),
    minimum_repr (by positivity) (by positivity)]
  congr 1
  simp only [Counting.sigma,Counting.alpha,Nat.cast_mul,Nat.cast_ofNat]

abbrev SampleCountInput := ℕ×SigmaInput

def invSigma (x : SampleCountInput) : Fraction := inverse (sigma x.2)
def reciprocalSigma : Realizer invSigma :=
  composition (f:=sigma ∘ Prod.snd) (g:=inverse)
    (composition (f:=Prod.snd) (g:=sigma) second sigmaRealizer) inverseRealizer
lemma polynomial_reciprocalSigma : PolynomialTime reciprocalSigma := by
  unfold reciprocalSigma
  exact polynomial_composition (polynomial_composition polynomial_second polynomial_sigma) polynomial_inverse

def fracProduct {A : Type} [Codec A] {f g : A→Fraction} (F : Realizer f) (G : Realizer g) :
    Realizer (fun x=>TreeFraction.mul (f x,g x)) := composition (f:=fun x=>(f x,g x)) (g:=TreeFraction.mul) (pair F G) mulRealizer
lemma polynomial_fracProduct {A : Type} [Codec A] {f g : A→Fraction} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (fracProduct F G) :=
  polynomial_composition (polynomial_pair hF hG) polynomial_mul

def sampleFactorFn (x : SampleCountInput) : Fraction := TreeFraction.mul ((10,1),TreeFraction.mul (invSigma x,invSigma x))
def sampleFactor : Realizer sampleFactorFn := fracProduct (constant (10,1)) (fracProduct reciprocalSigma reciprocalSigma)
lemma polynomial_sampleFactor : PolynomialTime sampleFactor :=
  polynomial_fracProduct (polynomial_constant _) (polynomial_fracProduct polynomial_reciprocalSigma polynomial_reciprocalSigma)

def sampleSumFn (x : SampleCountInput) : Fraction := (x.1+x.2.1.2+1,1)
def sampleSum : Realizer sampleSumFn :=
  pair ((first.addNat second.fst.snd).addNat (constant 1)) (constant 1)
lemma polynomial_sampleSum : PolynomialTime sampleSum := by
  exact polynomial_pair (polynomial_addNat (polynomial_addNat polynomial_first
    (polynomial_snd (polynomial_fst polynomial_second))) (polynomial_constant 1)) (polynomial_constant 1)

def sampleProduct (x : SampleCountInput) : Fraction := TreeFraction.mul (sampleFactorFn x,sampleSumFn x)
def sampleProductRealizer : Realizer sampleProduct := fracProduct sampleFactor sampleSum
lemma polynomial_sampleProduct : PolynomialTime sampleProductRealizer :=
  polynomial_fracProduct polynomial_sampleFactor polynomial_sampleSum

def sampleCount (x : SampleCountInput) : ℕ := natCeil (sampleProduct x)
def sampleCountRealizer : Realizer sampleCount :=
  composition (f:=sampleProduct) (g:=natCeil) sampleProductRealizer natCeilRealizer
lemma polynomial_sampleCount : PolynomialTime sampleCountRealizer :=
  polynomial_composition polynomial_sampleProduct polynomial_natCeil
lemma sampleCount_repr (n D K : ℕ) (e : ℚ) (he : 0≤e) :
    sampleCount (n,((D,K),TreeFraction.repr e))=
      ⌈10*(Counting.sigma D K e)⁻¹^2*((n:ℚ)+K+1)⌉₊ := by
  have hs := Counting.sigma_nonneg D K e he
  unfold sampleCount sampleProduct sampleFactorFn sampleSumFn invSigma
  rw [sigma_repr D K e he,inverse_repr _ (Counting.sigma_nonneg D K e he),
    show ((10,1) : Fraction)=TreeFraction.repr (10:ℚ) from rfl,
    ←repr_nat (n+K+1),mul_repr (by positivity) (by positivity),
    mul_repr (by positivity) (by positivity),mul_repr (by positivity) (by positivity),
    natCeil_repr _ (by positivity)]
  congr 1
  simp only [Nat.cast_add,Nat.cast_one,pow_two]

variable {G : GraphInput} [Nontrivial (Fin G.n)]
omit [Nontrivial (Fin G.n)] in
lemma sampleCount_source (p : Trial.Parameters G) :
    sampleCount (G.n,((FiniteTrial.sourceD (G:=G) p.K,p.K),TreeFraction.repr p.epsilon))=p.S := by
  rw [sampleCount_repr _ _ _ _ p.epsilon_pos.le]
  exact FiniteTrial.sampleCount_eq p

def repetitions (x : Fraction) : ℕ := 10*(Nat.clog 2 (natCeil (inverse x))+1)+1
def repetitionsRealizer : Realizer repetitions :=
  (((constant 10).mulNat ((composition (composition inverseRealizer natCeilRealizer) clogTwo).addNat (constant 1))).addNat (constant 1)).congr (fun _=>rfl)
lemma polynomial_repetitions : PolynomialTime repetitionsRealizer := by
  unfold repetitionsRealizer;apply polynomial_congr
  have := polynomial_clogTwo
  have := polynomial_natCeil
  have := polynomial_inverse
  simp only [Realizer.addNat,Realizer.mulNat]
  tree_cost
lemma repetitions_repr (d : ℚ) (hd : 0≤d) :
    repetitions (TreeFraction.repr d)=2*Amplification.halfRepetitions d+1 := by
  unfold repetitions
  rw [inverse_repr d hd,natCeil_repr _ (by positivity)]
  unfold Amplification.halfRepetitions
  omega
end MatchingFPRAS.OnlineSchedule

end OAI
