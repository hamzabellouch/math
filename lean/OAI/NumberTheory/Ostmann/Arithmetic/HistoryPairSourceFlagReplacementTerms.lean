import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementSelected

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceFlagReplacement
open Construction HistoryPairPattern HistoryPairRows HistoryPairRepresentativeVariables
open HistoryPairKernelReplacement HistoryPairFlags PolynomialFlagReplacementFinite
open HistoryPairRepresentatives
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def scaledActualTerm (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (r : Representative h k)
    (support : (PairKey h k → ℤ) → Bool) (w : (PairKey h k → ℤ) → ℝ)
    (x : PairKey h k → ℤ) : ℝ :=
  if support x then w x*((x (representativeMap h k r)).toNat:ℝ)*
    actualProbability mixed h k hs ks r (x (representativeMap h k r)).toNat x else 0

def scaledSymbolicTerm (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (r : Representative h k)
    (support : (PairKey h k → ℤ) → Bool) (w : (PairKey h k → ℤ) → ℝ)
    (x : PairKey h k → ℤ) : ℝ :=
  if support x then w x*((x (representativeMap h k r)).toNat:ℝ)*
    symbolicKernel mixed h k hs ks r (x (representativeMap h k r)).toNat else 0

def actualFlagTerm (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (r : Representative h k)
    (support : (PairKey h k → ℤ) → Bool) (w : (PairKey h k → ℤ) → ℝ)
    (x : PairKey h k → ℤ) : ℝ :=
  if support x then w x*∑j : Index h k r,
    flagError (polynomial h k hs ks r j) x (x (representativeMap h k r)).toNat else 0

theorem scaled_terms_update_error (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (r : Representative h k)
    (support : (PairKey h k → ℤ) → Bool) (w : (PairKey h k → ℤ) → ℝ)
    (x : PairKey h k → ℤ) (n : ℕ)
    (hw : 0 ≤ w (Function.update x (representativeMap h k r) (n:ℤ)))
    (herr : (n:ℝ)*|actualProbability mixed h k hs ks r n
      (Function.update x (representativeMap h k r) (n:ℤ))-
        symbolicKernel mixed h k hs ks r n| ≤
      4*∑j : Index h k r,flagError (polynomial h k hs ks r j)
        (Function.update x (representativeMap h k r) (n:ℤ)) n) :
    |scaledActualTerm mixed h k hs ks r support w
        (Function.update x (representativeMap h k r) (n:ℤ))-
      scaledSymbolicTerm mixed h k hs ks r support w
        (Function.update x (representativeMap h k r) (n:ℤ))| ≤
      4*actualFlagTerm h k hs ks r support w
        (Function.update x (representativeMap h k r) (n:ℤ)) := by
  simp only [scaledActualTerm,scaledSymbolicTerm,actualFlagTerm,Function.update_self,Int.toNat_natCast]
  split_ifs
  · rw [←mul_sub,abs_mul,abs_mul,abs_of_nonneg hw,abs_of_nonneg (Nat.cast_nonneg n)]
    have hh := mul_le_mul_of_nonneg_left herr hw
    convert hh using 1 <;> ring
  · simp only [sub_self,abs_zero,mul_zero,le_refl]

end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
