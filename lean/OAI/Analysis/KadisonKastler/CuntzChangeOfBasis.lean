import OAI.Analysis.KadisonKastler.CuntzMatrices
import OAI.Analysis.KadisonKastler.ConjugationFunctionalCalculus

namespace OAI

/-! # Unitary change between two finite Cuntz families -/

namespace KadisonKastler.CuntzFamily

open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

private theorem changeBasis_mul_star (S T : CuntzFamily ι H) :
    (∑ i, S.entry i*star (T.entry i))*star (∑ i, S.entry i*star (T.entry i))=1 := by
  rw [star_sum]
  simp only [star_mul,star_star,Finset.sum_mul,Finset.mul_sum]
  have he (i j : ι) : S.entry i*star (T.entry i)*(T.entry j*star (S.entry j)) =
      S.entry i*(star (T.entry i)*T.entry j)*star (S.entry j) := by simp only [mul_assoc]
  simp only [he,T.orthogonal]
  simpa using S.total

def changeBasis (S T : CuntzFamily ι H) : unitary (H →L[ℂ] H) :=
  ⟨∑ i, S.entry i*star (T.entry i),by
    constructor
    · have h := changeBasis_mul_star T S
      simpa only [star_sum,star_mul,star_star] using h
    · exact changeBasis_mul_star S T⟩

theorem changeBasis_conjugate (S T : CuntzFamily ι H) (a : H →L[ℂ] H)
    (ha : ∀ i, Commute a (T.entry i)) :
    unitaryConj (S.changeBasis T) a = ∑ i, S.entry i*a*star (S.entry i) := by
  change ((∑ i, S.entry i*star (T.entry i))*a)*
    star (∑ i, S.entry i*star (T.entry i)) = _
  rw [star_sum]
  simp only [star_mul,star_star,Finset.sum_mul,Finset.mul_sum]
  have he (i j : ι) : (S.entry i*star (T.entry i)*a)*(T.entry j*star (S.entry j)) =
      S.entry i*(star (T.entry i)*T.entry j)*a*star (S.entry j) := by
    calc
      _ = S.entry i*star (T.entry i)*(a*T.entry j)*star (S.entry j) := by
        simp only [mul_assoc]
      _ = _ := by rw [(ha j).eq]; simp only [mul_assoc]
  simp only [he,T.orthogonal]
  simp

def conjugate (S : CuntzFamily ι H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) : CuntzFamily ι H where
  entry i := conjugationOperator J (S.entry i)
  orthogonal i j := by
    change star (conjugationRealStarAlgEquiv J hJ (S.entry i))*
      conjugationRealStarAlgEquiv J hJ (S.entry j) = _
    rw [← map_star,← map_mul,S.orthogonal]
    split_ifs <;> simp
  total := by
    change (∑ i, conjugationRealStarAlgEquiv J hJ (S.entry i)*
      star (conjugationRealStarAlgEquiv J hJ (S.entry i)))=1
    simp only [← map_star,← map_mul,← map_sum,S.total,map_one]

end

end KadisonKastler.CuntzFamily

end OAI
