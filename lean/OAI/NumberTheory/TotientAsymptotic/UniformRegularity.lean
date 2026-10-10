import OAI.NumberTheory.TotientAsymptotic.RegularValueCount
import OAI.NumberTheory.TotientAsymptotic.UniformNonNormalCount

namespace OAI

/-! A uniform regularity error at a freely chosen normality cutoff. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem uniform_regularity_exception : ∃ C D A : ℝ,0 < C ∧ 0 < D ∧ 0 < A ∧
    ∀ S X J : ℕ,2 < S → 0 ≤ B S → 256 ≤ X → Real.exp (Real.exp 1) ≤ X →
    1 ≤ J → (X:ℝ) ≤ (2:ℝ)^J → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧ ¬CountingRegular S X v) →
    (Q.card:ℝ) ≤ C*X*(Real.log X)^(-5/4:ℝ)+(2*X+D*X*B X)/(S+1:ℕ)+
      A*dyadicTotientEnvelope J*X/Real.log X*(B (2*X))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,D,hC,hD,hreg⟩ := regular_value_exception_count
  obtain ⟨A,hA,hnorm⟩ := uniform_non_normal_value_count
  refine ⟨C,D,A,hC,hD,hA,?_⟩
  intro S X J hS hBS hX hx hJ hxJ Q hQ
  have hh := hreg S X (by omega) hx Q hQ
  have hn := hnorm S X J (by exact_mod_cast hS) hBS (by exact_mod_cast hX) hJ hxJ
    (nonNormalValues S X) (by
      intro v hv
      obtain ⟨hv,n,p,hn,hφ,hp,hpn,hbad⟩ := Finset.mem_filter.mp hv
      have hval := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2
      refine ⟨n,p,hn,hφ,hp,hpn,?_,hbad⟩
      exact (Nat.cast_le.mpr hval).trans (Nat.floor_le (Nat.cast_nonneg X)))
  exact hh.trans (add_le_add le_rfl hn)

end TotientAsymptotic

end

end OAI
