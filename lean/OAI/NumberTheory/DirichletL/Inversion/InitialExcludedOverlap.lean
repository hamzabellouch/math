import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPool

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedOverlap
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open HeckeFamily InverseInitialExcludedPolynomial
local notation "O"=>ActualEisensteinCubic.O

theorem reconstruct_outside (E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)(hc:outside E c)
    (hres:residual P j∣c):outside E (reconstruct P j c) := by
  intro Q hQ hQn
  rcases (hE Q hQ).dvd_mul.mp hQn with hQj|hQc
  · exact hP Q hQ (hQj.trans hj)
  · exact hc Q hQ (hQc.trans (idealQuotient_dvd hres))

theorem columns_filter (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P):
    columns (originalOutside A E) P j=(columns A P j).filter (outside E) := by
  ext c
  constructor
  · intro hc
    have hd:=(mem_columns hPs hj).mp hc
    apply Finset.mem_filter.mpr
    refine ⟨(mem_columns hPs hj).mpr ⟨hd.1,hd.2.1,hd.2.2.1,?_⟩,?_⟩
    · exact (Finset.mem_filter.mp hd.2.2.2).1
    · exact column_outside _ E hE hj hP (fun n hn=>(Finset.mem_filter.mp hn).2) hc
  · intro hc
    obtain ⟨hcA,hout⟩:=Finset.mem_filter.mp hc
    obtain ⟨hcs,hcj,hres,hnA⟩:=(mem_columns hPs hj).mp hcA
    exact (mem_columns hPs hj).mpr ⟨hcs,hcj,hres,
      Finset.mem_filter.mpr ⟨hnA,reconstruct_outside E hE hj hP hout hres⟩⟩

theorem deleted_zero_outside (χ:Character)(E:Finset (Ideal O))
    (hE:∀Q∈E,Prime Q)(I:Ideal O)(hn:¬outside E I):
    idealCoeff (χ.excludePrimes E hE) I=0 := by
  rw [idealCoeff_excludePrimes]
  apply ite_eq_right
  intro hc
  apply hn
  intro Q hQ hd
  have hu:IsUnit Q:=(hc Q hQ).isRelPrime hd (dvd_refl Q)
  exact (hE Q hQ).not_isUnit hu

theorem residual_filtered (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j η a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j η a W Z r z G u := by
  unfold residualNormalizedPolynomial
  rw [columns_filter A E hE hPs hj hP,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hout:outside E c
  · rw [ite_eq_left hout]
  · rw [ite_eq_right hout]
    simp only [overlapResidualCoefficient,hη c hout,mul_zero,zero_mul]

theorem residual_deleted_filtered (χ:Character)(A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j (idealCoeff (χ.excludePrimes E hE)).toMonoidHom a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j
      (idealCoeff (χ.excludePrimes E hE)).toMonoidHom a W Z r z G u :=
  residual_filtered A E hE hPs hj hP _ (deleted_zero_outside χ E hE) a W Z r z G u

end SevenEighths.InverseInitialExcludedOverlap

end

end OAI
