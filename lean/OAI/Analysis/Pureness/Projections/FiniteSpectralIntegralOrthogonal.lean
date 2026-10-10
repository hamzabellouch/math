import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralPolar
import OAI.Analysis.Pureness.Cuntz.FiniteCuntzSums

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set
open scoped ENNReal NNReal CStarAlgebra
variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma positive_mul_power_zero (a b : Positive D) (hab : a.1*b.1 = 0)
    (r : ℝ≥0) (hr : 0 < r) : a.1 * (Positive.power r b).1 = 0 := by
  have hf : Continuous (fun t : ℝ => t^(r : ℝ)) := continuous_id.rpow_const (fun _ => Or.inr r.2)
  have hz : (0 : ℝ)^(r : ℝ) = 0 := Real.zero_rpow (by exact_mod_cast hr.ne')
  have h := cfc_intertwine b Positive.zero a.1 (by simpa [Positive.zero] using hab)
    (fun t : ℝ => t^(r : ℝ)) hf hz
  change a.1 * b.1 ^ r = 0
  rw [CFC.nnrpow_eq_cfcₙ_real b.1 r b.2]
  simpa [Positive.zero] using h

lemma positive_sqrt_mul_zero (a b : Positive D) (hab : a.1*b.1 = 0) :
    CFC.sqrt a.1 * CFC.sqrt b.1 = 0 := by
  have h := positive_mul_power_zero a b hab (1/2) (by norm_num)
  have hs : (Positive.power (1/2) b).1*a.1 = 0 := by
    simpa only [star_mul,a.2.star_eq,(Positive.power (1/2) b).2.star_eq,star_zero] using congrArg star h
  have ht := positive_mul_power_zero (Positive.power (1/2) b) a hs (1/2) (by norm_num)
  have hu := congrArg star ht
  have hv : (Positive.power (1/2) a).1 * (Positive.power (1/2) b).1 = 0 := by
    simpa only [star_mul,(Positive.power (1/2) a).2.star_eq,
      (Positive.power (1/2) b).2.star_eq,star_zero] using hu
  simpa only [Positive.power,CFC.nnrpow_eq_pow,← CFC.sqrt_eq_nnrpow] using hv

lemma positive_orthogonal_square_roots (a b : Positive D) (hab : a.1 * b.1 = 0) :
    ∃ u v : D, star u = u ∧ star v = v ∧ u * u = a.1 ∧ v * v = b.1 ∧ u * v = 0 :=
  ⟨CFC.sqrt a.1, CFC.sqrt b.1, (CFC.sqrt_nonneg a.1).star_eq,
    (CFC.sqrt_nonneg b.1).star_eq, CFC.sqrt_mul_sqrt_self a.1 a.2,
    CFC.sqrt_mul_sqrt_self b.1 b.2, positive_sqrt_mul_zero a b hab⟩

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def finiteOrthogonalColumn (n : ℕ) (M N : FinMatrix A n) :
    CStarMatrix (Fin n × Fin 2) (Fin n × Fin 2) A :=
  fun i j => if j.2 = 0 then if i.2 = 0 then M i.1 j.1 else N i.1 j.1 else 0

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteOrthogonalColumn_starMul (n : ℕ) (M N : FinMatrix A n) :
    star (finiteOrthogonalColumn n M N)*finiteOrthogonalColumn n M N =
      matrixInterleaveRaw n (star M*M+star N*N,0) := by
  apply CStarMatrix.ext
  rintro ⟨i,r⟩ ⟨j,s⟩
  fin_cases r <;> fin_cases s <;>
    simp [finiteOrthogonalColumn,matrixInterleaveRaw_entry',CStarMatrix.mul_apply,CStarMatrix.star_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two,CStarMatrix.add_apply,Finset.sum_add_distrib,apply_ite star]

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteOrthogonalColumn_mulStar (n : ℕ) (M N : FinMatrix A n)
    (hMN : M*star N = 0) (hNM : N*star M = 0) :
    finiteOrthogonalColumn n M N*star (finiteOrthogonalColumn n M N) =
      matrixInterleaveRaw n (M*star M,N*star N) := by
  apply CStarMatrix.ext
  rintro ⟨i,r⟩ ⟨j,s⟩
  have h1 := congrArg (fun P : FinMatrix A n => P i j) hMN
  have h2 := congrArg (fun P : FinMatrix A n => P i j) hNM
  fin_cases r <;> fin_cases s <;>
    simp_all [finiteOrthogonalColumn,matrixInterleaveRaw_entry',CStarMatrix.mul_apply,CStarMatrix.star_apply,
      Fintype.sum_prod_type,apply_ite star]

theorem finiteSpectralIntegral_add_orthogonal
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M N : Positive (FinMatrix A n)) (hMN : M.1*N.1 = 0) :
    finiteSpectralIntegral d n (Positive.add M N) =
      finiteSpectralIntegral d n M + finiteSpectralIntegral d n N := by
  obtain ⟨u, v, hu, hv, huu, hvv, hcross⟩ := positive_orthogonal_square_roots M N hMN
  let e := CStarMatrix.reindexₐ ℂ A (finProdFinEquiv : (Fin n × Fin 2) ≃ Fin (n*2))
  let y := e (finiteOrthogonalColumn n (u) (v))
  have hcross' : v * u = 0 := by
    simpa only [star_mul,hu,hv,star_zero] using congrArg star hcross
  have hl : Positive.starMul y = Positive.map (matrixInterleave n) (positiveProduct (Positive.add M N) Positive.zero) := by
    apply Subtype.ext
    change star (e (finiteOrthogonalColumn n (u) (v))) *
      e (finiteOrthogonalColumn n (u) (v)) =
      e (matrixInterleaveRaw n (M.1+N.1,0))
    rw [← map_star,← map_mul,finiteOrthogonalColumn_starMul,
      hu,hv,
      huu,hvv]
  have hr : Positive.mulStar y = Positive.map (matrixInterleave n) (positiveProduct M N) := by
    apply Subtype.ext
    change e (finiteOrthogonalColumn n (u) (v)) *
      star (e (finiteOrthogonalColumn n (u) (v))) =
      e (matrixInterleaveRaw n (M.1,N.1))
    rw [← map_star,← map_mul,finiteOrthogonalColumn_mulStar n _ _
      (by simpa only [hv] using hcross)
      (by simpa only [hu] using hcross'),
      hu,hv,
      huu,hvv]
  have h := finiteSpectralIntegral_polar d (n*2) y
  rw [hl,hr,finiteSpectralIntegral_block_add d hd,finiteSpectralIntegral_block_add d hd,
    finiteSpectralIntegral_zero,add_zero] at h
  exact h
end CuntzPureness

end

end OAI
