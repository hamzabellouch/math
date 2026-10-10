import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.CornerComparison

namespace OAI

/-! Matrices for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaCorners
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma orthogonal_of_le_complement {p q r : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hr : IsStarProjection r) (hqp : q ≤ p)
    (hrpq : r ≤ p-q) : q*r=0 := by
  have hpq : IsStarProjection (p-q) := (hq.le_iff_sub hp).mp hqp
  have hpr : (p-q)*r=r := (hr.le_iff_mul_eq_right hpq).mp hrpq
  calc
    q*r = q*((p-q)*r) := congrArg (fun x => q*x) hpr.symm
    _ = 0 := by rw [← mul_assoc,mul_sub,(hq.le_iff_mul_eq_left hp).mp hqp,
      hq.isIdempotentElem.eq,sub_self,zero_mul]

section Dual
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in

theorem equal_partition (hdiff : NoMinimalProjections M) (n : ℕ)
    {p : M} (hp : IsStarProjection p) (t : ℝ) (ht : 0 ≤ t)
    (hnt : (n : ℝ)*t=(τ p).re) :
    ∃ q : Fin n → M, (∀ i, IsStarProjection (q i)) ∧
      (∀ i, q i ≤ p) ∧ (∀ i, (τ (q i)).re=t) ∧
      (∀ i j, i ≠ j → q i*q j=0) ∧ ∑ i, q i=p := by
  induction n generalizing p with
  | zero =>
    have hp0 : p=0 := by
      by_contra hn
      have hpos := projection_trace_pos τ hfaith hp hn
      simp only [Nat.cast_zero,zero_mul] at hnt
      linarith
    refine ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i,
      fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_⟩
    simp [hp0]
  | succ n ih =>
    have htp : t ≤ (τ p).re := by
      rw [← hnt,Nat.cast_succ,add_mul,one_mul]
      exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg n) ht)
    obtain ⟨a,ha,hap,hat⟩ := exists_projection_of_trace τ e
      (HochschildSakai.abstract_multiplication_normal e).1 hτ htr hfaith hdiff hp t ht htp
    have hpa : IsStarProjection (p-a) := (ha.le_iff_sub hp).mp hap
    have hrem : (n : ℝ)*t=(τ (p-a)).re := by
      rw [map_sub,Complex.sub_re,hat,← hnt,Nat.cast_succ]
      ring
    obtain ⟨q,hq,hqp,hqt,hqo,hqs⟩ := ih hpa hrem
    refine ⟨Fin.cons a q,?_,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ha
      · exact hq j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hap
      · exact (hqp j).trans (sub_le_self _ ha.nonneg)
    · intro i
      exact Fin.cases hat hqt i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i <;> intro j <;>
        refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
      · exact False.elim (hij rfl)
      · exact orthogonal_of_le_complement hp ha (hq j) hap (hqp j)
      · have he := congrArg star (orthogonal_of_le_complement hp ha (hq i) hap (hqp i))
        simpa only [Fin.cons_succ,Fin.cons_zero,star_mul,ha.isSelfAdjoint.star_eq,
          (hq i).isSelfAdjoint.star_eq,star_zero] using he
      · exact hqo i j (fun h => hij (congrArg Fin.succ h))
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,hqs]
      abel

structure System (n : ℕ) (p : M) where
  entry : Fin n → Fin n → M
  star_entry : ∀ i j, star (entry i j)=entry j i
  mul_entry : ∀ i j k l, entry i j*entry k l=if j=k then entry i l else 0
  sum_diag : ∑ i, entry i i=p

include e hτ htr hfaith in

theorem exists_system (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))
    (hdiff : NoMinimalProjections M) (n : ℕ) (hn : 0 < n)
    {p : M} (hp : IsStarProjection p) :
    ∃ s : System n p, ∀ i, (τ (s.entry i i)).re=(τ p).re/n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hpn : 0 ≤ (τ p).re := (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1
  obtain ⟨q,hq,hqp,hqt,hqo,hqs⟩ := equal_partition e τ hτ htr hfaith hdiff n hp
    ((τ p).re/n) (div_nonneg hpn (Nat.cast_nonneg n)) (by field_simp)
  let i0 : Fin n := ⟨0,hn⟩
  have hex (i : Fin n) : ∃ v : M, star v*v=q i0 ∧ v*star v=q i ∧
      v*q i0=v ∧ q i*v=v := CornerIso.equivalent_of_trace_eq e τ hτ htr hfaith
        h1 hfactor (hq i0) (hq i) (by rw [hqt,hqt])
  choose v hvi hvf hvr hlv using hex
  have hov (i j : Fin n) (hij : i ≠ j) : star (v i)*v j=0 := by
    have hstar : star (v i)*q i=star (v i) := by
      simpa only [star_mul,(hq i).isSelfAdjoint.star_eq] using congrArg star (hlv i)
    calc
      star (v i)*v j=star (v i)*(q i*(q j*v j)) := by rw [hlv,← mul_assoc,hstar]
      _ = 0 := by rw [← mul_assoc (q i),hqo i j hij,zero_mul,mul_zero]
  let s : System n p := {
    entry := fun i j => v i*star (v j)
    star_entry := fun i j => by simp only [star_mul,star_star]
    mul_entry := fun i j k l => by
      by_cases h : j=k
      · subst k
        rw [ite_eq_left rfl]
        calc
          (v i*star (v j))*(v j*star (v l)) = (v i*(star (v j)*v j))*star (v l) := by
            simp only [mul_assoc]
          _ = v i*star (v l) := by rw [hvi,hvr]
      · simp only [ite_eq_right h]
        calc
          (v i*star (v j))*(v k*star (v l)) = (v i*(star (v j)*v k))*star (v l) := by
            simp only [mul_assoc]
          _ = 0 := by rw [hov j k h,mul_zero,zero_mul]
    sum_diag := by simpa only [hvf] using hqs }
  exact ⟨s,fun i => by change (τ (v i*star (v i))).re=_; rw [hvf,hqt]⟩

end Dual
end PopaMatrices

end

end OAI
