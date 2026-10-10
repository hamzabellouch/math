import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers

namespace OAI

/-! Matrix systems in finite factors with minimal projections. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildMinimalFactor
open BoundedHochschild HochschildComparison HochschildMatrixSystems FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (h1 : τ 1=1)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1:M))

include e in
lemma abelian_of_minimal {p : M} (hp : IsStarProjection p)
    (hmin : ∀ q : M, IsStarProjection q → q ≤ p → q=0 ∨ q=p) : AbelianProjection p := by
  refine ⟨hp,fun a b => ?_⟩
  apply HochschildCorners.commute_corner_of_projections e hp
    (b:=p*b*p) _ (HochschildCorners.compress_mem_corner hp a)
  intro q hq hqp
  rcases hmin q hq hqp with hz | he
  · rw [hz]; exact Commute.zero_left _
  · rw [he]
    change p*(p*b*p)=(p*b*p)*p
    rw [(HochschildCorners.compress_mem_corner hp b).1,
      (HochschildCorners.compress_mem_corner hp b).2]

include e hτ h1 htr hfaith hfactor in
lemma copy_into_nonzero {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hmin : ∀ r : M, IsStarProjection r → r ≤ p → r=0 ∨ r=p)
    (hq : IsStarProjection q) (hq0 : q≠0) :
    ∃ v : PartialIso M, v.initial=p ∧ v.final ≤ q := by
  obtain ⟨a,ha⟩ := exists_nonzero_corner e τ (HochschildSakai.mul_hasPreadjoint e)
    hτ htr hfaith h1 hfactor hq hp hq0 hp0
  obtain ⟨v,hv,hvi,hvf⟩ := partialIso_of_nonzero_corner e hq hp (q*a*p) ha
    (by rw [← mul_assoc,← mul_assoc,hq.isIdempotentElem.eq])
    (by rw [mul_assoc,hp.isIdempotentElem.eq])
  refine ⟨v,?_,hvf⟩
  rcases hmin v.initial v.initial_proj hvi with hz | he
  · exact (hv ((CStarRing.star_mul_self_eq_zero_iff (v:M)).mp hz)).elim
  · exact he

structure Packing (p : M) (n : ℕ) where
  v : Fin n → PartialIso M
  initial : ∀ i, (v i).initial=p
  orthogonal : ∀ i j, i≠j → (v i).final*(v j).final=0

namespace Packing
variable {p : M} {n : ℕ} (P : Packing p n)
def total : M := ∑ i, (P.v i).final
omit [PartialOrder M] [StarOrderedRing M] in
lemma total_proj : IsStarProjection P.total := by
  classical
  have he (i j : Fin n) : (P.v i).final*(P.v j).final=
      if i=j then (P.v i).final else 0 := by
    by_cases h : i=j
    · subst j; rw [ite_eq_left rfl]; exact (P.v i).final_proj.isIdempotentElem.eq
    · rw [ite_eq_right h]; exact P.orthogonal i j h
  constructor
  · change (∑ i, (P.v i).final)*(∑ j, (P.v j).final)=∑ i, (P.v i).final
    rw [Finset.sum_mul_sum]
    simp only [he,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  · change star (∑ i, (P.v i).final)=∑ i, (P.v i).final
    simp only [star_sum,(P.v _).final_proj.isSelfAdjoint.star_eq]

lemma final_le_total (i : Fin n) : (P.v i).final ≤ P.total := by
  exact Finset.single_le_sum (fun j _ => (P.v j).final_proj.nonneg) (Finset.mem_univ i)
omit [StarOrderedRing M] in
include htr in
lemma total_trace : (τ P.total).re=(n:ℝ)*(τ p).re := by
  have he (i : Fin n) : τ (P.v i).final=τ p := by
    rw [PartialIso.final,htr,← PartialIso.initial,P.initial]
  simp [total,map_sum,he]

include e hτ h1 htr hfaith hfactor in
lemma extend (hp : IsStarProjection p) (hp0 : p≠0)
    (hmin : ∀ r : M, IsStarProjection r → r ≤ p → r=0 ∨ r=p)
    (hne : P.total≠1) : Nonempty (Packing p (n+1)) := by
  have hq0 : 1-P.total≠0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨w,hwi,hwf⟩ := copy_into_nonzero e τ hτ h1 htr hfaith hfactor hp hp0 hmin
    P.total_proj.one_sub hq0
  have hfw (i : Fin n) : (P.v i).final*w.final=0 := by
    have htw : P.total*w.final=0 := by
      have h := (w.final_proj.le_iff_mul_eq_right P.total_proj.one_sub).mp hwf
      rw [sub_mul,one_mul] at h
      exact sub_eq_self.mp h
    calc
      (P.v i).final*w.final=((P.v i).final*P.total)*w.final := by
        rw [((P.v i).final_proj.le_iff_mul_eq_left P.total_proj).mp (P.final_le_total i)]
      _ = 0 := by rw [mul_assoc,htw,mul_zero]
  refine ⟨⟨Fin.cases w P.v,?_,?_⟩⟩
  · intro i
    exact Fin.cases hwi P.initial i
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hj; exact (hj rfl).elim
      · intro _; exact PartialIso.orthogonal_final_symm (hfw j)
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _; exact hfw i
      · intro hij; exact P.orthogonal i j (fun he => hij (congrArg Fin.succ he))
end Packing

include e hτ h1 htr hfaith hfactor in
lemma exists_full_packing {p : M} (hp : IsStarProjection p) (hp0 : p≠0)
    (hmin : ∀ r : M, IsStarProjection r → r ≤ p → r=0 ∨ r=p) :
    ∃ (n : ℕ) (P : Packing p n), 0<n ∧ P.total=1 := by
  classical
  have ht0 : 0<(τ p).re := by
    have hn := Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)
    refine lt_of_le_of_ne hn.1 ?_
    intro hz
    have hz' : τ p=0 := Complex.ext hz.symm hn.2.symm
    exact hp0 (hfaith p (by simpa only [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using hz'))
  by_contra hfull
  have hnot (n : ℕ) (P : Packing p n) : P.total≠1 := by
    intro he
    have hn : 0<n := by
      by_contra hn
      have hn0 : n=0 := Nat.eq_zero_of_not_pos hn
      subst n
      have hz : (0:M)=1 := by simpa [Packing.total] using he
      have h01 : (0:ℂ)=1 := by simpa only [map_zero,h1] using congrArg τ hz
      exact zero_ne_one h01
    exact hfull ⟨n,P,hn,he⟩
  have hall : ∀ n, Nonempty (Packing p n) := by
    intro n
    induction n with
    | zero => exact ⟨⟨Fin.elim0,by simp,by simp⟩⟩
    | succ n ih =>
      obtain ⟨P⟩ := ih
      exact P.extend e τ hτ h1 htr hfaith hfactor hp hp0 hmin (hnot n P)
  obtain ⟨N,hN⟩ := exists_nat_gt ((τ 1).re/(τ p).re)
  obtain ⟨P⟩ := hall N
  have hle := Complex.re_le_re (τ.monotone P.total_proj.le_one)
  change (τ P.total).re ≤ (τ 1).re at hle
  rw [P.total_trace τ htr] at hle
  have hlt : (τ 1).re < (N:ℝ)*(τ p).re := (div_lt_iff₀ ht0).mp hN
  exact (not_lt_of_ge hle) hlt

omit [PartialOrder M] [StarOrderedRing M] in
lemma abelian_final (v : PartialIso M) (hp : AbelianProjection v.initial) :
    AbelianProjection v.final := by
  refine ⟨v.final_proj,fun a b => ?_⟩
  have hi : v.initial*star (v:M)=star (v:M) := by
    simpa only [star_mul,star_star,v.initial_proj.isSelfAdjoint.star_eq]
      using congrArg star v.mul_initial
  have he (a : M) : v.initial*(star (v:M)*a*v)*v.initial=star (v:M)*a*v := by
    calc
      v.initial*(star (v:M)*a*v)*v.initial=
          (v.initial*star (v:M))*a*((v:M)*v.initial) := by simp only [mul_assoc]
      _ = star (v:M)*a*v := by rw [hi,v.mul_initial]
  have h := (hp.2 (star (v:M)*a*v) (star (v:M)*b*v)).eq
  rw [he,he] at h
  have hprod (a b : M) :
      (v.final*a*v.final)*(v.final*b*v.final)=
        (v:M)*((star (v:M)*a*v)*(star (v:M)*b*v))*star (v:M) := by
    calc
      (v.final*a*v.final)*(v.final*b*v.final)=
          v.final*a*(v.final*v.final)*b*v.final := by noncomm_ring
      _ = v.final*a*v.final*b*v.final := by rw [v.final_proj.isIdempotentElem.eq]
      _ = _ := by simp only [PartialIso.final,mul_assoc]
  change (v.final*a*v.final)*(v.final*b*v.final)=(v.final*b*v.final)*(v.final*a*v.final)
  rw [hprod,hprod,h]

namespace Packing
variable {p : M} {n : ℕ} (P : Packing p n)
def matrixSystem (hfull : P.total=1) : MatrixSystem M n where
  entry i j := (P.v i:M)*star (P.v j:M)
  star_entry i j := by simp only [star_mul,star_star]
  entry_mul i j k l := by
    by_cases h : j=k
    · subst k
      rw [ite_eq_left rfl]
      have he : (P.v i:M)*(P.v j).initial=(P.v i:M) := by
        rw [(P.initial j).trans (P.initial i).symm,(P.v i).mul_initial]
      calc
        ((P.v i:M)*star (P.v j:M))*((P.v j:M)*star (P.v l:M)) =
            ((P.v i:M)*(P.v j).initial)*star (P.v l:M) := by simp only [PartialIso.initial,mul_assoc]
        _ = _ := by rw [he]
    · rw [ite_eq_right h]
      have hcross := PartialIso.star_mul_eq_zero_of_final_orthogonal (P.orthogonal j k h)
      calc
        ((P.v i:M)*star (P.v j:M))*((P.v k:M)*star (P.v l:M)) =
            (P.v i:M)*(star (P.v j:M)*(P.v k:M))*star (P.v l:M) := by simp only [mul_assoc]
        _ = 0 := by rw [hcross,mul_zero,zero_mul]
  sum_diagonal := hfull
omit [PartialOrder M] [StarOrderedRing M] in
lemma matrix_abelian_diagonal (hfull : P.total=1) (hp : AbelianProjection p) (i : Fin n) :
    AbelianProjection ((P.matrixSystem hfull).entry i i) := by
  apply abelian_final (P.v i)
  simpa only [P.initial i] using hp
end Packing

include e hτ h1 htr hfaith hfactor in

theorem exists_abelian_matrix_system (hnd : ¬HochschildDiffuse.NoMinimalProjections M) :
    ∃ (n : ℕ) (E : MatrixSystem M n) (i : Fin n), AbelianProjection (E.entry i i) := by
  classical
  rw [HochschildDiffuse.NoMinimalProjections] at hnd
  push Not at hnd
  obtain ⟨p,hp,hp0,hm⟩ := hnd
  have hmin (q : M) (hq : IsStarProjection q) (hqp : q ≤ p) : q=0 ∨ q=p := by
    by_cases hq0 : q=0
    · exact Or.inl hq0
    · exact Or.inr (hm q hq hqp hq0)
  obtain ⟨n,P,hn,hfull⟩ := exists_full_packing e τ hτ h1 htr hfaith hfactor hp hp0 hmin
  exact ⟨n,P.matrixSystem hfull,⟨0,hn⟩,
    P.matrix_abelian_diagonal hfull (abelian_of_minimal e hp hmin) _⟩

end HochschildMinimalFactor

end

end OAI
