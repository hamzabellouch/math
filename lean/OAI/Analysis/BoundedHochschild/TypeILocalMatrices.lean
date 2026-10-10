import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers
import OAI.Analysis.BoundedHochschild.CommutativePrimitives
import OAI.Analysis.BoundedHochschild.AtomicPrimitives

namespace OAI

/-!
# Local matrix packing beneath abelian projections

A packing either extends by an orthogonal equivalent projection or fills a nonzero central
cut. Faithfulness and finiteness of the trace rule out arbitrarily large packings.
-/

noncomputable section

open scoped ComplexOrder
namespace HochschildTypeILocal
open BoundedHochschild HochschildComparison HochschildCentralComparison
  HochschildMinimalFactor FinitePathMain HochschildTypeII
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma abelian_orthogonal_corner {p q : M} (hp : AbelianProjection p)
    (hq : IsStarProjection q) (hqp : q ≤ p) : ∀ a : M, (p-q)*a*q=0 := by
  intro a
  have hpq := (hq.le_iff_mul_eq_right hp.1).mp hqp
  have hqp' := (hq.le_iff_mul_eq_left hp.1).mp hqp
  have he : p*q*p=q := by rw [hpq,hqp']
  have hc := (hp.2 a q).eq
  rw [he] at hc
  have hrq : (p-q)*q=0 := by rw [sub_mul,hpq,hq.isIdempotentElem.eq,sub_self]
  have hrp : (p-q)*p=p-q := by rw [sub_mul,hp.1.isIdempotentElem.eq,hqp']
  calc
    (p-q)*a*q=((p-q)*p)*a*(p*q) := by rw [hrp,hpq]
    _ = (p-q)*(p*a*p)*q := by simp only [mul_assoc]
    _ = (p-q)*(q*(p*a*p)) := by rw [mul_assoc,hc]
    _ = 0 := by rw [← mul_assoc,hrq,zero_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_initial_zero_final (z : M) (hz : ∀ a : M, Commute z a)
    (v : PartialIso M) (hi : z*v.initial=0) : z*v.final=0 := by
  have hv : z*(v:M)=0 := by
    calc
      z*(v:M)=z*((v:M)*v.initial) := by rw [v.mul_initial]
      _ = (v:M)*(z*v.initial) := by rw [← mul_assoc,(hz (v:M)).eq,mul_assoc]
      _ = 0 := by rw [hi,mul_zero]
  change z*((v:M)*star (v:M))=0
  rw [← mul_assoc,hv,zero_mul]

include e hτ htr hfaith in
lemma packing_step {p : M} (hp : AbelianProjection p) {n : ℕ} (P : Packing p n) :
    (∃ z : M, CentralProjection z ∧ z*p≠0 ∧ z*P.total=z) ∨
      Nonempty (Packing p (n+1)) := by
  classical
  let q := 1-P.total
  have hq : IsStarProjection q := P.total_proj.one_sub
  obtain ⟨v,hvi,hvf,hmax⟩ := exists_maximal_partialIso e τ hτ htr hfaith hp.1 hq
  by_cases hi : v.initial=p
  · right
    have hfw (i : Fin n) : (P.v i).final*v.final=0 := by
      have ht : P.total*v.final=0 := by
        have h := (v.final_proj.le_iff_mul_eq_right hq).mp hvf
        change (1-P.total)*v.final=v.final at h
        rw [sub_mul,one_mul] at h
        exact sub_eq_self.mp h
      calc
        (P.v i).final*v.final=((P.v i).final*P.total)*v.final := by
          rw [((P.v i).final_proj.le_iff_mul_eq_left P.total_proj).mp (P.final_le_total i)]
        _ = 0 := by rw [mul_assoc,ht,mul_zero]
    refine ⟨⟨Fin.cases v P.v,?_,?_⟩⟩
    · intro i; exact Fin.cases hi P.initial i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro h; exact (h rfl).elim
        · intro _; exact PartialIso.orthogonal_final_symm (hfw j)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _; exact hfw i
        · intro h; exact P.orthogonal i j (fun he => h (congrArg Fin.succ he))
  · left
    let r := p-v.initial
    have hr : IsStarProjection r := (v.initial_proj.le_iff_sub hp.1).mp hvi
    have hr0 : r≠0 := sub_ne_zero.mpr (Ne.symm hi)
    obtain ⟨z,hz,hrz,hzvi⟩ := central_separator e τ hτ htr hfaith hr v.initial_proj
      (abelian_orthogonal_corner hp v.initial_proj hvi)
    have hq' := (v.final_proj.le_iff_sub hq).mp hvf
    have horth : ∀ a : M, r*a*(q-v.final)=0 := by
      intro a
      have hh := congrArg star (hmax (star a))
      have hrr : star (p-v.initial)=p-v.initial := hr.isSelfAdjoint.star_eq
      simpa only [star_mul,star_star,hrr,
        hq'.isSelfAdjoint.star_eq,star_zero,mul_assoc] using hh
    obtain ⟨t,ht,hrt,htq⟩ := central_separator e τ hτ htr hfaith hr hq' horth
    let w := z*t
    have hw : CentralProjection w := ⟨hz.1.mul ht.1 (hz.2 t),fun a => (hz.2 a).mul_left (ht.2 a)⟩
    have hwr : w*r=r := by
      dsimp [w]
      rw [mul_assoc,(hr.le_iff_mul_eq_right ht.1).mp hrt,
        (hr.le_iff_mul_eq_right hz.1).mp hrz]
    have hwi : w*v.initial=0 := by
      dsimp [w]
      rw [(hz.2 t).eq,mul_assoc,hzvi,mul_zero]
    have hwp : w*p=r := by
      have hh := hwr
      change w*(p-v.initial)=r at hh
      simpa only [mul_sub,hwi,sub_zero] using hh
    have hwq : w*q=0 := by
      have hfinal : w*v.final=0 := central_initial_zero_final w hw.2 v hwi
      have h := congrArg (fun a : M => z*a) htq
      change z*(t*(q-v.final))=z*0 at h
      rw [← mul_assoc,mul_sub,hfinal,mul_zero,sub_zero] at h
      exact h
    refine ⟨w,hw,by rwa [hwp],?_⟩
    change w*(1-P.total)=0 at hwq
    rw [mul_sub,mul_one,sub_eq_zero] at hwq
    exact hwq.symm

include e hτ htr hfaith in

theorem exists_local_full_packing {p : M} (hp : AbelianProjection p) (hp0 : p≠0) :
    ∃ (n : ℕ) (P : Packing p n) (z : M), 0<n ∧ CentralProjection z ∧ z*p≠0 ∧ z*P.total=z := by
  classical
  by_contra hn
  have hnot (n : ℕ) (P : Packing p n) :
      ¬∃ z : M, CentralProjection z ∧ z*p≠0 ∧ z*P.total=z := by
    rintro ⟨z,hz,hzp,hfull⟩
    have hn0 : 0<n := by
      by_contra hh
      have hnz : n=0 := Nat.eq_zero_of_not_pos hh
      subst n
      have hz0 : z=0 := by simpa only [Packing.total,Fin.sum_univ_zero,mul_zero] using hfull.symm
      exact hzp (by rw [hz0,zero_mul])
    exact hn ⟨n,P,z,hn0,hz,hzp,hfull⟩
  have hall : ∀ n, Nonempty (Packing p n) := by
    intro n
    induction n with
    | zero => exact ⟨⟨Fin.elim0,by simp,by simp⟩⟩
    | succ n ih =>
      obtain ⟨P⟩ := ih
      exact (packing_step e τ hτ htr hfaith hp P).resolve_left (hnot n P)
  have ht0 := HochschildDiffuse.projection_trace_pos τ hfaith hp.1 hp0
  obtain ⟨N,hN⟩ := exists_nat_gt ((τ 1).re/(τ p).re)
  obtain ⟨P⟩ := hall N
  have hle := Complex.re_le_re (τ.monotone P.total_proj.le_one)
  change (τ P.total).re≤(τ 1).re at hle
  rw [P.total_trace τ htr] at hle
  exact (not_lt_of_ge hle) ((div_lt_iff₀ ht0).mp hN)

end HochschildTypeILocal

end

end OAI
