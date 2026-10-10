import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.MatrixSeeds
import OAI.Analysis.BoundedHochschild.CentralIsometries

namespace OAI

/-! Central ranks and approximation by diagonal projections. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildCentralComparison
open BoundedHochschild HochschildComparison FinitePathMain HochschildMatrixSystems
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma central_projection_mul_le_left {z p : M} (hz : CentralProjection z) (hp : IsStarProjection p) :
    z*p ≤ z := by
  exact ((hz.1.mul hp (hz.2 p)).le_iff_mul_eq_left hz.1).mpr (central_mul_sandwich hz p)

lemma central_projection_mul_le_right {z p : M} (hz : CentralProjection z) (hp : IsStarProjection p) :
    z*p ≤ p := by
  apply ((hz.1.mul hp (hz.2 p)).le_iff_mul_eq_left hp).mpr
  rw [mul_assoc,hp.isIdempotentElem.eq]

lemma central_projection_mul_mono {z p q : M} (hz : CentralProjection z)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p ≤ q) : z*p ≤ z*q := by
  apply ((hz.1.mul hp (hz.2 p)).le_iff_mul_eq_left (hz.1.mul hq (hz.2 q))).mpr
  rw [central_mul_pair hz,(hp.le_iff_mul_eq_left hq).mp hpq]

variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

omit [StarOrderedRing M] in
include htr in
lemma central_diagonal_trace {n : ℕ} (E : MatrixSystem M n) (z : M)
    (hz : ∀ a : M, Commute z a) (i j : Fin n) :
    τ (z*E.entry i i)=τ (z*E.entry j j) := by
  calc
    _ = τ ((z*E.entry i j)*E.entry j i) := by rw [mul_assoc,E.entry_mul,ite_eq_left rfl]
    _ = τ (E.entry j i*(z*E.entry i j)) := htr _ _
    _ = τ (z*(E.entry j i*E.entry i j)) := by rw [← mul_assoc,← (hz _).eq,mul_assoc]
    _ = _ := by rw [E.entry_mul,ite_eq_left rfl]

omit [StarOrderedRing M] in
include htr in
lemma central_diagonal_trace_mul {n : ℕ} (E : MatrixSystem M n) (z : M)
    (hz : ∀ a : M, Commute z a) (i : Fin n) :
    (n:ℝ)*(τ (z*E.entry i i)).re=(τ z).re := by
  have hh := congrArg (fun a : M => (τ (z*a)).re) E.sum_diagonal
  rw [Finset.mul_sum,map_sum,Complex.re_sum,mul_one] at hh
  simpa only [central_diagonal_trace τ htr E z hz _ i,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh

structure CentralRank {n : ℕ} (E : MatrixSystem M n) (p : M) (m : ℕ) where
  val : PartialIso M
  color : Fin n → M
  color_central : ∀ i, CentralProjection (color i)
  color_zero : ∀ i, m ≤ i.val → color i=0
  initial_eq : val.initial=∑ i,color i*E.entry i i
  final_le : val.final ≤ p
  active : M
  active_central : CentralProjection active
  active_le_color : ∀ i, i.val < m → active ≤ color i
  error_bound : (n:ℝ)*(τ ((1-active)*(p-val.final))).re ≤ (τ (1-active)).re

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (hτ : TraceInPredual e τ) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma centralRank_zero {n : ℕ} (E : MatrixSystem M n) {p : M} (hp : IsStarProjection p) :
    Nonempty (CentralRank τ E p 0) := by
  refine ⟨⟨0,fun _ => 0,fun _ => ⟨IsStarProjection.zero M,fun a => Commute.zero_left a⟩,
    fun _ _ => rfl,?_,?_,1,⟨IsStarProjection.one M,fun a => Commute.one_left a⟩,
    (fun i hi => (Nat.not_lt_zero i.val hi).elim),?_⟩⟩
  · simp
  · simpa using hp.nonneg
  · simp

namespace CentralRank
variable {n : ℕ} {E : MatrixSystem M n} {p : M} {m : ℕ}

omit [StarOrderedRing M] in
lemma initial_mul_later (R : CentralRank τ E p m) (j : Fin n) (hj : m ≤ j.val) :
    R.val.initial*E.entry j j=0 := by
  rw [R.initial_eq,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [mul_assoc,E.entry_mul]
  by_cases hij : i=j
  · subst i
    rw [R.color_zero j hj,zero_mul]
  · rw [ite_eq_right hij,mul_zero]

include e hτ htr hfaith in
lemma step (hp : IsStarProjection p) (R : CentralRank τ E p m) (hm : m<n) :
    Nonempty (CentralRank τ E p (m+1)) := by
  classical
  let j : Fin n := ⟨m,hm⟩
  let r := p-R.val.final
  have hr : IsStarProjection r := (R.val.final_proj.le_iff_sub hp).mp R.final_le
  obtain ⟨z,v,hz,hvi,hvf,hvfr,hvie⟩ := central_comparison e τ hτ htr hfaith
    (E.diagonal_projection j) hr
  let d := R.active*(1-z)
  have hd : CentralProjection d := centralProjection_mul R.active_central (centralProjection_one_sub hz)
  have hdc : d ≤ R.active := central_projection_mul_le_left R.active_central hz.1.one_sub
  let w := PartialIso.centralCut v d hd
  have hwi : w.initial=d*E.entry j j := by
    rw [PartialIso.centralCut_initial]
    change (R.active*(1-z))*v.initial=(R.active*(1-z))*E.entry j j
    rw [mul_assoc,mul_assoc,hvie]
  have hwf : w.final ≤ r := (PartialIso.centralCut_final_le v d hd).trans hvf
  have hoi : R.val.initial*w.initial=0 := by
    rw [hwi,← mul_assoc,← (hd.2 R.val.initial).eq,mul_assoc,R.initial_mul_later τ j (by rfl),mul_zero]
  have hof : R.val.final*w.final=0 := orthogonal_of_le_sub hp R.val.final_proj w.final_proj R.final_le hwf
  let s := R.val.orthogonalSum w hoi hof
  have hsf : s.final=R.val.final+w.final := PartialIso.orthogonalSum_final _ _ _ _
  have hsp : s.final ≤ p := by
    rw [hsf]
    calc
      _ ≤ R.val.final+(p-R.val.final) := add_le_add_right hwf _
      _ = p := by abel
  have hdiw : (1-d)*w.final=0 := by
    rw [PartialIso.centralCut_final]
    rw [← mul_assoc,sub_mul,one_mul,hd.1.isIdempotentElem.eq,sub_self,zero_mul]
  have hid : 1-d=(1-R.active)+R.active*z := by dsimp [d]; noncomm_ring
  have hfail : (n:ℝ)*(τ ((R.active*z)*r)).re ≤ (τ (R.active*z)).re := by
    have hzv : (R.active*z)*v.final=(R.active*z)*r := by rw [mul_assoc,mul_assoc,hvfr]
    have htz : τ ((R.active*z)*r)=τ ((R.active*z)*v.initial) := by
      rw [← hzv]
      exact (central_weighted_trace_partialIso τ htr v _ (centralProjection_mul R.active_central hz).2).symm
    rw [htz,← central_diagonal_trace_mul τ htr E (R.active*z)
      (centralProjection_mul R.active_central hz).2 j]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    exact Complex.re_le_re (τ.monotone (central_projection_mul_mono
      (centralProjection_mul R.active_central hz) v.initial_proj (E.diagonal_projection j) hvi))
  have herr : (n:ℝ)*(τ ((1-d)*(p-s.final))).re ≤ (τ (1-d)).re := by
    have hleft : (1-d)*(p-s.final)=(1-d)*r := by
      rw [hsf,show p-(R.val.final+w.final)=(p-R.val.final)-w.final by abel,mul_sub,hdiw,sub_zero]
    rw [hleft,hid,add_mul,map_add,Complex.add_re,map_add,Complex.add_re,mul_add]
    exact add_le_add R.error_bound hfail
  refine ⟨⟨s,Function.update R.color j d,?_,?_,?_,hsp,d,hd,?_,herr⟩⟩
  · intro i
    by_cases hij : i=j
    · subst i; simpa only [Function.update_self] using hd
    · simpa only [Function.update_of_ne hij] using R.color_central i
  · intro i hi
    have hij : i ≠ j := by intro hh; subst i; dsimp [j] at hi; omega
    rw [Function.update_of_ne hij]
    exact R.color_zero i (by omega)
  · rw [PartialIso.orthogonalSum_initial,R.initial_eq,hwi]
    have hzj := R.color_zero j (by rfl)
    have hsum : (∑ i,Function.update R.color j d i*E.entry i i)=
        (∑ i,R.color i*E.entry i i)+d*E.entry j j := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
        ← Finset.sum_erase_add (Finset.univ : Finset (Fin n)) (fun i => R.color i*E.entry i i) (Finset.mem_univ j)]
      simp only [Function.update_self,hzj,zero_mul,add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    exact hsum.symm
  · intro i hi
    by_cases hij : i=j
    · subst i; simp only [Function.update_self,le_refl]
    · rw [Function.update_of_ne hij]
      exact hdc.trans (R.active_le_color i (by
        have hne : i.val≠m := fun hh => hij (Fin.ext hh)
        omega))

include htr in
lemma terminal_error (hp : IsStarProjection p) (R : CentralRank τ E p n) :
    (n:ℝ)*(τ (p-R.val.final)).re ≤ (τ 1).re := by
  have hci : R.active*R.val.initial=R.active := by
    rw [R.initial_eq,Finset.mul_sum]
    have hh : ∀ i : Fin n, R.active*(R.color i*E.entry i i)=R.active*E.entry i i := by
      intro i
      rw [← mul_assoc,(R.active_central.1.le_iff_mul_eq_left (R.color_central i).1).mp
        (R.active_le_color i i.isLt)]
    simp only [hh,← Finset.mul_sum,E.sum_diagonal,mul_one]
  have hct : τ (R.active*R.val.final)=τ R.active := by
    rw [← central_weighted_trace_partialIso τ htr R.val R.active R.active_central.2,hci]
  have hcr : (τ (R.active*(p-R.val.final))).re ≤ 0 := by
    rw [mul_sub,map_sub,Complex.sub_re,hct]
    have hh := Complex.re_le_re (τ.monotone (central_projection_mul_le_left R.active_central hp))
    change (τ (R.active*p)).re ≤ (τ R.active).re at hh
    linarith
  have he : p-R.val.final=(1-R.active)*(p-R.val.final)+R.active*(p-R.val.final) := by noncomm_ring
  rw [he,map_add,Complex.add_re,mul_add]
  have hc0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n : (0:ℝ)≤n) hcr
  have hbound : (τ (1-R.active)).re ≤ (τ 1).re :=
    Complex.re_le_re (τ.monotone R.active_central.1.one_sub.le_one)
  linarith [R.error_bound]
end CentralRank

include e hτ htr hfaith in
theorem exists_central_rank {n : ℕ} (E : MatrixSystem M n) {p : M} (hp : IsStarProjection p) :
    ∃ R : CentralRank τ E p n, (n:ℝ)*(τ (p-R.val.final)).re ≤ (τ 1).re := by
  have hh : ∀ m : ℕ, m ≤ n → Nonempty (CentralRank τ E p m) := by
    intro m
    induction m with
    | zero => intro _; exact centralRank_zero τ E hp
    | succ m ih =>
      intro hm
      obtain ⟨R⟩ := ih (by omega)
      exact R.step τ htr e hτ hfaith hp (by omega)
  obtain ⟨R⟩ := hh n le_rfl
  exact ⟨R,R.terminal_error τ htr hp⟩

end HochschildCentralComparison

end

end OAI
