import Mathlib
import OAI.Analysis.Commutator.DiffuseHalving
import OAI.Analysis.Commutator.FiniteNoReplicas
import OAI.Analysis.Commutator.ProjectionEquivalence

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ProjectionIn (M : VonNeumannAlgebra H) where
  val : H →L[ℂ] H
  mem : val∈M
  projection : IsStarProjection val

namespace DyadicCuts

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
    (hd : DiffuseProjection.HasNoMinimalProjections M)

def half (e : ProjectionIn M) : Link M e.val e.val :=
  (diffuse_halving M hfac hd e.mem e.projection).choose

lemma half_square (e : ProjectionIn M) : (half M hfac hd e).val*(half M hfac hd e).val=0 :=
  (diffuse_halving M hfac hd e.mem e.projection).choose_spec.1

lemma half_sum (e : ProjectionIn M) :
    (half M hfac hd e).initial+(half M hfac hd e).final=e.val :=
  (diffuse_halving M hfac hd e.mem e.projection).choose_spec.2

def next (e : ProjectionIn M) : ProjectionIn M :=
  ⟨(half M hfac hd e).initial,
    M.mul_mem (M.star_mem' (half M hfac hd e).mem) (half M hfac hd e).mem,
    (half M hfac hd e).initial_projection⟩

def cut : ℕ → ProjectionIn M
  | 0 => ⟨1,M.one_mem,IsStarProjection.one _⟩
  | n+1 => next M hfac hd (cut n)

def link (n : ℕ) := half M hfac hd (cut M hfac hd n)

def side (n : ℕ) : H →L[ℂ] H := (link M hfac hd n).final

lemma cut_succ (n : ℕ) : (cut M hfac hd (n+1)).val=(link M hfac hd n).initial := rfl

lemma side_projection (n : ℕ) : IsStarProjection (side M hfac hd n) :=
  (link M hfac hd n).final_projection

lemma side_mem (n : ℕ) : side M hfac hd n∈M :=
  M.mul_mem (link M hfac hd n).mem (M.star_mem' (link M hfac hd n).mem)

lemma side_le (n : ℕ) : side M hfac hd n≤(cut M hfac hd n).val :=
  (link M hfac hd n).target_le

lemma cut_antitone : Antitone (fun n => (cut M hfac hd n).val) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (link M hfac hd n).source_le

lemma cut_succ_add_side (n : ℕ) :
    (cut M hfac hd (n+1)).val+side M hfac hd n=(cut M hfac hd n).val :=
  half_sum M hfac hd (cut M hfac hd n)

lemma side_mul_cut_succ (n : ℕ) :
    side M hfac hd n*(cut M hfac hd (n+1)).val=0 := by
  have h := (link M hfac hd n).initial_mul_final_eq_zero
    (half_square M hfac hd (cut M hfac hd n))
  change (cut M hfac hd (n+1)).val*side M hfac hd n=0 at h
  simpa only [star_mul,(side_projection M hfac hd n).isSelfAdjoint.star_eq,
    (cut M hfac hd (n+1)).projection.isSelfAdjoint.star_eq,star_zero] using congrArg star h

lemma side_mul_side_of_lt {n m : ℕ} (hnm : n < m) : side M hfac hd n*side M hfac hd m=0 := by
  have hle : side M hfac hd m≤(cut M hfac hd (n+1)).val :=
    (side_le M hfac hd m).trans (cut_antitone M hfac hd (Nat.succ_le_of_lt hnm))
  have he := ((side_projection M hfac hd m).le_iff_mul_eq_right
    (cut M hfac hd (n+1)).projection).mp hle
  calc
    _=side M hfac hd n*((cut M hfac hd (n+1)).val*side M hfac hd m) := by rw [he]
    _=0 := by rw [←mul_assoc,side_mul_cut_succ,zero_mul]

lemma side_cross (n m : ℕ) (hne : n≠m) : side M hfac hd n*side M hfac hd m=0 := by
  rcases lt_or_gt_of_ne hne with h|h
  · exact side_mul_side_of_lt M hfac hd h
  · simpa only [star_mul,(side_projection M hfac hd n).isSelfAdjoint.star_eq,
      (side_projection M hfac hd m).isSelfAdjoint.star_eq,star_zero] using
      congrArg star (side_mul_side_of_lt M hfac hd h)

theorem exists_subEquivalent [TopologicalSpace.SeparableSpace H]
    (hfin : IsFiniteAlgebra M) {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hen : e≠0) :
    ∃ n,SubEquivalent M (cut M hfac hd n).val e := by
  classical
  by_contra hn
  push Not at hn
  have hrev (n : ℕ) : SubEquivalent M e (cut M hfac hd n).val := by
    exact (factor_subEquivalent_total M hfac heM (cut M hfac hd n).mem
      he (cut M hfac hd n).projection).resolve_right (hn n)
  choose v hv using hrev
  let b (n : ℕ) : Link M (cut M hfac hd (n+1)).val (side M hfac hd n) :=
    ⟨(link M hfac hd n).val,(link M hfac hd n).mem,(link M hfac hd n).triple,le_rfl,le_rfl⟩
  let a (n : ℕ) : Link M e (side M hfac hd n) :=
    (b n).compFull (v (n+1)) he (cut M hfac hd (n+1)).projection (hv (n+1)) rfl
  have hai (n : ℕ) : (a n).initial=e :=
    (b n).compFull_initial (v (n+1)) he (cut M hfac hd (n+1)).projection (hv (n+1)) rfl
  have hac (n m : ℕ) (hne : n≠m) : star (a n).val*(a m).val=0 := by
    have hl : star (a n).val*side M hfac hd n=star (a n).val := by
      simpa only [star_mul,(side_projection M hfac hd n).isSelfAdjoint.star_eq] using
        congrArg star ((a n).target_mul (side_projection M hfac hd n))
    calc
      _=(star (a n).val*side M hfac hd n)*(side M hfac hd m*(a m).val) := by
        rw [hl,(a m).target_mul (side_projection M hfac hd m)]
      _=star (a n).val*(side M hfac hd n*side M hfac hd m)*(a m).val := by noncomm_ring
      _=0 := by rw [side_cross M hfac hd n m hne,mul_zero,zero_mul]
  exact finite_no_replicas M hfac hfin heM he hen
    ⟨fun n => (a n).val,fun n => (a n).mem,hai,hac,fun n => (a n).mul_source he⟩

end DyadicCuts

end Kadison.PartialIsometryOrder

end

end
end

end OAI
