import Mathlib
import OAI.Analysis.Commutator.CornerPhaseAveraging
import OAI.Analysis.Commutator.TracialL2Tools

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.CornerPhase

open TracialL2

section Trace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma trace_projection_mul_le (e a : A) (he : IsStarProjection e) :
    ‖τ (e*a)‖ ≤ (τ e).re*‖a‖ := by
  have ht : τ (e*a)=τ (e*(a*e)) := by
    calc
      _=τ (a*e) := hτ _ _
      _=τ ((a*e)*e) := by rw [mul_assoc,he.isIdempotentElem.eq]
      _=_ := hτ _ _
  rw [ht]
  calc
    _ ≤ norm τ e*norm τ (a*e) := norm_trace_mul τ hτ _ _
    _ ≤ norm τ e*(‖a‖*norm τ e) :=
      mul_le_mul_of_nonneg_left (norm_mul_left τ a e) (norm_nonneg τ e)
    _ = (norm τ e)^2*‖a‖ := by ring
    _ = (τ e).re*‖a‖ := by rw [norm_projection_sq τ he]

variable {N : ℕ} [NeZero N]

variable (e : ZMod N → A) (he : ∀ i,IsStarProjection (e i))
  (ho : ∀ i j,i≠j → e i*e j=0)

def phaseElement (m : ZMod N) : A := diagonal e (fun j => ZMod.stdAddChar (j*m))

omit [PartialOrder A] [StarOrderedRing A] in
include he ho in
lemma phaseElement_corner (m : ZMod N) :
    star (phaseElement e m)*phaseElement e m=∑ j,e j ∧
      phaseElement e m*star (phaseElement e m)=∑ j,e j ∧
      phaseElement e m*(∑ j,e j)=phaseElement e m ∧
      (∑ j,e j)*phaseElement e m=phaseElement e m := by
  obtain ⟨h1,h2⟩ := diagonal_unitary e he ho (fun j => ZMod.stdAddChar (j*m))
    (fun _ => AddChar.norm_apply _ _)
  exact ⟨h1,h2,diagonal_support e he ho _⟩

omit [StarOrderedRing A] in
include he ho in
lemma phaseElement_power_trace (m : ZMod N) (k : ℕ) (hk : 0<k) (a : A) :
    τ (phaseElement e m^k*a)=phaseSum (fun j => τ (e j*a)) ((k:ZMod N)*m) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [phaseElement,diagonal_pow_succ e he ho]
  simp only [diagonal,Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,smul_eq_mul,phaseSum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  congr 1
  ring

include hτ he ho in
lemma phaseElement_mean_bound [Fact N.Prime] (q : A) (hq : IsStarProjection q)
    (hpart : ∑ j,e j=q) (ht : ∀ i,(τ (e i)).re=(τ q).re/(N:ℝ))
    (a : A) (k : ℕ) (hk : 0<k) (hkN : k<N) :
    (∑ m : ZMod N, ‖τ (phaseElement e m^k*a)‖^2) ≤ (τ q).re^2*‖a‖^2 := by
  rcases hpart with rfl
  have hkz : (k:ZMod N)≠0 := by
    intro hz
    have hh := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hkN,ZMod.val_zero] at hh
    omega
  simp only [phaseElement_power_trace τ e he ho _ k hk a]
  rw [phase_parseval_mul _ _ hkz]
  have htq : 0 ≤ (τ (∑ index,e index)).re := (τ.map_nonneg hq.nonneg).1
  have hN : 0<(N:ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  calc
    _ ≤ (N:ℝ)*∑ _i : ZMod N, ((τ (∑ index,e index)).re/(N:ℝ)*‖a‖)^2 := by
      apply mul_le_mul_of_nonneg_left _ hN.le
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mpr
      simpa only [ht] using trace_projection_mul_le τ hτ (e i) a (he i)
    _ = (τ (∑ index,e index)).re^2*‖a‖^2 := by
      simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
      field_simp

include hτ he ho in
theorem exists_phase_finite {J : Type*} [Fintype J] [Fact N.Prime]
    (q : A) (hq : IsStarProjection q) (hpart : ∑ j,e j=q)
    (ht : ∀ i,(τ (e i)).re=(τ q).re/(N:ℝ)) (hqt : 0<(τ q).re)
    (a : J → A) (k : J → ℕ) (hk : ∀ j,0<k j ∧ k j<N)
    {ε : ℝ} (hε : 0<ε) (hbudget : (∑ j,‖a j‖^2)<(N:ℝ)*ε^2) :
    ∃ u : A, star u*u=q ∧ u*star u=q ∧ u*q=u ∧ q*u=u ∧ ‖u‖ ≤ 1 ∧
      (∀ j,‖τ (u^k j*a j)‖<ε*(τ q).re) ∧
      (∀ S : StarSubalgebra ℂ A, (∀ i,e i∈S) → u∈S) := by
  classical
  have hsum : (∑ m : ZMod N, ∑ j,‖τ (phaseElement e m^k j*a j)‖^2)<
      ∑ _m : ZMod N,(ε*(τ q).re)^2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ j,(τ q).re^2*‖a j‖^2 :=
        Finset.sum_le_sum (fun j _ => phaseElement_mean_bound τ hτ e he ho q hq hpart ht
          (a j) (k j) (hk j).1 (hk j).2)
      _ = (τ q).re^2*(∑ j,‖a j‖^2) := (Finset.mul_sum _ _ _).symm
      _ < (τ q).re^2*((N:ℝ)*ε^2) := mul_lt_mul_of_pos_left hbudget (sq_pos_of_pos hqt)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]; ring
  obtain ⟨m,_,hm⟩ := Finset.exists_lt_of_sum_lt hsum
  obtain ⟨hu1,hu2,hu3,hu4⟩ := phaseElement_corner e he ho m
  rw [hpart] at hu1 hu2 hu3 hu4
  refine ⟨phaseElement e m,hu1,hu2,hu3,hu4,?_,?_,?_⟩
  · have hn : ‖phaseElement e m‖^2=‖q‖ := by
      rw [←hu1,CStarRing.norm_star_mul_self,pow_two]
    have hqnorm := hq.norm_le q
    nlinarith [_root_.norm_nonneg (phaseElement e m)]
  · intro j
    have hj : ‖τ (phaseElement e m^k j*a j)‖^2 < (ε*(τ q).re)^2 :=
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖τ (phaseElement e m^k i*a i)‖)
        (Finset.mem_univ j)).trans_lt hm
    exact (sq_lt_sq₀ (_root_.norm_nonneg _) (mul_nonneg hε.le hqt.le)).mp hj
  · intro S hS
    exact S.sum_mem (fun i _ => S.smul_mem (hS i) _)

end Trace

end Kadison.CornerPhase

end

end
end

end OAI
