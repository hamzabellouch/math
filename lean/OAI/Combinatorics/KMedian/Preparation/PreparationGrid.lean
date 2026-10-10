import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationOutcome
import OAI.Combinatorics.KMedian.Preparation.AssignmentCopies
import OAI.Combinatorics.KMedian.Rounding.GridEndpoint

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset PhysicalPotential CopyState FixedBatch
variable {I J X : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Nonempty J] [PseudoMetricSpace X]

theorem split_solution_rounding (Fj : J → Finset I) (y : I → ℝ)
    (client : J → X) (location : I → X) (v : J → ℝ)
    {M δ T₁ γ τ : ℝ} (p : Parameters τ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1/2)
    (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a ≤ 1)
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) (hT : 0 < T₁)
    (hθ : 1/(M*δ) ≤ 1/8) (hα : M/(δ*T₁) ≤ 1/4)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (heven : Even p.Δ)
    (hfail : failureFactor γ p.g < 1)
    (hjunit : ∀ c, ∑ a ∈ Fj c, y a=1)
    (hjcost : ∀ c, ∑ a ∈ Fj c, y a*dist (client c) (location a)=v c)
    (hnearest : ∀ c, ∀ a ∈ Fj c, ∀ b ∉ Fj c,
      dist (client c) (location a) ≤ dist (client c) (location b)) :
    ∃ O : Finset I, ∃ a : J → I,
      (∀ c, a c ∈ O) ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (∑ a, y a)+3*p.g+(p.T:ℝ)*(4/(p.g*p.b)) ∧
      (∑ c, dist (client c) (location (a c))) ≤
        (1+2/Real.exp 1+8*τ)*
        (max (farFactor δ (1-1/(M*δ)) (M/(δ*T₁)) (M/T₁) γ)
          (nearFactor (1-1/(M*δ)) (M+(1+δ)*T₁) γ p.g)/(1-failureFactor γ p.g))*(∑ c, v c) := by
  classical
  have hv : ∀ c, 0 ≤ v c := fun c =>
    (sum_nonneg (fun a _ => mul_nonneg (hy a).le dist_nonneg)).trans_eq (hjcost c)
  obtain ⟨S,_,hsep,hcover⟩ := representatives univ client v hM.le (fun c _ => hv c)
  let T := ↥S
  have hreps : ∀ c, ∃ t : T, v t.val ≤ v c ∧ dist (client c) (client t.val) ≤ M*v c := by
    intro c
    obtain ⟨t,ht,hv,hd⟩ := hcover c (mem_univ c)
    exact ⟨⟨t,ht⟩,hv,hd⟩
  choose rep hrepV hrepD using hreps
  obtain ⟨n,r,hn,hmass,hbudget,hr,hcost⟩ := preparation_outcome
    (fun t : T => Fj t.val) Fj y (fun t : T => client t.val) client location
    (fun t : T => v t.val) v rep hy hy1 hM hδ hδ1 hT hθ hα p.gpos hγ hγ1 heven p.unit hfail
    (fun t => hjunit t.val) hjunit (fun t => hjcost t.val) hjcost
    (fun t => hnearest t.val)
    (fun t u htu => hsep t.property u.property (fun he => htu (Subtype.ext he))) hrepV hrepD
  let loc : Physical I T → X := Sum.elim location (fun ti => location ti.2)
  have hcopies : ∀ c, ∃ A : Finset (Copy (F := Physical I T) p.Δ),
      A ⊆ activeSlots n hn ∧ mass p.g A=1 ∧
      PhysicalPotential.cost p.g (fun a => dist (client c) (loc a.1)) A ≤
        ∑ a, r c a*dist (client c) (loc a) := by
    intro c
    exact assignment_copies n hn (r c) (fun a => dist (client c) (loc a)) p.gpos p.unit
      (fun a => ((hr c).1 a).1) (fun a => ((hr c).1 a).2) (hr c).2
  choose A hA hm hcostA using hcopies
  have hradius : ∀ c, ∃ R : ℝ, 0 ≤ R ∧
      (∀ a ∈ A c, dist (client c) (loc a.1) ≤ R) ∧
      ∃ a ∈ A c, R=dist (client c) (loc a.1) := by
    intro c
    have hne : (A c).Nonempty := by
      by_contra h
      have hm' := hm c
      rw [not_nonempty_iff_eq_empty.mp h,mass,card_empty,Nat.cast_zero,mul_zero] at hm'
      norm_num at hm'
    obtain ⟨a,ha,hmax⟩ := (A c).exists_max_image (fun a => dist (client c) (loc a.1)) hne
    exact ⟨_,dist_nonneg,hmax,⟨a,ha,rfl⟩⟩
  choose R hR hd hmax using hradius
  obtain ⟨O,a,ha,hcount,hconn⟩ := grid_complete_parameters hτ hτ1 p (activeSlots n hn) A
    loc client R hR hm hd hmax (by rwa [activeSlots_mass]) hA
  let back : Physical I T → I := Sum.elim id Prod.snd
  have hloc : ∀ f, location (back f)=loc f := by intro f; cases f <;> rfl
  refine ⟨O.image back,fun c => back (a c),fun c => mem_image_of_mem back (ha c),?_,?_,?_⟩
  · obtain ⟨c⟩ := ‹Nonempty J›
    exact ⟨back (a c),mem_image_of_mem back (ha c)⟩
  · calc
      _ ≤ (O.card:ℝ) := by exact_mod_cast card_image_le
      _ ≤ mass p.g (activeSlots n hn)+(p.T:ℝ)*(4/(p.g*p.b)) := hcount
      _ ≤ _ := by rw [activeSlots_mass]; exact add_le_add hbudget le_rfl
  · simp_rw [hloc]
    have hc : (∑ c, PhysicalPotential.cost p.g (fun a => dist (client c) (loc a.1)) (A c)) ≤
        (max (farFactor δ (1-1/(M*δ)) (M/(δ*T₁)) (M/T₁) γ)
          (nearFactor (1-1/(M*δ)) (M+(1+δ)*T₁) γ p.g)/(1-failureFactor γ p.g))*(∑ c, v c) :=
      (sum_le_sum (fun c _ => hcostA c)).trans hcost
    exact hconn.trans ((mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_assoc _ _ _).symm)

end MetricKMedian.Preparation
end
end

end OAI
