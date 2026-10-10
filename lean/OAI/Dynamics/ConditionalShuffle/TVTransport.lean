import OAI.Dynamics.ConditionalShuffle.FiberTransport

namespace OAI

noncomputable section
namespace Thorp.Trim
open scoped Classical

lemma tv_push_le {X Y : Type*} [Fintype X] [Fintype Y] (μ ν : X → ℝ) (f : X → Y) :
    tv (push μ f) (push ν f) ≤ tv μ ν := by
  unfold tv push
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ y, ∑ x, if f x = y then |μ x - ν x| else 0 := by
      apply Finset.sum_le_sum
      intro y _
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ x, |(if f x = y then μ x else 0) - (if f x = y then ν x else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          split_ifs <;> simp
    _ = _ := by rw [Finset.sum_comm]; simp

end Thorp.Trim

namespace Revealed.Disintegration
open scoped Classical
open Thorp Thorp.Conditional
variable {E E' G G' Ω : Type} [fintype_E : Fintype E] [Fintype E'] [Fintype G] [Fintype G']
  [nonempty_G : Nonempty G] [nonempty_G' : Nonempty G'] [Fintype Ω]

lemma fairMass_fiber_uniform (a : Ω → E) (k : Ω → G ≃ G') :
    fairMass (fun z : Ω × G => (a z.1, k z.1 z.2)) =
      fairMass (fun z : Ω × G' => (a z.1, z.2)) := by
  let retained_fintype_E := fintype_E
  let retained_nonempty_G := nonempty_G
  let retained_nonempty_G' := nonempty_G'
  funext z
  rw [fairMass_eq_mean, fairMass_eq_mean, mean_prod, mean_prod]
  apply mean_congr
  intro ω
  exact mean_equiv (k ω) (fun g => if (a ω,g) = z then 1 else 0)

lemma average_tv_joint (a : Ω → E) (b : Ω → G) :
    (∑ e, marginal (fairMass (fun ω => (a ω,b ω))) e *
      tv (conditional (fairMass (fun ω => (a ω,b ω))) e) (fun _ => (Fintype.card G : ℝ)⁻¹)) =
      tv (fairMass (fun ω => (a ω,b ω))) (fairMass (fun z : Ω × G => (a z.1,z.2))) := by
  rw [average_tv_eq _ (fairMass_nonneg _)]
  congr 1
  funext z
  rw [marginal_fairMass]
  have h := fairMass_prod a (id : G → G) z.1 z.2
  have hid : fairMass (id : G → G) z.2 = (Fintype.card G : ℝ)⁻¹ := by simp [fairMass]
  rw [hid] at h
  exact h.symm

theorem average_tv_transport (a : Ω → E) (b : Ω → G) (f : E → E') (k : E → G ≃ G') :
    (∑ e', marginal (fairMass (fun ω => (f (a ω),k (a ω) (b ω)))) e' *
      tv (conditional (fairMass (fun ω => (f (a ω),k (a ω) (b ω)))) e')
        (fun _ => (Fintype.card G' : ℝ)⁻¹)) ≤
    ∑ e, marginal (fairMass (fun ω => (a ω,b ω))) e *
      tv (conditional (fairMass (fun ω => (a ω,b ω))) e) (fun _ => (Fintype.card G : ℝ)⁻¹) := by
  rw [average_tv_joint, average_tv_joint]
  have h := Trim.tv_push_le (fairMass (fun ω => (a ω,b ω)))
    (fairMass (fun z : Ω × G => (a z.1,z.2))) (fun z : E × G => (f z.1,k z.1 z.2))
  simp only [Trim.push_fairMass, Function.comp_def] at h
  rw [fairMass_fiber_uniform (fun ω => f (a ω)) (fun ω => k (a ω))] at h
  exact h

end Revealed.Disintegration

end

end OAI
