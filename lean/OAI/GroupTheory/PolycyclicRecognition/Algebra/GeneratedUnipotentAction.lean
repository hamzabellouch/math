import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingNilpotentWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ActionDepth
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # A finite nilpotent action filtration from unipotent abelian generators -/

noncomputable section
namespace PolycyclicRecognition
variable {V I : Type*} [AddCommGroup V] [Module ℝ V]

theorem action_filtration_preserved_of_commute (D : I → Module.End ℝ V)
    (T : Module.End ℝ V) (hT : ∀ i, Commute T (D i)) (n : ℕ) :
    ∀ x ∈ linearActionFiltration D n, T x ∈ linearActionFiltration D n := by
  induction n with
  | zero => exact fun _ _ => Submodule.mem_top
  | succ n ih =>
    have hs : linearActionFiltration D (n + 1) ≤
        (linearActionFiltration D (n + 1)).comap T := by
      change (⨆ i, (linearActionFiltration D n).map (D i)) ≤ _
      apply iSup_le
      intro i x hx
      obtain ⟨y, hy, rfl⟩ := hx
      change T (D i y) ∈ linearActionFiltration D (n + 1)
      rw [show T (D i y) = D i (T y) from LinearMap.congr_fun (hT i).eq y]
      exact (le_iSup (fun j => (linearActionFiltration D n).map (D j)) i) ⟨T y, ih y hy, rfl⟩
    exact hs

open scoped IsMulCommutative
variable {Q : Type*} [Group Q] [IsMulCommutative Q]

theorem unipotent_generated_abelian_action_filtration
    (ρ : Q →* Module.End ℝ V) (qs : List Q)
    (hgen : Subgroup.closure {q | q ∈ qs} = ⊤)
    (hnil : ∀ q ∈ qs, IsNilpotent (ρ q - 1)) :
    ∃ c, linearActionFiltration (fun q => ρ q - 1) c = ⊥ := by
  classical
  have hcomm (q r : Q) : Commute (ρ q) (ρ r) := by
    change ρ q * ρ r = ρ r * ρ q
    rw [← map_mul, ← map_mul, mul_comm]
  let D : Fin qs.length → Module.End ℝ V := fun i => ρ (qs.get i) - 1
  obtain ⟨c, hc⟩ := finite_commuting_nilpotent_action_filtration D
    (fun i j => ((hcomm _ _).sub_left (Commute.one_left _)).sub_right (Commute.one_right _))
    (fun i => hnil _ (List.get_mem qs i))
  have h0 (q : Q) : ActionDepth D 0 (ρ q) := by
    intro n x hx
    exact action_filtration_preserved_of_commute D (ρ q)
      (fun i => (hcomm _ _).sub_right (Commute.one_right _)) n x hx
  have hmul (q r : Q) : ρ (q * r) - 1 =
      (ρ q - 1) + (ρ r - 1) + (ρ q - 1) * (ρ r - 1) := by
    rw [map_mul]
    noncomm_ring
  have hinv (q : Q) : ρ q⁻¹ - 1 = -(ρ q⁻¹ * (ρ q - 1)) := by
    have he : ρ q⁻¹ * ρ q = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [mul_sub, he]
    noncomm_ring
  let H : Subgroup Q :=
    { carrier := {q | ActionDepth D 1 (ρ q - 1)}
      one_mem' := by
        change ActionDepth D 1 (ρ 1 - 1)
        rw [map_one, sub_self]
        exact ActionDepth.zero 1
      mul_mem' := by
        intro q r hq hr
        change ActionDepth D 1 (ρ (q * r) - 1)
        rw [hmul]
        exact (hq.add hr).add ((hq.mul hr).mono (by decide))
      inv_mem' := by
        intro q hq
        change ActionDepth D 1 (ρ q⁻¹ - 1)
        rw [hinv]
        exact ((h0 q⁻¹).mul hq).neg }
  have hH : H = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le H).mpr
    intro q hq
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
    change ActionDepth D 1 (ρ q - 1)
    rw [← hi]
    exact ActionDepth.generator i
  have hdepth (q : Q) : ActionDepth D 1 (ρ q - 1) := by
    have hq : q ∈ H := by rw [hH]; trivial
    exact hq
  have hle (n : ℕ) : linearActionFiltration (fun q => ρ q - 1) n ≤ linearActionFiltration D n := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      change (⨆ q, (linearActionFiltration (fun q => ρ q - 1) n).map (ρ q - 1)) ≤ _
      apply iSup_le
      intro q x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hdepth q n y (ih hy)
  exact ⟨c, eq_bot_iff.mpr ((hle c).trans_eq hc)⟩

end PolycyclicRecognition

end

end OAI
