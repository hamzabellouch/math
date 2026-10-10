import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.CharacteristicNilpotentCore

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A]

lemma finite_upperCentralSeriesStep [Group.FG A] [Finite (Subgroup.center A)]
    (N : Subgroup A) [N.Normal] [Finite N] :
    Finite (Subgroup.upperCentralSeriesStep N) := by
  obtain ⟨S,hS⟩ := Group.fg_def.mp (inferInstance : Group.FG A)
  let U := Subgroup.upperCentralSeriesStep N
  let f : U → (S → N) := fun u s => ⟨⁅u.val,s.val⁆,u.property s.val⟩
  have hdiff (u v : U) (h : f u=f v) : v.val⁻¹*u.val ∈ Subgroup.center A := by
    rw [←Subgroup.centralizer_univ,←Subgroup.coe_top,←hS,Subgroup.centralizer_closure]
    intro s hs
    have he := congrArg (fun g : S → N => (g ⟨s,hs⟩).val) h
    change ⁅u.val,s⁆=⁅v.val,s⁆ at he
    simp only [commutatorElement_def] at he
    calc
      s*(v.val⁻¹*u.val) = v.val⁻¹*(v.val*s*v.val⁻¹*s⁻¹)*s*u.val := by group
      _ = v.val⁻¹*(u.val*s*u.val⁻¹*s⁻¹)*s*u.val := by rw [he]
      _ = v.val⁻¹*u.val*s := by group
  have hf (b : S → N) : Finite {u : U // f u=b} := by
    by_cases hb : Nonempty {u : U // f u=b}
    · obtain ⟨v,hv⟩ := hb
      let e : {u : U // f u=b} → Subgroup.center A := fun u =>
        ⟨v.val⁻¹*u.val.val,hdiff u.val v (u.property.trans hv.symm)⟩
      apply Finite.of_injective e
      intro u w he
      apply Subtype.ext
      apply Subtype.ext
      have he' := congrArg Subtype.val he
      exact mul_left_cancel he'
    · let _ : IsEmpty {u : U // f u=b} := not_nonempty_iff.mp hb
      infer_instance
  let _ : ∀ b : S → N, Finite {u : U // f u=b} := hf
  apply Finite.of_injective (fun u : U => (⟨f u,⟨u,rfl⟩⟩ : Σ b : S → N, {u : U // f u=b}))
  intro u v h
  exact congrArg (fun x : Σ b : S → N, {u : U // f u=b} => x.2.val) h

theorem finite_of_finite_center [Group.FG A] [Group.IsNilpotent A]
    [Finite (Subgroup.center A)] : Finite A := by
  have hf (n : ℕ) : Finite (Subgroup.upperCentralSeries A n) := by
    induction n with
    | zero => simpa only [Subgroup.upperCentralSeries_zero] using
        (inferInstance : Finite (⊥ : Subgroup A))
    | succ n ih =>
      let _ := ih
      exact finite_upperCentralSeriesStep (Subgroup.upperCentralSeries A n)
  obtain ⟨n,hn⟩ := Group.IsNilpotent.nilpotent A
  let _ : Finite (⊤ : Subgroup A) := hn ▸ hf n
  exact Finite.of_surjective (⊤ : Subgroup A).subtype (by intro x; exact ⟨⟨x,Subgroup.mem_top x⟩,rfl⟩)

theorem infinite_center_of_nilpotent [Group.FG A] [Group.IsNilpotent A]
    [Infinite A] : Infinite (Subgroup.center A) := by
  rcases finite_or_infinite (Subgroup.center A) with hf | hi
  · let _ := hf
    let _ : Finite A := finite_of_finite_center
    exact False.elim (_root_.not_finite A)
  · exact hi

end CriticalPercolation.SparseGrowth
end
end

end OAI
