import OAI.Dynamics.ConditionalShuffle.RawLinear

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional

lemma ofSubtype_symm_apply_not_mem {α : Type*} {p : α → Prop} [DecidablePred p]
    (σ : Equiv.Perm {x // p x}) (x : α) (hx : ¬ p x) :
    (Equiv.Perm.ofSubtype σ).symm x = x := by
  apply (Equiv.Perm.ofSubtype σ).injective
  rw [Equiv.apply_symm_apply, Equiv.Perm.ofSubtype_apply_of_not_mem σ hx]

lemma ofSubtype_bool_preserves {α : Type*} (B : α → Bool)
    (σ : Equiv.Perm {x // B x = true}) (x : α) :
    B ((Equiv.Perm.ofSubtype σ).symm x) = B x := by
  by_cases hx : B x = true
  · have hh := ofSubtype_symm_apply σ ⟨x,hx⟩
    change (Equiv.Perm.ofSubtype σ).symm x = _ at hh
    rw [hh, (σ.symm ⟨x,hx⟩).property, hx]
  · rw [ofSubtype_symm_apply_not_mem σ x hx]

lemma sum_subtype_supported {α : Type*} [Fintype α] (B : α → Bool) (w : α → ℝ)
    (hw : ∀ x, B x = false → w x = 0) :
    (∑ x : {x // B x = true}, w x.val) = ∑ x, w x := by
  have hh := Fintype.sum_subtype_add_sum_subtype (fun x => B x = true) w
  have hz : (∑ x : {x // ¬ B x = true}, w x.val) = 0 := by
    apply Finset.sum_eq_zero; intro x _
    apply hw
    cases hx : B x.val
    · rfl
    · exact False.elim (x.property hx)
  rw [hz, add_zero] at hh
  exact hh

def rawPermute {d : ℕ} (v : RawState d) (g : State d) : RawState d :=
  ⟨v.free ∘ g.symm, v.weight ∘ g.symm⟩

lemma rawPermute_energy {d : ℕ} (v : RawState d) (g : State d) :
    rawEnergy (rawPermute v g) = rawEnergy v :=
  Equiv.sum_comp g.symm (fun x => v.weight x ^ 2)

lemma rawPermute_free_assignment {d : ℕ} (v : RawState d) (g : State d)
    (σ : Equiv.Perm {x // v.free x = true}) :
    (rawPermute v (g * Equiv.Perm.ofSubtype σ)).free = (rawPermute v g).free := by
  funext x
  exact ofSubtype_bool_preserves v.free σ (g.symm x)

lemma rawPermute_weight_assignment {d : ℕ} (v : RawState d)
    (hw : ∀ x, v.free x = false → v.weight x = 0) (g : State d)
    (σ : Equiv.Perm {x // v.free x = true}) (y : Position d) :
    (rawPermute v (g * Equiv.Perm.ofSubtype σ)).weight y =
      ∑ a : {x // v.free x = true}, if y = g a.val then v.weight (σ.symm a).val else 0 := by
  by_cases hf : v.free (g.symm y) = true
  · let a : {x // v.free x = true} := ⟨g.symm y,hf⟩
    rw [Finset.sum_eq_single a]
    · have he : y = g a.val := (g.apply_symm_apply y).symm
      rw [ite_eq_left he]
      change v.weight ((Equiv.Perm.ofSubtype σ).symm a.val) = _
      rw [ofSubtype_symm_apply]
    · intro b _ hba
      apply ite_eq_right
      intro hy
      apply hba
      apply Subtype.ext
      change b.val = g.symm y
      exact (g.symm_apply_apply b.val).symm.trans (congrArg g.symm hy.symm)
    · simp
  · have hfalse : v.free (g.symm y) = false := Bool.eq_false_iff.mpr hf
    change v.weight ((Equiv.Perm.ofSubtype σ).symm (g.symm y)) = _
    rw [ofSubtype_symm_apply_not_mem σ _ hf, hw _ hfalse]
    symm
    apply Finset.sum_eq_zero; intro a _
    apply ite_eq_right
    intro hy
    have hh := congrArg g.symm hy
    simp only [Equiv.symm_apply_apply] at hh
    exact hf (hh ▸ a.property)

lemma rawIterate_assignment_matrix (d : ℕ) (v : RawState (d+1))
    (hw : ∀ x, v.free x = false → v.weight x = 0) (g : State (d+1))
    (σ : Equiv.Perm {x // v.free x = true}) (t : ℕ) (ω : SweepHistory d t) (y) :
    (rawIterate d (rawPermute v (g * Equiv.Perm.ofSubtype σ)) t ω).weight y =
    ∑ a : {x // v.free x = true}, v.weight (σ.symm a).val *
      (rawIterate d (rawPoint (d+1) (v.free ∘ g.symm) (g a.val)) t ω).weight y := by
  have he : rawPermute v (g * Equiv.Perm.ofSubtype σ) =
      ⟨v.free ∘ g.symm, fun y => ∑ a : {x // v.free x = true},
        if y = g a.val then v.weight (σ.symm a).val else 0⟩ := by
    apply RawState.ext
    · exact rawPermute_free_assignment v g σ
    · funext y; exact rawPermute_weight_assignment v hw g σ y
  rw [he]
  exact rawIterate_point_decomposition d _ (fun a => g a.val)
    (fun a => v.weight (σ.symm a).val) t ω y

lemma rawIterate_assignment_energy_le (d : ℕ) (v : RawState (d+1))
    (hw : ∀ x, v.free x = false → v.weight x = 0) (hz : ∑ x, v.weight x = 0)
    [Nonempty {x // v.free x = true}] (g : State (d+1))
    (t : ℕ) (ω : SweepHistory d t) :
    mean (fun σ : Equiv.Perm {x // v.free x = true} =>
      rawEnergy (rawIterate d (rawPermute v (g * Equiv.Perm.ofSubtype σ)) t ω)) ≤
    mean (fun a : {x // v.free x = true} => v.weight a.val ^ 2) *
      ∑ a : {x // v.free x = true}, rawEnergy
        (rawIterate d (rawPoint (d+1) (v.free ∘ g.symm) (g a.val)) t ω) := by
  let A := {x // v.free x = true}
  let K (a : A) (y : Position (d+1)) :=
    (rawIterate d (rawPoint (d+1) (v.free ∘ g.symm) (g a.val)) t ω).weight y
  let H (σ : Equiv.Perm A) := ∑ y, (∑ a, v.weight (σ a).val * K a y)^2
  have he : mean (fun σ : Equiv.Perm A =>
      rawEnergy (rawIterate d (rawPermute v (g * Equiv.Perm.ofSubtype σ)) t ω)) = mean H := by
    trans mean (fun σ : Equiv.Perm A => H σ.symm)
    · apply mean_congr; intro σ
      apply Finset.sum_congr rfl; intro y _
      congr 1
      exact rawIterate_assignment_matrix d v hw g σ t ω y
    · exact mean_equiv (Equiv.inv (Equiv.Perm A)) H
  rw [he]
  exact mean_permuted_matrix_energy_le (fun a : A => v.weight a.val)
    ((sum_subtype_supported v.free v.weight hw).trans hz) K
    (fun a y => rawPoint_nonneg d t _ _ ω y)

lemma raw_uniform_sweep (d t : ℕ) (ht : t ≤ d+1) (v : RawState (d+1))
    (hw : ∀ x, v.free x = false → v.weight x = 0) (hz : ∑ x, v.weight x = 0)
    (hm : Fintype.card (Position (d+1)) ≤ 64 * freeCount v.free)
    (hs : 256 * (t+1) ≤ Fintype.card (Position (d+1))) :
    mean (fun g : State (d+1) => mean (fun ω : SweepHistory d t =>
      rawEnergy (rawIterate d (rawPermute v g) t ω))) ≤
        rawEnergy v * (255/256 : ℝ)^t := by
  let A := {x // v.free x = true}
  have hcard : Fintype.card A = freeCount v.free := Fintype.card_subtype _
  have hpos : 0 < Fintype.card A := by
    rw [hcard]
    have hh : 0 < Fintype.card (Position (d+1)) := Fintype.card_pos
    omega
  let : Nonempty A := Fintype.card_pos_iff.mp hpos
  let F (g : State (d+1)) := mean (fun ω : SweepHistory d t =>
    rawEnergy (rawIterate d (rawPermute v g) t ω))
  let C : ℝ := mean (fun a : A => v.weight a.val ^ 2)
  have hC : 0 ≤ C := mean_nonneg (fun a => sq_nonneg _)
  have hCE : C * Fintype.card A = rawEnergy v := by
    dsimp only [C, mean]
    rw [div_mul_cancel₀ _ (by exact_mod_cast Nat.ne_of_gt hpos)]
    exact sum_subtype_supported v.free (fun x => v.weight x ^ 2)
      (fun x hx => by rw [hw x hx]; norm_num)
  have hpoint (a : A) : mean (fun g : State (d+1) => mean (fun ω : SweepHistory d t =>
      rawEnergy (rawIterate d (rawPoint (d+1) (v.free ∘ g.symm) (g a.val)) t ω))) ≤
      (255/256 : ℝ)^t := rawPoint_uniform_sweep d t ht v.free a.val a.property hm hs
  change mean F ≤ _
  rw [mean_right_randomize (fun σ : Equiv.Perm A => Equiv.Perm.ofSubtype σ) F]
  calc
    _ ≤ mean (fun g : State (d+1) => mean (fun ω : SweepHistory d t =>
        C * ∑ a : A, rawEnergy
          (rawIterate d (rawPoint (d+1) (v.free ∘ g.symm) (g a.val)) t ω))) := by
      apply mean_le_mean; intro g
      change mean (fun σ : Equiv.Perm A => mean (fun ω : SweepHistory d t =>
        rawEnergy (rawIterate d (rawPermute v (g * Equiv.Perm.ofSubtype σ)) t ω))) ≤ _
      rw [mean_comm]
      exact mean_le_mean (fun ω => rawIterate_assignment_energy_le d v hw hz g t ω)
    _ = C * ∑ a : A, mean (fun g : State (d+1) => mean (fun ω : SweepHistory d t =>
        rawEnergy (rawIterate d (rawPoint (d+1) (v.free ∘ g.symm) (g a.val)) t ω))) := by
      simp only [mean_const_mul, mean_sum]
    _ ≤ C * ∑ _a : A, (255/256 : ℝ)^t :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hpoint a)) hC
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hCE]

end Thorp.Conditional

end

end OAI
