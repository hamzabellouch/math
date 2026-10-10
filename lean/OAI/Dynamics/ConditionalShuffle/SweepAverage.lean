import OAI.Dynamics.ConditionalShuffle.SampleProduct

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional

lemma freeCount_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (B : β → Bool) (e : α ≃ β) : freeCount (B ∘ e) = freeCount B := by
  apply Nat.cast_injective (R := ℝ)
  rw [← sum_free_indicator, ← sum_free_indicator]
  exact Equiv.sum_comp e (fun x => if B x then (1 : ℝ) else 0)

lemma card_without {α : Type*} [Fintype α] [DecidableEq α] (x : α) :
    Fintype.card {y : α // y ≠ x} + 1 = Fintype.card α := by
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨x⟩
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  omega

lemma freeCount_without {α : Type*} [Fintype α] [DecidableEq α] (B : α → Bool) (x : α) (hx : B x = true) :
    freeCount (fun y : {y : α // y ≠ x} => B y.val) + 1 = freeCount B := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [← sum_free_indicator, ← sum_free_indicator]
  have hh := Fintype.sum_eq_add_sum_subtype_ne (fun y => if B y then (1 : ℝ) else 0) x
  simpa [hx, add_comm] using hh.symm

lemma mean_right_randomize {G Ω : Type*} [Fintype G] [Group G] [Fintype Ω] [Nonempty Ω]
    (r : Ω → G) (F : G → ℝ) :
    mean F = mean (fun g => mean (fun ω => F (g * r ω))) := by
  rw [mean_comm]
  calc
    _ = mean (fun _ : Ω => mean F) := (mean_const _).symm
    _ = _ := mean_congr (fun ω => (mean_equiv (Equiv.mulRight (r ω)) F).symm)

lemma ofSubtype_symm_apply {α : Type*} {p : α → Prop} [DecidablePred p]
    (σ : Equiv.Perm {x // p x}) (x : {x // p x}) :
    (Equiv.Perm.ofSubtype σ).symm x.val = (σ.symm x).val := by
  apply (Equiv.Perm.ofSubtype σ).injective
  simp only [Equiv.apply_symm_apply]
  exact ((Equiv.Perm.ofSubtype_apply_of_mem σ (σ.symm x).property).trans
    (congrArg Subtype.val (σ.apply_symm_apply x))).symm

lemma rawPoint_energy_product (d t : ℕ) (ht : t ≤ d+1) (B : Position (d+1) → Bool)
    (tag : Position (d+1)) (hb : B tag = true) :
    mean (fun ω : SweepHistory d t => rawEnergy (rawIterate d (rawPoint (d+1) B tag) t ω)) =
      mean (fun ω : SweepHistory d t => ∏ i : Fin t,
        if B (encounterList d t tag ω i) then (1/2 : ℝ) else 1) :=
  (rawPoint_energy_identity d t B tag).trans
    (mean_congr (rawPoint_tag_product d t ht B tag hb))

lemma rawPoint_uniform_sweep (d t : ℕ) (ht : t ≤ d+1) (B : Position (d+1) → Bool)
    (tag : Position (d+1)) (hb : B tag = true)
    (hm : Fintype.card (Position (d+1)) ≤ 64 * freeCount B)
    (hs : 256 * (t+1) ≤ Fintype.card (Position (d+1))) :
    mean (fun g : State (d+1) => mean (fun ω : SweepHistory d t =>
      rawEnergy (rawIterate d (rawPoint (d+1) (B ∘ g.symm) (g tag)) t ω))) ≤
        (255/256 : ℝ)^t := by
  let A := {x : Position (d+1) // x ≠ tag}
  let lift (σ : Equiv.Perm A) : State (d+1) := Equiv.Perm.ofSubtype σ
  let F (g : State (d+1)) : ℝ := mean (fun ω : SweepHistory d t =>
    rawEnergy (rawIterate d (rawPoint (d+1) (B ∘ g.symm) (g tag)) t ω))
  have eqavg := mean_right_randomize lift F
  change mean F ≤ _
  rw [eqavg]
  apply mean_le_const
  intro g
  have hlift (σ : Equiv.Perm A) : lift σ tag = tag := by
    exact Equiv.Perm.ofSubtype_apply_of_not_mem σ (not_not.mpr rfl)
  have hpoint (σ : Equiv.Perm A) : F (g * lift σ) =
      mean (fun ω : SweepHistory d t => ∏ i : Fin t,
        if B ((lift σ).symm (g.symm (encounterList d t (g tag) ω i))) then (1/2 : ℝ) else 1) := by
    dsimp only [F]
    have hb' : (B ∘ (g * lift σ).symm) ((g * lift σ) tag) = true := by
      change B ((g * lift σ).symm ((g * lift σ) tag)) = true
      rw [Equiv.symm_apply_apply]; exact hb
    have hh := rawPoint_energy_product d t ht (B ∘ (g * lift σ).symm) ((g * lift σ) tag) hb'
    refine hh.trans (mean_congr (fun ω => ?_))
    simp only [Equiv.Perm.mul_apply, hlift]
    rfl
  simp_rw [hpoint]
  rw [mean_comm]
  apply mean_le_const; intro ω
  let e : Fin t ↪ A := ⟨fun i => ⟨g.symm (encounterList d t (g tag) ω i), by
    intro hh
    apply encounterList_ne d t ht (g tag) ω i
    simpa using congrArg g hh⟩,
    fun i j hij => encounterList_injective d t ht (g tag) ω
      (g.symm.injective (congrArg Subtype.val hij))⟩
  have hz (σ : Equiv.Perm A) (i : Fin t) :
      (lift σ).symm (g.symm (encounterList d t (g tag) ω i)) = (σ.symm (e i)).val := by
    change (Equiv.Perm.ofSubtype σ).symm (e i).val = _
    exact ofSubtype_symm_apply σ (e i)
  simp_rw [hz]
  have hmean := mean_equiv (Equiv.inv (Equiv.Perm A))
    (fun σ : Equiv.Perm A => ∏ i, if B (σ (e i)).val then (1/2 : ℝ) else 1)
  change mean (fun σ : Equiv.Perm A => ∏ i, if B (σ.symm (e i)).val then (1/2 : ℝ) else 1) = _ at hmean
  rw [hmean]
  have hm' : Fintype.card A + 1 ≤ 64 * (freeCount (fun x : A => B x.val) + 1) := by
    rw [freeCount_without B tag hb, card_without tag]
    exact hm
  have hs' : 256 * (t+1) ≤ Fintype.card A + 1 := by
    rw [card_without tag]
    exact hs
  have hh := mean_perm_half_le e (fun x : A => B x.val) hm' hs'
  exact hh

end Thorp.Conditional

end

end OAI
