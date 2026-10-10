import OAI.Probability.BenjaminiSchramm.Cayley

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.decEq

noncomputable def rightDefect (A : Finset Λ) (g : Λ) : ℕ :=
  ((A.image (fun x => x * g)) \ A).card

theorem rightDefect_mul (A : Finset Λ) (a b : Λ) :
    rightDefect A (a * b) ≤ rightDefect A a + rightDefect A b := by
  have hsub : A.image (fun x => x * (a * b)) \ A ⊆
      ((A.image (fun x => x * a) \ A).image (fun x => x * b)) ∪
        (A.image (fun x => x * b) \ A) := by
    intro x hx
    obtain ⟨hx, hnot⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    by_cases hya : y * a ∈ A
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_image.mpr ⟨y * a, hya, mul_assoc y a b⟩, hnot⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨y * a, Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩, hya⟩,
          mul_assoc y a b⟩)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_image_le) le_rfl))

theorem rightDefect_inv (A : Finset Λ) (a : Λ) : rightDefect A a⁻¹ = rightDefect A a := by
  have hinj : Function.Injective (fun x : Λ => x * a) := mul_left_injective a
  have himage : (A.image (fun x => x * a⁻¹) \ A).image (fun x => x * a) =
      A \ A.image (fun x => x * a) := by
    rw [Finset.image_sdiff _ _ hinj, Finset.image_image]
    simp only [Function.comp_def, inv_mul_cancel_right, Finset.image_id']
  calc
    rightDefect A a⁻¹ = ((A.image (fun x => x * a⁻¹) \ A).image (fun x => x * a)).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ = (A \ A.image (fun x => x * a)).card := congrArg Finset.card himage
    _ = rightDefect A a := Finset.card_sdiff_comm
      (Finset.card_image_of_injective A hinj).symm

theorem rightDefect_generator (S A : Finset Λ) (s : Λ) (hs : s ∈ S)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) :
    rightDefect A s ≤ (vertexBoundary (cayleyBond S) A).ncard := by
  have hf := finite_vertexBoundary (cayleyBond S) (cayleyBond_locallyFinite S hsym) A
  change (A.image (fun x => x * s) \ A).card ≤ _
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ hf
  intro y hy
  obtain ⟨hy, hnot⟩ := Finset.mem_sdiff.mp hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  refine ⟨hnot, x, hx, (cayleyBond_adj S x (x * s)).mpr ?_⟩
  apply (SimpleGraph.mulCayley_adj' (S : Set Λ) x (x * s)).mpr
  exact ⟨fun h => hnot (h ▸ hx), s, hs, Or.inl rfl⟩

theorem rightDefect_word_bound (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) (g : Λ) :
    ∃ L : ℕ, ∀ A : Finset Λ,
      rightDefect A g ≤ L * (vertexBoundary (cayleyBond S) A).ncard := by
  have hg : g ∈ Subgroup.closure (S : Set Λ) := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, fun A => by simpa using rightDefect_generator S A s hs hsym⟩
  | one => exact ⟨0, fun A => by simp [rightDefect]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨La, ha⟩ := ha
    obtain ⟨Lb, hb⟩ := hb
    exact ⟨La + Lb, fun A => (rightDefect_mul A a b).trans
      (by simpa only [Nat.add_mul] using Nat.add_le_add (ha A) (hb A))⟩
  | inv a _ ha =>
    obtain ⟨L, ha⟩ := ha
    exact ⟨L, fun A => by rw [rightDefect_inv]; exact ha A⟩

theorem folnerAmenable_of_cayley_hV_nonpos (S : Finset Λ)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set Λ) = ⊤)
    (hh : hV (cayleyBond S) ≤ 0) : FolnerAmenable Λ := by
  intro K ε hε
  choose L hL using rightDefect_word_bound S hsym hgen
  let M : ℕ := (∑ k ∈ K, L k) + 1
  have hM : (0 : ℝ) < M := by dsimp [M]; positivity
  have hset : {r : ℝ | ∃ A : Finset Λ, A.Nonempty ∧
      r = (vertexBoundary (cayleyBond S) A).ncard / (A.card : ℝ)}.Nonempty :=
    ⟨_, {1}, by simp, rfl⟩
  obtain ⟨r, ⟨A, hA, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hset
    (hh.trans_lt (div_pos hε hM))
  have hcard : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hbound : (M : ℝ) * (vertexBoundary (cayleyBond S) A).ncard < ε * A.card := by
    have ht := (div_lt_iff₀ hcard).mp hr
    have hh' : ((vertexBoundary (cayleyBond S) A).ncard : ℝ) * M < ε * A.card :=
      (lt_div_iff₀ hM).mp (by simpa only [div_mul_eq_mul_div] using ht)
    calc
      (M : ℝ) * (vertexBoundary (cayleyBond S) A).ncard =
          (vertexBoundary (cayleyBond S) A).ncard * (M : ℝ) := mul_comm _ _
      _ < ε * A.card := hh'
  refine ⟨A, hA, ?_⟩
  intro k hk
  have hkM : L k ≤ M := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk).trans
    (Nat.le_add_right _ 1)
  have hd : rightDefect A k ≤ M * (vertexBoundary (cayleyBond S) A).ncard :=
    (hL k A).trans (Nat.mul_le_mul_right _ hkM)
  exact lt_of_le_of_lt (by exact_mod_cast hd) hbound

theorem cayleyFolnerInput_proved : CayleyFolnerInput Λ := by
  intro hna S hsym hgen
  by_contra hh
  exact hna (folnerAmenable_of_cayley_hV_nonpos S hsym hgen (le_of_not_gt hh))

end Percolation.BenjaminiSchramm

end OAI
