import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- Counting an interval by its quotient and represented residue classes. The
second bound separates complete blocks from the final incomplete block. -/
theorem interval_card_le_residue_support (A : Finset ℕ) (N s : ℕ)
    (hs : 0 < s) (hA : A ⊆ Finset.range N) :
    let H := A.image (fun n : ℕ => (n : ZMod s))
    A.card ≤ (N / s + 1) * H.card ∧
      A.card ≤ N / s * H.card + N % s := by
  classical
  let : NeZero s := ⟨hs.ne'⟩
  let H := A.image (fun n : ℕ => (n : ZMod s))
  change A.card ≤ (N / s + 1) * H.card ∧
    A.card ≤ N / s * H.card + N % s
  have hinj : Function.Injective (fun n : ℕ => (n / s, (n : ZMod s))) := by
    intro a b hab
    have hq := congrArg Prod.fst hab
    change a / s = b / s at hq
    have hr := congrArg Prod.snd hab
    have hm := (ZMod.natCast_eq_natCast_iff a b s).mp hr
    change a % s = b % s at hm
    have ha := Nat.mod_add_div a s
    have hb := Nat.mod_add_div b s
    rw [hq, hm] at ha
    omega
  have hcount (T : Finset ℕ) (hT : T ⊆ A) (Q : ℕ)
      (hQ : ∀ n ∈ T, n / s < Q) : T.card ≤ Q * H.card := by
    have hh := Finset.card_le_card_of_injOn
      (s := T) (t := Finset.range Q ×ˢ H)
      (fun n : ℕ => (n / s, (n : ZMod s)))
      (by
        intro n hn
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hQ n hn),
          Finset.mem_image.mpr ⟨n, hT hn, rfl⟩⟩)
      (hinj.injOn)
    simpa only [Finset.card_product, Finset.card_range] using hh
  constructor
  · apply hcount A (fun _ h => h) (N / s + 1)
    intro n hn
    have hnN := Finset.mem_range.mp (hA hn)
    have hh : n / s ≤ N / s := Nat.div_le_div_right hnN.le
    omega
  · let Q := N / s
    have hfirst : (A.filter (fun n => n / s < Q)).card ≤ Q * H.card := by
      apply hcount _ (Finset.filter_subset _ _) Q
      intro n hn
      exact (Finset.mem_filter.mp hn).2
    have hrest : (A.filter (fun n => ¬n / s < Q)).card ≤ N % s := by
      calc
        _ ≤ (Finset.Ico (Q * s) N).card := by
          apply Finset.card_le_card
          intro n hn
          obtain ⟨hnA, hnQ⟩ := Finset.mem_filter.mp hn
          exact Finset.mem_Ico.mpr
            ⟨(Nat.le_div_iff_mul_le hs).mp (by omega),
              Finset.mem_range.mp (hA hnA)⟩
        _ = N % s := by
          rw [Nat.card_Ico, Nat.mod_eq_sub_div_mul]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := A) (fun n => n / s < Q)
    dsimp only [Q] at hfirst hsplit hrest
    omega

/-- If a residue support avoids its reflected copy, then a subset of an
interval containing at least a full period has density at most two thirds.
The target residue is arbitrary, including self-opposite residues. -/
theorem interval_card_le_two_thirds_of_no_modular_pair
    (A : Finset ℕ) (N s : ℕ) (hs : 0 < s) (hsN : s ≤ N)
    (hA : A ⊆ Finset.range N) (t : ZMod s)
    (hno : ∀ u ∈ A, ∀ v ∈ A, (u : ZMod s) + (v : ZMod s) ≠ t) :
    3 * A.card ≤ 2 * N := by
  classical
  let : NeZero s := ⟨hs.ne'⟩
  let H := A.image (fun n : ℕ => (n : ZMod s))
  let R := H.image (fun x => t - x)
  have hdisjoint : Disjoint H R := by
    apply Finset.disjoint_left.mpr
    intro x hx hxR
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxR
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    apply hno u hu v hv
    rw [← hxy]
    exact sub_add_cancel t (v : ZMod s)
  have hR : R.card = H.card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    exact sub_right_inj.mp hxy
  have hhalf : 2 * H.card ≤ s := by
    have hh := Finset.card_le_card (Finset.subset_univ (H ∪ R))
    rw [Finset.card_union_of_disjoint hdisjoint, hR] at hh
    simpa only [Finset.card_univ, ZMod.card, two_mul] using hh
  obtain ⟨ha, hb⟩ := interval_card_le_residue_support A N s hs hA
  change A.card ≤ (N / s + 1) * H.card at ha
  change A.card ≤ N / s * H.card + N % s at hb
  have hq : 1 ≤ N / s := (Nat.one_le_div_iff hs).mpr hsN
  have hdecomp := Nat.mod_add_div N s
  have hmul := Nat.mul_le_mul_left (N / s) hhalf
  have hqs := Nat.mul_le_mul_right s hq
  by_cases hr : 2 * (N % s) ≤ s
  · nlinarith
  · have hmul' := Nat.mul_le_mul_left (N / s + 1) hhalf
    nlinarith

/-- More than two thirds of a positive initial interval contains two elements
whose sum is divisible by any prescribed modulus not exceeding the endpoint.
The two elements are allowed to agree, as rational-supply lists allow repeats. -/
theorem exists_pair_dvd_sum_of_two_thirds
    (G : Finset ℕ) (N s : ℕ) (hs : 0 < s) (hsN : s ≤ N)
    (hG : G ⊆ Finset.Icc 1 N) (hcard : 2 * N < 3 * G.card) :
    ∃ u ∈ G, ∃ v ∈ G, s ∣ u + v := by
  classical
  let : NeZero s := ⟨hs.ne'⟩
  let A := G.image (fun n => n - 1)
  have hA : A ⊆ Finset.range N := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hu1, huN⟩ := Finset.mem_Icc.mp (hG hu)
    exact Finset.mem_range.mpr (by omega)
  have hAc : A.card = G.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv huv
    change u - 1 = v - 1 at huv
    have hu1 := (Finset.mem_Icc.mp (hG hu)).1
    have hv1 := (Finset.mem_Icc.mp (hG hv)).1
    omega
  by_contra hn
  have hno : ∀ a ∈ A, ∀ b ∈ A,
      (a : ZMod s) + (b : ZMod s) ≠ (-2 : ZMod s) := by
    intro a ha b hb hab
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    have hu1 := (Finset.mem_Icc.mp (hG hu)).1
    have hv1 := (Finset.mem_Icc.mp (hG hv)).1
    apply hn
    refine ⟨u, hu, v, hv, ?_⟩
    apply (ZMod.natCast_eq_zero_iff (u + v) s).mp
    rw [Nat.cast_add]
    rw [Nat.cast_sub hu1, Nat.cast_sub hv1, Nat.cast_one] at hab
    linear_combination hab
  have hbound := interval_card_le_two_thirds_of_no_modular_pair A N s hs hsN
    hA (-2) hno
  rw [hAc] at hbound
  omega

end Problem337

end

end OAI
