import OAI.Combinatorics.EditDistance.PrimeDisplacement

namespace OAI

/-!
# Weighted direct sums and normalized slice maps
-/

namespace EditL1
open scoped BigOperators

abbrev L1 := lp (fun _ : ℕ => ℝ) 1
abbrev L1On (I : Type*) := lp (fun _ : I => ℝ) 1

lemma norm_eq_tsum {I : Type*} (f : L1On I) : ‖f‖ = ∑' i, |f i| := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) f

lemma summable_abs {I : Type*} (f : L1On I) : Summable (fun i => |f i|) := by
  simpa using (lp.memℓp f).summable (by norm_num : 0 < (1 : ENNReal).toReal)

noncomputable def reindex {I J : Type*} (e : I ≃ J) (f : L1On I) : L1On J :=
  ⟨fun j => f (e.symm j), memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs, Function.comp_def] using!
      (e.symm.summable_iff).mpr (summable_abs f))⟩

lemma reindex_apply {I J : Type*} (e : I ≃ J) (f : L1On I) (j : J) :
    reindex e f j = f (e.symm j) := rfl

lemma reindex_norm {I J : Type*} (e : I ≃ J) (f : L1On I) :
    ‖reindex e f‖ = ‖f‖ := by
  simp_rw [norm_eq_tsum, reindex_apply]
  exact e.symm.tsum_eq (fun i => |f i|)

lemma reindex_sub {I J : Type*} (e : I ≃ J) (f g : L1On I) :
    reindex e (f - g) = reindex e f - reindex e g := by
  ext j
  rfl

section FiniteSum
variable {I : Type*} [Fintype I]

lemma family_summable (f : I → L1) : Summable (fun a : I × ℕ => |f a.1 a.2|) :=
  (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
    ⟨fun i => summable_abs (f i), (hasSum_fintype _).summable⟩

noncomputable def familyLp (f : I → L1) : L1On (I × ℕ) :=
  ⟨fun a => f a.1 a.2, memℓp_gen (by simpa using family_summable f)⟩

lemma familyLp_apply (f : I → L1) (i : I) (n : ℕ) : familyLp f (i, n) = f i n := rfl

lemma familyLp_norm (f : I → L1) : ‖familyLp f‖ = ∑ i, ‖f i‖ := by
  rw [norm_eq_tsum]
  change (∑' a : I × ℕ, |f a.1 a.2|) = _
  rw [(family_summable f).tsum_prod, tsum_fintype]
  exact Finset.sum_congr rfl (fun i _ => (norm_eq_tsum (f i)).symm)

lemma familyLp_sub (f g : I → L1) : familyLp (f - g) = familyLp f - familyLp g := by
  ext ⟨i, n⟩
  rfl

variable [Nonempty I]

noncomputable def indexEquiv : (I × ℕ) ≃ ℕ := Classical.choice inferInstance

noncomputable def pack (f : I → L1) : L1 := reindex indexEquiv (familyLp f)

lemma pack_norm (f : I → L1) : ‖pack f‖ = ∑ i, ‖f i‖ := by
  rw [pack, reindex_norm, familyLp_norm]

lemma pack_sub (f g : I → L1) : pack (f - g) = pack f - pack g := by
  rw [pack, familyLp_sub, reindex_sub]
  rfl

lemma pack_distance (f g : I → L1) : ‖pack f - pack g‖ = ∑ i, ‖f i - g i‖ := by
  rw [← pack_sub, pack_norm]
  rfl

lemma weighted_pack_distance (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (f g : I → L1) :
    ‖pack (fun i => w i • f i) - pack (fun i => w i • g i)‖ =
      ∑ i, w i * ‖f i - g i‖ := by
  rw [pack_distance]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]

end FiniteSum
end EditL1

namespace EditAverage
lemma avg_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    avg (fun z : X × Y => f z.1 z.2) = avg (fun x => avg (f x)) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, ← Finset.sum_div,
    div_div]
  rw [mul_comm]
end EditAverage

namespace EditSlices
open scoped BigOperators
open EditAverage EditFourier

variable {J : Type*} [Fintype J] [DecidableEq J]
variable (G : J → Type*) [∀ j, AddCommGroup (G j)] [∀ j, Fintype (G j)]

omit [Fintype J] [∀ j, Fintype (G j)] in
lemma split_add_single (i : J) (x u : G i) (y : ∀ j : {j // j ≠ i}, G j) :
    (Equiv.piSplitAt i G).symm (x + u, y) =
      (Equiv.piSplitAt i G).symm (x, y) + Pi.single i u := by
  ext j
  by_cases h : j = i
  · subst j
    simp [Equiv.piSplitAt]
  · simp [Equiv.piSplitAt, h]

noncomputable def slice (H : (∀ j, G j) → EditL1.L1) (i : J) (ω : ℝ) : G i → EditL1.L1 :=
  fun x => EditL1.pack (fun y : (∀ j : {j // j ≠ i}, G j) =>
    (1 / (ω * Fintype.card (∀ j : {j // j ≠ i}, G j))) •
      H ((Equiv.piSplitAt i G).symm (x,y)))

lemma variation_slice (H : (∀ j, G j) → EditL1.L1) (i : J) (ω : ℝ) (hω : 0 < ω)
    (u : G i) : variation (slice G H i ω) u = variation H (Pi.single i u) / ω := by
  let Y := ∀ j : {j // j ≠ i}, G j
  let E := Equiv.piSplitAt i G
  have hY : 0 < (Fintype.card Y : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hweight : 0 ≤ 1 / (ω * (Fintype.card Y : ℝ)) := by positivity
  have hd (x : G i) :
      ‖slice G H i ω (x + u) - slice G H i ω x‖ =
        (1 / ω) * avg (fun y : Y => ‖H (E.symm (x,y) + Pi.single i u) - H (E.symm (x,y))‖) := by
    rw [slice, slice, EditL1.weighted_pack_distance (fun _ => _) (fun _ => hweight)]
    simp_rw [split_add_single]
    rw [← Finset.mul_sum, avg]
    dsimp [E, Y]
    ring
  have he : variation H (Pi.single i u) =
      avg (fun x : G i => avg (fun y : Y =>
        ‖H (E.symm (x,y) + Pi.single i u) - H (E.symm (x,y))‖)) := by
    rw [← avg_prod]
    exact (avg_equiv E.symm (fun z => ‖H (z + Pi.single i u) - H z‖)).symm
  change avg (fun x => ‖slice G H i ω (x + u) - slice G H i ω x‖) = _
  simp_rw [hd]
  rw [avg_mul, ← he]
  ring

end EditSlices

end OAI
