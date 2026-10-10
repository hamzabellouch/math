import OAI.NumberTheory.JointDickman.Arithmetic.SieveRectangleCRT
import OAI.NumberTheory.JointDickman.Arithmetic.WeightedUpperSieve
import OAI.NumberTheory.JointDickman.Arithmetic.SieveRemainders

namespace OAI

/-! # Rectangle sieve with an explicit arithmetic remainder -/

namespace JointDickman

open Finset

noncomputable def pairRootEvents (P : Finset ℕ)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (r s : ℕ) : Finset ℕ :=
  P.filter (fun p => ((r : ZMod p), (s : ZMod p)) ∈ A p)

/-- Actual intersections in a rectangle have the CRT error. -/
theorem pair_root_sieve_remainder (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    {D : Finset ℕ} (hD : D ⊆ P) :
    |sieveRemainder
      (fun n : (Ico a b) × (Ico c d) => pairRootEvents P A n.1 n.2)
      (fun _ => 1) (((b : ℝ) - a) * ((d : ℝ) - c))
      (fun p => ((A p).card : ℝ) / (p : ℝ) ^ 2) D| ≤
        2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ p ∈ D, (p : ℝ)) + 2) *
          ∏ p ∈ D, ((A p).card : ℝ) := by
  classical
  have hcond (r s : ℕ) : D ⊆ pairRootEvents P A r s ↔
      ∀ p ∈ D, ((r : ZMod p), (s : ZMod p)) ∈ A p := by
    constructor
    · intro h p hp
      exact (mem_filter.mp (h hp)).2
    · intro h p hp
      exact mem_filter.mpr ⟨hD hp, h p hp⟩
  unfold sieveRemainder sieveIntersection
  simp_rw [hcond]
  rw [Fintype.sum_prod_type]
  have hout : (∑ r : Ico a b, ∑ s : Ico c d,
      if ∀ p ∈ D, ((r.val : ZMod p), (s.val : ZMod p)) ∈ A p then (1 : ℝ) else 0) =
      ∑ r ∈ Ico a b, ∑ s ∈ Ico c d,
        if ∀ p ∈ D, ((r : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0 := by
    apply Eq.trans _ ((Ico a b).sum_coe_sort (fun r : ℕ =>
      ∑ s ∈ Ico c d, if ∀ p ∈ D, ((r : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0))
    apply sum_congr rfl
    intro r _
    exact (Ico c d).sum_coe_sort (fun s : ℕ =>
      if ∀ p ∈ D, ((r.val : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0)
  rw [hout]
  exact prime_pair_rectangle_error D (fun p hp => hP p (hD hp)) A hab hcd

/-- With at most `k*p` local residue pairs, the denominator in the CRT
error cancels. This includes unions of at most `k` affine lines. -/
theorem pair_root_sieve_remainder_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (k : ℕ)
    (hA : ∀ p ∈ P, (A p).card ≤ k * p)
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    {D : Finset ℕ} (hD : D ⊆ P) :
    |sieveRemainder
      (fun n : (Ico a b) × (Ico c d) => pairRootEvents P A n.1 n.2)
      (fun _ => 1) (((b : ℝ) - a) * ((d : ℝ) - c))
      (fun p => ((A p).card : ℝ) / (p : ℝ) ^ 2) D| ≤
        2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * ∏ p ∈ D, (p : ℝ)) *
          (k : ℝ) ^ D.card := by
  have hprod : 0 < ∏ p ∈ D, (p : ℝ) := prod_pos (fun p hp => by
    exact_mod_cast (hP p (hD hp)).pos)
  have hL : 0 ≤ ((b : ℝ) - a) + ((d : ℝ) - c) := add_nonneg
    (sub_nonneg.mpr (by exact_mod_cast hab)) (sub_nonneg.mpr (by exact_mod_cast hcd))
  have hcount : (∏ p ∈ D, ((A p).card : ℝ)) ≤
      (k : ℝ) ^ D.card * ∏ p ∈ D, (p : ℝ) := by
    calc
      _ ≤ ∏ p ∈ D, (k : ℝ) * p := prod_le_prod₀ (by intros; positivity)
        (fun p hp => by exact_mod_cast hA p (hD hp))
      _ = _ := by rw [prod_mul_distrib]; simp
  apply (pair_root_sieve_remainder P hP A hab hcd hD).trans
  calc
    _ ≤ 2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ p ∈ D, (p : ℝ)) + 2) *
        ((k : ℝ) ^ D.card * ∏ p ∈ D, (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by field_simp

private theorem sum_rectangle_subtype (a b c d : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ x : (Ico a b) × (Ico c d), F x.1 x.2) =
      ∑ r ∈ Ico a b, ∑ s ∈ Ico c d, F r s := by
  rw [Fintype.sum_prod_type]
  have hin (r : Ico a b) : (∑ s : Ico c d, F r s) = ∑ s ∈ Ico c d, F r s :=
    (Ico c d).sum_coe_sort (fun s => F r s)
  simp_rw [hin]
  exact (Ico a b).sum_coe_sort (fun r => ∑ s ∈ Ico c d, F r s)

/-- The weighted rectangle sieve, with all intersection errors evaluated.
The only analytic assumptions are the cited Ford and Mertens inputs. -/
theorem weighted_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (A : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (θ : ℕ → ℝ)
      (a b c d Z : ℕ), a ≤ b → c ≤ d → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p ∈ P, (A p).card ≤ k * p) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p ∈ pairRootEvents P A r s, θ p) ≤
        C * ((b : ℝ) - a) * ((d : ℝ) - c) *
          (∏ p ∈ P, (1 - ((A p).card : ℝ) / (p : ℝ) ^ 2 +
            ((A p).card : ℝ) / (p : ℝ) ^ 2 * θ p)) +
        2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_upper_sieve_from_published hFord hM
    (show (0 : ℝ) < k by exact_mod_cast hk)
  refine ⟨C, hC, ?_⟩
  intro P A θ a b c d Z hab hcd hZ hP hA hθ
  let E := fun x : (Ico a b) × (Ico c d) => pairRootEvents P A x.1 x.2
  let g := fun p => ((A p).card : ℝ) / (p : ℝ) ^ 2
  let L := ((b : ℝ) - a) + ((d : ℝ) - c)
  have hL : 0 ≤ L := add_nonneg (sub_nonneg.mpr (by exact_mod_cast hab))
    (sub_nonneg.mpr (by exact_mod_cast hcd))
  have hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ (k : ℝ) / p := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    have hcard : ((A p).card : ℝ) ≤ (k : ℝ) * p := by exact_mod_cast hA p hp
    have hkp : 2 * (k : ℝ) ≤ p := by exact_mod_cast (hP p hp).2.2
    have hsmall : g p ≤ (k : ℝ) / p := by
      calc
        _ ≤ ((k : ℝ) * p) / (p : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hcard (sq_nonneg _)
        _ = _ := by field_simp
    refine ⟨by dsimp [g]; positivity, ?_, hsmall⟩
    exact hsmall.trans ((div_le_iff₀ hp0).mpr (by linarith))
  have h := hbound ((Ico a b) × (Ico c d)) P E (fun _ => 1)
    (((b : ℝ) - a) * ((d : ℝ) - c)) Z g θ (by exact_mod_cast hZ)
    (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hab))
      (sub_nonneg.mpr (by exact_mod_cast hcd))) (by intros; norm_num)
    (fun p hp => ⟨(hP p hp).1, by exact_mod_cast (hP p hp).2.1⟩)
    (fun x => filter_subset _ _) hg hθ
  simp only [one_mul] at h
  have hleft : (∑ x : (Ico a b) × (Ico c d), ∏ p ∈ E x, θ p) =
      ∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p ∈ pairRootEvents P A r s, θ p :=
    sum_rectangle_subtype a b c d (fun r s => ∏ p ∈ pairRootEvents P A r s, θ p)
  rw [hleft] at h
  have heq : P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ (Z : ℝ)) =
      P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z) := by
    ext D
    simp only [mem_filter, Nat.cast_le]
  rw [heq] at h
  have hrem : (∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z),
      |sieveRemainder E (fun _ => 1) (((b : ℝ) - a) * ((d : ℝ) - c)) g D|) ≤
      2 * (L + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
    calc
      _ ≤ ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z),
          2 * (L + 2 * Z) * (k : ℝ) ^ D.card := by
        apply sum_le_sum
        intro D hD
        have hDP := mem_powerset.mp (mem_filter.mp hD).1
        have hdZ : (∏ p ∈ D, (p : ℝ)) ≤ Z := by
          rw [← Nat.cast_prod]
          exact_mod_cast (mem_filter.mp hD).2
        apply (pair_root_sieve_remainder_le P (fun p hp => (hP p hp).1) A k hA hab hcd hDP).trans
        dsimp only [L]
        nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) k) D.card]
      _ = 2 * (L + 2 * Z) * ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z),
          (k : ℝ) ^ D.card := (mul_sum _ _ _).symm
      _ ≤ 2 * (L + 2 * Z) * ((Z + 1 : ℝ) * (Z : ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast sieve_level_power_sum P (fun p hp => (hP p hp).1) k Z
      _ = _ := by ring
  apply h.trans
  dsimp only [g, L] at hrem ⊢
  simpa only [mul_assoc] using add_le_add le_rfl hrem

end JointDickman

end OAI
