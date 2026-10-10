import OAI.NumberTheory.Ostmann.Quadratic.KernelPairIdentification
import OAI.NumberTheory.Ostmann.Tree.PairPopulationFibers
import OAI.NumberTheory.Ostmann.Quadratic.KernelPairPopulationBound

namespace OAI

/-! # Endpoint-pair counts for a fixed product of disjoint kernels -/

namespace Ostmann

open scoped Classical

theorem endpoint_kernel_product_count (S T : Finset ℤ) (f g : ℤ → ℤ) (d : ℤ)
    (hS : ∀ x ∈ S, f x ≠ 0)
    (hcross : ∀ x ∈ S, ∀ y ∈ T, (f x).natAbs.Coprime (g y).natAbs)
    (K : ℝ) (hK : 0 ≤ K)
    (hpop : ∀ u ∈ S.image f, ∀ v ∈ T.image g, u * v = d →
      ((S.filter fun x => f x = u).card : ℝ) * (T.filter fun y => g y = v).card ≤ K) :
    (Fintype.card {z : S × T // f z.1 * g z.2 = d} : ℝ) ≤ 2 * K := by
  let A := S.image f
  let B := T.image g
  let F : S → A := fun x => ⟨f x, Finset.mem_image.mpr ⟨x, x.property, rfl⟩⟩
  let G : T → B := fun y => ⟨g y, Finset.mem_image.mpr ⟨y, y.property, rfl⟩⟩
  have hA (u : ℤ) (hu : u ∈ A) : u ≠ 0 := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact hS x hx
  have hAB (u : ℤ) (hu : u ∈ A) (v : ℤ) (hv : v ∈ B) : u.natAbs.Coprime v.natAbs := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    exact hcross x hx y hy
  have hlabels : (Fintype.card {z : A × B // (z.1 : ℤ) * (z.2 : ℤ) = d} : ℝ) ≤ 2 := by
    exact_mod_cast kernel_product_fiber_card_le_two A B d hA hAB
  have hpops (q : {z : A × B // (z.1 : ℤ) * (z.2 : ℤ) = d}) :
      (Fintype.card {x : S // F x = q.1.1} : ℝ) * Fintype.card {y : T // G y = q.1.2} ≤ K := by
    have eF : {x : S // F x = q.1.1} ≃ {x : S // f x = (q.1.1 : ℤ)} :=
      Equiv.subtypeEquivRight (fun _ => Subtype.ext_iff)
    have eG : {y : T // G y = q.1.2} ≃ {y : T // g y = (q.1.2 : ℤ)} :=
      Equiv.subtypeEquivRight (fun _ => Subtype.ext_iff)
    rw [Fintype.card_congr eF, Fintype.card_congr eG]
    have hF := finset_fiber_card S f (q.1.1 : ℤ)
    have hG := finset_fiber_card T g (q.1.2 : ℤ)
    simp only [Fintype.card_eq_nat_card] at hF hG ⊢
    rw [hF, hG]
    exact hpop q.1.1 q.1.1.property q.1.2 q.1.2.property q.2
  have hb := filteredPair_card_le F G (fun u v => (u : ℤ) * (v : ℤ) = d) K 2 hK
    (by simpa only [Fintype.card_eq_nat_card] using hlabels)
    (by simpa only [Fintype.card_eq_nat_card] using hpops)
  simpa only [Fintype.card_eq_nat_card] using hb

/-- The exceptional signed product accounts for few endpoint pairs. The bound
is uniform over the two finite endpoint sets and their affine square roots. -/
theorem exists_endpoint_kernel_product_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset ℤ) (f g : ℤ → ℤ)
      (r s : ℤ → ℕ) (m : ℕ) (h d : ℤ) (X : ℝ),
      0 < m → 0 ≤ X →
      (∀ x ∈ S, f x ≠ 0) → (∀ y ∈ T, g y ≠ 0) →
      h.natAbs.Coprime m →
      (∀ x ∈ S, f x * (r x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ y ∈ T, g y * (s y : ℤ) ^ 2 = (m : ℤ) * y - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ S, ∀ y ∈ T, (f x).natAbs.Coprime (g y).natAbs) →
      (Fintype.card {z : S × T // f z.1 * g z.2 = d} : ℝ) ≤
        C * (X / Real.sqrt |(d : ℝ)| + 2 * Real.sqrt (X * m) + m) := by
  obtain ⟨C, hC, hpop⟩ := exists_kernel_population_uniform_bound
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  intro S T f g r s m h d X hm hX hf hg hred hr hs hspanS hspanT hcross
  let K := C ^ 2 * (X / Real.sqrt |(d : ℝ)| + 2 * Real.sqrt (X * m) + m)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb := endpoint_kernel_product_count S T f g d hf hcross K hK (by
    intro u hu v hv huv
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
    have hu0 : u ≠ 0 := hxu ▸ hf x hx
    have hv0 : v ≠ 0 := hyv ▸ hg y hy
    have hau : (1 : ℝ) ≤ |(u : ℝ)| := by
      have hn : 1 ≤ u.natAbs := Int.natAbs_pos.mpr hu0
      have hh : (1 : ℝ) ≤ u.natAbs := by exact_mod_cast hn
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
    have hav : (1 : ℝ) ≤ |(v : ℝ)| := by
      have hn : 1 ≤ v.natAbs := Int.natAbs_pos.mpr hv0
      have hh : (1 : ℝ) ≤ v.natAbs := by exact_mod_cast hn
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
    have hS := hpop (S.filter fun x => f x = u) r m h u X hm hu0 hred
      (by intro x hx; obtain ⟨hx, he⟩ := Finset.mem_filter.mp hx; rw [← he]; exact hr x hx)
      (by intro x hx y hy; exact hspanS x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
    have hT := hpop (T.filter fun y => g y = v) s m h v X hm hv0 hred
      (by intro y hy; obtain ⟨hy, he⟩ := Finset.mem_filter.mp hy; rw [← he]; exact hs y hy)
      (by intro x hx y hy; exact hspanT x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
    have hprod : |(u : ℝ)| * |(v : ℝ)| = |(d : ℝ)| := by
      rw [← abs_mul, ← Int.cast_mul, huv]
    calc
      _ ≤ (C * (Real.sqrt (X / |(u : ℝ)|) + Real.sqrt m)) *
          (C * (Real.sqrt (X / |(v : ℝ)|) + Real.sqrt m)) :=
        mul_le_mul hS hT (Nat.cast_nonneg _) (by positivity)
      _ ≤ C ^ 2 * (X / Real.sqrt (|(u : ℝ)| * |(v : ℝ)|) +
          2 * Real.sqrt (X * m) + m) :=
        root_population_product_bound X m |(u : ℝ)| |(v : ℝ)| C hX (Nat.cast_nonneg _) hau hav
      _ = K := by rw [hprod])
  convert hb using 1
  dsimp [K]
  ring

end Ostmann

end OAI
