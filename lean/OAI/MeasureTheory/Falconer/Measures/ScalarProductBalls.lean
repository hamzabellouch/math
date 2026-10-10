import OAI.MeasureTheory.Falconer.Radial.ScalarAffineFibers

namespace OAI

/-! Fine-scale ball bounds for a Cartesian product of separated scalar
sets, with its actual Euclidean embedding. -/
namespace Falconer

theorem scalar_interval_card {δ r : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (X : Finset ℝ) (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) (z : ℝ) :
    ((X.filter fun x => |x-z| ≤ r).card : ℝ) ≤ 9*r/δ := by
  classical
  let t := 2*r/δ
  let k := ⌈t⌉₊
  have hr0 : 0 < r := hδ.trans_le hr
  have ht : 0 ≤ t := div_nonneg (by positivity) hδ.le
  have hk : 2*r ≤ (k : ℝ)*δ := (div_le_iff₀ hδ).1 (Nat.le_ceil t)
  have hn := scalar_affine_fiber_card (δ := r) (u := -z) (v := 1) hδ zero_lt_one
    (by norm_num) (X.filter fun x => |x-z| ≤ r)
    (fun x hx y hy hne => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne)
    (fun x hx => by simpa only [mul_one,neg_add_eq_sub] using (Finset.mem_filter.mp hx).2)
    k (by simpa only [mul_one] using hk)
  have hnR : ((X.filter fun x => |x-z| ≤ r).card : ℝ) ≤ 2*(k : ℝ)+3 := by exact_mod_cast hn
  have hku : (k : ℝ) < t+1 := Nat.ceil_lt_add_one ht
  have hrd : 1 ≤ r/δ := (le_div_iff₀ hδ).2 (by simpa using hr)
  dsimp [t] at hku
  have hku' : (k : ℝ) < 2*(r/δ)+1 := by simpa only [mul_div_assoc] using hku
  rw [mul_div_assoc]
  linarith

noncomputable def scalarProductPoints (X Y : Finset ℝ) : Finset (Space 2) :=
  (X ×ˢ Y).image fun p => rowPoint p.1 p.2

theorem rowPoint_pair_injective : Function.Injective (fun p : ℝ × ℝ => rowPoint p.1 p.2) := by
  intro p q h
  have h0 := congrArg (fun v : Space 2 => v 0) h
  have h1 := congrArg (fun v : Space 2 => v 1) h
  exact Prod.ext h0 h1

theorem scalarProductPoints_card (X Y : Finset ℝ) :
    (scalarProductPoints X Y).card = X.card*Y.card := by
  rw [scalarProductPoints,Finset.card_image_of_injective _ rowPoint_pair_injective,Finset.card_product]

theorem scalarProductPoints_ball_card (X Y : Finset ℝ) (z : Space 2) (r : ℝ) :
    ((scalarProductPoints X Y).filter fun p => dist p z ≤ r).card ≤
      (X.filter (fun x => |x-z 0| ≤ r)).card*(Y.filter (fun y => |y-z 1| ≤ r)).card := by
  classical
  let U := X.filter fun x => |x-z 0| ≤ r
  let V := Y.filter fun y => |y-z 1| ≤ r
  have hsub : (scalarProductPoints X Y).filter (fun p => dist p z ≤ r) ⊆ scalarProductPoints U V := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    have h0 : |x-z 0| ≤ r := by
      have hh := (PiLp.dist_apply_le (rowPoint x y) z 0).trans hpr
      simpa only [rowPoint_zero,Real.dist_eq] using hh
    have h1 : |y-z 1| ≤ r := by
      have hh := (PiLp.dist_apply_le (rowPoint x y) z 1).trans hpr
      simpa only [rowPoint_one,Real.dist_eq] using hh
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hx,h0⟩,Finset.mem_filter.mpr ⟨hy,h1⟩⟩,rfl⟩
  exact (Finset.card_le_card hsub).trans_eq (scalarProductPoints_card U V)

theorem scalarProductPoints_fine_ball {δ r : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (X : Finset ℝ) (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) (z : Space 2) :
    (((scalarProductPoints X X).filter fun p => dist p z ≤ r).card : ℝ) ≤ 81*(r/δ)^2 := by
  have hc : (((scalarProductPoints X X).filter fun p => dist p z ≤ r).card : ℝ) ≤
      ((X.filter fun x => |x-z 0| ≤ r).card : ℝ)*((X.filter fun y => |y-z 1| ≤ r).card : ℝ) := by
    exact_mod_cast scalarProductPoints_ball_card X X z r
  have h0 := scalar_interval_card hδ hr X hsep (z 0)
  have h1 := scalar_interval_card hδ hr X hsep (z 1)
  have hr0 : 0 ≤ r := hδ.le.trans hr
  have hb := hc.trans (mul_le_mul h0 h1 (Nat.cast_nonneg _) (by positivity))
  convert hb using 1
  ring

end Falconer

end OAI
