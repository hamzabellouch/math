import OAI.MeasureTheory.Falconer.Geometry.ScalarGridThinning
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! Choosing the intermediate dyadic scale from the closest pair of a
 finite separated set. The entire set is separated at that scale, and
 two original points witness that the scale is not unnecessarily coarse. -/
namespace Falconer

 theorem scalar_closest_pair (E : Finset ℝ) (hE : 2 ≤ E.card) :
    ∃ x ∈ E, ∃ y ∈ E, x ≠ y ∧
      ∀ u ∈ E, ∀ v ∈ E, u ≠ v → |x-y| ≤ |u-v| := by
  classical
  let P := (E.product E).filter (fun p => p.1 ≠ p.2)
  have hP : P.Nonempty := by
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < E.card by omega)
    exact ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hxy⟩⟩
  obtain ⟨p,hp,hmin⟩ := P.exists_min_image (fun p => |p.1-p.2|) hP
  have hp' := Finset.mem_filter.mp hp
  have hpp := Finset.mem_product.mp hp'.1
  refine ⟨p.1,hpp.1,p.2,hpp.2,hp'.2,?_⟩
  intro u hu v hv huv
  exact hmin (u,v) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu,hv⟩,huv⟩)

 theorem scalar_closest_dyadic_scale (E : Finset ℝ) (hE : 2 ≤ E.card)
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, |x-y| ≤ 16) :
    ∃ n : ℕ, (∀ x ∈ E, ∀ y ∈ E, x ≠ y → 8*(1/2:ℝ)^n < |x-y|) ∧
      ∃ x ∈ E, ∃ y ∈ E, x ≠ y ∧ |x-y| ≤ 16*(1/2:ℝ)^n := by
  obtain ⟨x,hx,y,hy,hxy,hmin⟩ := scalar_closest_pair E hE
  have hg : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨n,hn0,hn1⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < |x-y|/16 by positivity)
    (show |x-y|/16 ≤ 1 by linarith [hdiam x hx y hy])
    (show 0 < (1/2:ℝ) by norm_num) (show (1/2:ℝ) < 1 by norm_num)
  rw [pow_succ] at hn0
  refine ⟨n,?_,x,hx,y,hy,hxy,by linarith⟩
  intro u hu v hv huv
  have hh := hmin u hu v hv huv
  linarith

 theorem scalar_dyadic_scale_indices (n lo hi : ℕ) (g : ℝ)
    (hn0 : 8*(1/2:ℝ)^n < g) (hn1 : g ≤ 16*(1/2:ℝ)^n)
    (hlo : g ≤ (1/2:ℝ)^lo) (hhi : 1024*(1/2:ℝ)^hi ≤ g) :
    lo+3 < n ∧ n+6 ≤ hi := by
  constructor
  · by_contra hn
    have hh : (1/2:ℝ)^(lo+3) ≤ (1/2:ℝ)^n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have he : (1/2:ℝ)^(lo+3) = (1/2:ℝ)^lo/8 := by rw [pow_add]; norm_num; ring
    rw [he] at hh
    linarith
  · by_contra hn
    have hh : (1/2:ℝ)^(n+5) ≤ (1/2:ℝ)^hi :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have he : (1/2:ℝ)^(n+5) = (1/2:ℝ)^n/32 := by rw [pow_add]; norm_num; ring
    rw [he] at hh
    have hp : 0 < (1/2:ℝ)^n := pow_pos (by norm_num) _
    nlinarith

end Falconer

end OAI
