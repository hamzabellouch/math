import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.PolygonArithmetic

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section QuadraticRectangleCounts
open Classical

theorem conjugateStrip_floor_inj (y b : ℝ) (hb : 0<b) :
    Set.InjOn (fun u : CutRing => ⌊b*ordinary u⌋)
      {u | conjugate u∈Set.Icc y (y+b)} := by
  intro u hu w hw he
  change ⌊b*ordinary u⌋=⌊b*ordinary w⌋ at he
  by_contra hne
  have hn := one_le_abs_cut_norm (sub_ne_zero.mpr hne)
  simp only [map_sub,abs_mul] at hn
  have hc : |conjugate u-conjugate w|≤b := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1,hu.2,hw.1,hw.2]
  have h₁ := Int.floor_le (b*ordinary u)
  have h₂ := Int.lt_floor_add_one (b*ordinary u)
  have h₃ := Int.floor_le (b*ordinary w)
  have h₄ := Int.lt_floor_add_one (b*ordinary w)
  rw [he] at h₁ h₂
  have hlt : |b*(ordinary u-ordinary w)|<1 := by
    apply abs_lt.mpr
    constructor <;> nlinarith
  rw [abs_mul,abs_of_pos hb] at hlt
  nlinarith [abs_nonneg (ordinary u-ordinary w)]

def cutRectangle (x y a b : ℝ) : Set CutRing :=
  {u | ordinary u∈Set.Icc x (x+a) ∧ conjugate u∈Set.Icc y (y+b)}

theorem cutRectangle_finite (x y a b : ℝ) (hb : 0<b) : (cutRectangle x y a b).Finite := by
  have him : ((fun u : CutRing => ⌊b*ordinary u⌋) '' cutRectangle x y a b).Finite := by
    apply (Set.finite_Icc ⌊b*x⌋ ⌊b*(x+a)⌋).subset
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨Int.floor_mono (mul_le_mul_of_nonneg_left hu.1.1 hb.le),
      Int.floor_mono (mul_le_mul_of_nonneg_left hu.1.2 hb.le)⟩
  exact him.of_finite_image (fun _ hu _ hw he =>
    conjugateStrip_floor_inj y b hb hu.2 hw.2 he)

theorem cutRectangle_card_floor (S : Finset CutRing) (x y a b : ℝ) (hb : 0<b)
    (hS : ∀u∈S,u∈cutRectangle x y a b) :
    S.card≤(⌊b*(x+a)⌋+1-⌊b*x⌋).toNat := by
  have hinj : Set.InjOn (fun u : CutRing => ⌊b*ordinary u⌋) (↑S) := by
    intro u hu w hw he
    exact conjugateStrip_floor_inj y b hb (hS u hu).2 (hS w hw).2 he
  rw [← Int.card_Icc,← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro t ht
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_Icc.mpr
    ⟨Int.floor_mono (mul_le_mul_of_nonneg_left (hS u hu).1.1 hb.le),
      Int.floor_mono (mul_le_mul_of_nonneg_left (hS u hu).1.2 hb.le)⟩

theorem cutRectangle_card_bound (S : Finset CutRing) (x y a b : ℝ)
    (ha : 0≤a) (hb : 0<b) (hS : ∀u∈S,u∈cutRectangle x y a b) :
    (S.card:ℝ)<a*b+2 := by
  have hc := cutRectangle_card_floor S x y a b hb hS
  have hle : ⌊b*x⌋≤⌊b*(x+a)⌋ := Int.floor_mono (by nlinarith)
  have hnon : 0≤⌊b*(x+a)⌋+1-⌊b*x⌋ := by omega
  have hc' : (S.card:ℤ)≤⌊b*(x+a)⌋+1-⌊b*x⌋ := by
    rw [← Int.toNat_of_nonneg hnon]
    exact_mod_cast hc
  have hc'' : (S.card:ℝ)≤(⌊b*(x+a)⌋:ℝ)+1-(⌊b*x⌋:ℝ) := by exact_mod_cast hc'
  have h₁ := Int.floor_le (b*(x+a))
  have h₂ := Int.lt_floor_add_one (b*x)
  nlinarith

end QuadraticRectangleCounts

end SimpleAmenable
end
end

end OAI
