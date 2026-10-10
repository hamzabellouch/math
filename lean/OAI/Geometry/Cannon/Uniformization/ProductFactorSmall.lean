import Mathlib
import OAI.Geometry.Cannon.Uniformization.EventualRelativeShrink
import OAI.Geometry.Cannon.Conformal.Distinct

namespace OAI

section
section
section
namespace CannonDistortion
open CannonQM Metric
open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

lemma product_factor_small {a b c d r : ℝ}
    (ha : 0<a) (_hb : 0<b) (_hc : 0<c) (hd : 0<d) (hr : 0<r)
    (hp : a*b ≤ r*(c*d)) :
    a ≤ Real.sqrt r*c ∨ b ≤ Real.sqrt r*d := by
  by_contra! hn
  have hs : 0<Real.sqrt r := Real.sqrt_pos.mpr hr
  have hm := mul_lt_mul hn.1 hn.2.le (mul_pos hs hd) ha.le
  have he : (Real.sqrt r*c)*(Real.sqrt r*d)=r*(c*d) := by
    calc
      _ = (Real.sqrt r)^2*(c*d) := by ring
      _ = _ := by rw [Real.sq_sqrt hr.le]
  rw [he] at hm
  exact (not_lt_of_ge hp) hm

lemma bounded_product {a b c d S L : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (_hd : 0 ≤ d) (hS : 0 ≤ S) (hL : 0 ≤ L)
    (hLa : a ≤ L*c) (hLb : b ≤ L*d) (hs : a ≤ S*c ∨ b ≤ S*d) :
    a*b ≤ S*L*(c*d) := by
  rcases hs with h|h
  · have hh := mul_le_mul h hLb hb (mul_nonneg hS hc)
    nlinarith
  · have hh := mul_le_mul hLa h hb (mul_nonneg hL hc)
    nlinarith

theorem power_control_crossRatio (f : X → Y) (hf : Function.Injective f)
    {K α β : ℝ} (hK : 0<K) (hα : 0<α) (hβ : 0<β) (hab : α ≤ β)
    (hcontrol : ∀ t : ℝ, 0 ≤ t → ∀ x a b : X, dist x a ≤ t*dist x b →
      dist (f x) (f a) ≤ K*powerGauge α β t*dist (f x) (f b))
    (x y z w : X) (hh : Distinct x y z w) :
    (crossRatio (f x) (f y) (f z) (f w) : ℝ)  ≤
      (K^2*5^β)*powerGauge (α/2) (3*β/2) (crossRatio x y z w) := by
  let r : ℝ := crossRatio x y z w
  have hr : 0<r := by exact_mod_cast crossRatio_pos hh
  have hden : 0<dist x w*dist y z := mul_pos (dist_pos.mpr hh.2.2.1) (dist_pos.mpr hh.2.2.2.1)
  have hprod : dist x y*dist z w=r*(dist x w*dist y z) := by
    exact (div_mul_cancel₀ _ hden.ne').symm
  have hprod' : dist x y*dist z w ≤ max r 1*(dist x w*dist y z) := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hden.le
  have hfh := hh.map hf
  have hfden : 0<dist (f x) (f w)*dist (f y) (f z) :=
    mul_pos (dist_pos.mpr hfh.2.2.1) (dist_pos.mpr hfh.2.2.2.1)
  let s := Real.sqrt r
  let L := 5*max r 1
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hL : 0 ≤ L := by dsimp [L]; nlinarith [le_max_right r 1]
  have hbig : 2*max r 1+3 ≤ L := by dsimp [L]; nlinarith [le_max_right r 1]
  have hKs : 0 ≤ K*powerGauge α β s := mul_nonneg hK.le (powerGauge_nonneg hs)
  have hKL : 0 ≤ K*powerGauge α β L := mul_nonneg hK.le (powerGauge_nonneg hL)
  have htarget : dist (f x) (f y)*dist (f z) (f w)  ≤
      (K*powerGauge α β s)*(K*powerGauge α β L)*(dist (f x) (f w)*dist (f y) (f z)) := by
    rcases CannonMetricQC.crossRatio_pair_bounds x y z w hh (le_max_right _ _) hprod' with hpair|hpair
    · have haL := hcontrol L hL x y w (hpair.1.trans (mul_le_mul_of_nonneg_right hbig dist_nonneg))
      have hbL := hcontrol L hL z w y (by
        rw [dist_comm z y]
        exact hpair.2.trans (mul_le_mul_of_nonneg_right hbig dist_nonneg))
      rw [dist_comm (f z) (f y)] at hbL
      have hsmall := product_factor_small (dist_pos.mpr hh.1) (dist_pos.mpr hh.2.2.2.2.2)
        (dist_pos.mpr hh.2.2.1) (dist_pos.mpr hh.2.2.2.1) hr hprod.le
      apply bounded_product dist_nonneg dist_nonneg dist_nonneg dist_nonneg hKs hKL haL hbL
      rcases hsmall with h|h
      · exact Or.inl (hcontrol s hs x y w h)
      · exact Or.inr (by simpa only [dist_comm] using hcontrol s hs z w y (by simpa only [dist_comm] using h))
    · have haL := hcontrol L hL y x z (by
        rw [dist_comm y x]
        exact hpair.1.trans (mul_le_mul_of_nonneg_right hbig dist_nonneg))
      have hbL := hcontrol L hL w z x (by
        rw [dist_comm w z,dist_comm w x]
        exact hpair.2.trans (mul_le_mul_of_nonneg_right hbig dist_nonneg))
      rw [dist_comm (f y) (f x)] at haL
      rw [dist_comm (f w) (f z),dist_comm (f w) (f x)] at hbL
      have hsmall := product_factor_small (dist_pos.mpr hh.1) (dist_pos.mpr hh.2.2.2.2.2)
        (dist_pos.mpr hh.2.2.2.1) (dist_pos.mpr hh.2.2.1) hr (by nlinarith [hprod])
      have he := bounded_product (a:=dist (f x) (f y)) (b:=dist (f z) (f w))
        dist_nonneg dist_nonneg dist_nonneg dist_nonneg hKs hKL haL hbL (by
        rcases hsmall with h|h
        · exact Or.inl (by simpa only [dist_comm] using hcontrol s hs y x z (by simpa only [dist_comm] using h))
        · exact Or.inr (by simpa only [dist_comm] using hcontrol s hs w z x (by simpa only [dist_comm] using h)))
      simpa only [mul_comm (dist (f y) (f z)) (dist (f x) (f w))] using he
  have hratio : (crossRatio (f x) (f y) (f z) (f w) : ℝ) ≤
      K^2*(powerGauge α β s*powerGauge α β L) := by
    change dist (f x) (f y)*dist (f z) (f w)/(dist (f x) (f w)*dist (f y) (f z)) ≤ _
    apply (div_le_iff₀ hfden).mpr
    calc
      _ ≤ (K*powerGauge α β s)*(K*powerGauge α β L)*(dist (f x) (f w)*dist (f y) (f z)) := htarget
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left (mixed_power_bound hα hβ hab hr) (sq_nonneg K)
  exact hratio.trans (by simpa only [s,L,mul_assoc] using hm)

theorem power_control_quasiMobius (f : X → Y) (hf : Function.Injective f)
    {K α β : ℝ} (hK : 0<K) (hα : 0<α) (hβ : 0<β) (hab : α ≤ β)
    (hcontrol : ∀ t : ℝ, 0 ≤ t → ∀ x a b : X, dist x a ≤ t*dist x b →
      dist (f x) (f a) ≤ K*powerGauge α β t*dist (f x) (f b)) : QuasiMobius f := by
  let C : ℝ≥0 := ⟨K^2*5^β,by positivity⟩
  have hC : 0<C := by change (0:ℝ)<K^2*5^β; positivity
  refine ⟨powerIso C hC (α/2) (3*β/2) (by positivity) (by positivity),?_⟩
  intro x y z w hh
  apply NNReal.coe_le_coe.mp
  rw [powerIso_coe]
  exact power_control_crossRatio f hf hK hα hβ hab hcontrol x y z w hh

end CannonDistortion

end
end
end

end OAI
