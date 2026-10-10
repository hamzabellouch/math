import Mathlib
import OAI.Geometry.Cannon.Conformal.Sphere

namespace OAI

section
section
section
section
noncomputable section
namespace CannonQM
open Metric
open scoped NNReal

def Distinct {X : Type*} (x y z w : X) : Prop :=
  x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w

lemma Distinct.map {X Y : Type*} {f : X → Y} (hf : Function.Injective f)
    {x y z w : X} (h : Distinct x y z w) : Distinct (f x) (f y) (f z) (f w) := by
  rcases h with ⟨hxy,hxz,hxw,hyz,hyw,hzw⟩
  exact ⟨fun h => hxy (hf h),fun h => hxz (hf h),fun h => hxw (hf h),
    fun h => hyz (hf h),fun h => hyw (hf h),fun h => hzw (hf h)⟩

lemma Distinct.flip {X : Type*} {x y z w : X} (h : Distinct x y z w) : Distinct x w z y := by
  rcases h with ⟨hxy,hxz,hxw,hyz,hyw,hzw⟩
  exact ⟨hxw,hxz,hxy,hzw.symm,hyw.symm,hyz.symm⟩

lemma nndist_pos {X : Type*} [MetricSpace X] {x y : X} : 0 < nndist x y ↔ x ≠ y := by
  rw [pos_iff_ne_zero,ne_eq,nndist_eq_zero]

def crossRatio {X : Type*} [MetricSpace X] (x y z w : X) : ℝ≥0 :=
  nndist x y * nndist z w / (nndist x w * nndist y z)

lemma crossRatio_pos {X : Type*} [MetricSpace X] {x y z w : X}
    (h : Distinct x y z w) : 0 < crossRatio x y z w := by
  exact div_pos (mul_pos (nndist_pos.mpr h.1) (nndist_pos.mpr h.2.2.2.2.2))
    (mul_pos (nndist_pos.mpr h.2.2.1) (nndist_pos.mpr h.2.2.2.1))

lemma crossRatio_flip {X : Type*} [MetricSpace X] (x y z w : X) :
    crossRatio x w z y = (crossRatio x y z w)⁻¹ := by
  simp only [crossRatio,inv_div,nndist_comm z y,nndist_comm w z]

abbrev Distortion := ℝ≥0 ≃o ℝ≥0

lemma distortion_zero (η : Distortion) : η 0 = 0 := η.map_bot

def reciprocal (η : Distortion) : Distortion where
  toFun t := (η t⁻¹)⁻¹
  invFun t := (η.symm t⁻¹)⁻¹
  left_inv t := by simp
  right_inv t := by simp
  map_rel_iff' := by
    intro x y
    change (η x⁻¹)⁻¹ ≤ (η y⁻¹)⁻¹ ↔ x ≤ y
    by_cases hx : x=0
    · subst x
      simp only [inv_zero,distortion_zero,zero_le]
    by_cases hy : y=0
    · subst y
      have hη : η x⁻¹ ≠ 0 := by
        rw [← distortion_zero η]
        exact fun hh => hx (inv_eq_zero.mp (η.injective hh))
      simp only [inv_zero,distortion_zero,le_zero_iff,inv_eq_zero]
      exact ⟨fun hh => (hη hh).elim,fun hh => (hx hh).elim⟩
    have hxpos : 0 < x := pos_iff_ne_zero.mpr hx
    have hypos : 0 < y := pos_iff_ne_zero.mpr hy
    have hηx : 0 < η x⁻¹ := by simpa only [distortion_zero] using η.strictMono (inv_pos.mpr hxpos)
    have hηy : 0 < η y⁻¹ := by simpa only [distortion_zero] using η.strictMono (inv_pos.mpr hypos)
    rw [inv_le_inv₀ hηx hηy,η.le_iff_le,inv_le_inv₀ hypos hxpos]

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

def Controlled (f : X → Y) (η : Distortion) : Prop :=
  ∀ x y z w, Distinct x y z w →
    crossRatio (f x) (f y) (f z) (f w) ≤ η (crossRatio x y z w)

def QuasiMobius (f : X → Y) : Prop := ∃ η : Distortion, Controlled f η

lemma Controlled.comp {f : X → Y} {g : Y → Z} {η θ : Distortion}
    (hg : Controlled g θ) (hf : Controlled f η) (hinj : Function.Injective f) :
    Controlled (g ∘ f) (η.trans θ) := by
  intro x y z w hh
  exact (hg _ _ _ _ (hh.map hinj)).trans (θ.monotone (hf _ _ _ _ hh))

lemma Controlled.inverse (f : X ≃ₜ Y) {η : Distortion} (hf : Controlled f η) :
    Controlled f.symm (reciprocal η.symm) := by
  intro x y z w hh
  have hh' := hh.map f.symm.injective
  have H := hf _ _ _ _ hh'.flip
  simp only [f.apply_symm_apply] at H
  rw [crossRatio_flip x y z w, crossRatio_flip (f.symm x) (f.symm y) (f.symm z) (f.symm w)] at H
  have H' := η.symm.monotone H
  simp only [OrderIso.symm_apply_apply] at H'
  change crossRatio (f.symm x) (f.symm y) (f.symm z) (f.symm w) ≤ (η.symm (crossRatio x y z w)⁻¹)⁻¹
  have hpos : 0 < η.symm (crossRatio x y z w)⁻¹ := by
    simpa only [distortion_zero] using η.symm.strictMono (inv_pos.mpr (crossRatio_pos hh))
  have hi := (inv_le_inv₀ (inv_pos.mpr (crossRatio_pos hh')) hpos).mpr H'
  simpa only [inv_inv] using hi

lemma QuasiMobius.inverse (f : X ≃ₜ Y) (hf : QuasiMobius f) : QuasiMobius f.symm := by
  obtain ⟨η,hη⟩ := hf
  exact ⟨reciprocal η.symm,hη.inverse f⟩

lemma QuasiMobius.comp {f : X → Y} {g : Y → Z} (hg : QuasiMobius g)
    (hf : QuasiMobius f) (hinj : Function.Injective f) : QuasiMobius (g ∘ f) := by
  obtain ⟨η,hη⟩ := hf
  obtain ⟨θ,hθ⟩ := hg
  exact ⟨η.trans θ,hθ.comp hη hinj⟩

lemma controlled_conjugates {ι : Type*} (ψ : X ≃ₜ Y) {η θ : Distortion}
    (hψ : Controlled ψ η) (f : ι → X ≃ₜ X) (hf : ∀ i, Controlled (f i) θ) :
    ∀ i, Controlled (ψ ∘ (f i) ∘ ψ.symm)
      (((reciprocal η.symm).trans θ).trans η) := by
  intro i
  exact hψ.comp ((hf i).comp (hψ.inverse ψ) ψ.symm.injective)
    ((f i).injective.comp ψ.symm.injective)

end CannonQM

namespace CannonQM
open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

lemma controlled_of_product_bound (f : X → Y) (hf : Function.Injective f)
    (C : ℝ≥0) (hC : 0 < C)
    (h : ∀ x y z w, Distinct x y z w →
      nndist (f x) (f y)*nndist (f z) (f w)*nndist x w*nndist y z ≤
      C*(nndist (f x) (f w)*nndist (f y) (f z)*nndist x y*nndist z w)) :
    Controlled f (OrderIso.mulLeft₀ C hC) := by
  intro x y z w hh
  have hhf := hh.map hf
  change crossRatio (f x) (f y) (f z) (f w) ≤ C*crossRatio x y z w
  unfold crossRatio
  rw [← mul_div_assoc,div_le_div_iff₀
    (mul_pos (nndist_pos.mpr hhf.2.2.1) (nndist_pos.mpr hhf.2.2.2.1))
    (mul_pos (nndist_pos.mpr hh.2.2.1) (nndist_pos.mpr hh.2.2.2.1))]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h x y z w hh

end CannonQM

end
end
namespace CannonMetricQC
open Metric CannonQM

lemma cycle_sorted_bounds {a b c d T : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hT : 1  ≤  T)
    (hab : a  ≤  b) (hcd : c  ≤  d) (hp : a*b  ≤  T*(c*d))
    (hbt : b  ≤  a+c+d) (hdt : d  ≤  a+b+c) :
    a  ≤  (2*T+3)*c ∧ b  ≤  (2*T+3)*d := by
  have hT0 : 0 < T := by linarith
  constructor
  · by_contra hn
    have hn' : (2*T+3)*c < a := lt_of_not_ge hn
    have hhdt : d  ≤  2*b+c := by linarith
    have hm := mul_le_mul_of_nonneg_left hhdt (mul_nonneg hT0.le hc.le)
    have hTb : T*c < b := by nlinarith
    have hm1 := mul_pos (sub_pos.mpr hn') hb
    have hm2 := mul_pos (sub_pos.mpr hTb) hc
    nlinarith
  · by_contra hn
    have hn' : (2*T+3)*d < b := lt_of_not_ge hn
    have hha : T*d < a := by nlinarith
    have hhb : d < b := by nlinarith
    have hm1 := mul_pos (sub_pos.mpr hha) hb
    have hm2 := mul_nonneg (mul_nonneg hT0.le hd.le) (sub_nonneg.mpr hhb.le)
    have hm3 := mul_le_mul_of_nonneg_left hcd (mul_nonneg hT0.le hd.le)
    nlinarith

lemma crossRatio_pair_bounds {X : Type*} [MetricSpace X] (x y z w : X)
    (hh : Distinct x y z w) {T : ℝ} (hT : 1  ≤  T)
    (hp : dist x y*dist z w  ≤  T*(dist x w*dist y z)) :
    (dist x y  ≤  (2*T+3)*dist x w ∧ dist z w  ≤  (2*T+3)*dist y z) ∨
    (dist x y  ≤  (2*T+3)*dist y z ∧ dist z w  ≤  (2*T+3)*dist x w) := by
  let a := dist x y
  let b := dist z w
  let c := dist x w
  let d := dist y z
  have ha : 0 < a := dist_pos.mpr hh.1
  have hb : 0 < b := dist_pos.mpr hh.2.2.2.2.2
  have hc : 0 < c := dist_pos.mpr hh.2.2.1
  have hd : 0 < d := dist_pos.mpr hh.2.2.2.1
  have ht1 : a  ≤  b+c+d := by
    have h1 := dist_triangle x w y
    have h2 := dist_triangle w z y
    dsimp [a,b,c,d]
    rw [dist_comm w z,dist_comm z y] at h2
    linarith
  have ht2 : b  ≤  a+c+d := by
    have h1 := dist_triangle z y w
    have h2 := dist_triangle y x w
    dsimp [a,b,c,d]
    rw [dist_comm z y] at h1
    rw [dist_comm y x] at h2
    linarith
  have ht3 : c  ≤  a+b+d := by
    have h1 := dist_triangle x y w
    have h2 := dist_triangle y z w
    dsimp [a,b,c,d]
    linarith
  have ht4 : d  ≤  a+b+c := by
    have h1 := dist_triangle y x z
    have h2 := dist_triangle x w z
    dsimp [a,b,c,d]
    rw [dist_comm y x] at h1
    rw [dist_comm w z] at h2
    linarith
  change (a  ≤  (2*T+3)*c ∧ b  ≤  (2*T+3)*d) ∨
    (a  ≤  (2*T+3)*d ∧ b  ≤  (2*T+3)*c)
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · exact Or.inl (cycle_sorted_bounds ha hb hc hd hT hab hcd hp ht2 ht4)
  · exact Or.inr (cycle_sorted_bounds ha hb hd hc hT hab hdc (by nlinarith [hp])
      (by linarith) ht3)
  · have hh := cycle_sorted_bounds hb ha hc hd hT hba hcd (by nlinarith [hp])
      (by linarith) (by linarith)
    exact Or.inr ⟨hh.2,hh.1⟩
  · have hh := cycle_sorted_bounds hb ha hd hc hT hba hdc (by nlinarith [hp])
      (by linarith) (by linarith)
    exact Or.inl ⟨hh.2,hh.1⟩

end CannonMetricQC

end
end
end

end OAI
