import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedFillingValue

namespace OAI

section


noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

lemma IsLocalSegment.dist_le {γ : ℝ → X} {L : ℝ} (h : IsLocalSegment γ L)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    dist (γ s) (γ t) ≤ |s-t| *L := by
  obtain ⟨ε,hε,hlocal⟩ := h.local_dist
  obtain ⟨N,hN⟩ := exists_nat_gt (2/ε)
  have hn : 0<N := by
    by_contra hh
    have hz : N=0 := by omega
    rw [hz,Nat.cast_zero] at hN
    exact (not_lt_of_ge (by positivity : 0≤2/ε)) hN
  have hn' : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have he : 2/(N:ℝ)<ε := by
    have := (div_lt_iff₀ hε).mp hN
    exact (div_lt_iff₀ hn').mpr (by nlinarith)
  let q : ℕ → ℝ := fun i => (1-(i:ℝ)/N)*s+((i:ℝ)/N)*t
  have hq (i : ℕ) (hi : i≤N) : q i ∈ Icc (0:ℝ) 1 := by
    have hi0 : 0≤(i:ℝ)/N := by positivity
    have hi1 : (i:ℝ)/N≤1 := (div_le_one hn').mpr (by exact_mod_cast hi)
    dsimp [q]
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hi1) hs.1) (mul_nonneg hi0 ht.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hi1) (sub_nonneg.mpr hs.2),
        mul_nonneg hi0 (sub_nonneg.mpr ht.2)]
  have hd (i : ℕ) : |q i-q (i+1)|=|s-t|/(N:ℝ) := by
    dsimp [q]
    push_cast
    rw [show (1-(i:ℝ)/N)*s+((i:ℝ)/N)*t-
      ((1-((i:ℝ)+1)/N)*s+(((i:ℝ)+1)/N)*t)=(s-t)/N by ring,abs_div,abs_of_pos hn']
  have hst : |s-t|≤1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
  have hb : |s-t|/(N:ℝ)<ε := (div_le_div_of_nonneg_right hst hn'.le).trans_lt ((div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤2) hn'.le).trans_lt he)
  have hh := dist_le_range_sum_of_dist_le (f:=fun i => γ (q i)) (n:=N)
    (d:=fun _ => |s-t|/(N:ℝ)*L) (fun {i} hi =>
      le_of_eq (by rw [hlocal _ (hq i (by omega)) _ (hq (i+1) (by omega)) (by rw [hd]; exact hb),hd]))
  have hq0 : q 0=s := by simp [q]
  have hqN : q N=t := by simp [q,ne_of_gt hn']
  rw [hq0,hqN,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have heq : (N:ℝ)*(|s-t|/(N:ℝ)*L)=|s-t| *L := by field_simp
  simpa only [heq] using hh

lemma IsLocalSegment.reparam {γ : ℝ → X} {L : ℝ} (h : IsLocalSegment γ L)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    IsLocalSegment (fun u => γ ((1-u)*s+u*t)) (|s-t| *L) := by
  have hm (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : (1-u)*s+u*t ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hu.2) hs.1) (mul_nonneg hu.1 ht.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hs.2),mul_nonneg hu.1 (sub_nonneg.mpr ht.2)]
  obtain ⟨ε,hε,hd⟩ := h.local_dist
  refine ⟨mul_nonneg (abs_nonneg _) h.nonneg,h.continuousOn.comp (by fun_prop) hm,ε,hε,?_⟩
  intro u hu v hv huv
  have he : (1-u)*s+u*t-((1-v)*s+v*t)=(u-v)*(t-s) := by ring
  have hab : |s-t|≤1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
  rw [hd _ (hm u hu) _ (hm v hv) (by rw [he,abs_mul,abs_sub_comm t s]; nlinarith [mul_le_mul_of_nonneg_left hab (abs_nonneg (u-v))]),he,abs_mul,abs_sub_comm t s]
  ring

lemma IsLocalSegment.length_unique {γ : ℝ → X} {L M : ℝ}
    (hL : IsLocalSegment γ L) (hM : IsLocalSegment γ M) : L=M := by
  obtain ⟨ε,hε,hd⟩ := hL.local_dist
  obtain ⟨δ,hδ,hd'⟩ := hM.local_dist
  let t := min (1/2:ℝ) (min (ε/2) (δ/2))
  have ht : 0<t := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ht1 : t≤1 := (min_le_left _ _).trans (by norm_num)
  have hte : t<ε := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have htd : t<δ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  have h0t : |(0:ℝ)-t|=t := by rw [zero_sub,abs_neg,abs_of_pos ht]
  have h1 := hd 0 (by norm_num) t ⟨ht.le,ht1⟩ (by rw [h0t]; exact hte)
  have h2 := hd' 0 (by norm_num) t ⟨ht.le,ht1⟩ (by rw [h0t]; exact htd)
  rw [h0t] at h1 h2
  nlinarith

lemma IsLocalSegment.close_length {α β : ℝ → X} {A B r : ℝ}
    (hα : IsLocalSegment α A) (hβ : IsLocalSegment β B)
    (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
    (hclose : ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t)<r/10)
    (h0 : α 0=β 0) : |A-B|≤dist (α 1) (β 1) := by
  obtain ⟨ε,hε,hd⟩ := hα.local_dist
  obtain ⟨δ,hδ,hd'⟩ := hβ.local_dist
  let t := min (1/2:ℝ) (min (ε/2) (δ/2))
  have ht : 0<t := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ht1 : t≤1 := (min_le_left _ _).trans (by norm_num)
  have hte : t<ε := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have htd : t<δ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  have h0t : |(0:ℝ)-t|=t := by rw [zero_sub,abs_neg,abs_of_pos ht]
  have h1 := hd 0 (by norm_num) t ⟨ht.le,ht1⟩ (by rw [h0t]; exact hte)
  have h2 := hd' 0 (by norm_num) t ⟨ht.le,ht1⟩ (by rw [h0t]; exact htd)
  rw [h0t] at h1 h2
  have hh := abs_dist_sub_le (α t) (β t) (α 0)
  rw [dist_comm (α t) (α 0),dist_comm (β t) (α 0),h1,h0,h2] at hh
  have hc' := hα.close_chord hβ hr hc g hclose t ⟨ht.le,ht1⟩
  rw [h0,dist_self,mul_zero,zero_add] at hc'
  rw [←mul_sub,abs_mul,abs_of_pos ht] at hh
  exact (le_of_mul_le_mul_left (hh.trans hc') ht)

end HyperbolicObstruction
end
end

section

end

end OAI
