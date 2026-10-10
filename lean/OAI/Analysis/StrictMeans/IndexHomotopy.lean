import OAI.Analysis.StrictMeans.CanonicalIndex

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V : Type*} [LinearOrder V] [AddCommGroup V]

def RegularStar (u : V → ℝ) (x y v : V) : Prop :=
  ∃ gx gy e : ℝ, 0 < e ∧ (4*e < |gx| ∨ 4*e < |gy|) ∧
    |u (v+x)-u v-gx| ≤ e ∧ |u (v+x+y)-u v-(gx+gy)| ≤ e ∧
    |u (v+y)-u v-gy| ≤ e ∧ |u (v-x)-u v-(-gx)| ≤ e ∧
    |u (v-(x+y))-u v-(-gx-gy)| ≤ e ∧ |u (v-y)-u v-(-gy)| ≤ e

lemma RegularStar.index_zero {u : V → ℝ} {x y v : V} (h : RegularStar u x y v) :
    heightIndex u x y v = 0 := by
  obtain ⟨gx,gy,e,he,hr,h₀,h₁,h₂,h₃,h₄,h₅⟩ := h
  apply heightIndex_regular (gx := gx) (gy := gy) (e := e) _ he.le h₀ h₁ h₂ h₃ h₄ h₅
  rcases hr with h|h <;> [left;right] <;> linarith

lemma star_error_perturb {A B a b g e : ℝ}
    (h : |A-B-g| ≤ e) (ha : |a-A|<e/2) (hb : |b-B|<e/2) : |a-b-g| ≤ 2*e := by
  have h₁ := (abs_lt.mp ha)
  have h₂ := (abs_lt.mp hb)
  have h₃ := (abs_le.mp h)
  rw [abs_le]
  constructor <;> linarith

lemma RegularStar.eventually_index_zero {P : Type*} [TopologicalSpace P]
    {u : P → V → ℝ} {t : P} {x y v : V}
    (hc : ∀ a ∈ meshStar x y v, ContinuousAt (fun s => u s a) t)
    (hr : RegularStar (u t) x y v) : ∀ᶠ s in 𝓝 t, heightIndex (u s) x y v = 0 := by
  obtain ⟨gx,gy,e,he,hr,h₀,h₁,h₂,h₃,h₄,h₅⟩ := hr
  have ht : ∀ᶠ s in 𝓝 t, ∀ a ∈ meshStar x y v, |u s a-u t a|<e/2 := by
    rw [Finset.eventually_all]
    intro a ha
    have hc' := (hc a ha).sub_const (u t a)
    have hm := hc'.abs.eventually (gt_mem_nhds (show |u t a-u t a|<e/2 by simpa using half_pos he))
    exact hm
  filter_upwards [ht] with s hs
  apply heightIndex_regular (gx := gx) (gy := gy) (e := 2*e) (by simpa only [← mul_assoc,show (2:ℝ)*2=4 by norm_num] using hr) (by linarith)
  · exact star_error_perturb h₀ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))
  · exact star_error_perturb h₁ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))
  · exact star_error_perturb h₂ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))
  · exact star_error_perturb h₃ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))
  · exact star_error_perturb h₄ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))
  · exact star_error_perturb h₅ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))

lemma local_index_homotopy {P : Type*} [TopologicalSpace P] [PreconnectedSpace P]
    (u : P → V → ℝ) (hc : ∀ a, Continuous (fun t => u t a))
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (S : Finset V)
    (hr : ∀ t v, v ∈ meshBoundary x y S → RegularStar (u t) x y v) (a b : P) :
    ∑ v ∈ S, heightIndex (u a) x y v = ∑ v ∈ S, heightIndex (u b) x y v := by
  have hl : IsLocallyConstant (fun t => ∑ v ∈ S, heightIndex (u t) x y v) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hm : ∀ᶠ s in 𝓝 t, ∀ v ∈ meshBoundary x y S,
        heightIndex (fun w => if w ∈ S then u s w else u t w) x y v = 0 := by
      rw [Finset.eventually_all]
      intro v hv
      apply RegularStar.eventually_index_zero
      · intro w _
        by_cases hw : w ∈ S
        · simpa only [ite_eq_left hw] using (hc w).continuousAt (x := t)
        · simpa only [ite_eq_right hw] using (continuousAt_const : ContinuousAt (fun _ : P => u t w) t)
      · simpa only [ite_self] using hr t v hv
    filter_upwards [hm] with s hs
    exact (heightIndex_local_change hx hy hd S
      (fun v hv => (hr t v hv).index_zero) (fun v hv => (hr s v hv).index_zero) hs).symm
  exact congrFun (hl.eq_const b) a

end
end StrictInverseFirstPower.Grid

end

end OAI
