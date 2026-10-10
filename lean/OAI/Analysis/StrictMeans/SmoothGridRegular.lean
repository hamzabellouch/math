import OAI.Analysis.StrictMeans.IndexHomotopy

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def StarCertificate (u : E → ℝ) (p dx dy : E) (s : ℝ) : Prop :=
  ∃ gx gy e : ℝ, 0 < e ∧ (4*e < |gx| ∨ 4*e < |gy|) ∧
    |u (p+s•dx)-u p-gx| ≤ e ∧ |u (p+s•(dx+dy))-u p-(gx+gy)| ≤ e ∧
    |u (p+s•dy)-u p-gy| ≤ e ∧ |u (p-s•dx)-u p-(-gx)| ≤ e ∧
    |u (p-s•(dx+dy))-u p-(-gx-gy)| ≤ e ∧ |u (p-s•dy)-u p-(-gy)| ≤ e

lemma strict_direction_bound {u : E → ℝ} {L : E →L[ℝ] ℝ} {p : E}
    (h : HasStrictFDerivAt u L p) (d : E) {c : ℝ} (hc : 0<c) :
    ∀ᶠ q : ℝ × E in 𝓝 (0,p),
      |u (q.2+q.1•d)-u q.2-q.1*L d| ≤ c*|q.1| *‖d‖ := by
  have ht : Tendsto (fun q : ℝ × E => (q.2+q.1•d,q.2)) (𝓝 (0,p)) (𝓝 (p,p)) := by
    have hc : Continuous (fun q : ℝ × E => (q.2+q.1•d,q.2)) := by fun_prop
    simpa using hc.tendsto (0,p)
  filter_upwards [ht.eventually (h.isLittleO.bound hc)] with q hq
  simpa only [add_sub_cancel_left,map_smul,smul_eq_mul,
    norm_smul,Real.norm_eq_abs,mul_assoc] using hq

lemma remainder_enlarge {A s c d e : ℝ} (h : |A| ≤ c*|s| *d)
    (hs : 0<s) (hc : 0≤c) (hd : d≤2) (he : 2*c*s≤e) : |A|≤e := by
  rw [abs_of_pos hs] at h
  have := mul_le_mul_of_nonneg_left hd (mul_nonneg hc hs.le)
  nlinarith

lemma strict_regular_star {u : E → ℝ} {L : E →L[ℝ] ℝ} {p dx dy : E}
    (h : HasStrictFDerivAt u L p) (hx : ‖dx‖≤1) (hy : ‖dy‖≤1)
    (hr : L dx ≠ 0 ∨ L dy ≠ 0) :
    ∀ᶠ q : ℝ × E in 𝓝 (0,p), 0<q.1 → StarCertificate u q.2 dx dy q.1 := by
  let M := max |L dx| |L dy|
  have hM : 0<M := by
    rcases hr with h|h
    · exact lt_of_lt_of_le (abs_pos.mpr h) (le_max_left _ _)
    · exact lt_of_lt_of_le (abs_pos.mpr h) (le_max_right _ _)
  have hc : 0<M/32 := by positivity
  filter_upwards [strict_direction_bound h dx hc,strict_direction_bound h (dx+dy) hc,
    strict_direction_bound h dy hc,strict_direction_bound h (-dx) hc,
    strict_direction_bound h (-(dx+dy)) hc,strict_direction_bound h (-dy) hc] with q h₀ h₁ h₂ h₃ h₄ h₅
  intro hs
  have hnxy : ‖dx+dy‖≤2 := (norm_add_le _ _).trans (by linarith)
  have hb {A : ℝ} {d : E} (hd : ‖d‖≤2)
      (ha : |A|≤M/32*|q.1| *‖d‖) : |A| ≤ q.1*M/16 :=
    remainder_enlarge ha hs hc.le hd (by ring_nf; rfl)
  refine ⟨q.1*L dx,q.1*L dy,q.1*M/16,by positivity,?_,
    hb (d:=dx) (by linarith) h₀,?_,hb (d:=dy) (by linarith) h₂,?_,?_,?_⟩
  · simp only [abs_mul,abs_of_pos hs]
    rcases le_total |L dx| |L dy| with hl|hl
    · right
      dsimp [M]
      rw [max_eq_right hl]
      have := mul_pos hs (lt_of_lt_of_le hM (by dsimp [M]; rw [max_eq_right hl]))
      nlinarith
    · left
      dsimp [M]
      rw [max_eq_left hl]
      have := mul_pos hs (lt_of_lt_of_le hM (by dsimp [M]; rw [max_eq_left hl]))
      nlinarith
  · simpa only [map_add,mul_add] using hb hnxy h₁
  · simpa only [norm_neg,smul_neg,← sub_eq_add_neg,map_neg,mul_neg] using
      hb (d := -dx) (by simpa using hx.trans (by norm_num : (1:ℝ)≤2)) h₃
  · have ht := hb (d := -(dx+dy)) (by simpa only [norm_neg] using hnxy) h₄
    rw [smul_neg, ← sub_eq_add_neg,map_neg,map_add,mul_neg,mul_add] at ht
    convert ht using 1
    congr 2
    ring
  · simpa only [norm_neg,smul_neg,← sub_eq_add_neg,map_neg,mul_neg] using
      hb (d := -dy) (by simpa using hy.trans (by norm_num : (1:ℝ)≤2)) h₅

lemma compact_regular_star {u : E → ℝ} {dx dy : E} {K : Set E}
    (hK : IsCompact K) (hx : ‖dx‖≤1) (hy : ‖dy‖≤1)
    (h : ∀ p∈K, ∃ L : E →L[ℝ] ℝ,
      HasStrictFDerivAt u L p ∧ (L dx≠0 ∨ L dy≠0)) :
    ∀ᶠ s in 𝓝 (0:ℝ), ∀ p∈K, 0<s → StarCertificate u p dx dy s := by
  apply hK.eventually_forall_of_forall_eventually
  intro p hp
  obtain ⟨L,hL,hr⟩ := h p hp
  exact strict_regular_star hL hx hy hr

end
end StrictInverseFirstPower.Grid

end

end OAI
