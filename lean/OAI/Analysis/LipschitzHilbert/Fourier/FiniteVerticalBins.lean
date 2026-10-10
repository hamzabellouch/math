import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinProfile

namespace OAI

/-! A concrete finite real square partition of a positive vertical band.
Only bins meeting the original band are retained. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def verticalBinCenter (K : ℕ) (W : ℝ) (n : ℕ) : ℝ := ((n:ℝ)-K)/W

def verticalBinWindow (K : ℕ) (W : ℝ) (n : ℕ) (eta : ℝ) : ℂ :=
  verticalBinProfile (W*(eta-verticalBinCenter K W n))

theorem verticalBinWindow_apply (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ) (eta : ℝ) :
    verticalBinWindow K W n eta=verticalBinProfile (W*eta+K-n) := by
  unfold verticalBinWindow verticalBinCenter
  congr 1
  field_simp
  ring

theorem verticalBinWindow_support (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ) (eta : ℝ)
    (h : verticalBinWindow K W n eta≠0) : |eta-verticalBinCenter K W n|≤1/W := by
  have hs := verticalBinProfile_support _ h
  rw [abs_mul,abs_of_pos hW] at hs
  exact (le_div_iff₀ hW).mpr (by nlinarith)

def verticalBinLabels (K : ℕ) (w W c C : ℝ) : Finset ℕ :=
  (Finset.range (2*K+1)).filter (fun n =>
    c-w/W≤w*verticalBinCenter K W n ∧ w*verticalBinCenter K W n≤C+w/W)

theorem verticalBinWindow_mem_labels (K : ℕ) (w W c C eta : ℝ)
    (hw : 0<w) (hW : 0<W) (hlo : c≤w*eta) (hhi : w*eta≤C)
    (n : ℕ) (hn : n∈Finset.range (2*K+1)) (h : verticalBinWindow K W n eta≠0) :
    n∈verticalBinLabels K w W c C := by
  have hs := abs_le.mp (verticalBinWindow_support K W hW n eta h)
  have hsl := mul_le_mul_of_nonneg_left hs.1 hw.le
  have hsu := mul_le_mul_of_nonneg_left hs.2 hw.le
  simp only [mul_neg,mul_one_div,mul_sub] at hsl hsu
  apply Finset.mem_filter.mpr
  refine ⟨hn,?_⟩
  constructor <;> nlinarith

theorem verticalBinWindow_sum_sq (K : ℕ) (w W c C eta : ℝ)
    (hw : 0<w) (hW : 0<W) (hlo : c≤w*eta) (hhi : w*eta≤C) (hK : |W*eta|≤K) :
    (∑ n∈verticalBinLabels K w W c C, (verticalBinWindow K W n eta)^2)=1 := by
  have heq : (∑ n∈verticalBinLabels K w W c C, (verticalBinWindow K W n eta)^2)=
      ∑ n∈Finset.range (2*K+1), (verticalBinWindow K W n eta)^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hn'
    have hz : verticalBinWindow K W n eta=0 := by
      by_contra h
      exact hn' (verticalBinWindow_mem_labels K w W c C eta hw hW hlo hhi n hn h)
    simp only [hz,zero_pow (by decide : 2≠0)]
  rw [heq]
  simp_rw [verticalBinWindow_apply K W hW]
  exact verticalBinProfile_sum_sq K (W*eta) hK

theorem verticalBinLabels_center_bounds (K : ℕ) (w W c C : ℝ)
    (n : verticalBinLabels K w W c C) :
    c-w/W≤w*verticalBinCenter K W n ∧ w*verticalBinCenter K W n≤C+w/W :=
  (Finset.mem_filter.mp n.property).2

theorem verticalBinLabels_admissible_centers (K : ℕ) (w W c C : ℝ)
    (hsmall : 5*(w/W)≤c/2) (hcC : c/2≤C)
    (n : verticalBinLabels K w W c C) :
    c/2+4*(w/W)≤w*verticalBinCenter K W n ∧
      w*verticalBinCenter K W n+4*(w/W)≤2*C := by
  obtain ⟨hlo,hhi⟩ := verticalBinLabels_center_bounds K w W c C n
  constructor <;> linarith

theorem verticalBinLabels_card (w W c C : ℝ) (hw : 0<w) (hW : 0<W) (hC : 0≤C) :
    ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)≤2*(C*W/w)+3 := by
  have hcard : (verticalBinLabels ⌈C*W/w⌉₊ w W c C).card≤2*⌈C*W/w⌉₊+1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  have hcard' : ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)≤2*(⌈C*W/w⌉₊:ℝ)+1 := by
    exact_mod_cast hcard
  have hceil := (Nat.ceil_lt_add_one (show 0≤C*W/w by positivity)).le
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
