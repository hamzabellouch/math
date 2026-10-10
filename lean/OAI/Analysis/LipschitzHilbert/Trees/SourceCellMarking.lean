import OAI.Analysis.LipschitzHilbert.Phase.SourceMarkedPrediction

namespace OAI

/-! The manuscript's marking rule uses the infimum of the parent mass
and the supremum of its absolute drop over the entire line cell. The
possible unmarked large drop is the last active index, hence is unique. -/

noncomputable section
open Set
namespace LipschitzHilbert

/-- The exact two inequalities in the source's cell marking rule. -/
def sourceMarkedCell (I : Set ℝ) (n h : ℝ → ℝ) (M : ℝ) : Prop :=
  M < sInf (n '' I) ∧ (1/2:ℝ) ≤ sSup (h '' I)

theorem sourceMarkedCell_active {I : Set ℝ} {n h : ℝ → ℝ} {M x : ℝ}
    (hn : ∀ y ∈ I, 0 ≤ n y) (hm : sourceMarkedCell I n h M) (hx : x ∈ I) :
    M < n x :=
  hm.1.trans_le (csInf_le ⟨0,by rintro _ ⟨y,hy,rfl⟩; exact hn y hy⟩ ⟨x,hx,rfl⟩)

theorem sourceMarkedCell_inactive {I : Set ℝ} {n h : ℝ → ℝ} {M x : ℝ}
    (hn : ∀ y ∈ I, 0 ≤ n y) (hx : x ∈ I) (hxn : n x ≤ M) :
    ¬ sourceMarkedCell I n h M := by
  intro hm
  exact (not_lt_of_ge hxn) (sourceMarkedCell_active hn hm hx)

/-- Relative motion on the entire cell turns the supremum condition
into a uniform positive absolute drop, also for a half-open cell. -/
theorem sourceMarkedCell_drop {I : Set ℝ} {n h : ℝ → ℝ} {M E x : ℝ}
    (hE : 0 < E) (hm : sourceMarkedCell I n h M) (hx : x ∈ I)
    (hmove : ∀ y ∈ I, h y ≤ E*h x) : (1/2:ℝ)/E ≤ h x := by
  apply (div_le_iff₀ hE).mpr
  have hs : sSup (h '' I) ≤ E*h x :=
    csSup_le ⟨h x,⟨x,hx,rfl⟩⟩ (by rintro _ ⟨y,hy,rfl⟩; exact hmove y hy)
  linarith [hm.2]

/-- If an unmarked cell contains a drop of at least one, its mass
infimum is at most M. Relative motion bounds every mass by E*M. -/
theorem source_unmarked_large_drop {I : Set ℝ} {n h : ℝ → ℝ} {M E x : ℝ}
    (hE : 0 < E) (hx : x ∈ I) (hm : ¬ sourceMarkedCell I n h M)
    (hlarge : 1 ≤ h x) (hbounded : BddAbove (h '' I))
    (hmove : ∀ y ∈ I, n x ≤ E*n y) : n x ≤ E*M := by
  have hsup : (1/2:ℝ) ≤ sSup (h '' I) :=
    (by norm_num : (1/2:ℝ) ≤ 1).trans (hlarge.trans (le_csSup hbounded ⟨x,hx,rfl⟩))
  have hinf : sInf (n '' I) ≤ M := le_of_not_gt (fun he => hm ⟨he,hsup⟩)
  have hlo : n x/E ≤ sInf (n '' I) :=
    le_csInf ⟨n x,⟨x,hx,rfl⟩⟩ (by
      rintro _ ⟨y,hy,rfl⟩
      apply (div_le_iff₀ hE).mpr
      simpa only [mul_comm] using hmove y hy)
  have he := mul_le_mul_of_nonneg_left (hlo.trans hinf) hE.le
  calc
    n x = E*(n x/E) := by field_simp
    _ ≤ E*M := he

/-- A unit absolute drop from a mass below M+1 crosses the stopping
threshold. This is the exceptional index in the source decomposition. -/
theorem source_unmarked_crosses_cutoff {I : Set ℝ} {n next : ℝ → ℝ} {M E x : ℝ}
    (hE : 0 < E) (hx : x ∈ I)
    (hm : ¬ sourceMarkedCell I n (fun y => n y-next y) M)
    (hlarge : 1 ≤ n x-next x)
    (hbounded : BddAbove ((fun y => n y-next y) '' I))
    (hmove : ∀ y ∈ I, n x ≤ E*n y) (hsmall : E*M < M+1) : next x < M := by
  have hn := source_unmarked_large_drop hE hx hm hlarge hbounded hmove
  linarith

/-- The marked/unmarked dichotomy under the quantitative relative motion
used for the actual source weights. -/
theorem source_cell_marking_cases (I : Set ℝ) (n next : ℝ → ℝ) (M q : ℝ)
    (hn : ∀ y ∈ I, 0 ≤ n y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hsmall : (1+q)*M < M+1)
    (hmove : ∀ x ∈ I, ∀ y ∈ I,
      n x ≤ (1+q)*n y ∧ n x-next x ≤ (1+q)*(n y-next y))
    (x : ℝ) (hx : x ∈ I) :
    (sourceMarkedCell I n (fun y => n y-next y) M →
      M < n x ∧ (1/4:ℝ) ≤ n x-next x) ∧
    (¬ sourceMarkedCell I n (fun y => n y-next y) M →
      1 ≤ n x-next x → n x < M+1 ∧ next x < M) := by
  have hE : 0 < 1+q := by linarith
  have hbounded : BddAbove ((fun y => n y-next y) '' I) :=
    ⟨(1+q)*(n x-next x),by rintro _ ⟨y,hy,rfl⟩; exact (hmove y hy x hx).2⟩
  constructor
  · intro hm
    refine ⟨sourceMarkedCell_active hn hm hx,?_⟩
    have hl := sourceMarkedCell_drop hE hm hx (fun y hy => (hmove y hy x hx).2)
    have hlo : (1/4:ℝ) ≤ (1/2:ℝ)/(1+q) := by
      apply (le_div_iff₀ hE).mpr
      linarith
    exact hlo.trans hl
  · intro hm hlarge
    have hnlarge := source_unmarked_large_drop hE hx hm hlarge hbounded
      (fun y hy => (hmove x hx y hy).1)
    exact ⟨hnlarge.trans_lt hsmall,source_unmarked_crosses_cutoff hE hx hm hlarge hbounded
      (fun y hy => (hmove x hx y hy).1) hsmall⟩

/-- Every exceptional unmarked large drop is the last active index.
There can be only one, independently of the number of angular levels. -/
theorem source_exceptional_index_unique (n : ℕ → ℝ) (M : ℝ)
    (hanti : Antitone n) (exceptional : ℕ → Prop)
    (hactive : ∀ j, exceptional j → M < n j)
    (hstop : ∀ j, exceptional j → n (j+1) ≤ M) :
    Set.Subsingleton {j | exceptional j} := by
  intro i hi j hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hle := hanti (show i+1 ≤ j by omega)
    exact (not_lt_of_ge (hle.trans (hstop i hi))) (hactive j hj)
  · have hle := hanti (show j+1 ≤ i by omega)
    exact (not_lt_of_ge (hle.trans (hstop j hj))) (hactive i hi)

end LipschitzHilbert

end

end OAI
