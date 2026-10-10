import OAI.NumberTheory.TotientAsymptotic.PPTFactorLabels

namespace OAI

/-! One finite label type for the actual residual comparison partition. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

abbrev PPTResidualLabel :=
  Σ b : ℕ, (Fin b → ℕ) × ℕ × (Σ _h : ℕ, ℕ × (Σ _s : ℕ, ℕ))

def pptResidualLabel (b h s c a j : ℕ) (g : Fin b → ℕ) : PPTResidualLabel :=
  ⟨b, (g, (j, ⟨h, (a, ⟨s, c⟩)⟩))⟩

def pptLabelB (l : PPTResidualLabel) : ℕ := l.1
def pptLabelGrid (l : PPTResidualLabel) : Fin (pptLabelB l) → ℕ := l.2.1
def pptLabelWindow (l : PPTResidualLabel) : ℕ := l.2.2.1
def pptLabelH (l : PPTResidualLabel) : ℕ := l.2.2.2.1
def pptLabelA (l : PPTResidualLabel) : ℕ := l.2.2.2.2.1
def pptLabelS (l : PPTResidualLabel) : ℕ := l.2.2.2.2.2.1
def pptLabelC (l : PPTResidualLabel) : ℕ := l.2.2.2.2.2.2

def pptLabelWeight (l : PPTResidualLabel) : ℝ :=
  ((pptLabelA l).totient : ℝ)⁻¹*((pptLabelC l).totient : ℝ)⁻¹

def pptResidualLabels (N H : ℕ) (δ : ℝ) : Finset PPTResidualLabel := by
  classical
  exact (Finset.range (H+1)).sigma (fun b =>
    (collisionGridFamilies δ b).product ((Finset.range (H+1)).product
      ((Finset.range (H+1)).sigma (fun h =>
        (pptPrimeProductFamily N h).product
          ((Finset.range (H+1)).sigma (fun s => pptPrimeProductFamily N s))))))

lemma ppt_residual_label_mem {N H b h s c a j : ℕ} {δ : ℝ} {g : Fin b → ℕ}
    (hb : b ≤ H) (hh : h ≤ H) (hs : s ≤ H) (hj : j ≤ H)
    (hg : g ∈ collisionGridFamilies δ b)
    (ha : a ∈ pptPrimeProductFamily N h) (hc : c ∈ pptPrimeProductFamily N s) :
    pptResidualLabel b h s c a j g ∈ pptResidualLabels N H δ := by
  classical
  simp only [pptResidualLabel, pptResidualLabels, Finset.product_eq_sprod,
    Finset.mem_sigma, Finset.mem_product,
    Finset.mem_range, Nat.lt_succ_iff]
  exact ⟨hb, hg, hj, hh, ha, hs, hc⟩

lemma ppt_residual_labels_mass (N H : ℕ) (δ : ℝ) :
    (∑ l ∈ pptResidualLabels N H δ, pptLabelWeight l) =
      ∑ b ∈ Finset.range (H+1), ∑ _g ∈ collisionGridFamilies δ b,
        ∑ _j ∈ Finset.range (H+1),
        ∑ h ∈ Finset.range (H+1), ∑ a ∈ pptPrimeProductFamily N h,
        ∑ s ∈ Finset.range (H+1), ∑ c ∈ pptPrimeProductFamily N s,
          (a.totient : ℝ)⁻¹*(c.totient : ℝ)⁻¹ := by
  classical
  simp only [pptResidualLabels, Finset.product_eq_sprod, Finset.sum_sigma, Finset.sum_product,
    pptLabelWeight, pptLabelA, pptLabelC]

/-- Any selected subfamily, including the image of the actual residual
label map, obeys the same complete weighted entropy estimate. -/
theorem ppt_selected_labels_mass {A : ℝ} (hA : 0 ≤ A) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ z : ℝ in atTop,
      ∀ (H : ℕ) (δ : ℝ) (I : Finset PPTResidualLabel),
        (H : ℝ) ≤ A*Real.log (B z) → 0 < δ → 1/B z ≤ δ →
        I ⊆ pptResidualLabels (discardPrimeBound (B z)) H δ →
        (∑ l ∈ I, pptLabelWeight l) ≤ Real.exp (M*(Real.log (B z))^2) := by
  obtain ⟨M,hM,hbound⟩ := ppt_residual_labels_exponential_mass hA
  refine ⟨M,hM,?_⟩
  filter_upwards [hbound] with z hz
  intro H δ I hdim hδ hmesh hI
  calc
    _ ≤ ∑ l ∈ pptResidualLabels (discardPrimeBound (B z)) H δ, pptLabelWeight l :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ => by unfold pptLabelWeight; positivity)
    _ ≤ _ := by rw [ppt_residual_labels_mass]; exact hz H δ hdim hδ hmesh

def pptResidualCell (R : Finset ℕ) (label : ℕ → PPTResidualLabel)
    (l : PPTResidualLabel) : Finset ℕ := by
  classical
  exact R.filter (fun n => label n=l)

lemma ppt_residual_cells_cover (R : Finset ℕ) (label : ℕ → PPTResidualLabel) :
    ∀ n ∈ R, ∃ l ∈ R.image label, n ∈ pptResidualCell R label l := by
  classical
  intro n hn
  exact ⟨label n, Finset.mem_image.mpr ⟨n, hn, rfl⟩,
    Finset.mem_filter.mpr ⟨hn, rfl⟩⟩

lemma ppt_residual_cells_count_le (R : Finset ℕ) (label : ℕ → PPTResidualLabel) :
    (R.card : ℝ) ≤ ∑ l ∈ R.image label, ((pptResidualCell R label l).card : ℝ) := by
  classical
  exact ppt_residual_block_cover (R.image label) (pptResidualCell R label) R
    (ppt_residual_cells_cover R label) le_rfl

end TotientAsymptotic

end

end OAI
