import OAI.NumberTheory.TotientAsymptotic.PPTFiniteLabels

namespace OAI

/-! Sum the actual residual partition using its finite arithmetic labels.
The reciprocal-factor entropy is a proved bound, not an additional input. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- Once the pointwise grids have been assigned, the full finite label
space absorbs their entropy while retaining every inverse-power saving. -/
theorem ppt_labeled_residual_count (d : ℕ) (hd : 0 < d)
    {A γ : ℝ} (hA : 0 < A) (hγ : 0 < γ) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (H : ℕ) (δ : ℝ) (R : Finset ℕ) (label : ℕ → PPTResidualLabel)
      (W V : PPTResidualLabel → ℝ) (Y U : PPTResidualLabel → ℕ → ℝ)
      (tail : (l : PPTResidualLabel) → Fin (pptLabelH l) → ℕ)
      (pair : (l : PPTResidualLabel) → ℕ → ShiftedPair (pptLabelB l)),
      (H : ℝ) ≤ A*Real.log (B z) → 0 < δ → 1/B z ≤ δ →
      (∀ n ∈ R, label n ∈ pptResidualLabels (discardPrimeBound (B z)) H δ) →
      (∀ l ∈ R.image label, 1 ≤ pptLabelB l ∧ pptLabelB l ≤ H ∧ pptLabelH l ≤ H) →
      (∀ l ∈ R.image label, 1 < W l ∧ 0 ≤ B (W l) ∧ W l ≤ V l) →
      (∀ l ∈ R.image label,
        1 < Y l (pptLabelB l) ∧ B (Y l (pptLabelB l)) ≤ 2*(B z)^(2/3 : ℝ)) →
      (∀ l ∈ R.image label, 0 ≤ B (V l) ∧ B (V l) ≤ 2*(B z)^(2/3 : ℝ)) →
      (∀ l ∈ R.image label, pptLabelA l = ∏ j, tail l j) →
      (∀ l ∈ R.image label, Function.Injective (tail l)) →
      (∀ l ∈ R.image label, ∀ j, IsNormalPrime (W l) (tail l j)) →
      (∀ l ∈ R.image label, ∀ j, (largestPrimeFactor (tail l j-1) : ℝ) ≤ V l) →
      (∀ l ∈ R.image label,
        -2+(∑ j ∈ Finset.Icc 1 (pptLabelB l-1),
          a j*(B (Y l j)/B z))+
          comparisonError (pptLabelB l) z (W l) (Y l) (U l) ≤ 
            -1-γ/(Real.log (B z))^3) →
      (∀ l ∈ R.image label, FordComparisonParameters (pptLabelB l) z (W l)
        (d*(pptLabelA l).totient) (pptLabelC l).totient (Y l) (U l)) →
      (∀ n ∈ R, n = pptLabelC (label n)*pptLabelA (label n)*
        ∏ j, (pair (label n) n).left j) →
      (∀ n ∈ R, FordComparisonConditions (pptLabelB (label n)) z (W (label n))
        (d*(pptLabelA (label n)).totient) (pptLabelC (label n)).totient
          (Y (label n)) (U (label n)) (pair (label n) n)) →
      (R.card : ℝ) ≤ z/((d : ℝ)*Real.log z)*(B z)^(-K) := by
  obtain ⟨M,hM,hmass⟩ := ppt_selected_labels_mass hA.le
  filter_upwards [hmass, ppt_finite_residual_block_decay d hd (M := M) hA.le hγ K]
    with z hmass hcount
  intro H δ R label W V Y U tail pair hdim hδ hmesh hlabels hlength hW hY hV
    htail hinj hnormal hsmall hexponent hparams hreal hconditions
  let I := R.image label
  have hI : I ⊆ pptResidualLabels (discardPrimeBound (B z)) H δ := by
    intro l hl
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hl
    exact hlabels n hn
  have hweights : (∑ l ∈ I,
      (1/((pptLabelA l).totient : ℝ))*(1/((pptLabelC l).totient : ℝ))) ≤ 
        Real.exp (M*(Real.log (B z))^2) := by
    simpa only [pptLabelWeight,one_div] using hmass H δ I hdim hδ hmesh hI
  have hgrouped := hcount PPTResidualLabel I pptLabelB pptLabelH pptLabelC pptLabelA
    W V Y U tail (pptResidualCell R label) pair
    (fun l hl => (hlength l hl).1)
    (fun l hl => (Nat.cast_le.mpr (hlength l hl).2.1).trans hdim)
    (fun l hl => (Nat.cast_le.mpr (hlength l hl).2.2).trans hdim)
    hW hY hV hweights htail hinj hnormal hsmall hexponent hparams
    (by
      intro l hl n hn
      change n ∈ R.filter (fun k=>label k=l) at hn
      obtain ⟨hnR,he⟩ := Finset.mem_filter.mp hn
      subst l
      exact hreal n hnR)
    (by
      intro l hl n hn
      change n ∈ R.filter (fun k=>label k=l) at hn
      obtain ⟨hnR,he⟩ := Finset.mem_filter.mp hn
      subst l
      exact hconditions n hnR)
  exact (ppt_residual_cells_count_le R label).trans hgrouped

end TotientAsymptotic

end

end OAI
