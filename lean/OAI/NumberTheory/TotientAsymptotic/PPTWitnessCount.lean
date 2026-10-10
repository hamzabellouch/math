import OAI.NumberTheory.TotientAsymptotic.PPTLabeledResidualCount
import OAI.NumberTheory.TotientAsymptotic.PPTSelectedGrid

namespace OAI

/-! The finite partition of actual regular residuals. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def pptLabelTerminalLower (z : ℝ) (N : ℕ) (l : PPTResidualLabel) : ℝ :=
  (B z)^(2/3:ℝ)+2*(pptLabelWindow l:ℝ)*((B z)^(2/3:ℝ)/(2*((N:ℝ)+1)))

def pptLabelTerminalUpper (z : ℝ) (N : ℕ) (l : PPTResidualLabel) : ℝ :=
  (B z)^(2/3:ℝ)+(2*(pptLabelWindow l:ℝ)+1)*((B z)^(2/3:ℝ)/(2*((N:ℝ)+1)))

def pptLabelTerminal (z : ℝ) (N : ℕ) (l : PPTResidualLabel) : ℝ :=
  Real.exp (Real.exp ((pptLabelTerminalLower z N l+pptLabelTerminalUpper z N l)/2))

def pptLabelUpper (z : ℝ) (N : ℕ) (l : PPTResidualLabel) : ℕ → ℝ :=
  pairedGridUpper (2*((Real.log (B z))^5/Real.sqrt (B z)))
    ((pptLabelTerminalLower z N l+pptLabelTerminalUpper z N l)/(2*B z)) (pptLabelGrid l)

def pptLabelLower (z : ℝ) (l : PPTResidualLabel) : ℕ → ℝ :=
  pptGridLower (2*((Real.log (B z))^5/Real.sqrt (B z)))
    (pptUniformHeadEdge (B z)-2*((Real.log (B z))^5/Real.sqrt (B z))) (pptLabelGrid l)

/-- Arithmetic evidence retained from the actual terminal-prefix
construction for one integer. Each field is supplied by `ppt_selected_grid_data`;
the structure contains no estimate for a finite family. -/
structure PPTResidualGridWitness (d N H : ℕ) (z S A : ℝ) (r : ℕ) where
  label : PPTResidualLabel
  length_pos : 1 ≤ pptLabelB label
  length_le : pptLabelB label ≤ H
  tail_length_le : pptLabelH label ≤ H
  label_mem : label ∈ pptResidualLabels (discardPrimeBound (B z)) H
    (2*((Real.log (B z))^5/Real.sqrt (B z)))
  terminal_normality : S ≤ pptLabelTerminal z N label
  terminal_height : 0 ≤ B (pptLabelTerminal z N label) ∧
    B (pptLabelTerminal z N label) ≤ 2*(B z)^(2/3:ℝ)
  terminal_eq : comparisonCutoffs z (pptLabelUpper z N label) (pptLabelB label)=
    pptLabelTerminal z N label
  tail : Fin (pptLabelH label) → ℕ
  tail_product : pptLabelA label=∏ i,tail i
  tail_injective : Function.Injective tail
  tail_normal : ∀ i,IsNormalPrime S (tail i)
  tail_smooth : ∀ i,(largestPrimeFactor (tail i-1):ℝ) ≤ pptLabelTerminal z N label
  pair : ShiftedPair (pptLabelB label)
  recovery : r=pptLabelC label*pptLabelA label*∏ i,pair.left i
  parameters : FordComparisonParameters (pptLabelB label) z S
    (d*(pptLabelA label).totient) (pptLabelC label).totient
    (comparisonCutoffs z (pptLabelUpper z N label)) (comparisonCutoffs z (pptLabelLower z label))
  conditions : FordComparisonConditions (pptLabelB label) z S
    (d*(pptLabelA label).totient) (pptLabelC label).totient
    (comparisonCutoffs z (pptLabelUpper z N label)) (comparisonCutoffs z (pptLabelLower z label)) pair
  exponent : -2+(∑ i ∈ Finset.Icc 1 (pptLabelB label-1),
      a i*(B (comparisonCutoffs z (pptLabelUpper z N label) i)/B z))+
    comparisonError (pptLabelB label) z S (comparisonCutoffs z (pptLabelUpper z N label))
      (comparisonCutoffs z (pptLabelLower z label)) ≤ 
        -1-(1/(80*A^3))/(Real.log (B z))^3

/-- Partition any finite set of actual witnessed residuals, choose the
small tail only after fixing its integer label, and apply the saved Ford
bound. Witness multiplicities and alternative prime lists do not enter
the count. -/
theorem ppt_witnessed_residual_count (d : ℕ) (hd : 0 < d) {A : ℝ}
    (hA : 0 < A) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop, ∀ (N H : ℕ) (S : ℝ) (R : Finset ℕ),
      (H:ℝ) ≤ A*Real.log (B z) → 1 < S → 0 ≤ B S →
      (∀ r∈R,Nonempty (PPTResidualGridWitness d N H z S A r)) →
      (R.card:ℝ) ≤ z/((d:ℝ)*Real.log z)*(B z)^(-K) := by
  classical
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [ppt_labeled_residual_count d hd hA hγ K,
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ)),
    B_tendsto.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)))]
    with z hcount hB hlog
  intro N H S R hdim hS hBS hwitness
  let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
  have hδ : 0 < δ := by
    have hlog0 := Real.log_pos hB
    dsimp only [δ]
    positivity
  have hδrec : 1/B z ≤ δ := by
    have hh := ppt_mesh_reciprocal_lower (zero_lt_one.trans hB) hlog
    dsimp only [δ]
    have hm : 0 ≤ (Real.log (B z))^5/Real.sqrt (B z) := by
      have hlog0 := (Real.log_pos hB).le
      positivity
    linarith only [hh,hm]
  have hchoose : ∀ r : ℕ,∃ l : PPTResidualLabel,
      r∈R → ∃ w : PPTResidualGridWitness d N H z S A r,w.label=l := by
    intro r
    by_cases hr : r∈R
    · let w := Classical.choice (hwitness r hr)
      exact ⟨w.label,fun _ => ⟨w,rfl⟩⟩
    · exact ⟨pptResidualLabel 0 0 0 1 1 0 (fun i => Fin.elim0 i),fun h => (hr h).elim⟩
  choose label hlabel using hchoose
  let I := R.image label
  have hperlabel : ∀ l : PPTResidualLabel,∃ tail : Fin (pptLabelH l) → ℕ,
      l∈I →
        (1 ≤ pptLabelB l ∧ pptLabelB l ≤ H ∧ pptLabelH l ≤ H) ∧
        l∈pptResidualLabels (discardPrimeBound (B z)) H δ ∧
        (S ≤ pptLabelTerminal z N l) ∧
        (0 ≤ B (pptLabelTerminal z N l) ∧ B (pptLabelTerminal z N l) ≤ 2*(B z)^(2/3:ℝ)) ∧
        (comparisonCutoffs z (pptLabelUpper z N l) (pptLabelB l)=pptLabelTerminal z N l) ∧
        pptLabelA l=∏ i,tail i ∧ Function.Injective tail ∧
        (∀ i,IsNormalPrime S (tail i)) ∧
        (∀ i,(largestPrimeFactor (tail i-1):ℝ) ≤ pptLabelTerminal z N l) ∧
        FordComparisonParameters (pptLabelB l) z S (d*(pptLabelA l).totient)
          (pptLabelC l).totient (comparisonCutoffs z (pptLabelUpper z N l))
          (comparisonCutoffs z (pptLabelLower z l)) ∧
        -2+(∑ i ∈ Finset.Icc 1 (pptLabelB l-1),a i*(B (comparisonCutoffs z (pptLabelUpper z N l) i)/B z))+
          comparisonError (pptLabelB l) z S (comparisonCutoffs z (pptLabelUpper z N l))
            (comparisonCutoffs z (pptLabelLower z l)) ≤ -1-(1/(80*A^3))/(Real.log (B z))^3 := by
    intro l
    by_cases hl : l∈I
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨w,hw⟩ := hlabel r hr
      rw [←hw]
      exact ⟨w.tail,fun _ => ⟨⟨w.length_pos,w.length_le,w.tail_length_le⟩,
        w.label_mem,w.terminal_normality,w.terminal_height,w.terminal_eq,w.tail_product,
        w.tail_injective,w.tail_normal,w.tail_smooth,w.parameters,w.exponent⟩⟩
    · exact ⟨fun _=>0,fun h=>(hl h).elim⟩
  choose tail htail using hperlabel
  have hpairs : ∀ (l : PPTResidualLabel) (r : ℕ),∃ pair : ShiftedPair (pptLabelB l),
      r∈pptResidualCell R label l →
        r=pptLabelC l*pptLabelA l*∏ i,pair.left i ∧
        FordComparisonConditions (pptLabelB l) z S (d*(pptLabelA l).totient)
          (pptLabelC l).totient (comparisonCutoffs z (pptLabelUpper z N l))
          (comparisonCutoffs z (pptLabelLower z l)) pair := by
    intro l r
    by_cases hr : r∈pptResidualCell R label l
    · change r ∈ R.filter (fun k=>label k=l) at hr
      obtain ⟨hrR,he⟩ := Finset.mem_filter.mp hr
      obtain ⟨w,hw⟩ := hlabel r hrR
      have hwl : w.label=l := hw.trans he
      rw [←hwl]
      exact ⟨w.pair,fun _=>⟨w.recovery,w.conditions⟩⟩
    · exact ⟨⟨fun _=>0,fun _=>0,1⟩,fun h=>(hr h).elim⟩
  choose pair hpair using hpairs
  apply hcount H δ R label (fun _=>S) (pptLabelTerminal z N)
    (fun l=>comparisonCutoffs z (pptLabelUpper z N l))
    (fun l=>comparisonCutoffs z (pptLabelLower z l)) tail pair hdim hδ hδrec
  · intro r hr
    exact (htail (label r) (Finset.mem_image.mpr ⟨r,hr,rfl⟩)).2.1
  · intro l hl
    exact (htail l hl).1
  · intro l hl
    exact ⟨hS,hBS,(htail l hl).2.2.1⟩
  · intro l hl
    rw [(htail l hl).2.2.2.2.1]
    exact ⟨Real.one_lt_exp_iff.mpr (Real.exp_pos _),(htail l hl).2.2.2.1.2⟩
  · intro l hl
    exact (htail l hl).2.2.2.1
  · intro l hl
    exact (htail l hl).2.2.2.2.2.1
  · intro l hl
    exact (htail l hl).2.2.2.2.2.2.1
  · intro l hl
    exact (htail l hl).2.2.2.2.2.2.2.1
  · intro l hl
    exact (htail l hl).2.2.2.2.2.2.2.2.1
  · intro l hl
    exact (htail l hl).2.2.2.2.2.2.2.2.2.2
  · intro l hl
    exact (htail l hl).2.2.2.2.2.2.2.2.2.1
  · intro r hr
    exact (hpair (label r) r (Finset.mem_filter.mpr ⟨hr,rfl⟩)).1
  · intro r hr
    exact (hpair (label r) r (Finset.mem_filter.mpr ⟨hr,rfl⟩)).2

end TotientAsymptotic

end

end OAI
