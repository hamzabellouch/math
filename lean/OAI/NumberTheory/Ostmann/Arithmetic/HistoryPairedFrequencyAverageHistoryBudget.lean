import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageHistoryBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Construction Characters FrequencyTreeSum FrequencyExposure HistoryFrequencyResidues

theorem schedule_budget_eq_historyWeight (S : List Bool → Finset (ℤ × ℤ))
    (C : NNReal) (ε : ℝ) {R : ℕ} (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (p : List Bool)
    {l : ℕ} (h h' : History l) (hh : LabelsIn S p h h') (hm : ScheduleMatches d f p h h') :
    ((FrequencyExposure.budget C ε d l p).value : ℝ) =
      weight S (PairedFrequencyTreeSum.factor (C : ℝ) ε) (historyAssignment S p h h' hh) := by
  induction h generalizing p with
  | leaf a => cases h'; rfl
  | @node l a pivot u hp hm0 left right ihl ihr =>
    cases h' with
    | node b pivot' u' hp' hm' left' right' =>
      obtain ⟨hds,hds',hdv,hdw,hdv',hdw',_,_,hml,hmr⟩ := hm
      change ((C : ℝ)*(reducedPair (d p) : ℝ)^(ε-1))*
        ((FrequencyExposure.budget C ε d l (false::p)).value : ℝ)*
        ((FrequencyExposure.budget C ε d l (true::p)).value : ℝ) = _
      rw [ihl (false::p) left' hh.2.1 hml, ihr (true::p) right' hh.2.2 hmr]
      simp only [historyAssignment,weight,historyAssignment_root,PairedFrequencyTreeSum.factor,
        PairedFrequencyTreeSum.modulus,reducedPair,hds,hds',hdv,hdw,hdv',hdw']

theorem scheduleMatches_ambientData (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (p : List Bool) {l : ℕ}
    (h h' : History l) (hm : ScheduleMatches d f p h h') :
    ScheduleMatches (fun q => Characters.Template.ambientData K R (d q)) f p h h' := by
  induction h generalizing p with
  | leaf a => cases h'; trivial
  | node a pivot u hp hm0 left right ihl ihr =>
    cases h' with
    | node b pivot' u' hp' hm' left' right' =>
      obtain ⟨hs,hs',hv,hw,hv',hw',hf,hf',hml,hmr⟩ := hm
      exact ⟨hs,hs',hv,hw,hv',hw',hf,hf',ihl _ _ hml,ihr _ _ hmr⟩

theorem ambient_schedule_budget_eq_historyWeight (S : List Bool → Finset (ℤ × ℤ))
    (K R : ℕ) (C : NNReal) (ε : ℝ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (p : List Bool)
    {l : ℕ} (h h' : History l) (hh : LabelsIn S p h h') (hm : ScheduleMatches d f p h h') :
    ((FrequencyExposure.budget C ε (fun q => Characters.Template.ambientData K R (d q)) l p).value : ℝ) =
      weight S (PairedFrequencyTreeSum.factor (C : ℝ) ε) (historyAssignment S p h h' hh) :=
  schedule_budget_eq_historyWeight S C ε _ f p h h' hh
    (scheduleMatches_ambientData K R d f p h h' hm)

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
