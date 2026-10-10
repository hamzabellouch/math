import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionLocal

namespace OAI

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistorySupportReduction
open Construction

theorem supported_iff_root_coprime_reduced {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ}
    (h : History l) (hlarge : LargePrimes V h) :
    h.Supported V outside ↔ h.root.Coprime outside ∧ Reduced V outside h := by
  induction h with
  | leaf a =>
    simp only [History.Supported,Reduced,RootData,History.root]
    tauto
  | @node l a p u hp hm left right ihl ihr =>
    have hleftLarge := hlarge.2.2.1
    have hrightLarge := hlarge.2.2.2
    rw [Reduced]
    constructor
    · intro hs
      have hsplit := (History.supported_node_iff V outside a p u hp hm left right).mp hs
      refine ⟨History.supported_root_coprime hs,rootData_of_supported hs,hsplit.1.2.2,
        localTests_of_supported_node hs hlarge.2.1,?_,?_⟩
      · exact ((ihl hleftLarge).mp (History.supported_left hs)).2
      · exact ((ihr hrightLarge).mp (History.supported_right hs)).2
    · rintro ⟨hcop,hdata,hrel,htests,hl,hr⟩
      have hldata : RootData V left := by
        have hh := hl
        rw [Reduced.eq_def] at hh
        exact hh.1
      have hrdata : RootData V right := by
        have hh := hr
        rw [Reduced.eq_def] at hh
        exact hh.1
      obtain ⟨hlcop,hrcop⟩ := child_coprime_of_reduced_data hcop hrel htests hldata hrdata
        (largePrimes_root hleftLarge) (largePrimes_root hrightLarge)
      have hls := (ihl hleftLarge).mpr ⟨hlcop,hl⟩
      have hrs := (ihr hrightLarge).mpr ⟨hrcop,hr⟩
      obtain ⟨hpos,hprime,htemplate,hfreq,hbound,hguard⟩ := hdata
      obtain ⟨hpositive,hroles,hperm,hlp,hrp,hlm,hrm,hlsmall,hrsmall,hN⟩ := hrel
      rw [History.Supported]
      exact ⟨hpos,hprime,htemplate,hcop,hfreq,hbound,hguard,hpositive,hroles,hperm,
        hlp,hrp,hlm,hrm,hlsmall,hrsmall,hN,hls,hrs⟩

theorem supportedWeight_eq_reduced (V : ℕ → ℕ) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ) {l : ℕ} (h : History l)
    (hlarge : LargePrimes V h) :
    h.supportedWeight V outside base φ G =
      if h.root.Coprime outside ∧ Reduced V outside h then h.weight base φ G else 0 := by
  classical
  simp only [History.supportedWeight,supported_iff_root_coprime_reduced h hlarge]

end Ostmann.Arithmetic.HistorySupportReduction

end

end OAI
