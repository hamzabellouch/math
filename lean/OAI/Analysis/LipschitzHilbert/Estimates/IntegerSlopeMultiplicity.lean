import OAI.Analysis.LipschitzHilbert.Trees.SourceSlopeLabels

namespace OAI

/-! The fixed angular lattice has local multiplicity independently of
its finite truncation. These bounds supply the model's label hypothesis. -/
noncomputable section
namespace LipschitzHilbert.SourceSlopeLabels

 theorem integer_slope_multiplicity_one (labels : Finset ℤ) (offset spacing : ℝ)
    (hspacing : 0<spacing) :
    LocalMultiplicity labels (fun n : ℤ => offset+spacing*(n:ℝ)) spacing 1 := by
  classical
  intro a
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hupper : spacing*((i:ℝ)-(j:ℝ))<spacing := by linarith
  have hlower : spacing*((j:ℝ)-(i:ℝ))<spacing := by linarith
  have hu : (i:ℝ)-(j:ℝ)<1 := (mul_lt_mul_iff_right₀ hspacing).mp (by nlinarith only [hupper])
  have hl : (j:ℝ)-(i:ℝ)<1 := (mul_lt_mul_iff_right₀ hspacing).mp (by nlinarith only [hlower])
  have habs : |(i:ℝ)-(j:ℝ)|<1 := abs_lt.mpr ⟨by linarith,hu⟩
  have hInt : |i-j|<(1:ℤ) := by exact_mod_cast habs
  have habsInt := abs_lt.mp hInt
  omega

 theorem integer_slope_multiplicity (labels : Finset ℤ) (offset spacing precision : ℝ)
    (hspacing : 0<spacing) (_hprecision : 0≤precision) (K : ℕ)
    (hK : precision≤2*K*spacing) :
    LocalMultiplicity labels (fun n : ℤ => offset+spacing*(n:ℝ)) precision (2*K+1) := by
  classical
  intro a
  have hlocal := integer_slope_multiplicity_one labels offset spacing hspacing
  apply (Finset.card_le_card (show labels.filter (fun n : ℤ =>
      a≤offset+spacing*(n:ℝ) ∧ offset+spacing*(n:ℝ)<a+precision) ⊆
      window labels (fun n : ℤ => offset+spacing*(n:ℝ)) (a+precision/2) spacing K from ?_)).trans
    ((window_card_le labels (fun n : ℤ => offset+spacing*(n:ℝ)) hspacing hlocal
      (le_refl (K:ℝ))).trans_eq (by omega))
  intro n hn
  obtain ⟨hn,hlo,hhi⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨hn,abs_le.mpr ⟨?_,?_⟩⟩ <;> nlinarith

 theorem integer_label_multiplicity (labels : Finset ℤ) (offset spacing precision : ℝ)
    (hspacing : 0<spacing) (hprecision : 0≤precision) (K : ℕ)
    (hK : precision≤2*K*spacing) :
    LocalMultiplicity (Finset.univ : Finset labels)
      (fun n => offset+spacing*(n.val:ℝ)) precision (2*K+1) := by
  classical
  intro a
  have h := integer_slope_multiplicity labels offset spacing precision hspacing hprecision K hK a
  apply (Finset.card_le_card_of_injOn (fun n : labels => n.val) ?_ ?_).trans h
  · intro n hn
    exact Finset.mem_filter.mpr ⟨n.property,(Finset.mem_filter.mp hn).2⟩
  · intro n _ m _ heq
    exact Subtype.ext heq

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
