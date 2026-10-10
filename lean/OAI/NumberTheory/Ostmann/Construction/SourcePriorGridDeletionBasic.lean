import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer
import OAI.NumberTheory.Ostmann.Construction.LogCellReindex
import OAI.NumberTheory.Ostmann.Construction.SourcePriors

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction.SourcePriorGridDeletion

def gridMean (G : ℝ) (E : Finset ℕ) (F : ℕ→ℂ) : ℂ :=
  ∑p∈logCellPrimes G,((logCellWeight G p/logCellMass G E:ℝ):ℂ)*F p

def deletedMean (G : ℝ) (E : Finset ℕ) (F : ℕ→ℂ) : ℂ :=
  ∑p∈logCellPrimes G\E,((logCellWeight G p/logCellMass G E:ℝ):ℂ)*F p

def pointCap (G : ℝ) (E : Finset ℕ) : ℝ := Real.exp (1-G)/logCellMass G E

def deletionCap (G : ℝ) (E : Finset ℕ) : ℝ := E.card*pointCap G E

def fullMassRatio (G : ℝ) (E : Finset ℕ) : ℝ := logCellMass G ∅/logCellMass G E

theorem source_cmean_eq_deletedMean (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (F : ℕ→ℂ) :
    (logCellPrimeSource G E hZ).law.cmean (fun p => F p)=deletedMean G E F := by
  change (∑p : LogCellSample G E,
    ((logCellWeight G p/(∑q : LogCellSample G E,logCellWeight G q):ℝ):ℂ)*F p)=_
  rw [logCell_sample_sum]
  exact Finset.sum_coe_sort (logCellPrimes G\E)
    (fun p : ℕ => ((logCellWeight G p/logCellMass G E:ℝ):ℂ)*F p)

theorem finite_complex_deletion_bound (S E : Finset ℕ) (w : ℕ→ℝ) (F : ℕ→ℂ)
    {C A : ℝ} (hC : 0≤C) (hA : 0≤A) (hw : ∀p,0≤w p) (hbound : ∀p,w p≤C)
    (hF : ∀p∈S,w p≠0→‖F p‖≤A) :
    ‖(∑p∈S,(w p:ℂ)*F p)-(∑p∈S\E,(w p:ℂ)*F p)‖≤(E.card:ℝ)*C*A := by
  have heq := Finset.sum_sdiff (f:=fun p => (w p:ℂ)*F p)
    (Finset.inter_subset_left (s₁:=S) (s₂:=E))
  rw [Finset.sdiff_inter_self_left] at heq
  have he : (∑p∈S,(w p:ℂ)*F p)-(∑p∈S\E,(w p:ℂ)*F p)=
      ∑p∈S∩E,(w p:ℂ)*F p := by rw [←heq]; ring
  rw [he]
  calc
    _ ≤ ∑p∈S∩E,‖(w p:ℂ)*F p‖ := norm_sum_le _ _
    _ ≤ ∑_p∈S∩E,C*A := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hz : w p=0
      · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero]
        exact mul_nonneg hC hA
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw p)]
        exact (mul_le_mul_of_nonneg_left (hF p (Finset.mem_inter.mp hp).1 hz) (hw p)).trans
          (mul_le_mul_of_nonneg_right (hbound p) hA)
    _ = ((S∩E).card:ℝ)*(C*A) := by simp
    _ ≤ _ := by
      have hc : ((S∩E).card:ℝ)≤E.card := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=S) (s₂:=E))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (mul_nonneg hC hA)

theorem gridMean_sub_deletedMean_le (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (F : ℕ→ℂ) {A : ℝ} (hA : 0≤A)
    (hF : ∀p∈logCellPrimes G,logCellWeight G p≠0→‖F p‖≤A) :
    ‖gridMean G E F-deletedMean G E F‖≤deletionCap G E*A := by
  apply finite_complex_deletion_bound (logCellPrimes G) E
    (fun p => logCellWeight G p/logCellMass G E) F
    (div_nonneg (Real.exp_pos _).le hZ.le) hA
    (fun p => div_nonneg (logCellWeight_nonneg G p) hZ.le)
    (fun p => div_le_div_of_nonneg_right (logCellWeight_le_exp G p) hZ.le)
  intro p hp hn
  exact hF p hp (fun hz => hn (by rw [hz,zero_div]))

theorem gridMean_sub_source_cmean_le (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (F : ℕ→ℂ) {A : ℝ} (hA : 0≤A)
    (hF : ∀p∈logCellPrimes G,logCellWeight G p≠0→‖F p‖≤A) :
    ‖gridMean G E F-(logCellPrimeSource G E hZ).law.cmean (fun p => F p)‖≤deletionCap G E*A := by
  rw [source_cmean_eq_deletedMean]
  exact gridMean_sub_deletedMean_le G E hZ F hA hF

theorem normalized_weights_sum (G : ℝ) (E : Finset ℕ) :
    (∑p∈logCellPrimes G,logCellWeight G p/logCellMass G E)=fullMassRatio G E := by
  rw [←Finset.sum_div]
  rfl

theorem gridMean_norm_le (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (F : ℕ→ℂ) {A : ℝ} (_hA : 0≤A)
    (hF : ∀p∈logCellPrimes G,logCellWeight G p≠0→‖F p‖≤A) :
    ‖gridMean G E F‖≤fullMassRatio G E*A := by
  calc
    _ ≤ ∑p∈logCellPrimes G,‖((logCellWeight G p/logCellMass G E:ℝ):ℂ)*F p‖ := norm_sum_le _ _
    _ ≤ ∑p∈logCellPrimes G,(logCellWeight G p/logCellMass G E)*A := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hz : logCellWeight G p=0
      · simp [hz]
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (logCellWeight_nonneg G p) hZ.le)]
        exact mul_le_mul_of_nonneg_left (hF p hp hz)
          (div_nonneg (logCellWeight_nonneg G p) hZ.le)
    _ = _ := by rw [←Finset.sum_mul,normalized_weights_sum]

end Ostmann.Construction.SourcePriorGridDeletion

end

end OAI
