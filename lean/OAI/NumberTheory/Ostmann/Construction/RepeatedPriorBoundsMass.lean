import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsBasic
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsCenters
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsProduct

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
open Filter
open InitialEta RepeatedPriorBounds

theorem initial_jointPrior_mass_bound_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (hZ : 0<harmonicPrimeMass P),
      L/5000≤harmonicPrimeMass P →
      ∀ x : JointSample C.giant C.bulk (harmonicPrimeSource P hP hZ) C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2),
      (jointPrior C.giant C.bulk (harmonicPrimeSource P hP hZ) C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)).mass x ≤
      (5000/L)^(2*Conclusion.bulkSize k L)*Real.exp (24*(Conclusion.bulkSize k L:ℝ)) /
        (∏i,(tupleValues x i:ℝ)) := by
  filter_upwards [initial_cell_centers_eventually d Bs BD Bz hk,
    cell_mass_exp_bound_eventually,bulk_mass_lower_eventually,cell_center_ranges_eventually hk]
    with L hcenter hcell hbulk hr
  intro E C hG hGu hc hcu hb hd P hP hZ hspec x
  have hL : 0<L := by linarith [hr.1]
  have hcenter := hcenter E C hG hGu hc hcu hb hd
  have hinv {Z : ℝ} (hZl : L/5000≤Z) : Z⁻¹≤5000/L := by
    have h := one_div_le_one_div_of_le (by positivity : 0<L/(5000:ℝ)) hZl
    simpa only [one_div,inv_div] using h
  have hg : ∀p : C.giant.Sample,C.giant.law.mass p≤Real.exp L/(p:ℕ) :=
    hcell C.giantCenter hcenter.1.1 hcenter.1.2 ∅ (by simp) C.giantPositive
  have hbm : ∀p : C.bulk.Sample,C.bulk.law.mass p≤(5000/L)/(p:ℕ) := by
    apply harmonic_mass_le _ C.bulkPositive
    apply hinv
    have h := hbulk E C.deleted_card
    linarith
  have hsm : ∀p : (harmonicPrimeSource P hP hZ).Sample,
      (harmonicPrimeSource P hP hZ).law.mass p≤(5000/L)/(p:ℕ) :=
    harmonic_mass_le hP hZ (hinv hspec)
  have ham : ∀i,∀p : (C.auxiliary i).Sample,
      (C.auxiliary i).law.mass p≤Real.exp L/(p:ℕ) := by
    intro i
    have hc := hcenter.2 i
    cases i with
    | inl i => exact hcell (C.cells.top i) hc.1 hc.2 E C.deleted_card _
    | inr ji => exact hcell (C.cells.comp ji.1 ji.2) hc.1 hc.2 E C.deleted_card _
  have hprod := RepeatedPriorBounds.jointPrior_mass_le C.giant C.bulk
    (harmonicPrimeSource P hP hZ) C.auxiliary (Conclusion.bulkSize k L/2)
      (Conclusion.bulkSize k L/2) (5000/L) (Real.exp L) hg hbm hsm ham x
  have hcount : 2*(Conclusion.bulkSize k L/2)+2*(Conclusion.bulkSize k L/2)=
      2*Conclusion.bulkSize k L := by
    obtain ⟨n,hn⟩ := Conclusion.bulkSize_even k L
    omega
  rw [hcount,card_auxiliaryIndex,show 2+2*(3+2*k)=4*k+8 by omega,← Real.exp_nat_mul] at hprod
  apply hprod.trans
  apply div_le_div_of_nonneg_right _ (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (div_nonneg (by norm_num) hL.le) _)
  exact Real.exp_le_exp.mpr hr.2.2.2.2.2

end Ostmann.Construction

end

end OAI
