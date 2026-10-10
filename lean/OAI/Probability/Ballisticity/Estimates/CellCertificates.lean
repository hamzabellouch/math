import Mathlib
import OAI.Probability.Ballisticity.Estimates.ScheduledCellSuccess

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma cellEarly_prefix_certificate {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (Hs He h : ℕ) (hh : h ≤ He)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    cellSeedMass e f a G Hs π ω*ENNReal.ofReal (cellEarlyMass e f hef a G Hs He π ω) ≤
      rawTupleMixture (realPosition (step e)) (Hs+h) (π ω).val ω {y | TupleSeparated f (G-G/4) y} := by
  let p := seedSeparatedProfile e f hef a G Hs (π ω) ω
  have hp : cellSeedMass e f a G Hs π ω • p.val=seedSeparatedRaw e f Hs G (π ω).val ω :=
    seedSeparatedProfile_mass e f hef a G Hs (π ω) ω
  have hi := budget_profile_prefix_certificate e f (a+Hs) G (G/4) p ω h He hh
  have he : ENNReal.ofReal (cellEarlyMass e f hef a G Hs He π ω)=relativeBudgetMassENN e f He (G/4) p.val ω := by
    change ENNReal.ofReal (relativeBudgetMass e f He (G/4) p.val ω)=_
    rw [←relativeBudgetMassENN_toReal,ENNReal.ofReal_toReal]
    exact (lt_of_le_of_lt (relativeBudgetMassENN_le_one e f He (G/4) p.val ω) ENNReal.one_lt_top).ne
  rw [he]
  calc
    _ ≤ cellSeedMass e f a G Hs π ω*rawTupleMixture (realPosition (step e)) h p.val ω
        {y | TupleSeparated f (G-G/4) y} := mul_le_mul_right hi _
    _ = rawTupleMixture (realPosition (step e)) h (cellSeedMass e f a G Hs π ω • p.val) ω
        {y | TupleSeparated f (G-G/4) y} := by
          rw [rawTupleMixture_smul,Measure.smul_apply,smul_eq_mul]
    _ ≤ rawTupleMixture (realPosition (step e)) h
        (rawTupleMixture (realPosition (step e)) Hs (π ω).val ω) ω
        {y | TupleSeparated f (G-G/4) y} := by
          rw [hp]
          exact (rawTupleMixture_mono _ _ _ Measure.restrict_le_self) _
    _ ≤ _ := rawTupleMixture_comp_le e Hs h (π ω).val ω _

lemma cellLate_prefix_certificate {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (Hs He s : ℕ) (H : ℕ → ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (n h : ℕ) (hh : h ≤ H n) (ω : Environment d) :
    (cellSeedMass e f a (c*ρ) Hs π ω*ENNReal.ofReal (cellEarlyMass e f hef a (c*ρ) Hs He π ω))*
      (∏ i∈Finset.range (n+1),ENNReal.ofReal (cellLateMass e f hef a c ρ hc hρ Hs He s H π i ω)) ≤
      rawTupleMixture (realPosition (step e)) (Hs+He+(∑ i∈Finset.range n,H i)+h) (π ω).val ω
        {y | TupleSeparated f (c*ρ/2) y} := by
  have hret := cellEarlyProfile_retained e f hef a (c*ρ) (mul_nonneg hc.le hρ.le) Hs He π ω
  have hh' := protection_prefix_after_retention e f (a+Hs+He) (3*c*ρ/4) H
    (lateBudget c ρ s) (fun i => (lateBudget_pos hc hρ s i).le)
    (cellLateInitial e f hef a c ρ hc.le hρ.le Hs He π) n h hh ω (π ω).val (Hs+He)
    (cellSeedMass e f a (c*ρ) Hs π ω*ENNReal.ofReal (cellEarlyMass e f hef a (c*ρ) Hs He π ω)) hret
  apply hh'.trans
  apply measure_mono
  intro y hy i j hij
  exact (lateBudget_gaps hc hρ s n).2.trans (hy i j hij)

lemma fullStream_prefix_certificate {d k : ℕ} (e : Direction d) (a : ℝ)
    (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) (t h : ℕ)
    (E : Set (Fin k → Lattice d)) (b : ℝ≥0∞)
    (hb : b ≤ rawTupleMixture (realPosition (step e)) h (fullTupleProfile e a t π ω).val ω E) :
    rawTupleMixture (realPosition (step e)) t π.val ω Set.univ*b ≤
      rawTupleMixture (realPosition (step e)) (t+h) π.val ω E := by
  calc
    _ ≤ rawTupleMixture (realPosition (step e)) t π.val ω Set.univ*
      rawTupleMixture (realPosition (step e)) h (fullTupleProfile e a t π ω).val ω E :=
        mul_le_mul_right hb _
    _ = rawTupleMixture (realPosition (step e)) h
      (rawTupleMixture (realPosition (step e)) t π.val ω) ω E := by
        conv_rhs => rw [←fullTupleProfile_mass e a t π ω]
        rw [rawTupleMixture_smul,Measure.smul_apply,smul_eq_mul]
    _ ≤ _ := rawTupleMixture_comp_le e t h π.val ω E

end DirectionalTransience

end

section

open scoped BigOperators
namespace DirectionalTransience

lemma cell_early_covers (v w m i s : ℕ) (hv : 2*cellWidth w m 0 ≤ v)
    (hi : i < m) (hs : 0 < s) (hsmall : m-i ≤ s) :
    cellOpportunity v w m i+cellWidth w m i ≤ v ∧
      cellOpportunity v w m i+cellWidth w m i+cellEarlyHeight v w m i s=v+w := by
  constructor
  · rw [cell_seed_endpoint v w m i hv hi]; omega
  · rw [cellEarly_endpoint v w m i s hv hi hs,min_eq_right hsmall,
      Nat.add_sub_of_le hi.le,cellOpportunity_last]

lemma cell_late_covers (v w m i s : ℕ) (hv : 2*cellWidth w m 0 ≤ v)
    (hi : i < m) (hs : 0 < s) (hlarge : s < m-i) :
    let n := m-i-s-1
    (cellOpportunity v w m i+cellWidth w m i+cellEarlyHeight v w m i s+
      (∑ j∈Finset.range n,cellLateHeight v w m i s j) ≤ v) ∧
    (cellOpportunity v w m i+cellWidth w m i+cellEarlyHeight v w m i s+
      (∑ j∈Finset.range n,cellLateHeight v w m i s j)+cellLateHeight v w m i s n=v+w) := by
  dsimp only
  have hmin : min s (m-i)=s := min_eq_left hlarge.le
  have hearly := cellEarly_endpoint v w m i s hv hi hs
  rw [hmin] at hearly
  have hlast : i+s+(m-i-s-1)=m-1 := by omega
  have hlast' : i+s+(m-i-s-1+1)=m := by omega
  have hprev := cellLate_endpoint v w m i s (m-i-s-1) hv (by omega)
  rw [hlast,←hearly] at hprev
  have hfin := cellLate_endpoint v w m i s (m-i-s-1+1) hv (by omega)
  rw [hlast',←hearly,Finset.sum_range_succ,cellOpportunity_last,←Nat.add_assoc] at hfin
  refine ⟨?_,hfin⟩
  rw [hprev]
  simp only [cellOpportunity,ite_eq_left (show m-1 < m by omega)]
  omega

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

theorem successful_cell_certificate {d k : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A : ℝ) (hc : 0 < c)
    (hA : 0 ≤ A) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (v w m s i : ℕ) (hv : 2*cellWidth w m 0 ≤ v) (hs : 0 < s)
    (ω : Environment d) (hS : ω ∈ scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π v w m s i)
    (t : ℕ) (hvt : v ≤ t) (ht : t ≤ v+w) :
    rawTupleMixture (realPosition (step e)) (cellOpportunity v w m i) (π ω).val ω Set.univ*
      (ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m))) ≤
    rawTupleMixture (realPosition (step e)) t (π ω).val ω
      {y | TupleSeparated f (c*cellRadius ν e f C w m i/2) y} := by
  have hi : i < m := by
    by_contra hh
    simp only [scheduledCellSuccess,ite_eq_right hh,Set.mem_empty_iff_false] at hS
  rw [scheduledCellSuccess,ite_eq_left hi] at hS
  let t₀ := cellOpportunity v w m i
  let ρ := cellRadius ν e f C w m i
  let π₀ := cellRestart e a π v w m i
  let Hs := cellWidth w m i
  let He := cellEarlyHeight v w m i s
  let H := cellLateHeight v w m i s
  have hρ : 0 < ρ := cellRadius_pos ν e f C w m i
  have hseed := hS.1
  have hear := hS.2.1
  have hlate := hS.2.2
  have hcoef : ENNReal.ofReal g₀*ENNReal.ofReal g₁ ≤
      cellSeedMass e f (a+t₀) (c*ρ) Hs π₀ ω*ENNReal.ofReal
        (cellEarlyMass e f hef (a+t₀) (c*ρ) Hs He π₀ ω) :=
    mul_le_mul hseed (ENNReal.ofReal_le_ofReal hear) zero_le zero_le
  suffices ∃ h : ℕ, t₀+h=t ∧
      ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m)) ≤
        rawTupleMixture (realPosition (step e)) h (π₀ ω).val ω
          {y | TupleSeparated f (c*ρ/2) y} by
    obtain ⟨h,he,hc⟩ := this
    have hh := fullStream_prefix_certificate e a (π ω) ω t₀ h _ _ hc
    rw [he] at hh
    exact hh
  by_cases hsmall : m-i ≤ s
  · obtain ⟨hstart,hend⟩ := cell_early_covers v w m i s hv hi hs hsmall
    have hb : t₀+Hs ≤ t := hstart.trans hvt
    let h := t-(t₀+Hs)
    have hhe : h ≤ He := by dsimp [h,He,t₀,Hs] at *; omega
    have he : t₀+(Hs+h)=t := by dsimp [h]; omega
    have hcert := cellEarly_prefix_certificate e f hef (a+t₀) (c*ρ) Hs He h hhe π₀ ω
    refine ⟨Hs+h,he,?_⟩
    apply le_trans _ (hcert.trans ?_)
    · apply le_trans _ hcoef
      have hexp : ENNReal.ofReal (Real.exp (-A*k*m)) ≤ 1 := by
        rw [←ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_one_iff.mpr
        have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
        have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
        nlinarith only [mul_nonneg (mul_nonneg hA hk0) hm0]
      simpa only [mul_one] using mul_le_mul_right hexp (ENNReal.ofReal g₀*ENNReal.ofReal g₁)
    · apply measure_mono
      intro y hy j l hjl
      have hg : c*ρ/2 ≤ c*ρ-c*ρ/4 := by nlinarith only [mul_pos hc hρ]
      exact hg.trans (hy j l hjl)
  · have hlarge : s < m-i := by omega
    let n := m-i-s-1
    obtain ⟨hstart,hend⟩ := cell_late_covers v w m i s hv hi hs hlarge
    change t₀+Hs+He+(∑ j∈Finset.range n,H j) ≤ v at hstart
    change t₀+Hs+He+(∑ j∈Finset.range n,H j)+H n=v+w at hend
    let z := t₀+Hs+He+(∑ j∈Finset.range n,H j)
    have hz : z ≤ t := hstart.trans hvt
    let h := t-z
    have hh : h ≤ H n := by dsimp [h,z] at *; omega
    have he : t₀+(Hs+He+(∑ j∈Finset.range n,H j)+h)=t := by dsimp [h,z]; omega
    have hcert := cellLate_prefix_certificate e f hef (a+t₀) c ρ hc hρ Hs He s H π₀ n h hh ω
    have hn : n < m-i-s := by dsimp [n]; omega
    have hpass := hlate n hn
    have hqn : ∀ j, 0 ≤ cellLateMass e f hef (a+t₀) c ρ hc hρ Hs He s H π₀ j ω := by
      intro j
      exact (protectionMass_bounds e f (a+t₀+Hs+He) (3*c*ρ/4) H (lateBudget c ρ s)
        (fun u => (lateBudget_pos hc hρ s u).le)
        (cellLateInitial e f hef (a+t₀) c ρ hc.le hρ.le Hs He π₀) j ω).1
    have hprod : ENNReal.ofReal (Real.exp (-A*k*m)) ≤
        ∏ j∈Finset.range (n+1),ENNReal.ofReal (cellLateMass e f hef (a+t₀) c ρ hc hρ Hs He s H π₀ j ω) := by
      rw [←ENNReal.ofReal_prod_of_nonneg (fun j _ => hqn j)]
      apply ENNReal.ofReal_le_ofReal
      apply le_trans _ hpass
      apply Real.exp_le_exp.mpr
      have hcst : (s:ℝ)+(n:ℝ)+1 ≤ m := by
        have hsn : s+n+1 ≤ m := by dsimp [n]; omega
        exact_mod_cast hsn
      have ha : 0 ≤ A*(k:ℝ) := mul_nonneg hA (Nat.cast_nonneg _)
      nlinarith only [mul_nonneg ha (sub_nonneg.mpr hcst)]
    exact ⟨_,he,(mul_le_mul hcoef hprod zero_le zero_le).trans hcert⟩

end DirectionalTransience

end

end OAI
