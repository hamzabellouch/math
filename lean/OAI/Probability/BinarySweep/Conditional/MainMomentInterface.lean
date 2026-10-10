import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.ManySparse
import OAI.Probability.BinarySweep.GridBounds.BalancedGrid

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Irrep Representation Signed

def SpechtMomentBound (q : ℕ) {b : ℕ} (bits : Fin b → ℕ) (z : ℝ) : Prop :=
  ∀h : ℕ, ∀H : PathFamily bits h, ∀μ : YoungDiagram, ∀e : Cell μ ≃ FreeSlot H 0,
  evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
    (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
    Real.exp (-cExponent (gridSize bits)*diagramF μ+
      eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H)

lemma spechtMomentBound_enumerated {q b : ℕ} {bits : Fin b → ℕ} {z : ℝ}
    (hB : SpechtMomentBound q bits z) : EnumeratedMomentBound q bits z := by
  intro h H α
  let e : Cell (diagram α) ≃ FreeSlot H 0 :=
    (cellsEquivFin α).trans (Fintype.equivFin _).symm
  have hb := hB h H (diagram α) e
  have he : groupAverage ((hilbertSpecht (diagram α)).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ)) =
      groupAverage (partitionHilbertRep α)
        (fun a => (conditionalGroupLaw H z ((Fintype.equivFin _).symm.permCongr a):ℂ)) := by
    rw [groupAverage_comp_slots]
    symm
    rw [partitionHilbertRep,groupAverage_comp_slots]
    rfl
  rw [he] at hb
  simpa only [typeF,hilbertSpecht_finrank,diagramF] using hb

lemma hilbert_specht_complete {X V : Type*} [Fintype X] [DecidableEq X]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm X) V) [ρ.IsIrreducible] :
    ∃(μ : YoungDiagram) (e : Cell μ ≃ X), Nonempty (ρ.Equiv
      ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)) := by
  obtain ⟨μ,e,⟨f⟩⟩ := specht_complete ρ
  let σ : Representation ℂ (Equiv.Perm X) (SpechtSpace μ) := (spechtRep μ).comp e.symm.permCongrHom.toMonoidHom
  let τ : Representation ℂ (Equiv.Perm X) (SpechtHilbert μ) := (hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom
  have a : σ.Equiv τ := .mk (spechtHilbertEquiv μ) (by
    intro g
    apply LinearMap.ext
    intro v
    change spechtHilbertEquiv μ (spechtRep μ _ v)=
      spechtHilbertEquiv μ (spechtRep μ _ ((spechtHilbertEquiv μ).symm (spechtHilbertEquiv μ v)))
    rw [LinearEquiv.symm_apply_apply])
  exact ⟨μ,e,⟨f.trans a⟩⟩

lemma spechtMomentBound_main {q b : ℕ} {bits : Fin b → ℕ} {z : ℝ}
    (hB : SpechtMomentBound q bits z) (h D : ℕ) (H : PathFamily bits h)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hρ : IsUnitaryRep ρ) :
    logMoment (traceMoment q (conditionalOperator H z ρ)) ≤
      ((-cExponent (gridSize bits)*Real.log D+
        eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H:ℝ):EReal) := by
  obtain ⟨μ,e,⟨f⟩⟩ := hilbert_specht_complete ρ
  have he := equivalent_evenMoment _ _ f hρ (fun g v => hilbertSpecht_unitary μ _ v)
    (fun g => (conditionalGroupLaw H z g:ℂ)) q
  have hD := f.toLinearEquiv.finrank_eq
  rw [finrank_euclideanSpace_fin,hilbertSpecht_finrank] at hD
  apply (logMoment_le_iff_le_exp _ _).mpr
  rw [conditionalMoment_evenMoment,he]
  simpa only [hD,diagramF] using hB h H μ e

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Young Irrep Representation GridSplit

theorem conditional_moment_main : ConditionalMomentTarget := by
  obtain ⟨S,hS⟩ := sparse_closing_radius
  have hq : 2 ≤ mainMomentPower := by norm_num [mainMomentPower]
  obtain ⟨T,hT⟩ := eventually_atTop.mp (dense_induction_step_eventually mainMomentPower hq)
  let A : ℝ := max ((10:ℝ)^26) ((max S T:ℕ):ℝ)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨r,hr⟩ := exists_nat_gt (max (2:ℝ) (A/Real.log 2))
  have hr2 : 2 ≤ r := by
    have : (2:ℝ) < r := (le_max_left _ _).trans_lt hr
    exact_mod_cast this.le
  have hrA : A ≤ (r:ℝ)*Real.log 2 := by
    have : A/Real.log 2 < r := (le_max_right _ _).trans_lt hr
    exact (div_lt_iff₀ hlog2).mp this |>.le
  have hrL : (10:ℝ)^26 ≤ (r:ℝ)*Real.log 2 := (le_max_left _ _).trans hrA
  have hrM : ((max S T:ℕ):ℝ) ≤ (r:ℝ)*Real.log 2 := (le_max_right _ _).trans hrA
  have hr4 : (4000000000:ℝ) ≤ (r:ℝ)*Real.log 2 := by linarith
  obtain ⟨δ,hδ,hδline,hsp⟩ := hS r hr2 hr4
  let zStar := min δ (oneAxisRadius r)
  have hzStar : 0 < zStar := lt_min hδ (oneAxisRadius_pos r)
  have hlarge {b : ℕ} (hb : 1 ≤ b) (bits : Fin b → ℕ)
      (hd : ∀j,r ≤ bits j ∧ bits j ≤ 2*r) :
      max S T ≤ gridSize bits ∧ (10:ℝ)^26 ≤ Real.log (gridSize bits) := by
    have hl := grid_log_lower (fun j => (hd j).1)
    have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
    have hr0 : 0 ≤ (r:ℝ)*Real.log 2 := by positivity
    have hbase : (r:ℝ)*Real.log 2 ≤ Real.log (gridSize bits) := by
      have := mul_le_mul_of_nonneg_right hbR hr0
      nlinarith
    refine ⟨?_,hrL.trans hbase⟩
    have hpos : (0:ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
    have hexp := Real.log_le_sub_one_of_pos hpos
    have : ((max S T:ℕ):ℝ) ≤ gridSize bits := by linarith [hrM.trans hbase]
    exact_mod_cast this
  have hproof : ∀b : ℕ, 1 ≤ b → ∀bits : Fin b → ℕ,
      (∀j,r ≤ bits j ∧ bits j ≤ 2*r) → ∀z : ℝ, 0 ≤ z → z ≤ zStar →
      SpechtMomentBound mainMomentPower bits z := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro hb bits hd z hz hzr h H μ e
      by_cases hb1 : b=1
      · subst b
        have := irreducible_comp_equiv e.symm.permCongrHom (hilbertSpecht μ)
        have hbase := hilbert_conditional_one_axis (by linarith : (400000000:ℝ) ≤ (r:ℝ)*Real.log 2)
          (by omega : 0 < mainMomentPower) bits hd H hz (hzr.trans (min_le_right _ _))
          ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
          (fun g v => hilbertSpecht_unitary μ _ v)
        simpa only [hilbertSpecht_finrank,diagramF] using hbase
      · have hb2 : 2 ≤ b := by omega
        obtain ⟨m,n,rfl,hm,hn,hmb,hnb,hmn,hnm⟩ := balanced_counts b hb2
        obtain ⟨hsize,hL⟩ := hlarge hb bits hd
        by_cases hF : (gridSize bits:ℝ)^(399/400:ℝ) ≤ diagramF μ
        · obtain ⟨hu,hv,hub,hvb,haxes⟩ := balanced_grid_bounds bits hm hn hmn hnm hd (by linarith)
          apply hT (gridSize bits) ((le_max_right S T).trans hsize) m n h r bits H rfl
            hu hv hub hvb (fun j => (hd j).2) haxes μ e hF z hz
            ((hzr.trans (min_le_left _ _)).trans hδline)
          · apply spechtMomentBound_enumerated
            exact ih m hmb hm (leftBits bits) (fun j => hd (j.castAdd n)) z hz hzr
          · apply spechtMomentBound_enumerated
            exact ih n hnb hn (rightBits bits) (fun j => hd (j.natAdd m)) z hz hzr
        · exact hsp (gridSize bits) ((le_max_left S T).trans hsize) (m+n) h bits rfl hb hd hL H μ e
            (lt_of_not_ge hF) z hz (hzr.trans (min_le_left _ _))
  refine ⟨r,by omega,mainMomentPower,by omega,zStar,hzStar,?_⟩
  intro b hb bits hd h H z hz hzr D ρ hi hρ
  have := hi
  exact spechtMomentBound_main (hproof b hb bits hd z hz hzr) h D H ρ hρ

end BinaryCoordinateSweeps

end

end OAI
