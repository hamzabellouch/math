import OAI.NumberTheory.DukePrimeDegree.Dynamics.MautnerLatticeL2

namespace OAI

/-!
# Almost invariance extends from a dense subgroup

Continuity of the actual pullback representation on lattice L² extends
almost invariance of an observable from a dense subgroup. This does not
turn pointwise invariance into a topological assertion about a measurable
observable; the continuous object is its L² equivalence class.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem lattice_function_ae_fixed_of_dense
    {n : ℕ} (H : Subgroup (G n))
    {S : Type*} [Group S] (φ : S →* H) (hdense : DenseRange φ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ)
    (f : X n → ℝ) (hf : MemLp f 2 μ)
    (hfix : ∀ s : S, (fun x : X n => f (φ s • x)) =ᵐ[μ] f) :
    ∀ h : H, (fun x : X n => f (h • x)) =ᵐ[μ] f := by
  let : SMulInvariantMeasure H (X n) μ :=
    ⟨fun h B hB => (latticeSubgroup_preserving H μ hH h).measure_preimage
      hB.nullMeasurableSet⟩
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let F : Lp ℝ 2 μ := hf.toLp f
  have hF : (F : X n → ℝ) =ᵐ[μ] f := hf.coeFn_toLp
  have hrep (h : H) : (DomMulAct.mk h • F : Lp ℝ 2 μ) =ᵐ[μ]
      (fun x : X n => f (h • x)) := by
    exact (DomMulAct.smul_Lp_ae_eq (DomMulAct.mk h) F).trans
      ((latticeSubgroup_preserving H μ hH h).quasiMeasurePreserving.ae_eq_comp hF)
  have hcont : Continuous (fun h : H => (DomMulAct.mk h • F : Lp ℝ 2 μ)) :=
    DomMulAct.continuous_mk.smul continuous_const
  have hfull (h : H) : (DomMulAct.mk h • F : Lp ℝ 2 μ) = F := by
    exact hdense.induction_on h (isClosed_eq hcont continuous_const)
      (fun s => Lp.ext (((hrep (φ s)).trans (hfix s)).trans hF.symm))
  intro h
  have he := hrep h
  rw [hfull h] at he
  exact he.symm.trans hF

end DukePrimeDegree

end

end OAI
