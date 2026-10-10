import OAI.Analysis.PlanarPacking.FiniteProjection
import OAI.Analysis.PlanarPacking.Certificate.TableData

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open Numerical
lemma tableRaw_large {n : ℕ} (hn : 100<n) : tableRaw n=(0,0,0,0) := by
  unfold tableRaw
  split <;> first | omega | rfl
lemma tableC_large (a : Bool) {n : ℕ} (hn : 100<n) : tableC a n=0 := by
  simp [tableC,tableRaw_large hn,show n≠0 by omega]
lemma tableD_large (a : Bool) {n : ℕ} (hn : 100<n) : tableD a n=0 := by
  simp [tableD,tableRaw_large hn,show n≠0 by omega]
noncomputable def tableCoords (a : Bool) (ni : Node×Bool) : ℝ :=
  if ni.2 then (tableD a ni.1.val:ℝ) else (tableC a ni.1.val:ℝ)
lemma tableCoords_mem (a : Bool) : Memℓp (tableCoords a) 1 := by
  classical
  apply memℓp_gen
  have hs : (Function.support (fun ni => |tableCoords a ni|)).Finite := by
    apply (Set.finite_range finiteIndex).subset
    intro ni hni
    change (∃ i, finiteIndex i=ni)
    have hindex : (∃ i, finiteIndex i=ni) ↔ ni.1.val≤100 := by
      rcases ni with ⟨n,d⟩
      exact finiteIndex_range n d
    rw [hindex]
    by_contra hn
    have hn' : 100<ni.1.val := by omega
    have hz : tableCoords a ni=0 := by
      simp [tableCoords,tableD_large a hn',tableC_large a hn']
    exact hni (by simp [hz])
  simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using summable_of_hasFiniteSupport hs
noncomputable def tableList (a : Bool) : X := ⟨tableCoords a,tableCoords_mem a⟩
lemma tableList_apply (a : Bool) (ni : Node×Bool) :
    tableList a ni = if ni.2 then (tableD a ni.1.val:ℝ) else (tableC a ni.1.val:ℝ) := rfl
noncomputable def tableData (a : Bool) : CardinalData :=
  ⟨(tableConstant a:ℝ),(tableC a 0:ℝ),(tableD a 0:ℝ),tableList a⟩
lemma tableData_false : tableData false=fixed₁ (tableList false) := by
  simp [tableData,tableConstant,tableC,tableD,fixed₁]
lemma tableData_true : tableData true=fixed₂ (tableList true) := by
  simp [tableData,tableConstant,tableC,tableD,fixed₂]
lemma tableList_discard (a : Bool) : tableList a-IF (RF (tableList a))=0 := by
  apply lp.ext; funext ni
  have hh := finiteProjection_apply finiteIndex finiteIndex_injective (tableList a) ni
  change IF (RF (tableList a)) ni = _ at hh
  rw [lp.coeFn_sub,Pi.sub_apply,hh]
  rcases ni with ⟨n,d⟩
  simp only [finiteIndex_range]
  split
  · simp
  · have hn : 100<n.val := by omega
    simp [tableList_apply,tableD_large a hn,tableC_large a hn]
end SharpPlanar

end OAI
