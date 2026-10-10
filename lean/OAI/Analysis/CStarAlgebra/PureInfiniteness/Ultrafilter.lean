import OAI.Analysis.CStarAlgebra.PureInfiniteness.Representation
import OAI.Analysis.CStarAlgebra.PureInfiniteness.Defect

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable (A : Type*)
abbrev FourIndex := ℕ × Finset A

def fourEta (i : FourIndex A) : ℝ := 1 / ((i.1 : ℝ)+1)

lemma fourEta_pos (i : FourIndex A) : 0 < fourEta A i := by
  unfold fourEta
  positivity

lemma fourEta_tendsto : Tendsto (fourEta A) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hf : Tendsto (fun i : FourIndex A => i.1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    filter_upwards [eventually_ge_atTop (n, (∅ : Finset A))] with i hi
    exact hi.1
  exact h.comp hf

lemma fourIndex_eventually_mem (w : A) : ∀ᶠ i : FourIndex A in atTop, w ∈ i.2 := by
  classical
  filter_upwards [eventually_ge_atTop ((0:ℕ), ({w} : Finset A))] with i hi
  exact hi.2 (Finset.mem_singleton_self w)

noncomputable def fourUltra : Ultrafilter (FourIndex A) := by
  classical
  exact Ultrafilter.of atTop

lemma fourUltra_le : (fourUltra A : Filter (FourIndex A)) ≤ atTop := by
  classical
  exact Ultrafilter.of_le atTop

lemma fourEta_ultra : Tendsto (fourEta A) (fourUltra A : Filter (FourIndex A)) (𝓝 0) :=
  (fourEta_tendsto A).mono_left (fourUltra_le A)
end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance ultrafilterPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance ultrafilterStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma cut_zero_of_le {d : A} (hd : 0 ≤ d) {h : ℝ} (hh : 0 ≤ h)
    (hle : d ≤ h • (1:A)) : cut d h = 0 := by
  have hdsa : IsSelfAdjoint d := .of_nonneg hd
  have hle' : cfc (fun t : ℝ => t) d ≤ cfc (fun _ : ℝ => h) d := by
    rw [cfc_id' ℝ d hdsa, cfc_const h d hdsa, Algebra.algebraMap_eq_smul_one]
    exact hle
  have hs := (cfc_le_iff _ _ d continuousOn_id continuousOn_const hdsa).mp hle'
  rw [cut_eq_cfc d hh, ← cfc_zero d (R := ℝ)]
  apply cfc_congr
  intro t ht
  exact max_eq_right (sub_nonpos.mpr (hs t ht))

lemma le_of_cut_zero {d : A} (hd : 0 ≤ d) {h : ℝ} (hh : 0 ≤ h)
    (hz : cut d h = 0) : d ≤ h • (1:A) := by
  have hn := norm_sub_cut_le hd hh
  rw [hz, sub_zero] at hn
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (CStarAlgebra.norm_le_iff_le_algebraMap d hh hd).mp hn

end MainGap

end

end OAI
