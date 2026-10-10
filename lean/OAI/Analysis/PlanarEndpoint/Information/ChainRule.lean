import OAI.Analysis.PlanarEndpoint.Information.FiniteLaws
import OAI.Analysis.PlanarEndpoint.Information.FiniteTables
import OAI.Analysis.PlanarEndpoint.Information.Logarithms
import OAI.Analysis.PlanarEndpoint.Information.Sampling

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S V W Y : Type*} [Fintype S] [Fintype V] [Fintype W] [Fintype Y]

omit [Fintype V] [Fintype Y] in
lemma le_sampledTable_self (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (v : S → V) (y : S → Y) (s : S) : a s ≤ sampledTable a v y (v s) (y s) := by
  unfold sampledTable
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun t => if v t = v s ∧ y t = y s then a t else 0)
    (fun t _ => by split_ifs; exact ha t; exact le_rfl) (Finset.mem_univ s)
  simpa only [and_self, ite_true] using h

omit [Fintype V] in
lemma sampledTable_row (a : S → ℝ) (v : S → V) (y : S → Y) (b : V) :
    rowMass (sampledTable a v y) b = ∑ s, if v s = b then a s else 0 := by
  unfold rowMass sampledTable
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : v s = b <;> simp [h, eq_comm]

omit [Fintype V] [Fintype W] [Fintype Y] in
lemma sampledTable_pair_target (a : S → ℝ) (v : S → V) (u : S → W)
    (y : S → Y) (b : V) (c : W) (z : Y) :
    sampledTable a v (fun s => (u s, y s)) b (c,z) =
      sampledTable a (fun s => (v s, u s)) y (b,c) z := by
  unfold sampledTable
  simp only [Prod.mk.injEq, and_assoc]

omit [Fintype V] [Fintype W] in
lemma sampledTable_pair_row (a : S → ℝ) (v : S → V) (u : S → W)
    (y : S → Y) (b : V) (c : W) :
    rowMass (sampledTable a (fun s => (v s, u s)) y) (b,c) =
      sampledTable a v u b c := by
  rw [sampledTable_row]
  simp only [sampledTable, Prod.mk.injEq]

omit [Fintype V]

lemma sampledInformation_chain (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (v : S → V) (u : S → W) (y : S → Y) {s : S} (hs : 0 < a s) (L : ℝ) :
    sampledInformation L a v (fun s => (u s, y s)) s =
      sampledInformation L a v u s +
        sampledInformation L a (fun s => (v s, u s)) y s := by
  let A := sampledTable a (fun s => (v s, u s)) y (v s,u s) (y s)
  let B := sampledTable a v u (v s) (u s)
  let D := rowMass (sampledTable a v u) (v s)
  have hA : 0 < A := hs.trans_le (le_sampledTable_self a ha _ y s)
  have hB : 0 < B := hs.trans_le (le_sampledTable_self a ha v u s)
  have hD : 0 < D := hB.trans_le (le_rowMass _ (sampledTable_nonneg a ha v u) _ _)
  have hrow : rowMass (sampledTable a v (fun s => (u s,y s))) (v s) = D := by
    rw [sampledTable_row]
    exact (sampledTable_row a v u (v s)).symm
  change information L (_ / _) = information L (B / D) + information L (_ / _)
  rw [sampledTable_pair_target, hrow, sampledTable_pair_row]
  change information L (A / D) = information L (B / D) + information L (A / B)
  have h := conditional_information_chain (L := L) (div_pos hA hD) (div_pos hB hD)
  have heq : (A / D) / (B / D) = A / B := by field_simp
  rwa [heq] at h

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

lemma finiteInformationLaw_chain (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (ha1 : ∑ s, a s = 1) (v : S → V) (u : S → W) (y : S → Y)
    (L : ℝ) (X : S → Ω) {f g h : Ω → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hrep : ∀ s, f (X s) = sampledInformation L a v (fun s => (u s,y s)) s ∧
      g (X s) = sampledInformation L a v u s ∧
      h (X s) = sampledInformation L a (fun s => (v s,u s)) y s) :
    f =ᵐ[(finiteInformationLaw a ha ha1 X : Measure Ω)] (fun x => g x + h x) := by
  apply finiteInformationLaw_ae a ha ha1 X (fun x => f x = g x + h x)
    (isClosed_eq hf (hg.add hh)).measurableSet
  intro s hs
  rw [(hrep s).1, (hrep s).2.1, (hrep s).2.2]
  exact sampledInformation_chain a ha v u y hs L

end PlanarEndpoint.TransverseInformation
end

end OAI
