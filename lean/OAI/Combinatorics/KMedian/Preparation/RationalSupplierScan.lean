import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalCompletedCost
import OAI.Combinatorics.KMedian.Preparation.RationalPreparedScan
import OAI.Combinatorics.KMedian.Rounding.RationalRoundParameters
import OAI.Combinatorics.KMedian.Sparse.SparseSupplierSupport

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

structure Data (f n : ℕ) where
  y : Fin f → ℚ
  P : Fin n → Finset (Fin f)
  A : Fin n → Finset (Fin f)
  p : Fin n → ℚ
  c : Fin n → ℚ
  γ : ℚ
  hy : ∀ i, 0 ≤ y i
  hp : ∀ t, 0 < p t
  hP : Pairwise (fun s t => Disjoint (P s) (P t))
  hm : ∀ t, ∑ i ∈ P t, y i=p t
  hc : ∀ t, ∑ i ∈ A t, y i=c t
  hc0 : ∀ t, 0 ≤ c t
  hc1 : ∀ t, c t ≤ 1/8
  hunit : ∀ t, p t+c t=1
  hγ : 0 < γ
  hγ1 : γ ≤ 1

namespace FixedParameters
theorem positive {τ : ℝ} (qR : FixedBatch.RationalParameters τ) : 0<qR.g := by exact_mod_cast qR.gpos
theorem grid {τ : ℝ} (qR : FixedBatch.RationalParameters τ) : qR.g*(qR.Δ:ℚ)=1 := by exact_mod_cast qR.unit
end FixedParameters

namespace Data
variable {f n j : ℕ} {τ : ℝ} (D : Data f n) (qR : FixedBatch.RationalParameters τ)

def law := SparsePrepared.law (RationalSuppliers.D D.A) a
  (q D.y D.P D.A D.c D.γ qR.g) qR.Δ D.P D.y D.p a_bounds
  (q_nonneg D.y D.P D.A D.c D.γ qR.g D.hy D.hc0 D.hγ.le (FixedParameters.positive qR).le)

noncomputable def coupled (heven : Even qR.Δ) := RationalSuppliers.coupled D.y D.P D.A D.p D.c D.γ qR.g qR.Δ
  D.hy D.hp D.hP D.hm D.hc D.hc0 D.hc1 D.hunit D.hγ D.hγ1 (FixedParameters.positive qR) heven (FixedParameters.grid qR)

def tables : List (Fin (f+n*f) → ℕ) :=
  (D.law qR).states.toList.map (counts D.y D.P D.A D.c D.γ qR.g)

theorem tables_support (heven : Even qR.Δ)
    (z : (D.coupled qR heven).Ω × (Fin n → Finset (Fin f)))
    (hz : 0 < ((D.coupled qR heven).ν.joint (D.coupled qR heven).κ).weight z) :
    ∃ N ∈ D.tables qR, ∀ a, N a=physicalCount (D.coupled qR heven) z (physicalIndex a) := by
  obtain ⟨b,hb⟩ := coupled_support D.y D.P D.A D.p D.c D.γ qR.g qR.Δ
    D.hy D.hp D.hP D.hm D.hc D.hc0 D.hc1 D.hunit D.hγ D.hγ1
    (FixedParameters.positive qR) heven (FixedParameters.grid qR) z hz
  refine ⟨counts D.y D.P D.A D.c D.γ qR.g (D.law qR).states[b.val],?_,hb⟩
  apply List.mem_map.mpr
  exact ⟨(D.law qR).states[b.val],Vector.mem_toList_iff.mpr (Vector.getElem_mem b.isLt),rfl⟩

def scan (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ) (B : ℚ) :=
  qR.roundList df dc (original (f:=f) (n:=n)) (D.tables qR) B

theorem score_reindex {X : Type} [PseudoMetricSpace X]
    (dc : Fin j → Fin f → ℚ) (i : Fin f → X) (client : Fin j → X)
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (r : Fin j → Physical (Fin f) (Fin n) → ℝ) :
    (∑ c, ∑ a : Fin (f+n*f), r c (physicalIndex a)*(dc c (original a):ℝ))=
      (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a)) := by
  apply sum_congr rfl
  intro c _
  have hd : ∀ a : Fin (f+n*f), (dc c (original a):ℝ)=
      dist (client c) (Sum.elim i (fun ti => i ti.2) (physicalIndex a)) := by
    intro a
    rw [← hdc]
    unfold original
    cases physicalIndex a <;> rfl
  simp only [hd]
  exact (physicalIndex (f:=f) (n:=n)).sum_comp
    (fun a => r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a))

theorem scan_certificate {X : Type} [PseudoMetricSpace X]
    (hτ : τ<1) (hj : 0<j)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (B : ℚ) (ns : List (Fin (f+n*f) → ℕ)) (n₀ : Physical (Fin f) (Fin n) → ℕ)
    (N : Fin (f+n*f) → ℕ) (hN : N∈ns)
    (heq : ∀ a, N a=n₀ (physicalIndex a))
    (hcap : ∀ a, n₀ a ≤ qR.Δ)
    (hm : 1 ≤ ∑ a, (qR.g:ℝ)*(n₀ a:ℝ))
    (hB : (∑ a, (qR.g:ℝ)*(n₀ a:ℝ))+(qR.allowance:ℝ) ≤ (B:ℝ))
    (r : Fin j → Physical (Fin f) (Fin n) → ℝ)
    (hr : ∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ (qR.g:ℝ)*(n₀ a:ℝ)) ∧
      (∑ a, r c a)=1) :
    ∃ O : Finset (Fin f), qR.roundList df dc (original (f:=f) (n:=n)) ns B=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (B:ℝ) ∧
      (Completion.Rational.score dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*
        (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a)) := by
  have hmass : (∑ a, (qR.g:ℝ)*(N a:ℝ)) = ∑ a, (qR.g:ℝ)*(n₀ a:ℝ) := by
    simp only [heq]
    exact (physicalIndex (f:=f) (n:=n)).sum_comp (fun a => (qR.g:ℝ)*(n₀ a:ℝ))
  obtain ⟨O,hO,hOn,hOc,hOs⟩ := qR.roundList_spec hτ hj df dc i client hdf hdc (original (f:=f) (n:=n))
    (ns) B N hN (by intro a; rw [heq]; exact hcap (physicalIndex a))
    (by rwa [hmass]) (by rwa [hmass]) (fun c a => r c (physicalIndex a))
    (fun c a => (hr c).1 (physicalIndex a) |>.1)
    (fun c a => by rw [heq]; exact ((hr c).1 (physicalIndex a)).2)
    (fun c => ((physicalIndex (f:=f) (n:=n)).sum_comp (r c)).trans (hr c).2)
  refine ⟨O,hO,hOn,hOc,?_⟩
  rwa [score_reindex dc i client hdc r] at hOs

theorem scan_feasible {X : Type} [PseudoMetricSpace X]
    (heven : Even qR.Δ) (hτ : τ<1) (hj : 0<j)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (B : ℚ) (z : (D.coupled qR heven).Ω × (Fin n → Finset (Fin f)))
    (hz : 0 < ((D.coupled qR heven).ν.joint (D.coupled qR heven).κ).weight z)
    (hcap : ∀ a, physicalCount (D.coupled qR heven) z a ≤ qR.Δ)
    (hm : 1 ≤ ∑ a, (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ))
    (hB : (∑ a, (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ))+(qR.allowance:ℝ) ≤ (B:ℝ))
    (r : Fin j → Physical (Fin f) (Fin n) → ℝ)
    (hr : ∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ)) ∧
      (∑ a, r c a)=1) :
    ∃ O : Finset (Fin f), D.scan qR df dc B=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (B:ℝ) ∧
      (Completion.Rational.score dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*
        (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a)) := by
  obtain ⟨N,hN,heq⟩ := D.tables_support qR heven z hz
  exact scan_certificate qR hτ hj df dc i client hdf hdc B (D.tables qR)
    (physicalCount (D.coupled qR heven) z) N hN heq hcap hm hB r hr

end Data
end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
