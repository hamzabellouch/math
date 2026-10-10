import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

namespace Yau.Geometry
open Set
open scoped ContDiff
noncomputable section
variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def finiteChartDerivativeValues (P : Finset I) (Q : Set E) (J : ℕ) (f : I → E → F) : Set ℝ :=
  {0} ∪ {t | ∃ p ∈ P, ∃ i, i ≤ J ∧ ∃ x ∈ Q, t = ‖iteratedFDeriv ℝ i (f p) x‖}

def finiteChartDerivativeSize (P : Finset I) (Q : Set E) (J : ℕ) (f : I → E → F) : ℝ :=
  sSup (finiteChartDerivativeValues P Q J f)

lemma finiteChartDerivativeValues_nonempty (P : Finset I) (Q : Set E) (J : ℕ) (f : I → E → F) :
    (finiteChartDerivativeValues P Q J f).Nonempty := ⟨0,Or.inl rfl⟩

lemma finiteChartDerivativeValues_bddAbove (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    BddAbove (finiteChartDerivativeValues P Q J f) := by
  classical
  have hb (p : P) (i : Fin (J+1)) : ∃ C : ℝ, ∀ x ∈ Q, ‖iteratedFDeriv ℝ i.val (f p) x‖ ≤ C :=
    hQ.exists_bound_of_continuousOn ((hf p p.property).continuous_iteratedFDeriv
      (by exact_mod_cast (show (i.val:ℕ∞) ≤ ⊤ from le_top))).continuousOn
  choose C hC using hb
  let B : ℝ := 1+∑ p : P, ∑ i, |C p i|
  have hsum : 0 ≤ ∑ p : P, ∑ i, |C p i| :=
    Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))
  refine ⟨B,?_⟩
  rintro t (ht | ⟨p,hp,i,hi,x,hx,rfl⟩)
  · have ht0 : t=0 := ht
    rw [ht0]
    change 0 ≤ 1+∑ p : P, ∑ i, |C p i|
    linarith
  · let pi : P := ⟨p,hp⟩
    let ii : Fin (J+1) := ⟨i,by omega⟩
    have hci : C pi ii ≤ ∑ p : P, ∑ j, |C p j| :=
      (le_abs_self _).trans ((Finset.single_le_sum (fun j _ ↦ abs_nonneg (C pi j)) (Finset.mem_univ ii)).trans
        (Finset.single_le_sum (fun p _ ↦ Finset.sum_nonneg (fun j _ ↦ abs_nonneg (C p j))) (Finset.mem_univ pi)))
    exact (hC pi ii x hx).trans (by change C pi ii ≤ 1+∑ p : P, ∑ j, |C p j|; linarith)

lemma finiteChartDerivativeSize_le (P : Finset I) (Q : Set E) (J : ℕ) (f : I → E → F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ p ∈ P, ∀ i, i ≤ J → ∀ x ∈ Q,
      ‖iteratedFDeriv ℝ i (f p) x‖ ≤ C) : finiteChartDerivativeSize P Q J f ≤ C := by
  apply csSup_le (finiteChartDerivativeValues_nonempty P Q J f)
  rintro t (ht | ⟨p,hp,i,hi,x,hx,rfl⟩)
  · have ht0 : t=0 := ht
    simpa only [ht0] using hC
  · exact hb p hp i hi x hx

lemma finiteChartDerivativeSize_nonneg (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    0 ≤ finiteChartDerivativeSize P Q J f :=
  le_csSup (finiteChartDerivativeValues_bddAbove P hQ J f hf) (Or.inl rfl)

lemma norm_le_finiteChartDerivativeSize (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p))
    (p : I) (hp : p ∈ P) (i : ℕ) (hi : i ≤ J) (x : E) (hx : x ∈ Q) :
    ‖iteratedFDeriv ℝ i (f p) x‖ ≤ finiteChartDerivativeSize P Q J f :=
  le_csSup (finiteChartDerivativeValues_bddAbove P hQ J f hf) (Or.inr ⟨p,hp,i,hi,x,hx,rfl⟩)

lemma finiteChartDerivativeSize_add_le (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f g : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p))
    (hg : ∀ p ∈ P, ContDiff ℝ ∞ (g p)) :
    finiteChartDerivativeSize P Q J (fun p x ↦ f p x+g p x) ≤
      finiteChartDerivativeSize P Q J f+finiteChartDerivativeSize P Q J g := by
  apply finiteChartDerivativeSize_le _ _ _ _
    (add_nonneg (finiteChartDerivativeSize_nonneg P hQ J f hf) (finiteChartDerivativeSize_nonneg P hQ J g hg))
  intro p hp i hi x hx
  rw [fun_iteratedFDeriv_add_apply
    ((hf p hp).of_le (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    ((hg p hp).of_le (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_le_finiteChartDerivativeSize P hQ J f hf p hp i hi x hx)
    (norm_le_finiteChartDerivativeSize P hQ J g hg p hp i hi x hx))

end
end Yau.Geometry

end OAI
