import OAI.Probability.InvariantIsing.Core.FiniteMinmax

namespace OAI

/-! Finite extrema transport under shifts, order and continuous evaluation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

omit [Fintype V] [Nonempty V] in
lemma finiteRowMax_add_constant (H : U × V → ℝ) (a : ℝ) (v : V) :
    finiteRowMax (fun x => H x+a) v = finiteRowMax H v+a := by
  obtain ⟨u,hu,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun u => H (u,v))
  apply le_antisymm
  · apply Finset.sup'_le
    intro u _
    exact add_le_add (Finset.le_sup' (fun u => H (u,v)) (Finset.mem_univ u)) (le_refl a)
  · change (Finset.univ.sup' Finset.univ_nonempty (fun u => H (u,v)))+a ≤ _
    rw [he]
    exact Finset.le_sup' (fun u => H (u,v)+a) hu

lemma finiteMinmax_add_constant (H : U × V → ℝ) (a : ℝ) :
    finiteMinmax (fun x => H x+a) = finiteMinmax H+a := by
  obtain ⟨v,hv,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (finiteRowMax H)
  apply le_antisymm
  · calc
      _ ≤ finiteRowMax (fun x => H x+a) v := finiteMinmax_le_row _ v
      _ = finiteRowMax H v+a := finiteRowMax_add_constant H a v
      _ = finiteMinmax H+a := by rw [← he]; rfl
  · apply Finset.le_inf'
    intro v _
    rw [finiteRowMax_add_constant]
    exact add_le_add (finiteMinmax_le_row H v) (le_refl a)

lemma finiteMinmax_mono {H J : U × V → ℝ} (h : ∀ x, H x ≤ J x) :
    finiteMinmax H ≤ finiteMinmax J := by
  apply Finset.le_inf'
  intro v _
  apply (finiteMinmax_le_row H v).trans
  apply Finset.sup'_le
  intro u _
  exact (h (u,v)).trans (Finset.le_sup' (fun u => J (u,v)) (Finset.mem_univ u))

lemma finiteMinmax_abs_le (H : U × V → ℝ) (K : ℝ) (h : ∀ x, |H x| ≤ K) :
    |finiteMinmax H| ≤ K := by
  obtain ⟨v,_,hv⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (finiteRowMax H)
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun u => H (u,v))
  change |Finset.univ.inf' Finset.univ_nonempty _| ≤ K
  rw [hv]
  change |Finset.univ.sup' Finset.univ_nonempty _| ≤ K
  rw [hu]
  exact h (u,v)

lemma continuous_finiteMinmax {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) : Continuous (fun s => finiteMinmax (H s)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty (fun v _ =>
    Continuous.finset_sup'_apply Finset.univ_nonempty (fun u _ => hH (u,v)))

end InvariantIsing

end

end OAI
