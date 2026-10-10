import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.TriangleDrift

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave

noncomputable def finish {n : ℕ} (G : Graph n) : PMF (Graph n) :=
  evolve G G.card

theorem pmf_bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  apply PMF.ext
  intro b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem evolve_eq_finish {n : ℕ} (G : Graph n) (k : ℕ) (hk : G.card ≤ k) :
    evolve G k = finish G := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact evolve_stable G G.card l le_rfl

theorem finish_absorbing {n : ℕ} (G : Graph n) (hG : triangles G = ∅) :
    finish G = PMF.pure G := evolve_absorbing G hG G.card

theorem finish_harmonic {n : ℕ} (G : Graph n) :
    finish G = (step G).bind finish := by
  have heq : evolve G (1 + G.card) = (step G).bind (fun H => evolve H G.card) := by
    rw [evolve_add]
    simp [evolve]
  rw [evolve_eq_finish G _ (by omega)] at heq
  rw [heq]
  apply pmf_bind_congr_support
  intro H hH
  exact evolve_eq_finish H G.card (Finset.card_le_card (step_support_subset hH))

def scanAction {n : ℕ} (G : Graph n) (t : Finset (Fin n)) : Graph n :=
  if t ∈ triangles G then G \ t.powersetCard 2 else G

noncomputable def scanLaw {n : ℕ} : ℕ → Graph n → Finset (Finset (Fin n)) → PMF (Graph n)
  | 0, G, _ => PMF.pure G
  | k + 1, G, C =>
      if h : C.Nonempty then
        (PMF.uniformOfFinset C h).bind (fun t => scanLaw k (scanAction G t) (C.erase t))
      else PMF.pure G

theorem scanAction_subset {n : ℕ} (G : Graph n) (t : Finset (Fin n)) :
    scanAction G t ⊆ G := by
  unfold scanAction
  split_ifs
  · exact Finset.sdiff_subset
  · exact Finset.Subset.rfl

theorem triangle_not_mem_delete {n : ℕ} (G : Graph n) (t : Finset (Fin n)) :
    t ∉ triangles (G \ t.powersetCard 2) := by
  intro ht
  have hc : (t.powersetCard 2).card = 3 := by
    simp [(mem_triangles.mp ht).1]
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (t.powersetCard 2).card)
  exact (Finset.mem_sdiff.mp ((mem_triangles.mp ht).2 he)).2 he

theorem triangles_scanAction_subset {n : ℕ} (G : Graph n) (C : Finset (Finset (Fin n)))
    (hC : triangles G ⊆ C) (t : Finset (Fin n)) :
    triangles (scanAction G t) ⊆ C.erase t := by
  intro u hu
  apply Finset.mem_erase.mpr
  refine ⟨?_, hC (triangles_mono (scanAction_subset G t) hu)⟩
  intro heq
  subst u
  by_cases ht : t ∈ triangles G
  · exact triangle_not_mem_delete G t (by simpa [scanAction, ht] using hu)
  · exact ht (triangles_mono (scanAction_subset G t) hu)

theorem finish_mean_uniform_candidates {n : ℕ} (G : Graph n)
    (C : Finset (Finset (Fin n))) (hC : C.Nonempty) (hall : triangles G ⊆ C)
    (f : Graph n → ℝ) :
    pmfMean (PMF.uniformOfFinset C hC) (fun t => pmfMean (finish (scanAction G t)) f) =
      pmfMean (finish G) f := by
  classical
  by_cases hG : (triangles G).Nonempty
  · let w : ℝ := pmfMean (finish G) f
    have hw : ∑ t ∈ triangles G, pmfMean (finish (G \ t.powersetCard 2)) f =
        ((triangles G).card : ℝ) * w := by
      have hh := congrArg (fun p => pmfMean p f) (finish_harmonic G)
      rw [pmfMean_bind, step_mean G _ hG] at hh
      have hpos : (0 : ℝ) < (triangles G).card := by exact_mod_cast hG.card_pos
      have he := (div_eq_iff hpos.ne').mp hh.symm
      simpa only [mul_comm] using he
    rw [pmfMean_uniformOfFinset]
    have hsplit : C = (triangles G) ∪ (C \ triangles G) := by
      exact (Finset.union_sdiff_of_subset hall).symm
    have hsum : ∑ t ∈ C, pmfMean (finish (scanAction G t)) f = (C.card : ℝ) * w := by
      have hdisj : Disjoint (triangles G) (C \ triangles G) := by
        exact Finset.disjoint_left.mpr fun t ht hdiff => (Finset.mem_sdiff.mp hdiff).2 ht
      conv_lhs => rw [hsplit]
      rw [Finset.sum_union hdisj]
      have hfirst : ∑ t ∈ triangles G, pmfMean (finish (scanAction G t)) f =
          ((triangles G).card : ℝ) * w := by
        calc
          _ = ∑ t ∈ triangles G, pmfMean (finish (G \ t.powersetCard 2)) f := by
            apply Finset.sum_congr rfl
            intro t ht
            simp [scanAction, ht]
          _ = _ := hw
      rw [hfirst]
      have hsecond : ∑ t ∈ C \ triangles G, pmfMean (finish (scanAction G t)) f =
          ((C \ triangles G).card : ℝ) * w := by
        calc
          _ = ∑ _t ∈ C \ triangles G, w := Finset.sum_congr rfl fun t ht => by
            simp [scanAction, (Finset.mem_sdiff.mp ht).2, w]
          _ = _ := by simp
      rw [hsecond, Finset.card_sdiff_of_subset hall, Nat.cast_sub (Finset.card_le_card hall)]
      ring
    rw [hsum]
    exact mul_div_cancel_left₀ w (by exact_mod_cast hC.card_pos.ne')
  · have ht : triangles G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    have heq : (fun t => pmfMean (finish (scanAction G t)) f) =
        (fun _ => pmfMean (finish G) f) := by
      funext t
      simp [scanAction, ht]
    rw [heq, pmfMean_const]

theorem pmf_ext_mean {α : Type*} [Fintype α] (p q : PMF α)
    (h : ∀ f : α → ℝ, pmfMean p f = pmfMean q f) : p = q := by
  classical
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp
  simpa [pmfMean] using h (fun b => if b = a then 1 else 0)

theorem scan_mean_eq_finish {n : ℕ} (k : ℕ) (G : Graph n)
    (C : Finset (Finset (Fin n))) (hk : C.card ≤ k) (hall : triangles G ⊆ C)
    (f : Graph n → ℝ) : pmfMean (scanLaw k G C) f = pmfMean (finish G) f := by
  classical
  induction k generalizing G C with
  | zero =>
    have hC : C = ∅ := Finset.card_eq_zero.mp (by omega)
    have ht : triangles G = ∅ := Finset.subset_empty.mp (hC ▸ hall)
    simp [scanLaw, finish_absorbing G ht]
  | succ k ih =>
    by_cases hC : C.Nonempty
    · rw [scanLaw, dite_eq_left hC, pmfMean_bind]
      calc
        _ = pmfMean (PMF.uniformOfFinset C hC)
            (fun t => pmfMean (finish (scanAction G t)) f) := by
          apply pmfMean_congr
          intro t ht
          have htC : t ∈ C := by simpa using ht
          exact ih (scanAction G t) (C.erase t)
            (by rw [Finset.card_erase_of_mem htC]; omega)
            (triangles_scanAction_subset G C hall t)
        _ = _ := finish_mean_uniform_candidates G C hC hall f
    · have hCe : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      have ht : triangles G = ∅ := Finset.subset_empty.mp (hCe ▸ hall)
      simp [scanLaw, hC, finish_absorbing G ht]

theorem scanLaw_eq_finish {n : ℕ} (k : ℕ) (G : Graph n)
    (C : Finset (Finset (Fin n))) (hk : C.card ≤ k) (hall : triangles G ⊆ C) :
    scanLaw k G C = finish G :=
  pmf_ext_mean _ _ (scan_mean_eq_finish k G C hk hall)

theorem scan_complete_eq_terminalLaw (n : ℕ) :
    scanLaw (triangles (completeGraph n)).card (completeGraph n)
      (triangles (completeGraph n)) = terminalLaw n := by
  rw [scanLaw_eq_finish _ _ _ le_rfl (by rfl)]
  simp [finish, terminalLaw]

end SharpTerminalLeave

end

end OAI
