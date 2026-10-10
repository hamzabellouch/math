import OAI.Combinatorics.BalancedRyser.Profiles.ProfileEmpiricalMeasure

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

universe u

variable {A : ProfileClass.{u}} {a : ℝ}
variable {K : ℕ → Type u} [∀ n, Field (K n)] [∀ n, Fintype (K n)]
  [∀ n, DecidableEq (K n)]

theorem ProfileClassSizeGap.eventually_empty
    (hgap : ProfileClassSizeGap a A)
    (D C : ∀ n, Finset (Line (K n)))
    (hA : ∀ n, A (K n) (D n) (C n)) {c : ℝ}
    (hlim : Tendsto (fun n => ((C n).card : ℝ) /
      (Fintype.card (K n) : ℝ)) atTop (𝓝 c)) (hca : c < a) :
    ∀ᶠ n in atTop, C n = ∅ := by
  filter_upwards [hlim.eventually (Iio_mem_nhds hca)] with n hn
  rcases hgap (K n) (D n) (C n) (hA n) with hz | hlarge
  · exact Finset.card_eq_zero.mp hz
  · have hq : (0 : ℝ) < Fintype.card (K n) := by
      exact_mod_cast Fintype.card_pos (α := K n)
    have ha : a ≤ ((C n).card : ℝ) / (Fintype.card (K n) : ℝ) :=
      (le_div_iff₀ hq).2 hlarge
    exact (not_le_of_gt hn ha).elim

theorem ProfileClassSizeGap.limit_dichotomy
    (hgap : ProfileClassSizeGap a A)
    (D C : ∀ n, Finset (Line (K n)))
    (hA : ∀ n, A (K n) (D n) (C n)) {c : ℝ}
    (hlim : Tendsto (fun n => ((C n).card : ℝ) /
      (Fintype.card (K n) : ℝ)) atTop (𝓝 c)) :
    c = 0 ∨ a ≤ c := by
  have hclosed : IsClosed ({0} ∪ Set.Ici a : Set ℝ) :=
    isClosed_singleton.union isClosed_Ici
  have hmem : c ∈ ({0} ∪ Set.Ici a : Set ℝ) := by
    apply hclosed.mem_of_tendsto hlim
    filter_upwards with n
    rcases hgap (K n) (D n) (C n) (hA n) with hz | hlarge
    · left
      simp [hz]
    · right
      have hq : (0 : ℝ) < Fintype.card (K n) := by
        exact_mod_cast Fintype.card_pos (α := K n)
      exact (le_div_iff₀ hq).2 hlarge
  simpa only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ici] using hmem

theorem exists_visible_profile_subsequence
    (k : ℕ) (hvalid : ProfileClassValid k A)
    (hgap : ProfileClassSizeGap a A) (hvisible : ProfileVisibleExcess A)
    (D C : ∀ n, Finset (Line (K n)))
    (hA : ∀ n, A (K n) (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop) :
    ∃ c ∈ Set.Icc (0 : ℝ) 1, (c = 0 ∨ a ≤ c) ∧
      ∃ P : Profile, IsBoundedProfile (2 * (k : ℝ) + 4) P ∧
      ∃ νD νC : FiniteMeasure Profile, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ n, A (K (φ n)) (D (φ n)) (C (φ n))) ∧
        Tendsto (fun n => Fintype.card (K (φ n))) atTop atTop ∧
        ProfileSequenceLimit (fun n => D (φ n)) (fun n => C (φ n)) c P νD νC ∧
        c < (νD : Measure Profile).real (deletionVisible P) +
          (νC : Measure Profile).real (coverVisible P) := by
  have hpair (n : ℕ) : IsProfilePair k (D n) (C n) :=
    hvalid (K n) (D n) (C n) (hA n)
  obtain ⟨c, hc, P, hP, νD, νC, φ, hφ, hlim⟩ :=
    exists_actual_profile_subsequence k D C (fun n => (hpair n).1)
      (fun n => (hpair n).2.2)
  have hA' : ∀ n, A (K (φ n)) (D (φ n)) (C (φ n)) := fun n => hA (φ n)
  have hq' : Tendsto (fun n => Fintype.card (K (φ n))) atTop atTop :=
    hq.comp hφ.tendsto_atTop
  have hgap' := hgap.limit_dichotomy (fun n => D (φ n))
    (fun n => C (φ n)) hA' hlim.1
  refine ⟨c, hc, hgap', P, hP, νD, νC, φ, hφ, hA', hq', hlim, ?_⟩
  exact hvisible (fun n => K (φ n)) (fun n => D (φ n))
    (fun n => C (φ n)) hA' hq' c P νD νC hlim

end Balanced

end

end OAI
