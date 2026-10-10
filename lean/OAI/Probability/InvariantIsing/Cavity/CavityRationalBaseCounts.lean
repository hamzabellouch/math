import OAI.Probability.InvariantIsing.Cavity.CavityRationalCounts
import OAI.Probability.InvariantIsing.Cavity.CavityOrderedBase

namespace OAI

/-! The special axes have exactly the missing rational multiplicities,
so the retained-plus-special base spectrum equals the prescribed count. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityBaseGroupDimension_filter_card {m d : ℕ} (k : Fin m → ℕ)
    (g : Fin d → Fin m) (a : Fin m) :
    cavityBaseGroupDimension k g a=k a+(Finset.univ.filter (fun j => g j=a)).card := by
  simp only [cavityBaseGroupDimension, Fintype.card_subtype]

lemma cavityRationalBase_counts {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) (a : Fin m) :
    cavityBaseGroupDimension (fun a => cavityRationalCount s (d+n+3) (r+1) a-n) g a=
      cavityRationalCount s (d+n+3) r a := by
  rw [cavityBaseGroupDimension_filter_card, hg]
  exact cavityRationalRetained_base s hs hsum r a

lemma cavityRationalBase_sum {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) :
    ∑ a, cavityBaseGroupDimension (fun a => cavityRationalCount s (d+n+3) (r+1) a-n) g a=
      (r+(d+n+3))*n := by
  simp_rw [cavityRationalBase_counts s hs hsum g hg r]
  exact cavityRationalCount_sum s hsum (d+n+3) r

end InvariantIsing

end

end OAI
