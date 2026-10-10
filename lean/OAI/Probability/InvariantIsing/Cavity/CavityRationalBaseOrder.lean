import OAI.Probability.InvariantIsing.Cavity.CavityRationalBaseCounts

namespace OAI

/-! The base spectrum from the physical coupling is exactly the canonical
ordered rational spectrum, including its group labels. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityRationalBase_order {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin ((r+(d+n+3))*n)) :
    let k := fun a => cavityRationalCount s (d+n+3) (r+1) a-n
    let hbase := cavityRationalBase_sum s hs hsum g hg r
    Sum.elim (fun w => w.1) g ((cavityOrderedBase k g hbase).symm i)=
      cavityOrderedGroup (cavityRationalCount s (d+n+3) r)
        (cavityRationalCount_sum s hsum (d+n+3) r) i := by
  intro k hbase
  rw [cavityOrderedBase_label]
  have hcount : cavityBaseGroupDimension k g=cavityRationalCount s (d+n+3) r := by
    funext a
    exact cavityRationalBase_counts s hs hsum g hg r a
  simp only [hcount]

end InvariantIsing

end

end OAI
