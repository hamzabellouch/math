import OAI.Probability.DilutedSpin.CavityEndpointCount

namespace OAI

section
namespace DilutedSpinGlass
lemma snoc_exponents_pos {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    ∀ i : Fin (r+1),0 < Fin.snoc (α := fun _ => ℝ) m (1:ℝ) i := by
  intro i
  exact Fin.lastCases (by simp) (fun j => by simpa using (hm.2 j).1) i
lemma snoc_exponents_mono {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    Monotone (Fin.snoc (α := fun _ => ℝ) m (1:ℝ)) := by
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    simpa only [Fin.snoc_last] using
      (Fin.lastCases (by simp) (fun a => by simpa using (hm.2 a).2.le) i : Fin.snoc (α := fun _ => ℝ) m (1:ℝ) i≤1)
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact False.elim ((not_le_of_gt (Fin.castSucc_lt_last j)) hij)
    | cast i =>
      simpa only [Fin.snoc_castSucc] using hm.1.monotone (show i≤j from hij)
lemma cons_snoc_exponents_mono {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    Monotone (Fin.cons (α := fun _ => ℝ) (0:ℝ) (Fin.snoc (α := fun _ => ℝ) m (1:ℝ))) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact le_refl _
    | succ j => simpa using (snoc_exponents_pos hm j).le
  | succ i =>
    induction j using Fin.cases with
    | zero => exact False.elim ((not_le_of_gt (Fin.succ_pos i)) hij)
    | succ j =>
      simpa only [Fin.cons_succ] using snoc_exponents_mono hm (show i≤j from Fin.succ_le_succ_iff.mp hij)
lemma cons_snoc_exponents_nonneg {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    ∀ i,0 ≤ Fin.cons (α := fun _ => ℝ) (0:ℝ) (Fin.snoc (α := fun _ => ℝ) m (1:ℝ)) i := by
  intro i
  exact Fin.cases (by simp) (fun j => by simpa using (snoc_exponents_pos hm j).le) i
end DilutedSpinGlass

end

end OAI
