import OAI.Combinatorics.ContingencyTables.Transport.FinitePartialDraw
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts

namespace OAI

/-! # Exact integer-weighted choice for the residual correction branch -/

namespace ContingencyTables.ExactIntegerChoice
open MatchingFPRAS MatchingFPRAS.FiniteChoice ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {r : ℕ} (w : Fin r → ℕ)

def totalWeight : ℕ := ∑ i,w i

def normalized : Fin r → ℚ := fun i => (w i:ℚ)/totalWeight w

def prefixWeight (n : ℕ) : ℕ := ∑ i,if i.val<n then w i else 0

lemma normalized_nonnegative (i : Fin r) : 0≤normalized w i := by
  unfold normalized
  positivity

lemma normalized_total (h : 0<totalWeight w) : ∑ i,normalized w i=1 := by
  simp only [normalized,←Finset.sum_div,←Nat.cast_sum]
  exact div_self (by exact_mod_cast h.ne' : (totalWeight w:ℚ)≠0)

lemma cumulative_normalized (n : ℕ) :
    cumulative (normalized w) n=(prefixWeight w n:ℚ)/totalWeight w := by
  simp only [cumulative,normalized,prefixWeight,Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma grid_scaled_cumulative (h : 0<totalWeight w) (n : ℕ) :
    (totalWeight w:ℚ)*cumulative (normalized w) n=(prefixWeight w n:ℚ) := by
  rw [cumulative_normalized]
  exact mul_div_cancel₀ _ (by exact_mod_cast h.ne')

/-- On the integer grid with size equal to the total weight, the cumulative
selector has exactly the desired rational law, with no approximation. -/
theorem integer_choice_exact (h : 0<totalWeight w) (i : Fin r) :
    outputLaw (normalized w) (normalized_total w h) h i=normalized w i := by
  have hp := normalized_nonnegative w
  have hs := normalized_total w h
  rw [outputLaw_grid _ hp hs h i,gridInterval_card _ h _ _
    (cumulative_mono _ hp (by omega))
    (cumulative_le_one _ hp hs _ (by omega))]
  have hc (n : ℕ) : (⌈(totalWeight w:ℚ)*cumulative (normalized w) n⌉₊:ℚ)=
      (totalWeight w:ℚ)*cumulative (normalized w) n := by
    rw [grid_scaled_cumulative w h]
    simp
  rw [hc,hc,←mul_sub,cumulative_step]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast h.ne')

/-- One bounded trial rejects only the unused terminal indices. -/
def intervalTrial {V Q : ℕ} (_h : V≤Q) (j : Fin Q) : Option (Fin V) :=
  if hj : j.val<V then some ⟨j.val,hj⟩ else none

lemma intervalTrial_eq_some {V Q : ℕ} (h : V≤Q) (j : Fin Q) (x : Fin V) :
    intervalTrial h j=some x ↔ j=Fin.castLE h x := by
  by_cases hj : j.val<V
  · simp only [intervalTrial,dite_eq_left hj,Option.some.injEq,Fin.ext_iff,Fin.val_castLE]
  · have hn : j≠Fin.castLE h x := by
      intro he
      have hv := congrArg (fun z : Fin Q => z.val) he
      exact hj (hv ▸ x.isLt)
    simp only [intervalTrial,dite_eq_right hj,reduceCtorEq,hn]

lemma intervalTrial_mass {V Q : ℕ} [NeZero Q] (h : V≤Q) (x : Fin V) :
    (mapLaw (uniformLaw (α := Fin Q)) (intervalTrial h)).mass (some x)=1/(Q:ℚ) := by
  simp only [mapLaw,uniformLaw,uniformMass,Fintype.card_fin]
  simp_rw [intervalTrial_eq_some]
  simp

/-- A rational choice with integer weights, after a single binary rejection
trial. The sum of these masses is totalWeight / 2^k. -/
def weightedTrial (h : 0<totalWeight w) {Q : ℕ} (hQ : totalWeight w≤Q)
    (j : Fin Q) : Option (Fin r) :=
  (intervalTrial hQ j).map (choose (normalized w) (normalized_total w h) h)

lemma weightedTrial_mass (h : 0<totalWeight w) {Q : ℕ} [NeZero Q] (hQ : totalWeight w≤Q)
    (i : Fin r) :
    (mapLaw (uniformLaw (α := Fin Q)) (weightedTrial w h hQ)).mass (some i)=
      (w i:ℚ)/Q := by
  have hQpos : (0:ℚ)<Q := by exact_mod_cast h.trans_le hQ
  have hVpos : (0:ℚ)<totalWeight w := by exact_mod_cast h
  unfold weightedTrial
  rw [←mapLaw_comp]
  change (∑ j : Option (Fin (totalWeight w)),
    if j.map (choose (normalized w) (normalized_total w h) h)=some i then
      (mapLaw (uniformLaw (α := Fin Q)) (intervalTrial hQ)).mass j else 0)=_
  rw [Fintype.sum_option]
  simp only [Option.map_none,reduceCtorEq,ite_false,zero_add,Option.map_some,Option.some.injEq,
    intervalTrial_mass]
  have he := integer_choice_exact w h i
  unfold FiniteChoice.outputLaw at he
  have hc : ((Finset.univ.filter (fun j : Fin (totalWeight w) =>
      choose (normalized w) (normalized_total w h) h j=i)).card:ℚ)=w i := by
    change _/(totalWeight w:ℚ)=(w i:ℚ)/totalWeight w at he
    exact (div_left_inj' hVpos.ne').mp he
  have hsum : (∑ j : Fin (totalWeight w),
      if choose (normalized w) (normalized_total w h) h j=i then 1/(Q:ℚ) else 0)=
      (∑ j : Fin (totalWeight w),
        if choose (normalized w) (normalized_total w h) h j=i then (1:ℚ) else 0)/(Q:ℚ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hsum,Finset.sum_boole,hc]

end
end ContingencyTables.ExactIntegerChoice

end OAI
