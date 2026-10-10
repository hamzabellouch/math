import OAI.Analysis.LipschitzHilbert.Fourier.LineWeightAverage

namespace OAI

/-! Averaging along selected generations of the actual line grid. Angular
blocks may have different numbers of steps; no uniform block length is needed. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.FiniteLineGrid

/-- The ancestor map across any number of generations of the same grid. -/
def ancestor (g : FiniteLineGrid) (steps : ℕ) (i : Fin (g.branching^g.depth)) :
    Fin (g.branching^g.depth) :=
  ⟨i.val/g.branching^steps,(Nat.div_le_self _ _).trans_lt i.isLt⟩

theorem rawIndex_add_div (g : FiniteLineGrid) (level steps : ℕ) (x : ℝ) :
    g.rawIndex (level+steps) x/g.branching^steps = g.rawIndex level x := by
  induction steps with
  | zero => simp
  | succ steps ih =>
    rw [pow_succ,mul_comm (g.branching^steps) g.branching,← Nat.div_div_eq_div_mul]
    rw [show level+(steps+1) = (level+steps)+1 by omega,g.rawIndex_parent,ih]

theorem index_ancestor (g : FiniteLineGrid) {coarse fine : ℕ}
    (hcf : coarse ≤ fine) (hf : fine ≤ g.depth) (x : ℝ) :
    g.index coarse x = g.ancestor (fine-coarse) (g.index fine x) := by
  apply Fin.ext
  change g.rawIndex (min coarse g.depth) x =
    g.rawIndex (min fine g.depth) x/g.branching^(fine-coarse)
  rw [Nat.min_eq_left (hcf.trans hf),Nat.min_eq_left hf]
  have h := g.rawIndex_add_div coarse (fine-coarse) x
  rw [Nat.add_sub_of_le hcf] at h
  exact h.symm

private theorem nonnegative_profile {α κ : Type} (P : α → κ) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hconstant : ∀ x y, P x = P y → f x = f y) :
    ∃ c : κ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ x, f x = c (P x) := by
  classical
  let c := fun i => if h : ∃ x, P x = i then f h.choose else 0
  refine ⟨c,?_,?_⟩
  · intro i
    dsimp only [c]
    split_ifs with h
    · exact hf _
    · exact le_rfl
  · intro x
    have h : ∃ y, P y = P x := ⟨x,rfl⟩
    dsimp only [c]
    rw [dite_eq_left h]
    exact hconstant x h.choose h.choose_spec.symm

/-- The conditional-average product estimate on any increasing list of
actual generations, including the initial short angular block. -/
theorem skipped_product_average (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (level : ℕ → ℕ) (N : ℕ) (hlevel : ∀ n ≤ N, level n ≤ g.depth)
    (hmono : ∀ n < N, level n ≤ level (n+1)) (Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ n < N, ∀ x, 0 ≤ Γ n x)
    (hconstant : ∀ n < N, ∀ x y,
      g.index (level (n+1)) x = g.index (level (n+1)) y → Γ n x = Γ n y)
    (haverage : ∀ n < N, ∀ i : Fin (g.branching^g.depth),
      (∫ x in {x | g.index (level n) x = i}, Γ n x ∂μ) ≤
        μ.real {x | g.index (level n) x = i}) :
    Integrable (fun x => ∏ n ∈ Finset.range N, Γ n x) μ ∧
      (∫ x, ∏ n ∈ Finset.range N, Γ n x ∂μ) ≤ μ.real Set.univ := by
  classical
  have hprofile : ∀ n : ℕ, ∃ c : Fin (g.branching^g.depth) → ℝ,
      (∀ i, 0 ≤ c i) ∧
        ∀ x, (if n < N then Γ n x else 1) = c (g.index (level (n+1)) x) := by
    intro n
    apply nonnegative_profile
    · intro x
      split_ifs with hn
      · exact hΓ n hn x
      · exact zero_le_one
    · intro x y hxy
      split_ifs with hn
      · exact hconstant n hn x y hxy
      · rfl
  choose c hc heq using hprofile
  let P := fun n => g.index (level n)
  let R := fun n => g.ancestor (level (n+1)-level n)
  have hrefine : ∀ n < N, ∀ x, P n x = R n (P (n+1) x) := by
    intro n hn x
    exact g.index_ancestor (hmono n hn) (hlevel (n+1) (by omega)) x
  have hprod : (fun x => ∏ n ∈ Finset.range N, Γ n x) =
      fun x => ∏ n ∈ Finset.range N, c n (P (n+1) x) := by
    funext x
    apply Finset.prod_congr rfl
    intro n hn
    simpa only [ite_eq_left (Finset.mem_range.mp hn)] using heq n x
  rw [hprod]
  refine ⟨integrable_nested_product μ P R c N (g.measurable_index_fiber _) hrefine,?_⟩
  apply nested_average_product_le μ P R c N
    (fun n _ => g.measurable_index_fiber (level n)) hrefine (fun n _ => hc n)
  intro n hn i
  simpa only [P,← heq n,ite_eq_left hn] using haverage n hn i

/-- The same skipped-generation product can be integrated against the
original decaying top weight. -/
theorem top_weight_skipped_average (g : FiniteLineGrid) (T : SlopeBox) (y : ℝ)
    {K D : ℝ} (hK : 1 ≤ K) (hD : 0 ≤ D) (hwidth : g.width ≤ T.length)
    (level : ℕ → ℕ) (N : ℕ) (hlevel : ∀ n ≤ N, level n ≤ g.depth)
    (hmono : ∀ n < N, level n ≤ level (n+1)) (Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ n < N, ∀ x, 0 ≤ Γ n x)
    (hconstant : ∀ n < N, ∀ x z,
      g.index (level (n+1)) x = g.index (level (n+1)) z → Γ n x = Γ n z)
    (haverage : ∀ n < N, ∀ i : Fin (g.branching^g.depth),
      (∫ x in {x | g.index (level n) x = i}, Γ n x ∂volume.restrict g.root) ≤
        (volume.restrict g.root).real {x | g.index (level n) x = i}) :
    Integrable (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ n ∈ Finset.range N, Γ n x) (volume.restrict g.root) ∧
      (∫ x in g.root, T.weight K D (x,y+T.slope*x)*∏ n ∈ Finset.range N, Γ n x) ≤
        Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x) := by
  let : IsFiniteMeasure (volume.restrict g.root) := isFiniteMeasure_restrict.mpr (by
    simp only [root,Real.volume_Ico,ENNReal.ofReal_ne_top,ne_eq,not_false_eq_true])
  let c := Real.exp (-D)*T.weight K D (g.origin,y+T.slope*g.origin)
  have hc : 0 ≤ c := (mul_pos (Real.exp_pos _) (T.weight_pos (by linarith) _ _)).le
  have hcompare : ∀ᵐ x ∂volume.restrict g.root,
      c ≤ T.weight K D (x,y+T.slope*x) ∧
      T.weight K D (x,y+T.slope*x) ≤ Real.exp (2*D)*c := by
    filter_upwards [ae_restrict_mem (show MeasurableSet g.root from measurableSet_Ico)] with x hx
    have h := T.line_weight_comparable g.origin y x hK hD hwidth hx
    refine ⟨h.1,h.2.trans_eq ?_⟩
    dsimp only [c]
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  obtain ⟨hint,havg⟩ := g.skipped_product_average (volume.restrict g.root) level N hlevel hmono
    Γ hΓ hconstant haverage
  exact weighted_average_le (volume.restrict g.root)
    (fun x => T.weight K D (x,y+T.slope*x)) _ hc (Real.exp_pos _).le
    ((T.continuous_weight (by linarith) D).comp (by fun_prop)).aestronglyMeasurable
    hint (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun n hn =>
      hΓ n (Finset.mem_range.mp hn) x)
    (hcompare.mono fun _ h => h.1) (hcompare.mono fun _ h => h.2) havg

end LipschitzHilbert.FiniteLineGrid

end

end OAI
