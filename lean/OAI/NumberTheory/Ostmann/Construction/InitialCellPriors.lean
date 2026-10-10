import OAI.NumberTheory.Ostmann.Construction.SelectedInitialCells
import OAI.NumberTheory.Ostmann.Construction.FixedInitialCutoffMass

namespace OAI

/-! # The selected initial small cells on a common prime space -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialRegularPrimeRange (L : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊Real.exp (Real.exp ((11 / 1000 : ℝ) * L))⌋₊

theorem initialRegularPrimeRange_prime (L : ℝ) (p : ℕ)
    (hp : p ∈ initialRegularPrimeRange L) : p.Prime := Nat.prime_of_mem_primesLE hp

theorem mem_initialRegularPrimeRange (L : ℝ) (p : ℕ) (hp : p.Prime)
    (hbound : (p : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) :
    p ∈ initialRegularPrimeRange L := Nat.mem_primesLE.mpr ⟨Nat.le_floor hbound, hp⟩

theorem initial_broad_cell_subset (L α β : ℝ) (hL : 0 ≤ L) (hβ : β ≤ 11 / 1000)
    (D : Finset ℕ) :
    primeLogCellSet 1 0 (Real.exp (α * L)) (Real.exp (β * L)) \ D ⊆
      initialRegularPrimeRange L := by
  intro p hp
  obtain ⟨hprime, _, _, hlog⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
  apply mem_initialRegularPrimeRange L p hprime
  apply ((Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mp hlog).trans
  exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ hL))

theorem SelectedSmallTailCell.subset_initialRegularPrimeRange
    {A B : Set ℕ} {N hi j : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L Y hi D target j) :
    selectedTailCellPrimes A B N Y hi D j ⊆ initialRegularPrimeRange L := by
  intro p hp
  obtain ⟨_, _, hindex, _, _, _, hsupport⟩ := h
  have hs := hsupport p hp
  apply mem_initialRegularPrimeRange L p hs.1
  exact hs.2.2.1.trans (Real.exp_le_exp.mpr hindex)

theorem initialSmallCellList_property (top : ℕ) (centers : List ℕ) (P : ℕ → Prop)
    (htop : P top) (hcenters : ∀ j ∈ centers, P j) :
    ∀ j ∈ initialSmallCellList top centers, P j := by
  intro j hj
  simp only [initialSmallCellList, List.mem_append, List.mem_replicate, List.mem_flatMap] at hj
  rcases hj with ⟨_, rfl⟩ | ⟨w, hw, hjw⟩
  · exact htop
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hjw
    rcases hjw with rfl | rfl <;> exact hcenters _ hw

theorem initial_selected_cells_valid
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets) :
    ∀ j ∈ initialSmallCellList top centers,
      ∃ t, SelectedSmallTailCell A B N a C L Y hi D t j := by
  refine initialSmallCellList_property top centers
    (fun j => ∃ t, SelectedSmallTailCell A B N a C L Y hi D t j) ⟨target, htop⟩ ?_
  induction hcenters with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ⟨w / 4, hj⟩
    · exact ih i hi

/-- Append every actual top/compensation cell to the two already chosen
cutoff weights. The cells are not conditioned on any new event. -/
theorem initial_selected_cells_balanced_mass
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (P : Finset ℕ) (hsmallP : initialRegularPrimeRange L ⊆ P)
    (b d m : ℕ) (Qb Qd : Finset ℕ) (cb cd : ℝ)
    (hb : Real.exp (-(Real.log 2 + 2) * m) ≤
      ∑ x ∈ balancedTupleSet b (fun _ (p : P) =>
        (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
          residueDensity (tailDensityMask A N p) ≤ 2 / 3),
        productPrior (fun _ => primeSubsetPrior P Qb) x *
          initialLogSumWeight (fun p : P => (p : ℕ)) cb x)
    (hd : Real.exp (-(Real.log 2 + 2) * m) ≤
      ∑ x ∈ balancedTupleSet d (fun _ (p : P) =>
        (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
          residueDensity (tailDensityMask A N p) ≤ 2 / 3),
        productPrior (fun _ => primeSubsetPrior P Qd) x *
          initialLogSumWeight (fun p : P => (p : ℕ)) cd x) :
    let cells := initialSmallCellList top centers
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y hi D (cells.get i))
    let good := fun p : P => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
      residueDensity (tailDensityMask A N p) ≤ 2 / 3
    Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
      ∑ x ∈ balancedTupleSet (b + (d + cells.length)) (fun _ p => good p),
        productPrior (Fin.append (fun _ : Fin b => primeSubsetPrior P Qb)
          (Fin.append (fun _ : Fin d => primeSubsetPrior P Qd) μc)) x *
            (initialLogSumWeight (fun p : P => (p : ℕ)) cb (fun i => x (i.castAdd (d + cells.length)))) *
              initialLogSumWeight (fun p : P => (p : ℕ)) cd
                (fun i => x ((i.castAdd cells.length).natAdd b)) := by
  intro cells μc good
  have hc (i : Fin cells.length) :=
    initial_selected_cells_valid htop hcenters _ (List.get_mem cells i)
  have hdata (i : Fin cells.length) :=
    (hc i).choose_spec.prior_data P ((hc i).choose_spec.subset_initialRegularPrimeRange.trans hsmallP)
  have he : Fin.append (fun _ : Fin b => good) (Fin.append (fun _ : Fin d => good)
      (fun _ : Fin cells.length => good)) = (fun _ => good) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) j
      · simp only [Fin.append_right, Fin.append_left]
      · simp only [Fin.append_right]
  have hh := initial_balanced_cell_mass_at P b d cells.length m
    (fun _ => primeSubsetPrior P Qb) (fun _ => primeSubsetPrior P Qd) μc
    (fun _ p => good p) (fun _ p => good p) (fun _ p => good p) cb cd hb hd
    (fun i => (hdata i).1) (fun i p hp => (hdata i).2.2 p hp)
  simpa only [he, mul_assoc] using hh

end Ostmann

end OAI
