import OAI.MeasureTheory.Falconer.Frostman.GeometricCapacity
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable def DyadicSquare.descendant (Q : DyadicSquare) :
    List (Bool × Bool) → DyadicSquare
  | [] => Q
  | (i,j) :: p => (Q.child i j).descendant p

theorem DyadicSquare.descendant_side_pos (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : List (Bool × Bool)) : 0 < (Q.descendant p).side := by
  induction p generalizing Q with
  | nil => exact hQ
  | cons a p ih => exact ih _ (Q.child_side_pos hQ a.1 a.2)

theorem DyadicSquare.descendant_subset (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : List (Bool × Bool)) : (Q.descendant p).carrier ⊆ Q.carrier := by
  induction p generalizing Q with
  | nil => exact Subset.rfl
  | cons a p ih =>
    exact (ih _ (Q.child_side_pos hQ a.1 a.2)).trans (Q.child_subset hQ.le a.1 a.2)

theorem measure_zero_of_disjoint_carrier {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {A B : Set X} (hAB : Disjoint A B) (hμ : μ Bᶜ = 0) :
    μ A = 0 :=
  measure_mono_null (fun _ hx hy => Set.disjoint_left.mp hAB hx hy) hμ

theorem four_measures_on_branch (Q : DyadicSquare)
    (μ : Bool → Bool → Measure Plane)
    (hμ : ∀ i j, μ i j (Q.child i j).carrierᶜ = 0)
    (i j : Bool) {A : Set Plane} (hA : A ⊆ (Q.child i j).carrier) :
    (μ false false + μ false true + μ true false + μ true true) A = μ i j A := by
  have hz (k l : Bool) (h : (i,j) ≠ (k,l)) : μ k l A = 0 :=
    measure_zero_of_disjoint_carrier _ ((Q.children_disjoint h).mono_left hA) (hμ k l)
  cases i <;> cases j <;>
    simp only [Measure.add_apply] <;>
    simp [hz false false, hz false true, hz true false, hz true true]

def DyadicMassBounds (s : ℝ) (Q : DyadicSquare) (K : ℕ) (μ : Measure Plane) : Prop :=
  ∀ p : List (Bool × Bool), p.length ≤ K →
    μ (Q.descendant p).carrier ≤ ENNReal.ofReal ((Q.descendant p).side ^ s)

theorem routes_mass_bounds {t : CapacityTree} {m : ℝ} (h : Routes t m) :
    0 ≤ m ∧ m ≤ t.rootCapacity := by
  cases h with
  | leaf hm hc => exact ⟨hm,hc⟩
  | node hm hc _ _ _ _ _ => exact ⟨hm,hc⟩

theorem measure_from_geometric_routes (E : Set Plane) (s : ℝ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (K : ℕ) (m : ℝ)
    (hroute : Routes (geometricTree E s Q K) m) :
    ∃ μ : Measure Plane, μ univ = ENNReal.ofReal m ∧
      μ (E ∩ Q.carrier)ᶜ = 0 ∧ DyadicMassBounds s Q K μ := by
  classical
  induction K generalizing Q m with
  | zero =>
    have hm := (routes_mass_bounds hroute).1
    have hc : m ≤ occupiedCapacity E s Q := (routes_mass_bounds hroute).2
    by_cases h : (E ∩ Q.carrier).Nonempty
    · obtain ⟨x,hx⟩ := h
      refine ⟨ENNReal.ofReal m • Measure.dirac x, by simp, ?_, ?_⟩
      · simp [Measure.smul_apply, hx]
      · intro p hp
        have : p = [] := by cases p <;> simp_all
        subst p
        change (ENNReal.ofReal m • Measure.dirac x) Q.carrier ≤ ENNReal.ofReal (Q.side^s)
        rw [occupiedCapacity, ite_eq_left ⟨x,hx⟩] at hc
        simpa [Measure.smul_apply, Measure.dirac_apply' _ Q.measurable, hx.2] using
          ENNReal.ofReal_le_ofReal hc
    · have hm0 : m = 0 := by rw [occupiedCapacity, ite_eq_right h] at hc; linarith
      refine ⟨0,by simp [hm0],by simp,?_⟩
      intro p hp
      simp
  | succ K ih =>
    cases hroute with
    | node hm hc hsum hr00 hr01 hr10 hr11 =>
      obtain ⟨μ00,hm00,hc00,hb00⟩ := ih _ (Q.child_side_pos hQ false false) _ hr00
      obtain ⟨μ01,hm01,hc01,hb01⟩ := ih _ (Q.child_side_pos hQ false true) _ hr01
      obtain ⟨μ10,hm10,hc10,hb10⟩ := ih _ (Q.child_side_pos hQ true false) _ hr10
      obtain ⟨μ11,hm11,hc11,hb11⟩ := ih _ (Q.child_side_pos hQ true true) _ hr11
      let μ : Bool → Bool → Measure Plane := fun i j =>
        if i then (if j then μ11 else μ10) else (if j then μ01 else μ00)
      have hcarry : ∀ i j, μ i j (E ∩ (Q.child i j).carrier)ᶜ = 0 := by
        intro i j; cases i <;> cases j <;> assumption
      have hchild : ∀ i j, μ i j (Q.child i j).carrierᶜ = 0 := by
        intro i j
        exact measure_mono_null (compl_subset_compl.mpr inter_subset_right) (hcarry i j)
      have hparent : ∀ i j, μ i j (E ∩ Q.carrier)ᶜ = 0 := by
        intro i j
        apply measure_mono_null _ (hcarry i j)
        exact compl_subset_compl.mpr (inter_subset_inter_right E (Q.child_subset hQ.le i j))
      have hbounds : ∀ i j, DyadicMassBounds s (Q.child i j) K (μ i j) := by
        intro i j; cases i <;> cases j <;> assumption
      let ν := μ00 + μ01 + μ10 + μ11
      have hmass : ν univ = ENNReal.ofReal m := by
        simp only [ν, Measure.add_apply, hm00,hm01,hm10,hm11]
        rw [← ENNReal.ofReal_add (routes_mass_bounds hr00).1 (routes_mass_bounds hr01).1,
          ← ENNReal.ofReal_add (add_nonneg (routes_mass_bounds hr00).1
            (routes_mass_bounds hr01).1) (routes_mass_bounds hr10).1,
          ← ENNReal.ofReal_add (add_nonneg (add_nonneg (routes_mass_bounds hr00).1
            (routes_mass_bounds hr01).1) (routes_mass_bounds hr10).1)
            (routes_mass_bounds hr11).1, hsum]
      refine ⟨ν,hmass,?_,?_⟩
      · change (μ false false + μ false true + μ true false + μ true true) _ = 0
        simp only [Measure.add_apply, hparent, add_zero]
      · intro p hp
        cases p with
        | nil =>
          have hcap : occupiedCapacity E s Q ≤ Q.side^s := by
            unfold occupiedCapacity; split_ifs
            · exact le_rfl
            · positivity
          exact (measure_mono (subset_univ _)).trans (hmass ▸ ENNReal.ofReal_le_ofReal
            (hc.trans hcap))
        | cons a p =>
          change (μ false false + μ false true + μ true false + μ true true)
            ((Q.child a.1 a.2).descendant p).carrier ≤ _
          rw [four_measures_on_branch Q μ hchild a.1 a.2
            ((Q.child a.1 a.2).descendant_subset (Q.child_side_pos hQ a.1 a.2) p)]
          exact hbounds a.1 a.2 p (by simpa using Nat.le_of_succ_le_succ hp)

theorem exists_dyadic_probability_sequence (E : Set Plane) (hE : IsCompact E)
    {s : ℝ≥0} (hs : 0 < s) (hd : (s : ℝ≥0∞) < dimH E)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (hEQ : E ⊆ Q.carrier) :
    ∃ c : ℝ, 0 < c ∧ ∃ ζ : ℕ → ProbabilityMeasure Plane,
      ∀ K, (ζ K : Measure Plane) Eᶜ = 0 ∧
        ∀ p : List (Bool × Bool), p.length ≤ K →
          (ζ K : Measure Plane) (Q.descendant p).carrier ≤
            ENNReal.ofReal (c⁻¹ * (Q.descendant p).side^(s : ℝ)) := by
  classical
  obtain ⟨c,hc,hr⟩ := exists_uniform_geometric_routes E hE hs hd Q hQ hEQ
  choose μ hmass hcarry hb using fun K =>
    measure_from_geometric_routes E s Q hQ K c (hr K)
  have hprob (K : ℕ) : IsProbabilityMeasure (ENNReal.ofReal c⁻¹ • μ K) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul, hmass K,
      ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  let ζ : ℕ → ProbabilityMeasure Plane := fun K => ⟨ENNReal.ofReal c⁻¹ • μ K,hprob K⟩
  refine ⟨c,hc,ζ,fun K => ⟨?_,?_⟩⟩
  · have he : μ K Eᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr inter_subset_left) (hcarry K)
    simp [ζ, Measure.smul_apply, he]
  · intro p hp
    change (ENNReal.ofReal c⁻¹ • μ K) _ ≤ _
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_right (hb K p hp) _

end PlanarFalconer

end OAI
