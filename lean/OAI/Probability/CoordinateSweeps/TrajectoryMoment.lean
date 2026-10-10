import Mathlib
import OAI.Probability.CoordinateSweeps.Attachment
import OAI.Probability.Moments.LineExpansion

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
namespace CoordinateSweeps.Grid.Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

def auxCount (x y : Fin k → G.Slot) (A : Finset (Fin k)) (j : Fin G.b) (L : G.Line j) : ℕ :=
  (A.filter (fun i => G.pathLine (x i) (y i) j = L)).card

theorem auxCount_sum (x y : Fin k → G.Slot) (A : Finset (Fin k)) (j : Fin G.b) :
    ∑ L : G.Line j, auxCount x y A j L = A.card := by
  unfold auxCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem selected_sum {R : Type*} [AddCommMonoid R]
    (A : Finset (Fin k)) (f : Fin k → R) :
    (∑ i : Fin A.card, f (selected A i)) = ∑ a ∈ A, f a := by
  change (∑ i : Fin A.card, (fun a : A => f a.val)
    ((Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm i)) = _
  calc
    _ = ∑ a : A, f a.val := by
      exact Equiv.sum_comp (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm (fun a : A => f a.val)
    _ = _ := Finset.sum_coe_sort A f

theorem augment_selected_extraCount (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A : Finset (Fin k)) (ω : G.Choices) (hω : H.Compatible ω)
    (he : G.endpointEvent x y A ω) (j : Fin G.b) (L : G.Line j) :
    (H.augment (fun i => x (selected A i)) (fun i => y (selected A i))
      (H.validInput_selected x hx A) ω hω ((endpointEvent_iff_selected x y A ω).mp he)).extraCount j L =
      auxCount x y A j L := by
  unfold extraCount auxCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, OnLine, augment_new]
  change (∑ i : Fin A.card, if G.pathLine (x (selected A i)) (y (selected A i)) j = L then 1 else 0) = _
  exact selected_sum (R := ℕ) A (fun i => if G.pathLine (x i) (y i) j = L then 1 else 0)

theorem size_pow_eq_aux_product (x y : Fin k → G.Slot) (A : Finset (Fin k)) :
    (G.size : ℝ)^A.card =
      ∏ j, ∏ L : G.Line j, ((2^G.bits j : ℕ) : ℝ)^auxCount x y A j L := by
  simp only [Finset.prod_pow_eq_pow_sum, auxCount_sum]
  rw [Finset.prod_pow]
  congr 1
  simp [Grid.size]

/- Very same endpoint feasibility event as the conditioned finite sample space. -/
def EndpointPossible (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k)) : Prop :=
  ∃ ω, H.Compatible ω ∧ G.endpointEvent x y A ω

theorem descFactorial_add_split (n a b : ℕ) :
    n.descFactorial (a+b) = n.descFactorial a * (n-a).descFactorial b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, Nat.descFactorial_succ, ih, Nat.descFactorial_succ,
      Nat.sub_sub]
    ring

/- Uniform scaled entries have exactly the falling-factorial moments that enter
the shared-line gamma expansion, zero for impossible simultaneous paths. -/
theorem scaled_extraProbability_uniform (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A : Finset (Fin k)) :
    (G.size : ℝ)^A.card * H.extraProbability x y A (fun _ => FiniteLaw.uniform _) =
      if H.EndpointPossible x y A then
        ∏ j, ∏ L : G.Line j, fallingMoment (2^G.bits j) (H.lineCount j L) (auxCount x y A j L)
      else 0 := by
  classical
  rw [H.extraProbability_eq_conditionalEndpoint]
  by_cases he : H.EndpointPossible x y A
  · rw [ite_eq_left he]
    obtain ⟨ω,hω,he⟩ := he
    let J := H.augment (fun i => x (selected A i)) (fun i => y (selected A i))
      (H.validInput_selected x hx A) ω hω ((endpointEvent_iff_selected x y A ω).mp he)
    have hext : J.Extends H := H.augment_extends _ _ _ _ _ _
    have hcount (j : Fin G.b) (L : G.Line j) :
        J.lineCount j L = H.lineCount j L + auxCount x y A j L := by
      rw [J.lineCount_add H hext]
      exact congrArg (H.lineCount j L + ·) (H.augment_selected_extraCount x y hx A ω hω he j L)
    have hprob : H.conditionalEndpointProbability x y A (fun _ => FiniteLaw.uniform _) =
        J.probability 0 / H.probability 0 := by
      have hu : (fun j : Fin G.b => lineLaw (G.bits j) 0 (le_refl 0) zero_le_one) =
          (fun _ => FiniteLaw.uniform _) := by
        funext j
        ext σ
        simp [lineLaw, FiniteLaw.mix, FiniteLaw.uniform]
      rw [← hu]
      unfold conditionalEndpointProbability
      rw [H.lineMass_hole_normalizer, ← J.lineMass_hole_normalizer (le_refl 0) zero_le_one]
      congr 1
      apply Finset.sum_congr rfl
      intro ν _
      have hj : J.Compatible ν ↔ H.Compatible ν ∧ G.endpointEvent x y A ν := by
        dsimp [J]
        rw [H.augment_compatible_iff, endpointEvent_iff_selected]
      simp only [hj]
    rw [hprob, J.probability_zero, H.probability_zero, size_pow_eq_aux_product x y A,
      ← Finset.prod_div_distrib]
    simp only [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro L _
    rw [hcount, descFactorial_add_split]
    have hfa : ((2^G.bits j).descFactorial (H.lineCount j L) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr (H.lineCount_le j L)).ne'
    have hsub : auxCount x y A j L ≤ 2^G.bits j-H.lineCount j L := by
      have hj := J.lineCount_le j L
      rw [hcount] at hj
      omega
    have hfb : ((2^G.bits j-H.lineCount j L).descFactorial (auxCount x y A j L) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hsub).ne'
    unfold fallingMoment
    push_cast
    field_simp
  · rw [ite_eq_right he]
    have hn : ∀ ω, ¬ (H.Compatible ω ∧ G.endpointEvent x y A ω) := by
      simpa only [EndpointPossible, not_exists] using he
    simp [conditionalEndpointProbability, hn]

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

/- Geometric validity at EVERY boundary, not only at endpoints. -/
def JointDisjoint (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k)) : Prop :=
  (∀ i ∈ A, ∀ a s, G.pathBetween (x i) (y i) s ≠ H.path a s) ∧
  (∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ s,
    G.pathBetween (x i) (y i) s ≠ G.pathBetween (x j) (y j) s)

/- Build the augmented hole family directly from disjoint geometry. -/
def adjoin (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (hv : H.JointDisjoint x y A) : G.Holes (h+A.card) where
  path i s := Fin.append (fun a => H.path a s)
    (fun a => G.pathBetween (x (selected A a)) (y (selected A a)) s) i
  disjoint s := by
    apply Fin.append_injective_iff.mpr
    refine ⟨H.disjoint s, ?_, ?_⟩
    · intro a b he
      apply (selected A).injective
      by_contra hab
      exact hv.2 (selected A a) (selected_mem A a) (selected A b) (selected_mem A b) hab s he
    · intro a b he
      exact hv.1 (selected A b) (selected_mem A b) a s he.symm
  coordinate_step i j l hlj := by
    cases i using Fin.addCases with
    | left a => simpa using H.coordinate_step a j l hlj
    | right a => simpa using G.pathBetween_step (x (selected A a)) (y (selected A a)) j l hlj

@[simp] theorem adjoin_old (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (hv : H.JointDisjoint x y A) (a : Fin h) (s : Fin (G.b+1)) :
    (H.adjoin x y A hv).path (Fin.castAdd A.card a) s = H.path a s := by simp [adjoin]

@[simp] theorem adjoin_new (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (hv : H.JointDisjoint x y A) (a : Fin A.card) (s : Fin (G.b+1)) :
    (H.adjoin x y A hv).path (Fin.natAdd h a) s =
      G.pathBetween (x (selected A a)) (y (selected A a)) s := by simp [adjoin]

/- Every geometrically specified hole family already has a positive uniform
normalizer, whose proved factorial formula yields a real completion witness. -/
theorem feasible_of_disjoint_paths (H : G.Holes h) : H.Feasible := by
  by_contra hn
  have hz : H.probability 0 = 0 := by
    unfold probability
    exact Finset.sum_eq_zero (fun ω _ => (hn ⟨ω.val,ω.property⟩).elim)
  have hp := H.probability_zero_pos
  rw [hz] at hp
  exact lt_irrefl 0 hp

theorem adjoin_compatible_iff (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (hv : H.JointDisjoint x y A) (ω : G.Choices) :
    (H.adjoin x y A hv).Compatible ω ↔ H.Compatible ω ∧ G.endpointEvent x y A ω := by
  rw [endpointEvent_iff_selected]
  constructor
  · intro hJ
    constructor
    · intro a s
      simpa only [adjoin_old] using hJ (Fin.castAdd A.card a) s
    · intro a
      simpa only [adjoin_new, Grid.pathBetween_zero, Grid.pathBetween_last,
        Grid.sweep, Fin.val_last] using hJ (Fin.natAdd h a) (Fin.last G.b)
  · rintro ⟨hω,he⟩
    intro i s
    cases i using Fin.addCases with
    | left a => simpa only [adjoin_old] using hω a s
    | right a =>
      simp only [adjoin_new, Grid.pathBetween_zero]
      rw [G.boundary_eq_pathBetween, he a]

/- Exact event feasibility equals disjointness of the unique full trajectories. -/
theorem endpointPossible_iff_jointDisjoint (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A : Finset (Fin k)) :
    H.EndpointPossible x y A ↔ H.JointDisjoint x y A := by
  constructor
  · rintro ⟨ω,hω,he⟩
    have hb (i : Fin k) (hi : i ∈ A) (s : Fin (G.b+1)) :
        G.boundary ω s (x i) = G.pathBetween (x i) (y i) s := by
      rw [G.boundary_eq_pathBetween, he i hi]
    constructor
    · intro i hi a s hf
      exact hx.2 i a ((G.boundary ω s).injective ((hb i hi s).trans (hf.trans (hω a s).symm)))
    · intro i hi j hj hij s hf
      exact hij (hx.1 ((G.boundary ω s).injective ((hb i hi s).trans (hf.trans (hb j hj s).symm))))
  · intro hv
    obtain ⟨ω,hω⟩ := (H.adjoin x y A hv).feasible_of_disjoint_paths
    exact ⟨ω,(H.adjoin_compatible_iff x y A hv ω).mp hω⟩

/- Precisely the vertex-isolation condition in the source's definition of good. -/
def VertexIsolated (H : G.Holes h) (x y : Fin k → G.Slot) (i : Fin k) : Prop :=
  (∀ a s, G.pathBetween (x i) (y i) s ≠ H.path a s) ∧
  (∀ j, i ≠ j → ∀ s, G.pathBetween (x i) (y i) s ≠ G.pathBetween (x j) (y j) s)

theorem jointDisjoint_mono (H : G.Holes h) (x y : Fin k → G.Slot)
    {A B : Finset (Fin k)} (hAB : A ⊆ B) (hB : H.JointDisjoint x y B) :
    H.JointDisjoint x y A :=
  ⟨fun i hi => hB.1 i (hAB hi), fun i hi j hj => hB.2 i (hAB hi) j (hAB hj)⟩

theorem jointDisjoint_union_iff (H : G.Holes h) (x y : Fin k → G.Slot)
    (A S : Finset (Fin k)) (hS : ∀ i ∈ S, H.VertexIsolated x y i) :
    H.JointDisjoint x y (A∪S) ↔ H.JointDisjoint x y A := by
  constructor
  · exact H.jointDisjoint_mono x y Finset.subset_union_left
  · intro hA
    constructor
    · intro i hi a s
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hA.1 i hi a s
      · exact (hS i hi).1 a s
    · intro i hi j hj hij s
      rcases Finset.mem_union.mp hi with hi | hi
      · rcases Finset.mem_union.mp hj with hj | hj
        · exact hA.2 i hi j hj hij s
        · exact Ne.symm ((hS j hj).2 i hij.symm s)
      · exact (hS i hi).2 j hij s

/- Adding any subset of good paths CANNOT change validity, as needed before
alternation is taken inside the shared-line expectation. -/
theorem endpointPossible_union_iff (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A S : Finset (Fin k))
    (hS : ∀ i ∈ S, H.VertexIsolated x y i) :
    H.EndpointPossible x y (A∪S) ↔ H.EndpointPossible x y A := by
  rw [H.endpointPossible_iff_jointDisjoint x y hx, H.endpointPossible_iff_jointDisjoint x y hx]
  exact H.jointDisjoint_union_iff x y A S hS

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid
/- A line is named by both its stage and its remaining coordinates. -/
abbrev StageLine (G : Grid) := Σ j : Fin G.b, G.Line j

def stagePath (G : Grid) {k : ℕ} (x y : Fin k → G.Slot) (i : Fin k) (j : Fin G.b) : G.StageLine :=
  ⟨j, G.pathLine (x i) (y i) j⟩

namespace Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

theorem incidenceCount_stagePath (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (j : Fin G.b) (L : G.Line j) :
    incidenceCount A (G.stagePath x y) ⟨j,L⟩ = auxCount x y A j L := by
  unfold incidenceCount auxCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single j]
  · simp [stagePath]
  · intro a ha haj
    have hn : G.stagePath x y i a ≠ ⟨j,L⟩ := fun he => haj (congrArg Sigma.fst he)
    simp [hn]
  · simp

theorem incidenceCount_stagePath_any (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (l : G.StageLine) :
    incidenceCount A (G.stagePath x y) l = auxCount x y A l.1 l.2 := by
  cases l with
  | mk j L => exact incidenceCount_stagePath x y A j L

theorem incidenceCount_total (x y : Fin k → G.Slot) (A : Finset (Fin k)) :
    ∑ l : G.StageLine, incidenceCount A (G.stagePath x y) l = G.b*A.card := by
  rw [Fintype.sum_sigma]
  simp only [incidenceCount_stagePath, auxCount_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

def Light (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (l : G.StageLine) : Prop :=
  ((H.lineCount l.1 l.2 + auxCount x y Finset.univ l.1 l.2 : ℕ) : ℝ) ≤
    (2^G.bits l.1 : ℕ)*η

def Good (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (i : Fin k) : Prop :=
  H.VertexIsolated x y i ∧ ∀ j, H.Light x y η (G.stagePath x y i j)

noncomputable def goodSet (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) : Finset (Fin k) :=
  Finset.univ.filter (H.Good x y η)

@[simp] theorem mem_goodSet (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (i : Fin k) :
    i ∈ H.goodSet x y η ↔ H.Good x y η i := by simp [goodSet]

def lightMoment (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (l : G.StageLine) (n : ℕ) : ℝ :=
  if H.Light x y η l then fallingMoment (2^G.bits l.1) (H.lineCount l.1 l.2) n else 1

@[simp] theorem lightMoment_zero (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (l : G.StageLine) :
    H.lightMoment x y η l 0 = 1 := by simp [lightMoment, fallingMoment_zero]

theorem incidenceCount_good_nonlight (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ)
    (l : G.StageLine) (hl : ¬ H.Light x y η l) {A : Finset (Fin k)}
    (hA : A ⊆ H.goodSet x y η) : incidenceCount A (G.stagePath x y) l = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j _
  have hn : G.stagePath x y i j ≠ l := by
    intro he
    exact hl (he ▸ ((H.mem_goodSet x y η i).mp (hA hi)).2 j)
  simp [hn]

theorem incidenceCount_mono (x y : Fin k → G.Slot) {A B : Finset (Fin k)}
    (hAB : A ⊆ B) (l : G.StageLine) :
    incidenceCount A (G.stagePath x y) l ≤ incidenceCount B (G.stagePath x y) l :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun _ _ _ => Nat.zero_le _)

theorem incidenceCount_union (x y : Fin k → G.Slot) {A B : Finset (Fin k)}
    (hAB : Disjoint A B) (l : G.StageLine) :
    incidenceCount (A∪B) (G.stagePath x y) l =
      incidenceCount A (G.stagePath x y) l + incidenceCount B (G.stagePath x y) l :=
  Finset.sum_union hAB

/- The actual shared-line moment bound: inactive (non-light) line variables
are set to 1, not made independent per particle. -/
theorem goodExpansion_lightMoment_le (H : G.Holes h) (x y : Fin k → G.Slot)
    {η : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1/8) (J : Finset (Fin k))
    (hJ : Disjoint J (H.goodSet x y η)) :
    |shiftedMoment (H.lightMoment x y η) (incidenceCount J (G.stagePath x y))
      (goodExpansion (H.goodSet x y η) (G.stagePath x y))| ≤
      (16 * Real.exp 2)^(G.b*J.card) * (1+16 * Real.exp 2)^(G.b*(H.goodSet x y η).card) *
        η^(((H.goodSet x y η).card : ℝ)/2) := by
  have hC : (1 : ℝ) ≤ 16*Real.exp 2 := by
    have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have he := goodExpansion_moment_le (H.lightMoment x y η)
    (H.lightMoment_zero x y η) (incidenceCount J (G.stagePath x y))
    (H.goodSet x y η) (G.stagePath x y) (16*Real.exp 2) (Real.sqrt η)
    (by positivity) (Real.sqrt_nonneg η) (by
      apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).mpr
      linarith) (by
      intro l u hu
      by_cases hl : H.Light x y η l
      · have hline : ∀ n, H.lightMoment x y η l n =
            fallingMoment (2^G.bits l.1) (H.lineCount l.1 l.2) n := by
          intro n; simp [lightMoment, hl]
        simp only [lineCenteredMoment, hline]
        apply fallingCenteredMoment_abs_le (fun l : G.StageLine => 2^G.bits l.1)
          (fun l => H.lineCount l.1 l.2) l (by positivity) _ u hη hηsmall
        apply le_trans _ hl
        have htotal := incidenceCount_mono x y (Finset.subset_univ
          (J ∪ H.goodSet x y η)) l
        rw [incidenceCount_union x y hJ l] at htotal
        simp only [incidenceCount_stagePath_any] at htotal
        change u ≤ incidenceCount (H.goodSet x y η) (G.stagePath x y) l at hu
        rw [incidenceCount_stagePath_any] at hu
        exact_mod_cast (show H.lineCount l.1 l.2 + u + incidenceCount J (G.stagePath x y) l ≤
            H.lineCount l.1 l.2 + auxCount x y Finset.univ l.1 l.2 by
          rw [incidenceCount_stagePath_any]
          omega)
      · have hzero := H.incidenceCount_good_nonlight x y η l hl (Finset.Subset.refl _)
        have hu0 : u = 0 := by change u ≤ incidenceCount _ _ l at hu; omega
        subst u
        simpa [lineCenteredMoment, lightMoment, hl] using
          (one_le_pow₀ hC : (1 : ℝ) ≤ (16*Real.exp 2)^incidenceCount J (G.stagePath x y) l))
  have hs : (Real.sqrt η)^(H.goodSet x y η).card = η^(((H.goodSet x y η).card : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hη]
    congr 1; ring
  simpa only [incidenceCount_total, Fintype.card_fin, hs] using he

end Holes
end CoordinateSweeps.Grid

namespace CoordinateSweeps.MomentExpansion

theorem fallingMoment_one_le {m h n : ℕ} (hn : h+n ≤ m) : 1 ≤ fallingMoment m h n := by
  have hd : (0 : ℝ) < (m-h).descFactorial n := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega : n ≤ m-h)
  unfold fallingMoment
  apply (le_div_iff₀ hd).mpr
  rw [one_mul]
  exact_mod_cast (Nat.descFactorial_le_pow (m-h) n).trans
    (Nat.pow_le_pow_left (Nat.sub_le m h) n)

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.Grid.Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

theorem endpointPossible_lineCount_le (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A : Finset (Fin k)) (hA : H.EndpointPossible x y A)
    (l : G.StageLine) : H.lineCount l.1 l.2 + incidenceCount A (G.stagePath x y) l ≤ 2^G.bits l.1 := by
  obtain ⟨ω,hω,he⟩ := hA
  let J := H.augment (fun i => x (selected A i)) (fun i => y (selected A i))
    (H.validInput_selected x hx A) ω hω ((endpointEvent_iff_selected x y A ω).mp he)
  have hext : J.Extends H := H.augment_extends _ _ _ _ _ _
  have hc := J.lineCount_le l.1 l.2
  rw [J.lineCount_add H hext,
    H.augment_selected_extraCount x y hx A ω hω he l.1 l.2] at hc
  simpa only [incidenceCount_stagePath_any] using hc

/- Product outside the light-line expectation; zero validity is handled
separately, never by interpreting a divergent inverse-gamma moment. -/
def nonlightFactor (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (J : Finset (Fin k)) : ℝ :=
  ∏ l : G.StageLine, if H.Light x y η l then 1 else
    fallingMoment (2^G.bits l.1) (H.lineCount l.1 l.2) (incidenceCount J (G.stagePath x y) l)

theorem nonlightFactor_nonneg (H : G.Holes h) (x y : Fin k → G.Slot)
    (η : ℝ) (J : Finset (Fin k)) : 0 ≤ H.nonlightFactor x y η J := by
  apply Finset.prod_nonneg
  intro l _
  split_ifs
  · norm_num
  · unfold fallingMoment; positivity

theorem nonlightFactor_le (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (η : ℝ) (J : Finset (Fin k)) (hJ : H.EndpointPossible x y J) :
    H.nonlightFactor x y η J ≤ Real.exp ((G.b : ℝ)*(h+k)+Real.log 4*k*G.b) := by
  have hu (j : Fin G.b) : lineLaw (G.bits j) 0 (le_refl 0) zero_le_one = FiniteLaw.uniform _ := by
    ext σ
    simp [lineLaw, FiniteLaw.mix, FiniteLaw.uniform]
  have he := H.scaled_extraProbability_le x y hx J (le_refl 0) zero_le_one
    (by intro j σ; rw [hu]; have := (FiniteLaw.uniform _).nonneg σ; linarith)
    (by intro j σ; rw [hu]; have := (FiniteLaw.uniform _).nonneg σ; linarith)
  simp_rw [hu] at he
  rw [H.scaled_extraProbability_uniform x y hx J, ite_eq_left hJ] at he
  apply le_trans _ he
  rw [← Fintype.prod_sigma (fun l : G.StageLine =>
    fallingMoment (2^G.bits l.1) (H.lineCount l.1 l.2) (auxCount x y J l.1 l.2))]
  unfold nonlightFactor
  apply Finset.prod_le_prod₀
  · intro l _
    split_ifs
    · norm_num
    · unfold fallingMoment; positivity
  · intro l _
    split_ifs
    · apply fallingMoment_one_le
      simpa only [incidenceCount_stagePath_any] using H.endpointPossible_lineCount_le x y hx J hJ l
    · rw [incidenceCount_stagePath_any]

/- Exact factorization for adding any collection of good paths. -/
theorem scaled_extraProbability_good_union (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (η : ℝ) (J S : Finset (Fin k))
    (hJ : Disjoint J (H.goodSet x y η)) (hS : S ⊆ H.goodSet x y η) :
    (G.size : ℝ)^(J∪S).card * H.extraProbability x y (J∪S) (fun _ => FiniteLaw.uniform _) =
      (if H.EndpointPossible x y J then H.nonlightFactor x y η J else 0) *
        ∏ l : G.StageLine, H.lightMoment x y η l
          (incidenceCount J (G.stagePath x y) l+incidenceCount S (G.stagePath x y) l) := by
  rw [H.scaled_extraProbability_uniform x y hx (J∪S)]
  have hv := H.endpointPossible_union_iff x y hx J S (fun i hi =>
    ((H.mem_goodSet x y η i).mp (hS hi)).1)
  rw [hv]
  split_ifs with hp
  · rw [← Fintype.prod_sigma (fun l : G.StageLine =>
        fallingMoment (2^G.bits l.1) (H.lineCount l.1 l.2) (auxCount x y (J∪S) l.1 l.2)),
      nonlightFactor, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro l _
    rw [← incidenceCount_stagePath_any, incidenceCount_union x y (hJ.mono_right hS)]
    unfold lightMoment
    split_ifs with hl
    · simp
    · rw [H.incidenceCount_good_nonlight x y η l hl hS]
      simp
  · simp

end CoordinateSweeps.Grid.Holes
/- Finite subset rearrangements needed for the actual good/non-good path
alternation in source04:eq10. -/
noncomputable section
open scoped BigOperators
namespace CoordinateSweeps
variable {I : Type*} [DecidableEq I]

theorem sum_powerset_union {R : Type*} [AddCommMonoid R]
    (A B : Finset I) (hAB : Disjoint A B) (f : Finset I → R) :
    ∑ S ∈ (A∪B).powerset, f S =
      ∑ J ∈ A.powerset, ∑ S ∈ B.powerset, f (J∪S) := by
  rw [← Finset.sum_product A.powerset B.powerset (fun p => f (p.1 ∪ p.2))]
  symm
  apply Finset.sum_bij (fun p _ => p.1 ∪ p.2)
  · intro p hp
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_powerset.mpr (Finset.union_subset_union
      (Finset.mem_powerset.mp hp1) (Finset.mem_powerset.mp hp2))
  · intro p hp q hq he
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hq1,hq2⟩ := Finset.mem_product.mp hq
    have hp1 := Finset.mem_powerset.mp hp1
    have hp2 := Finset.mem_powerset.mp hp2
    have hq1 := Finset.mem_powerset.mp hq1
    have hq2 := Finset.mem_powerset.mp hq2
    apply Prod.ext
    · ext i
      constructor
      · intro hi
        have hu : i ∈ q.1 ∪ q.2 := he ▸ Finset.mem_union_left _ hi
        rcases Finset.mem_union.mp hu with h | h
        · exact h
        · exact False.elim (Finset.disjoint_left.mp hAB (hp1 hi) (hq2 h))
      · intro hi
        have hu : i ∈ p.1 ∪ p.2 := he.symm ▸ Finset.mem_union_left _ hi
        rcases Finset.mem_union.mp hu with h | h
        · exact h
        · exact False.elim (Finset.disjoint_left.mp hAB (hq1 hi) (hp2 h))
    · ext i
      constructor
      · intro hi
        have hu : i ∈ q.1 ∪ q.2 := he ▸ Finset.mem_union_right _ hi
        rcases Finset.mem_union.mp hu with h | h
        · exact False.elim (Finset.disjoint_left.mp hAB (hq1 h) (hp2 hi))
        · exact h
      · intro hi
        have hu : i ∈ p.1 ∪ p.2 := he.symm ▸ Finset.mem_union_right _ hi
        rcases Finset.mem_union.mp hu with h | h
        · exact False.elim (Finset.disjoint_left.mp hAB (hp1 h) (hq2 hi))
        · exact h
  · intro S hS
    refine ⟨(S∩A,S∩B), Finset.mem_product.mpr ⟨?_,?_⟩, ?_⟩
    · exact Finset.mem_powerset.mpr Finset.inter_subset_right
    · exact Finset.mem_powerset.mpr Finset.inter_subset_right
    · simp only [Finset.mem_powerset] at hS
      ext i
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · tauto
      · intro hi
        have hu := Finset.mem_union.mp (hS hi)
        tauto
  · intro p hp
    rfl

theorem sum_powerset_sdiff {R : Type*} [AddCommMonoid R]
    (A : Finset I) (f : Finset I → R) :
    ∑ S ∈ A.powerset, f (A\S) = ∑ S ∈ A.powerset, f S := by
  apply Finset.sum_bij (fun S _ => A\S)
  · intro S hS
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro S hS T hT he
    have hS := Finset.mem_powerset.mp hS
    have hT := Finset.mem_powerset.mp hT
    apply_fun (fun U => A\U) at he
    simpa only [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hS,
      Finset.inter_eq_right.mpr hT] using he
  · intro S hS
    have hS := Finset.mem_powerset.mp hS
    exact ⟨A\S, Finset.mem_powerset.mpr Finset.sdiff_subset, by simp [hS]⟩
  · intro S hS
    rfl

theorem alternating_good_split [Fintype I] (G : Finset I) (f : Finset I → ℝ) :
    (∑ A ∈ (Finset.univ : Finset I).powerset,
      (-1 : ℝ)^(Fintype.card I-A.card)*f A) =
    ∑ J ∈ ((Finset.univ : Finset I)\G).powerset,
      (-1 : ℝ)^(Fintype.card I-J.card-G.card) *
        ∑ A ∈ G.powerset, (-1 : ℝ)^A.card * f (J ∪ (G\A)) := by
  have hg : ((Finset.univ : Finset I)\G) ∪ G = Finset.univ := by simp
  conv_lhs => rw [← hg, sum_powerset_union _ _ disjoint_sdiff_self_left]
  apply Finset.sum_congr rfl
  intro J hJ
  have hJ := Finset.mem_powerset.mp hJ
  have hd : Disjoint J G := Finset.disjoint_of_subset_left hJ disjoint_sdiff_self_left
  rw [← sum_powerset_sdiff G (fun S => (-1 : ℝ)^(Fintype.card I-(J∪S).card)*f (J∪S))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hA := Finset.mem_powerset.mp hA
  have hdc : Disjoint J (G\A) := hd.mono_right Finset.sdiff_subset
  have hcard : J.card+G.card ≤ Fintype.card I := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_univ _
  have hAc := Finset.card_le_card hA
  rw [Finset.card_union_of_disjoint hdc, Finset.card_sdiff_of_subset hA]
  have he : Fintype.card I-(J.card+(G.card-A.card)) =
      (Fintype.card I-J.card-G.card)+A.card := by omega
  rw [he, pow_add]
  ring

end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

theorem alternating_good_extensions (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (η : ℝ) (J : Finset (Fin k))
    (hJ : Disjoint J (H.goodSet x y η)) :
    (∑ A ∈ (H.goodSet x y η).powerset, (-1 : ℝ)^A.card *
      ((G.size : ℝ)^(J∪(H.goodSet x y η\A)).card *
        H.extraProbability x y (J∪(H.goodSet x y η\A)) (fun _ => FiniteLaw.uniform _))) =
      (if H.EndpointPossible x y J then H.nonlightFactor x y η J else 0) *
        shiftedMoment (H.lightMoment x y η) (incidenceCount J (G.stagePath x y))
          (goodExpansion (H.goodSet x y η) (G.stagePath x y)) := by
  rw [shiftedMoment_goodExpansion_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [H.scaled_extraProbability_good_union x y hx η J _ hJ Finset.sdiff_subset]
  ring

/- Source04:eq10, now proved for literal uniform stage-line laws and actual
conditioned path probabilities. Constants are explicit and absolute; all
non-light factors and validity indicators remain outside the moment. -/
theorem scaled_placementKernel_good_bound (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) {η : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1/8) :
    |(G.size : ℝ)^k * H.placementKernel x y (fun _ => FiniteLaw.uniform _)| ≤
      (2 : ℝ)^k * Real.exp ((G.b : ℝ)*(h+k)+Real.log 4*k*G.b) *
        (16*Real.exp 2)^(G.b*k) * (1+16*Real.exp 2)^(G.b*k) *
          η^(((H.goodSet x y η).card : ℝ)/2) := by
  have hs : (G.size : ℝ) ≠ 0 := by unfold Grid.size; positivity
  have hC : (1 : ℝ) ≤ 16*Real.exp 2 := by
    have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hC' : (1 : ℝ) ≤ 1+16*Real.exp 2 := by linarith
  let GG := H.goodSet x y η
  let E := Real.exp ((G.b : ℝ)*(h+k)+Real.log 4*k*G.b)
  let U := (16*Real.exp 2)^(G.b*k) * (1+16*Real.exp 2)^(G.b*k) * η^((GG.card : ℝ)/2)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  rw [placementKernel, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]
  conv_lhs => simp only [mul_assoc]
  have hsplit := alternating_good_split GG (fun A =>
    (G.size : ℝ)^A.card * H.extraProbability x y A (fun _ => FiniteLaw.uniform _))
  simp only [Fintype.card_fin] at hsplit
  rw [hsplit]
  have hterm (J : Finset (Fin k)) (hJ : J ∈ ((Finset.univ : Finset (Fin k))\GG).powerset) :
      |(-1 : ℝ)^(k-J.card-GG.card) *
        ∑ A ∈ GG.powerset, (-1 : ℝ)^A.card *
          ((G.size : ℝ)^(J∪(GG\A)).card *
            H.extraProbability x y (J∪(GG\A)) (fun _ => FiniteLaw.uniform _))| ≤ E*U := by
    have hsub := Finset.mem_powerset.mp hJ
    have hd : Disjoint J GG := Finset.disjoint_of_subset_left hsub disjoint_sdiff_self_left
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      H.alternating_good_extensions x y hx η J hd, abs_mul]
    have hD : |if H.EndpointPossible x y J then H.nonlightFactor x y η J else 0| ≤ E := by
      split_ifs with hp
      · rw [abs_of_nonneg (H.nonlightFactor_nonneg x y η J)]
        exact H.nonlightFactor_le x y hx η J hp
      · simp only [abs_zero]
        exact (Real.exp_pos _).le
    have hM := H.goodExpansion_lightMoment_le x y hη hηsmall J hd
    have hJk : J.card ≤ k := by simpa using Finset.card_le_univ J
    have hGk : GG.card ≤ k := by simpa using Finset.card_le_univ GG
    have hM' : |shiftedMoment (H.lightMoment x y η) (incidenceCount J (G.stagePath x y))
        (goodExpansion GG (G.stagePath x y))| ≤ U := by
      apply hM.trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hη _)
      apply mul_le_mul
      · exact pow_le_pow_right₀ hC (Nat.mul_le_mul_left G.b hJk)
      · exact pow_le_pow_right₀ hC' (Nat.mul_le_mul_left G.b hGk)
      · positivity
      · positivity
    exact mul_le_mul hD hM' (abs_nonneg _) (Real.exp_pos _).le
  calc
    _ ≤ ∑ J ∈ ((Finset.univ : Finset (Fin k))\GG).powerset,
        |(-1 : ℝ)^(k-J.card-GG.card) *
          ∑ A ∈ GG.powerset, (-1 : ℝ)^A.card *
            ((G.size : ℝ)^(J∪(GG\A)).card *
              H.extraProbability x y (J∪(GG\A)) (fun _ => FiniteLaw.uniform _))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ J ∈ ((Finset.univ : Finset (Fin k))\GG).powerset, E*U :=
      Finset.sum_le_sum hterm
    _ = (2 : ℝ)^((Finset.univ : Finset (Fin k))\GG).card*(E*U) := by simp
    _ ≤ (2 : ℝ)^k*(E*U) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.exp_pos _).le hU)
      apply pow_le_pow_right₀ (by norm_num)
      exact le_trans (Finset.card_le_card Finset.sdiff_subset) (by simp)
    _ = _ := by dsimp [E,U,GG]; ring

end CoordinateSweeps.Grid.Holes
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
