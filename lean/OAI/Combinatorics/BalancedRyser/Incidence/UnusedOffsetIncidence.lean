import OAI.Combinatorics.BalancedRyser.Incidence.AffineDirectionCounting
import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Probability.UniformRestriction

namespace OAI

noncomputable section
open scoped BigOperators
open scoped Classical

namespace Balanced.UnusedOffsetIncidence

def probability {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω

theorem probability_eq_pmf {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    probability E = ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E ω}).toReal := by
  classical
  rw [PMF.uniformOfFintype, PMF.toOuterMeasure_uniformOfFinset_apply]
  simp [probability, ENNReal.toReal_div]

theorem probability_nonneg {Ω : Type*} [Fintype Ω] (E : Ω → Prop) :
    0 ≤ probability E := by
  unfold probability
  positivity

theorem probability_mono {Ω : Type*} [Fintype Ω] {E G : Ω → Prop}
    (h : ∀ ω, E ω → G ω) : probability E ≤ probability G := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro ω hω
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, h ω (Finset.mem_filter.mp hω).2⟩

theorem probability_exists_le {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (E : ι → Ω → Prop) :
    probability (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, probability (E i) := by
  classical
  have heq : Finset.univ.filter (fun ω => ∃ i ∈ s, E i ω) =
      s.biUnion (fun i => Finset.univ.filter (E i)) := by
    ext ω
    simp
  have hb : (Finset.univ.filter (fun ω => ∃ i ∈ s, E i ω)).card ≤
      ∑ i ∈ s, (Finset.univ.filter (E i)).card := by
    rw [heq]
    exact Finset.card_biUnion_le
  unfold probability
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hc := (Nat.cast_le (α := ℝ)).mpr hb
  push_cast at hc
  convert hc using 1
  congr 1
  congr 1
  ext ω
  simp

theorem probability_exists_fintype_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (E : ι → Ω → Prop) :
    probability (fun ω => ∃ i, E i ω) ≤ ∑ i, probability (E i) := by
  simpa using probability_exists_le (Finset.univ : Finset ι) E

theorem probability_or_le {Ω : Type*} [Fintype Ω] (E G : Ω → Prop) :
    probability (fun ω => E ω ∨ G ω) ≤ probability E + probability G := by
  simpa [Bool.exists_bool, Fintype.sum_bool, add_comm, or_comm] using
    probability_exists_fintype_le (fun s : Bool => if s then E else G)

theorem probability_union3_bound {Ω : Type*} [Fintype Ω]
    {E A B C : Ω → Prop} {a b c : ℝ}
    (h : ∀ ω, E ω → A ω ∨ B ω ∨ C ω)
    (hA : probability A ≤ a) (hB : probability B ≤ b)
    (hC : probability C ≤ c) : probability E ≤ a + (b + c) := by
  have h₁ := probability_mono h
  have h₂ := probability_or_le A (fun ω => B ω ∨ C ω)
  have h₃ := probability_or_le B C
  exact h₁.trans (h₂.trans (add_le_add hA (h₃.trans (add_le_add hB hC))))

theorem uniform_map_eval {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [Nonempty A] (i : ι) :
    (PMF.uniformOfFintype (ι → A)).map (fun o => o i) =
      PMF.uniformOfFintype A := by
  classical
  have h := congrArg (fun p => p.map Prod.fst)
    (TupleAlignment.uniform_map_equiv (Equiv.funSplitAt i A))
  rw [PMF.map_comp, TupleAlignment.uniform_map_fst] at h
  exact h

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
theorem pair_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (s : Bool) (a b : F) :
    probability (fun o : ι → Bool → F => o i s = a ∧ o i (!s) = b) =
      1 / (Fintype.card F : ℝ) ^ 2 := by
  classical
  let v : Bool → F := fun t => if t = s then a else b
  have heq : {o : ι → Bool → F | o i s = a ∧ o i (!s) = b} =
      (fun o : ι → Bool → F => o i) ⁻¹' {v} := by
    ext o
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ha, hb⟩
      funext t
      cases s <;> cases t <;> simpa [v] using (by assumption)
    · intro h
      constructor
      · simpa [v] using congrFun h s
      · simpa [v] using congrFun h (!s)
  rw [probability_eq_pmf, heq, ← PMF.toOuterMeasure_map_apply,
    uniform_map_eval, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply]
  simp [ENNReal.toReal_inv, one_div]

abbrev Offsets (D : Finset (Direction F)) := D → Bool → F

def constituent (D : Finset (Direction F)) (o : Offsets D)
    (d : D) (s : Bool) : Line F := (d.1, o d s)

def Precoverage (D : Finset (Direction F)) (p : Point F)
    (P : Finset (Point F)) (o : Offsets D) : Prop :=
  ∃ d : D, ∃ s : Bool, ∃ x ∈ P,
    OnLine p (constituent D o d s) ∧ OnLine x (constituent D o d (!s))

theorem precoverage_probability_le (D : Finset (Direction F))
    (p : Point F) (P : Finset (Point F)) :
    probability (Precoverage D p P) ≤
      2 * (D.card : ℝ) * (P.card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  classical
  calc
    probability (Precoverage D p P) ≤
        ∑ d : D, probability (fun o => ∃ s : Bool, ∃ x ∈ P,
          OnLine p (constituent D o d s) ∧
            OnLine x (constituent D o d (!s))) :=
      probability_exists_fintype_le _
    _ ≤ ∑ d : D, ∑ s : Bool, probability (fun o => ∃ x ∈ P,
          OnLine p (constituent D o d s) ∧
            OnLine x (constituent D o d (!s))) := by
      exact Finset.sum_le_sum (fun d _ => probability_exists_fintype_le _)
    _ ≤ ∑ d : D, ∑ s : Bool, ∑ x ∈ P, probability (fun o =>
          OnLine p (constituent D o d s) ∧
            OnLine x (constituent D o d (!s))) := by
      apply Finset.sum_le_sum
      intro d _
      exact Finset.sum_le_sum (fun s _ => probability_exists_le P _)
    _ = ∑ _d : D, ∑ _s : Bool, ∑ _x ∈ P,
          1 / (Fintype.card F : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro x _
      simpa only [OnLine, constituent, eq_comm] using
        pair_probability d s (lineEval d.1 p) (lineEval d.1 x)
    _ = _ := by simp; ring

def Noncollinear (x y z : Point F) : Prop :=
  ¬ ∃ l : Line F, OnLine x l ∧ OnLine y l ∧ OnLine z l

omit [Fintype F] in
theorem Noncollinear.pairwise_ne {x y z : Point F} (h : Noncollinear x y z) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  refine ⟨?_, ?_, ?_⟩
  · intro hxy
    subst y
    exact h ⟨joiningLine x z, onLine_joiningLine_left x z,
      onLine_joiningLine_left x z, onLine_joiningLine_right x z⟩
  · intro hxz
    subst z
    exact h ⟨joiningLine x y, onLine_joiningLine_left x y,
      onLine_joiningLine_right x y, onLine_joiningLine_left x y⟩
  · intro hyz
    subst z
    exact h ⟨joiningLine x y, onLine_joiningLine_left x y,
      onLine_joiningLine_right x y, onLine_joiningLine_right x y⟩

def PairCover (D : Finset (Direction F)) (x y z : Point F)
    (s : Bool) (o : Offsets D) : Prop :=
  ∃ d : D, OnLine x (constituent D o d s) ∧
    OnLine y (constituent D o d s) ∧ OnLine z (constituent D o d (!s))

omit [Fintype F] in
private theorem direction_eq_joining (D : Finset (Direction F))
    (o : Offsets D) (d : D) (s : Bool) (x y : Point F) (hne : x ≠ y)
    (hx : OnLine x (constituent D o d s))
    (hy : OnLine y (constituent D o d s)) : d.1 = (joiningLine x y).1 := by
  exact congrArg Prod.fst (eq_of_two_common_points x y hne
    (constituent D o d s) (joiningLine x y) hx hy
    (onLine_joiningLine_left x y) (onLine_joiningLine_right x y))

theorem pairCover_probability_le (D : Finset (Direction F))
    (x y z : Point F) (hne : x ≠ y) (s : Bool) :
    probability (PairCover D x y z s) ≤ 1 / (Fintype.card F : ℝ) ^ 2 := by
  classical
  by_cases hd : (joiningLine x y).1 ∈ D
  · let d₀ : D := ⟨(joiningLine x y).1, hd⟩
    calc
      probability (PairCover D x y z s) ≤
          probability (fun o : Offsets D =>
            o d₀ s = lineEval d₀.1 x ∧ o d₀ (!s) = lineEval d₀.1 z) := by
        apply probability_mono
        rintro o ⟨d, hx, hy, hz⟩
        have hdd : d = d₀ := Subtype.ext (direction_eq_joining D o d s x y hne hx hy)
        subst d
        exact ⟨hx.symm, hz.symm⟩
      _ = _ := pair_probability d₀ s _ _
  · have hzero : probability (PairCover D x y z s) ≤ probability (fun _ : Offsets D => False) := by
      apply probability_mono
      rintro o ⟨d, hx, hy, _⟩
      exact hd ((direction_eq_joining D o d s x y hne hx hy) ▸ d.2)
    have hfalse : probability (fun _ : Offsets D => False) = 0 := by
      simp [probability]
    rw [hfalse] at hzero
    exact hzero.trans (div_nonneg zero_le_one (sq_nonneg (Fintype.card F : ℝ)))

def TwoOneCover (D : Finset (Direction F)) (x y z : Point F)
    (o : Offsets D) : Prop := ∃ s : Bool, PairCover D x y z s o

theorem twoOneCover_probability_le (D : Finset (Direction F))
    (x y z : Point F) (hne : x ≠ y) :
    probability (TwoOneCover D x y z) ≤ 2 / (Fintype.card F : ℝ) ^ 2 := by
  calc
    probability (TwoOneCover D x y z) ≤ ∑ s : Bool, probability (PairCover D x y z s) :=
      probability_exists_fintype_le _
    _ ≤ ∑ _s : Bool, 1 / (Fintype.card F : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun s _ => pairCover_probability_le D x y z hne s)
    _ = _ := by simp; ring

def TripleCovered (D : Finset (Direction F)) (x y z : Point F)
    (o : Offsets D) : Prop :=
  ∃ d : D, (∃ s : Bool, OnLine x (constituent D o d s)) ∧
    (∃ s : Bool, OnLine y (constituent D o d s)) ∧
    (∃ s : Bool, OnLine z (constituent D o d s))

omit [Fintype F] [DecidableEq F] in
theorem tripleCovered_split (D : Finset (Direction F))
    (x y z : Point F) (hn : Noncollinear x y z) (o : Offsets D)
    (h : TripleCovered D x y z o) :
    TwoOneCover D x y z o ∨ TwoOneCover D x z y o ∨ TwoOneCover D y z x o := by
  obtain ⟨d, ⟨sx, hx⟩, ⟨sy, hy⟩, ⟨sz, hz⟩⟩ := h
  cases sx <;> cases sy <;> cases sz
  · exact (hn ⟨constituent D o d false, hx, hy, hz⟩).elim
  · exact Or.inl ⟨false, d, hx, hy, hz⟩
  · exact Or.inr (Or.inl ⟨false, d, hx, hz, hy⟩)
  · exact Or.inr (Or.inr ⟨true, d, hy, hz, hx⟩)
  · exact Or.inr (Or.inr ⟨false, d, hy, hz, hx⟩)
  · exact Or.inr (Or.inl ⟨true, d, hx, hz, hy⟩)
  · exact Or.inl ⟨true, d, hx, hy, hz⟩
  · exact (hn ⟨constituent D o d true, hx, hy, hz⟩).elim

theorem tripleCovered_probability_le (D : Finset (Direction F))
    (x y z : Point F) (hn : Noncollinear x y z) :
    probability (TripleCovered D x y z) ≤ 6 / (Fintype.card F : ℝ) ^ 2 := by
  obtain ⟨hxy, hxz, hyz⟩ := hn.pairwise_ne
  have h := probability_union3_bound (tripleCovered_split D x y z hn)
    (twoOneCover_probability_le D x y z hxy)
    (twoOneCover_probability_le D x z y hxz)
    (twoOneCover_probability_le D y z x hyz)
  convert h using 1
  ring

def NoncollinearTripleInPair (D : Finset (Direction F))
    (P : Finset (Point F)) (o : Offsets D) : Prop :=
  ∃ x ∈ P, ∃ y ∈ P, ∃ z ∈ P,
    Noncollinear x y z ∧ TripleCovered D x y z o

theorem noncollinearTripleInPair_probability_le (D : Finset (Direction F))
    (P : Finset (Point F)) :
    probability (NoncollinearTripleInPair D P) ≤
      6 * (P.card : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  have hsingle (x y z : Point F) :
      probability (fun o : Offsets D => Noncollinear x y z ∧ TripleCovered D x y z o) ≤
        6 / (Fintype.card F : ℝ) ^ 2 := by
    by_cases hn : Noncollinear x y z
    · exact (probability_mono (fun _ h => h.2)).trans
        (tripleCovered_probability_le D x y z hn)
    · simp only [hn, false_and, probability, Finset.filter_false,
        Finset.card_empty, Nat.cast_zero, zero_div]
      exact div_nonneg (by norm_num) (sq_nonneg _)
  calc
    probability (NoncollinearTripleInPair D P) ≤
        ∑ x ∈ P, probability (fun o : Offsets D => ∃ y ∈ P, ∃ z ∈ P,
          Noncollinear x y z ∧ TripleCovered D x y z o) := probability_exists_le P _
    _ ≤ ∑ x ∈ P, ∑ y ∈ P, probability (fun o : Offsets D => ∃ z ∈ P,
          Noncollinear x y z ∧ TripleCovered D x y z o) :=
      Finset.sum_le_sum (fun x _ => probability_exists_le P _)
    _ ≤ ∑ x ∈ P, ∑ y ∈ P, ∑ z ∈ P, probability (fun o : Offsets D =>
          Noncollinear x y z ∧ TripleCovered D x y z o) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => probability_exists_le P _))
    _ ≤ ∑ _x ∈ P, ∑ _y ∈ P, ∑ _z ∈ P, 6 / (Fintype.card F : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
        Finset.sum_le_sum (fun z _ => hsingle x y z)))
    _ = _ := by simp; ring

end Balanced.UnusedOffsetIncidence

end

end OAI
