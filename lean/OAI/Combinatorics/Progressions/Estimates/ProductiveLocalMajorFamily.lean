import OAI.Combinatorics.Progressions.Lattices.ResidueBoxSliceSubtypeSites
import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

variable {I L : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure ProductiveLocalMajorSliceTest (D : RationalFilteredNilmanifold L s d)
    (N : I → ℕ) (cost budget : ℝ) where
  stride : ℕ
  stride_pos : 0 < stride
  slice : ResidueBoxSlice N stride
  dense : IsDenseCommonStrideBox N cost slice.integerPoints
  test : D.Niltest (fun _ : I => 1)
  norm : (test.normBound : ℝ) ≤ 1
  complexity : test.ComplexityLE budget

namespace ProductiveLocalMajorSliceTest

variable {D : RationalFilteredNilmanifold L s d} {N : I → ℕ} {cost budget : ℝ}

noncomputable def weight (A : ProductiveLocalMajorSliceTest D N cost budget) (x : I → ℤ) : ℂ :=
  star (A.test.eval (commonStrideIndex (fun i => (A.slice.start i : ℤ)) A.stride x))

theorem weight_norm (A : ProductiveLocalMajorSliceTest D N cost budget) (x : I → ℤ) :
    ‖A.weight x‖ ≤ 1 := by
  simpa only [weight, norm_star] using
    (A.test.norm_eval_le (commonStrideIndex (fun i => (A.slice.start i : ℤ))
      A.stride x)).trans A.norm

noncomputable def full (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (cost budget : ℝ) (hcost : 0 ≤ cost)
    (T : D.Niltest (fun _ : I => 1)) (hT : (T.normBound : ℝ) ≤ 1)
    (hcomplexity : T.ComplexityLE budget) : ProductiveLocalMajorSliceTest D N cost budget := by
  let A : ResidueBoxSlice N 1 :=
    { start := fun _ => 0
      length := N
      inside := fun i j hj => by simpa using hj }
  refine ⟨1, Nat.zero_lt_one, A, ?_, T, hT, hcomplexity⟩
  have hA := A.isDenseCommonStrideBox Nat.zero_lt_one (ρ := 4) (by norm_num)
    hN (fun i => by dsimp [A]; norm_num)
  have hzero : IsDenseCommonStrideBox N 0 A.integerPoints := by
    simpa using hA
  exact hzero.mono hcost

end ProductiveLocalMajorSliceTest

theorem exists_productive_localMajorSlice_family
    {Ω X : Type*} [Fintype Ω]
    (D : RationalFilteredNilmanifold L s d)
    (law : FiniteProbabilityWeights Ω) (good : Finset Ω)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (cost budget δ : ℝ)
    (fallback : ProductiveLocalMajorSliceTest D N cost budget)
    (physical : Ω → (I → ℤ) → X) (signal : X → ℂ)
    (hlocal : ∀ z ∈ good, ∃ A : ProductiveLocalMajorSliceTest D N cost budget,
      δ ≤ ‖𝔼 x ∈ A.slice.integerPoints, signal (physical z x) * A.weight x‖) :
    ∃ chosen : Ω → ProductiveLocalMajorSliceTest D N cost budget,
      (∀ z ∈ good, δ ≤ ‖𝔼 x ∈ (chosen z).slice.integerPoints,
        signal (physical z x) * (chosen z).weight x‖) ∧
      δ * law.mass good ≤ sampledSliceSeminorm law
        (fun z (x : integerBox N) => physical z x.val)
        (fun z (_ : Unit) => (chosen z).slice.subtypeSites)
        (fun z (_ : Unit) (x : integerBox N) => (chosen z).weight x.val) signal := by
  classical
  let chosen (z : Ω) : ProductiveLocalMajorSliceTest D N cost budget :=
    if hz : z ∈ good then Classical.choose (hlocal z hz) else fallback
  have hchosen (z : Ω) (hz : z ∈ good) :
      δ ≤ ‖𝔼 x ∈ (chosen z).slice.integerPoints,
        signal (physical z x) * (chosen z).weight x‖ := by
    have hchoice : chosen z = Classical.choose (hlocal z hz) := dite_eq_left hz
    rw [hchoice]
    exact Classical.choose_spec (hlocal z hz)
  refine ⟨chosen, hchosen, ?_⟩
  let : Nonempty (integerBox N) := ⟨⟨fun _ => 0,
    (mem_integerBox _ _).mpr (fun i => ⟨le_rfl, by exact_mod_cast hN i⟩)⟩⟩
  apply productive_mass_mul_le_sampledSliceSeminorm law good
    (fun z (x : integerBox N) => physical z x.val)
    (fun z (_ : Unit) => (chosen z).slice.subtypeSites)
    (fun z (_ : Unit) (x : integerBox N) => (chosen z).weight x.val)
    (fun z _ => (chosen z).slice.subtypeSites_nonempty_of_integerPoints (chosen z).dense.nonempty)
    (fun z _ x => (chosen z).weight_norm x.val) signal δ
  intro z hz
  refine ⟨(), ?_⟩
  rw [(chosen z).slice.expect_subtypeSites
    (fun point => signal (physical z point) * (chosen z).weight point)]
  exact hchosen z hz

theorem exists_productive_localMajorFamilySlice_coordinate_family
    {Ω X η : Type*} [Fintype Ω]
    (D : RationalFilteredNilmanifold L s d)
    (law : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (cost budget δ : ℝ)
    (fallback : ProductiveLocalMajorSliceTest D N cost budget)
    (physical : Ω → (I → ℤ) → X) (signal : η → X → ℂ)
    (hlocal : ∀ j z, z ∈ good j → ∃ A : ProductiveLocalMajorSliceTest D N cost budget,
      δ ≤ ‖𝔼 x ∈ A.slice.integerPoints, signal j (physical z x) * A.weight x‖) :
    ∃ chosen : Ω → Option η → ProductiveLocalMajorSliceTest D N cost budget,
      (∀ j z, z ∈ good j → δ ≤ ‖𝔼 x ∈ (chosen z (some j)).slice.integerPoints,
        signal j (physical z x) * (chosen z (some j)).weight x‖) ∧
      ∀ j, δ * law.mass (good j) ≤ sampledSliceSeminorm law
        (fun z (x : integerBox N) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox N) => (chosen z a).weight x.val) (signal j) := by
  classical
  let chosen (z : Ω) : Option η → ProductiveLocalMajorSliceTest D N cost budget
    | none => fallback
    | some j => if hz : z ∈ good j then Classical.choose (hlocal j z hz) else fallback
  have hchosen (j : η) (z : Ω) (hz : z ∈ good j) :
      δ ≤ ‖𝔼 x ∈ (chosen z (some j)).slice.integerPoints,
        signal j (physical z x) * (chosen z (some j)).weight x‖ := by
    have hchoice : chosen z (some j) = Classical.choose (hlocal j z hz) := dite_eq_left hz
    rw [hchoice]
    exact Classical.choose_spec (hlocal j z hz)
  refine ⟨chosen, hchosen, ?_⟩
  intro j
  let : Nonempty (integerBox N) := ⟨⟨fun _ => 0,
    (mem_integerBox _ _).mpr (fun i => ⟨le_rfl, by exact_mod_cast hN i⟩)⟩⟩
  apply productive_mass_mul_le_sampledSliceSeminorm law (good j)
    (fun z (x : integerBox N) => physical z x.val)
    (fun z a => (chosen z a).slice.subtypeSites)
    (fun z a (x : integerBox N) => (chosen z a).weight x.val)
    (fun z a => (chosen z a).slice.subtypeSites_nonempty_of_integerPoints
      (chosen z a).dense.nonempty)
    (fun z a x => (chosen z a).weight_norm x.val) (signal j) δ
  intro z hz
  refine ⟨some j, ?_⟩
  rw [(chosen z (some j)).slice.expect_subtypeSites
    (fun point => signal j (physical z point) * (chosen z (some j)).weight point)]
  exact hchosen j z hz

end Erdos3

end

end OAI
