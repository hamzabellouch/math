import Mathlib
import OAI.Geometry.HyperbolicGroups.GeometricAction

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace HyperbolicObstruction
open scoped BigOperators

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem expect_comm (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → β → ℝ) :
    μ.expect (fun a => ν.expect (f a)) = ν.expect (fun b => μ.expect (fun a => f a b)) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expect_le_of_totalVariation (μ ν : FiniteLaw α) (f : α → ℝ) {B η : ℝ}
    (hB : 0 ≤ B) (hf : ∀ a, |f a| ≤ B) (hη : μ.totalVariation ν ≤ η) :
    μ.expect f ≤ ν.expect f + 2 * B * η := by
  have hh := (abs_le.mp (μ.expect_sub_bound ν f hf)).2
  have hm := mul_le_mul_of_nonneg_left hη (show (0 : ℝ) ≤ 2 * B by positivity)
  linarith

theorem totalVariation_comm (μ ν : FiniteLaw α) : μ.totalVariation ν = ν.totalVariation μ := by
  unfold totalVariation
  simp_rw [abs_sub_comm (μ.mass _) (ν.mass _)]

end FiniteLaw

namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

theorem abs_pairing_le (x y : X) :
    |T.pairing x y| ≤ dist T.vertex x * dist T.vertex y := by
  have ha := dist_nonneg (x := T.vertex) (y := x)
  have hb := dist_nonneg (x := T.vertex) (y := y)
  have hd := dist_nonneg (x := x) (y := y)
  have hab : dist x y ≤ dist T.vertex x + dist T.vertex y := by
    simpa [dist_comm] using dist_triangle x T.vertex y
  have hba : |dist T.vertex x - dist T.vertex y| ≤ dist x y := by
    have h₁ := dist_triangle T.vertex x y
    have h₂ := dist_triangle T.vertex y x
    rw [dist_comm y x] at h₂
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := sq_le_sq₀ (abs_nonneg (dist T.vertex x - dist T.vertex y)) hd |>.mpr hba
  have hs' := sq_le_sq₀ hd (add_nonneg ha hb) |>.mpr hab
  rw [sq_abs] at hs
  unfold pairing normSq
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem normSq_inductiveMean_le (h : CATZero X) {M : ℝ} (hM : 0 ≤ M)
    (n : ℕ) (v : Fin n → X) (hv : ∀ i, dist T.vertex (v i) ≤ M) :
    T.normSq (T.inductiveMean h n v) ≤ M ^ 2 := by
  induction n with
  | zero => simpa [inductiveMean] using sq_nonneg M
  | succ n ih =>
    have hi := ih (fun i => v i.castSucc) (fun i => hv i.castSucc)
    have hl : T.normSq (v (Fin.last n)) ≤ M ^ 2 :=
      (sq_le_sq₀ dist_nonneg hM).mpr (hv _)
    have ht := reciprocal_mem n
    have hc := T.normSq_segment h (T.inductiveMean h n (fun i => v i.castSucc))
      (v (Fin.last n)) ht
    have hh := add_le_add (mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hl ht.1)
    have hd := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
      (sq_nonneg (dist (T.inductiveMean h n (fun i => v i.castSucc)) (v (Fin.last n))))
    change T.normSq (CATZero.segment h _ _ _) ≤ _
    nlinarith

theorem dist_inductiveMean_le (h : CATZero X) {M : ℝ} (hM : 0 ≤ M)
    (n : ℕ) (v : Fin n → X) (hv : ∀ i, dist T.vertex (v i) ≤ M) :
    dist T.vertex (T.inductiveMean h n v) ≤ M := by
  have hh := T.normSq_inductiveMean_le h hM n v hv
  unfold normSq at hh
  nlinarith [dist_nonneg (x := T.vertex) (y := T.inductiveMean h n v)]

/-- The manuscript's quantitative conditional test. The hypotheses describe
an actual finite coupling, with all of its branch and leaf errors explicit.
The action-dependent function is not required to be independent of the law. -/
theorem conditional_test {α β ι : Type*} [Fintype α] [Fintype β]
    [Fintype ι] [Nonempty ι] (h : CATZero X)
    (μ : FiniteLaw α) (κ : FiniteLaw β) (v : ι → X)
    (hbar : ∀ u, (𝔼 i, T.pairing u (v i)) ≤ 0)
    (hen : (𝔼 i, T.normSq (v i)) = 1)
    (test : α → X) (letter : α → ι) (n : ℕ)
    (branch : Fin (n + 1) → β → α)
    (agree : ∀ j b, test (branch j b) = test (branch 0 b))
    {M B η : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hv : ∀ i, dist T.vertex (v i) ≤ M)
    (htest : ∀ a, dist T.vertex (test a) ≤ B)
    (hbranch : ∀ j, (κ.map (branch j)).totalVariation μ ≤ η)
    (hleaf : (κ.map (fun b j => letter (branch j b))).totalVariation
      (FiniteLaw.uniform : FiniteLaw (Fin (n + 1) → ι)) ≤ η) :
    μ.expect (fun a => T.pairing (test a) (v (letter a))) ≤
      B * Real.sqrt (1 / (n + 1 : ℝ) + 2 * M ^ 2 * η) + 2 * B * M * η := by
  let f : α → ℝ := fun a => T.pairing (test a) (v (letter a))
  let ℓ : β → (Fin (n + 1) → ι) := fun b j => letter (branch j b)
  let mean : (Fin (n + 1) → ι) → X := fun a => T.inductiveMean h (n + 1) (v ∘ a)
  let U : FiniteLaw (Fin (n + 1)) := FiniteLaw.uniform
  have hf : ∀ a, |f a| ≤ B * M := by
    intro a
    exact (T.abs_pairing_le _ _).trans
      (mul_le_mul (htest a) (hv _) dist_nonneg hB)
  have hb : μ.expect f ≤ κ.expect (fun b => U.expect (fun j => f (branch j b))) +
      2 * B * M * η := by
    have hh : ∀ j, μ.expect f ≤ κ.expect (fun b => f (branch j b)) + 2 * (B * M) * η := by
      intro j
      have hj := μ.expect_le_of_totalVariation (κ.map (branch j)) f (η := η) (mul_nonneg hB hM) hf
        (by rw [FiniteLaw.totalVariation_comm]; exact hbranch j)
      rw [FiniteLaw.expect_map] at hj
      exact hj
    have he := U.expect_mono hh
    rw [U.expect_const, U.expect_add, U.expect_const, FiniteLaw.expect_comm] at he
    nlinarith
  have hmean : κ.expect (fun b => T.normSq (mean (ℓ b))) ≤
      1 / (n + 1 : ℝ) + 2 * M ^ 2 * η := by
    have hh := (κ.map ℓ).expect_le_of_totalVariation FiniteLaw.uniform
      (fun a => T.normSq (mean a)) (sq_nonneg M)
      (fun a => by
        rw [abs_of_nonneg (T.normSq_nonneg _)]
        exact T.normSq_inductiveMean_le h hM _ _ (fun i => hv _)) hleaf
    rw [FiniteLaw.expect_map, FiniteLaw.expect_uniform] at hh
    have hi := T.expected_inductiveMean h v hbar hen n
    exact hh.trans (add_le_add hi le_rfl)
  have hp : ∀ b, U.expect (fun j => f (branch j b)) ≤
      B * dist T.vertex (mean (ℓ b)) := by
    intro b
    have hi := T.pairing_inductiveMean h (test (branch 0 b)) (n + 1) (v ∘ ℓ b)
    have hd : (0 : ℝ) < n + 1 := by positivity
    have hc : U.expect (fun j => f (branch j b)) ≤ T.pairing (test (branch 0 b)) (mean (ℓ b)) := by
      rw [FiniteLaw.expect_uniform, Fintype.expect_eq_sum_div_card]
      simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      apply (div_le_iff₀ hd).mpr
      have he : (∑ j, f (branch j b)) = ∑ j, T.pairing (test (branch 0 b)) (v (ℓ b j)) := by
        apply Finset.sum_congr rfl
        intro j _
        change T.pairing (test (branch j b)) (v _) = _
        rw [agree j b]
      rw [he]
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_comm] using hi
    exact hc.trans ((le_abs_self _).trans ((T.abs_pairing_le _ _).trans
      (mul_le_mul_of_nonneg_right (htest _) dist_nonneg)))
  have hs := κ.expect_le_sqrt (fun b => dist T.vertex (mean (ℓ b)))
  have hs' := Real.sqrt_le_sqrt hmean
  have hfinal := κ.expect_mono hp
  rw [κ.expect_mul] at hfinal
  calc
    _ ≤ κ.expect (fun b => U.expect (fun j => f (branch j b))) + 2 * B * M * η := hb
    _ ≤ B * κ.expect (fun b => dist T.vertex (mean (ℓ b))) + 2 * B * M * η :=
      add_le_add hfinal le_rfl
    _ ≤ B * Real.sqrt (1 / (n + 1 : ℝ) + 2 * M ^ 2 * η) + 2 * B * M * η :=
      add_le_add (mul_le_mul_of_nonneg_left (hs.trans hs') hB) le_rfl

end ConeData
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators
open Filter Topology

/-- Passing to the limit in the quantitative conditional test, first with
sample size fixed and then letting it tend to infinity. -/
theorem conditional_test_eventually {a : ℕ → ℝ} {B M : ℝ}
    (hbound : ∀ n : ℕ, ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ ν in atTop, a ν ≤ B * Real.sqrt (1 / (n + 1 : ℝ) + 2 * M ^ 2 * η ν) +
        2 * B * M * η ν) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ ν in atTop, a ν < ε := by
  intro ε hε
  have hz : Tendsto (fun n : ℕ => B * Real.sqrt (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp
      tendsto_one_div_add_atTop_nhds_zero_nat).const_mul B
  obtain ⟨n, hn⟩ := (hz.eventually (gt_mem_nhds hε)).exists
  obtain ⟨η, hη, hineq⟩ := hbound n
  have ht : Tendsto (fun ν => B * Real.sqrt (1 / (n + 1 : ℝ) + 2 * M ^ 2 * η ν) +
      2 * B * M * η ν) atTop (𝓝 (B * Real.sqrt (1 / (n + 1 : ℝ)))) := by
    have hsum : Tendsto (fun ν => 1 / (n + 1 : ℝ) + 2 * M ^ 2 * η ν) atTop
        (𝓝 (1 / (n + 1 : ℝ) + 2 * M ^ 2 * 0)) :=
      tendsto_const_nhds.add (hη.const_mul (2 * M ^ 2))
    have hh := ((Real.continuous_sqrt.tendsto _).comp hsum).const_mul B
    simpa using hh.add (hη.const_mul (2 * B * M))
  filter_upwards [hineq, ht.eventually (gt_mem_nhds hn)] with ν hν hν'
  exact hν.trans_lt hν'

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem expect_le_density (μ ν : FiniteLaw α) {R : ℝ}
    (hm : ∀ a, μ.mass a ≤ R * ν.mass a) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    μ.expect f ≤ R * ν.expect f := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hm a) (hf a)

theorem expect_map_le_uniform [Nonempty β] (μ : FiniteLaw α) (e : α → β) {R : ℝ}
    (hm : ∀ b, (μ.map e).mass b ≤ R / Fintype.card β)
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    μ.expect (f ∘ e) ≤ R * (𝔼 b, f b) := by
  have hh := (μ.map e).expect_le_density uniform (R := R)
    (fun b => by simpa [uniform, div_eq_mul_inv] using hm b) f hf
  rwa [expect_map, expect_uniform] at hh

end FiniteLaw

namespace GeometricAction
variable {G X : Type*} [Group G] [MetricSpace X]

theorem displacement_inv (A : GeometricAction G X) (x : X) (g : G) :
    dist x (A.act g⁻¹ x) = dist x (A.act g x) := by
  have hh := (A.act g).isometry.dist_eq x (A.act g⁻¹ x)
  have he : A.act g (A.act g⁻¹ x) = x := by
    rw [← IsometryEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [he, dist_comm] at hh
  exact hh.symm

theorem displacement_mul_le (A : GeometricAction G X) (x : X) (g k : G) :
    dist x (A.act (g * k) x) ≤ dist x (A.act g x) + dist x (A.act k x) := by
  calc
    _ ≤ dist x (A.act g x) + dist (A.act g x) (A.act (g * k) x) := dist_triangle _ _ _
    _ = _ := by rw [map_mul, IsometryEquiv.mul_apply, (A.act g).isometry.dist_eq]

theorem displacement_prod_le (A : GeometricAction G X) (x : X) (w : List G) :
    dist x (A.act w.prod x) ≤ (w.map (fun g => dist x (A.act g x))).sum := by
  induction w with
  | nil => simp
  | cons g w ih =>
    simpa only [List.prod_cons, List.map_cons, List.sum_cons] using
      (A.displacement_mul_le x g w.prod).trans (add_le_add le_rfl ih)

/-- Averaging the actual six-letter relations gives the uniform displacement
bound. Marginal domination is pointwise, so no independence of the action
chosen after the rows is needed. -/
theorem six_letter_displacement_bound {α ι : Type*} [Fintype α] [Fintype ι]
    [Nonempty ι] (A : GeometricAction G X) (x : X) (letter : ι → G)
    (hen : (𝔼 i, dist x (A.act (letter i) x) ^ 2) = 1)
    (a : G) (κ : FiniteLaw α) (row : α → Fin 5 → ι)
    (hrow : ∀ b, (List.ofFn (letter ∘ row b)).prod = a⁻¹)
    {R : ℝ} (hmarg : ∀ j i, (κ.map (fun b => row b j)).mass i ≤ R / Fintype.card ι) :
    dist x (A.act a x) ^ 2 ≤ 25 * R := by
  have hb : ∀ b, dist x (A.act a x) ^ 2 ≤ 5 * ∑ j, dist x (A.act (letter (row b j)) x) ^ 2 := by
    intro b
    have hp := A.displacement_prod_le x (List.ofFn (letter ∘ row b))
    rw [hrow b, A.displacement_inv x a, List.map_ofFn, List.sum_ofFn] at hp
    have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j : Fin 5 => dist x (A.act (letter (row b j)) x))
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hc
    have hs := (sq_le_sq₀ dist_nonneg (Finset.sum_nonneg (fun _ _ => dist_nonneg))).mpr hp
    exact hs.trans hc
  have hh := κ.expect_mono hb
  rw [κ.expect_const, κ.expect_mul, κ.expect_sum] at hh
  have hj : ∀ j : Fin 5, κ.expect (fun b => dist x (A.act (letter (row b j)) x) ^ 2) ≤ R := by
    intro j
    have he := κ.expect_map_le_uniform (fun b => row b j) (hmarg j)
      (fun i => dist x (A.act (letter i) x) ^ 2) (fun _ => sq_nonneg _)
    simpa only [Function.comp_def, hen, mul_one] using he
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) => hj j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at hs
  linarith

end GeometricAction
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

/-- The exact equality case of the quadrilateral inequality, also used for
hexagons whose diagonals have squared length at least three. -/
theorem quadrilateral_saturation (h : CATZero X) (a b c d : X) (r s : ℝ)
    (hac : r ≤ dist a c ^ 2) (hbd : s ≤ dist b d ^ 2)
    (hsides : dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 = r + s) :
    dist a c ^ 2 = r ∧ dist b d ^ 2 = s ∧ mid h a c = mid h b d := by
  have hq := quadrilateral h a b c d
  rw [hsides] at hq
  have hn := sq_nonneg (dist (mid h a c) (mid h b d))
  refine ⟨by linarith, by linarith, ?_⟩
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := mid h a c) (y := mid h b d)]

end CATZero

/-- Six cyclic vertices, with exactly the path information obtained from the
square decorations and admissible three-edge paths. -/
structure MetricHexagon {X : Type*} [MetricSpace X] (z : Fin 6 → X) : Prop where
  side : ∀ i, dist (z i) (z (i + 1)) ^ 2 = 1
  twoStep : ∀ i, dist (z i) (z (i + 2)) ^ 2 = 2
  opposite : ∀ i, 3 ≤ dist (z i) (z (i + 3)) ^ 2

/-- The squared distances, by cyclic separation, not planar hexagon angles. -/
def hexDistSq (i j : Fin 6) : ℕ :=
  (![![0,1,2,3,2,1], ![1,0,1,2,3,2], ![2,1,0,1,2,3],
      ![3,2,1,0,1,2], ![2,3,2,1,0,1], ![1,2,3,2,1,0]] : Fin 6 → Fin 6 → ℕ) i j

lemma hexDistSq_opposite_sum : ∀ i j : Fin 6,
    hexDistSq i j + hexDistSq i (j + 3) = 3 := by
  decide

lemma hexDistSq_opposite : ∀ j : Fin 6, hexDistSq j (j + 3) = 3 := by
  decide

namespace MetricHexagon
variable {X : Type*} [MetricSpace X] {z : Fin 6 → X}

theorem rigidity (D : MetricHexagon z) (h : CATZero X) :
    (∀ i j, dist (z i) (z j) ^ 2 = hexDistSq i j) ∧
    (∀ j, CATZero.mid h (z j) (z (j + 3)) = CATZero.mid h (z 0) (z 3)) := by
  have hs0 : dist (z 0) (z 1) ^ 2 = 1 := D.side 0
  have hs1 : dist (z 1) (z 2) ^ 2 = 1 := D.side 1
  have hs2 : dist (z 2) (z 3) ^ 2 = 1 := D.side 2
  have hs3 : dist (z 3) (z 4) ^ 2 = 1 := D.side 3
  have hs4 : dist (z 4) (z 5) ^ 2 = 1 := D.side 4
  have hs5 : dist (z 5) (z 0) ^ 2 = 1 := D.side 5
  have ht0 : dist (z 0) (z 2) ^ 2 = 2 := D.twoStep 0
  have ht1 : dist (z 1) (z 3) ^ 2 = 2 := D.twoStep 1
  have ht2 : dist (z 2) (z 4) ^ 2 = 2 := D.twoStep 2
  have ht3 : dist (z 3) (z 5) ^ 2 = 2 := D.twoStep 3
  have ht4 : dist (z 4) (z 0) ^ 2 = 2 := D.twoStep 4
  have ht5 : dist (z 5) (z 1) ^ 2 = 2 := D.twoStep 5
  have ho0 : 3 ≤ dist (z 0) (z 3) ^ 2 := D.opposite 0
  have ho1 : 3 ≤ dist (z 1) (z 4) ^ 2 := D.opposite 1
  have ho2 : 3 ≤ dist (z 2) (z 5) ^ 2 := D.opposite 2
  have hq0 := CATZero.quadrilateral_saturation h (z 0) (z 1) (z 3) (z 4) 3 3
    ho0 ho1 (by rw [hs0, ht1, hs3, ht4]; norm_num)
  have hq1 := CATZero.quadrilateral_saturation h (z 1) (z 2) (z 4) (z 5) 3 3
    ho1 ho2 (by rw [hs1, ht2, hs4, ht5]; norm_num)
  have hd0 := hq0.1
  have hd1 := hq0.2.1
  have hd2 := hq1.2.1
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · change dist (z 0) (z 0) ^ 2 = (0 : ℕ)
      simp
    · change dist (z 0) (z 1) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs0
    · change dist (z 0) (z 2) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht0
    · change dist (z 0) (z 3) ^ 2 = (3 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd0
    · change dist (z 0) (z 4) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht4
    · change dist (z 0) (z 5) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs5
    · change dist (z 1) (z 0) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs0
    · change dist (z 1) (z 1) ^ 2 = (0 : ℕ)
      simp
    · change dist (z 1) (z 2) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs1
    · change dist (z 1) (z 3) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht1
    · change dist (z 1) (z 4) ^ 2 = (3 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd1
    · change dist (z 1) (z 5) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht5
    · change dist (z 2) (z 0) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht0
    · change dist (z 2) (z 1) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs1
    · change dist (z 2) (z 2) ^ 2 = (0 : ℕ)
      simp
    · change dist (z 2) (z 3) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs2
    · change dist (z 2) (z 4) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht2
    · change dist (z 2) (z 5) ^ 2 = (3 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd2
    · change dist (z 3) (z 0) ^ 2 = (3 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd0
    · change dist (z 3) (z 1) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht1
    · change dist (z 3) (z 2) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs2
    · change dist (z 3) (z 3) ^ 2 = (0 : ℕ)
      simp
    · change dist (z 3) (z 4) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs3
    · change dist (z 3) (z 5) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht3
    · change dist (z 4) (z 0) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht4
    · change dist (z 4) (z 1) ^ 2 = (3 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd1
    · change dist (z 4) (z 2) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht2
    · change dist (z 4) (z 3) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs3
    · change dist (z 4) (z 4) ^ 2 = (0 : ℕ)
      simp
    · change dist (z 4) (z 5) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs4
    · change dist (z 5) (z 0) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs5
    · change dist (z 5) (z 1) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht5
    · change dist (z 5) (z 2) ^ 2 = (3 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd2
    · change dist (z 5) (z 3) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht3
    · change dist (z 5) (z 4) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs4
    · change dist (z 5) (z 5) ^ 2 = (0 : ℕ)
      simp
  · intro j
    fin_cases j
    · rfl
    · exact hq0.2.2.symm
    · exact hq1.2.2.symm.trans hq0.2.2.symm
    · exact CATZero.mid_swap h (z 0) (z 3)
    · exact (CATZero.mid_swap h (z 1) (z 4)).trans hq0.2.2.symm
    · exact (CATZero.mid_swap h (z 2) (z 5)).trans (hq1.2.2.symm.trans hq0.2.2.symm)

/-- The radius squared at the common opposite-pair midpoint. -/
theorem radius (D : MetricHexagon z) (h : CATZero X) (j : Fin 6) :
    dist (CATZero.mid h (z 0) (z 3)) (z j) ^ 2 = 3 / 4 := by
  obtain ⟨hd, hc⟩ := D.rigidity h
  rw [← hc j, dist_comm, CATZero.dist_left_mid, div_pow, hd, hexDistSq_opposite]
  norm_num

end MetricHexagon
end HyperbolicObstruction

noncomputable section

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
