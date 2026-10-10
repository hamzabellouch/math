import Mathlib
import OAI.Geometry.HyperbolicGroups.CATZeroFurther

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

namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

theorem dist_mid_mid_le (h : CATZero X) (a b c d : X) :
    dist (mid h a b) (mid h c d) ≤ (dist a c + dist b d) / 2 := by
  have h₁ := radial_contraction h a b d (t := 1 / 2) (by norm_num)
  have h₂ := radial_contraction h d a c (t := 1 / 2) (by norm_num)
  change dist (mid h a b) (mid h a d) ≤ _ at h₁
  change dist (mid h d a) (mid h d c) ≤ _ at h₂
  rw [mid_swap h a d, mid_swap h c d] at h₂
  have ht := dist_triangle (mid h a b) (mid h a d) (mid h c d)
  linarith

theorem dist_mid_mid_sq_le (h : CATZero X) (a b c d : X) :
    dist (mid h a b) (mid h c d) ^ 2 ≤ (dist a c ^ 2 + dist b d ^ 2) / 2 := by
  have he := dist_mid_mid_le h a b c d
  have hn := dist_nonneg (x := mid h a b) (y := mid h c d)
  have ha := dist_nonneg (x := a) (y := c)
  have hb := dist_nonneg (x := b) (y := d)
  nlinarith [sq_nonneg (dist a c - dist b d)]

theorem isometry_mid (h : CATZero X) (e : X ≃ᵢ X) (a b : X) :
    e (mid h a b) = mid h (e a) (e b) :=
  map_segment_of_dist h h e (fun a b => (e.isometry.dist_eq a b).le) a b
    (e.isometry.dist_eq a b) (by norm_num)

/-- Crossed-midpoint convexity turns a minimum of a symmetric displacement
energy into a minimum of the squared distances to the fixed orbit tuple. -/
theorem orbit_minimum_of_energy_minimum {ι : Type*} [Fintype ι]
    (h : CATZero X) (e : ι → X ≃ᵢ X) (σ : ι ≃ ι)
    (hinv : ∀ i, e (σ i) = (e i).symm) (o : X)
    (hmin : ∀ y : X, (∑ i, dist o (e i o) ^ 2) ≤ ∑ i, dist y (e i y) ^ 2) :
    ∀ y : X, (∑ i, dist o (e i o) ^ 2) ≤ ∑ i, dist y (e i o) ^ 2 := by
  intro y
  have hc (i : ι) : dist (mid h o y) (e i (mid h o y)) ^ 2 ≤
      (dist o (e i y) ^ 2 + dist y (e i o) ^ 2) / 2 := by
    rw [isometry_mid, mid_swap h (e i y) (e i o)]
    exact dist_mid_mid_sq_le h o y (e i y) (e i o)
  have he (i : ι) : dist o (e i y) = dist y (e (σ i) o) := by
    rw [hinv i, dist_comm y]
    simpa using ((e i).symm.isometry.dist_eq o (e i y)).symm
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hc i)
  simp_rw [he] at hs
  simp only [← Finset.sum_div, Finset.sum_add_distrib] at hs
  rw [σ.sum_comp (fun i => dist y (e i o) ^ 2)] at hs
  have hm := hmin (mid h o y)
  linarith

end CATZero

/-- The zero-barycenter conclusion, for any attained symmetric
isometric displacement-energy minimum. -/
theorem energy_tangent_barycenter {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]
    (h : CATZero X) (e : ι → X ≃ᵢ X) (σ : ι ≃ ι)
    (hinv : ∀ i, e (σ i) = (e i).symm) (o : X)
    (hmin : ∀ y : X, (∑ i, dist o (e i o) ^ 2) ≤ ∑ i, dist y (e i y) ^ 2)
    (v : TangentCone h o) :
    (∑ i, (TangentCone.coneData h o).pairing v (TangentCone.log h o (e i o))) ≤ 0 :=
  TangentCone.pairing_sum_nonpos_of_minimum h o (fun i => e i o)
    (CATZero.orbit_minimum_of_energy_minimum h e σ hinv o hmin) v

end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace GeometricAction
open Filter Topology
variable {G X : Type*} [Group G] [MetricSpace X]

/-- Displacement is invariant under simultaneous point/generator conjugation. -/
theorem displacement_conjugate (A : GeometricAction G X) (g s : G) (x : X) :
    dist x (A.act (g⁻¹ * s * g) x) = dist (A.act g x) (A.act s (A.act g x)) := by
  calc
    _ = dist (A.act g x) (A.act g (A.act (g⁻¹ * s * g) x)) :=
      ((A.act g).isometry.dist_eq _ _).symm
    _ = _ := by simp [map_mul, IsometryEquiv.mul_apply]

/-- Properness and cocompactness give an attained displacement-energy minimum.
No CAT(0) assumption is needed for this compactness step. -/
theorem energy_minimum [Nonempty X] [ProperSpace X] {ι : Type*} [Fintype ι]
    (A : GeometricAction G X) (S : ι → G) :
    ∃ o : X, ∀ y : X, (∑ i, dist o (A.act (S i) o) ^ 2) ≤
      ∑ i, dist y (A.act (S i) y) ^ 2 := by
  classical
  let E (x : X) : ℝ := ∑ i, dist x (A.act (S i) x) ^ 2
  have hE : Continuous E := by
    unfold E
    fun_prop
  have hn (x : X) : 0 ≤ E x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : BddBelow (Set.range E) := ⟨0, by rintro _ ⟨x, rfl⟩; exact hn x⟩
  obtain ⟨v, hvanti, hv, hvr⟩ := exists_seq_tendsto_sInf (Set.range_nonempty E) hb
  choose u hu using hvr
  obtain ⟨C, hC, hcover⟩ := A.cocompact
  choose g c hc hgc using fun n : ℕ => hcover (u n)
  let x₀ : X := Classical.arbitrary X
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall x₀
  have hv₀ : 0 ≤ v 0 := by rw [← hu 0]; exact hn _
  let B := Metric.closedBall x₀ (R + v 0 + 1)
  have hCB : C ⊆ B := by
    intro x hx
    have hr := hR hx
    change dist x x₀ ≤ _ at hr ⊢
    linarith
  let H : Set G := {s | ∃ x ∈ B, A.act s x ∈ B}
  have hH : H.Finite := A.proper B (isCompact_closedBall _ _)
  have hd (n : ℕ) (i : ι) : dist (u n) (A.act (S i) (u n)) ≤ v 0 + 1 := by
    have hi : dist (u n) (A.act (S i) (u n)) ^ 2 ≤ E (u n) := by
      change dist (u n) (A.act (S i) (u n)) ^ 2 ≤ ∑ j, dist (u n) (A.act (S j) (u n)) ^ 2
      exact Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
        sq_nonneg (dist (u n) (A.act (S j) (u n)))) (Finset.mem_univ i)
    rw [hu n] at hi
    have hvn := hvanti (Nat.zero_le n)
    nlinarith [sq_nonneg (dist (u n) (A.act (S i) (u n)) - 1 / 2)]
  have hconj (n : ℕ) (i : ι) : (g n)⁻¹ * S i * g n ∈ H := by
    refine ⟨c n, hCB (hc n), ?_⟩
    have hdr : dist (c n) (A.act ((g n)⁻¹ * S i * g n) (c n)) ≤ v 0 + 1 := by
      rw [displacement_conjugate, hgc n]
      exact hd n i
    have hcr := hR (hc n)
    have ht := dist_triangle (A.act ((g n)⁻¹ * S i * g n) (c n)) (c n) x₀
    rw [dist_comm (A.act _ _) (c n)] at ht
    change dist (c n) x₀ ≤ R at hcr
    change dist (A.act _ _) x₀ ≤ _
    linarith
  let : Fintype H := hH.fintype
  let q (n : ℕ) : ι → H := fun i => ⟨(g n)⁻¹ * S i * g n, hconj n i⟩
  have hf : ∃ᶠ n : ℕ in atTop, ∃ k : ι → H, q n = k :=
    Filter.Frequently.of_forall fun n => ⟨q n, rfl⟩
  obtain ⟨k, hk⟩ := Filter.frequently_exists.mp hf
  obtain ⟨φ, hφ, hq⟩ := Filter.extraction_of_frequently_atTop hk
  obtain ⟨z, _, ψ, hψ, hz⟩ := hC.tendsto_subseq (fun n => hc (φ n))
  let E' (x : X) : ℝ := ∑ i, dist x (A.act ((g (φ 0))⁻¹ * S i * g (φ 0)) x) ^ 2
  have hE' : Continuous E' := by
    unfold E'
    fun_prop
  have heq (n : ℕ) : E' (c (φ (ψ n))) = v (φ (ψ n)) := by
    have hh (i : ι) : (g (φ 0))⁻¹ * S i * g (φ 0) =
        (g (φ (ψ n)))⁻¹ * S i * g (φ (ψ n)) := by
      exact congrArg Subtype.val (congrFun ((hq 0).trans (hq (ψ n)).symm) i)
    simp_rw [E', hh, displacement_conjugate, hgc]
    exact hu _
  have hez : E' z = sInf (Set.range E) := by
    apply tendsto_nhds_unique ((hE'.tendsto z).comp hz)
    have hlim := hv.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
    exact hlim.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
  refine ⟨A.act (g (φ 0)) z, ?_⟩
  intro y
  have hx : E (A.act (g (φ 0)) z) = E' z := by
    simp_rw [E, E', ← displacement_conjugate]
  change E _ ≤ E y
  rw [hx, hez]
  exact csInf_le hb (Set.mem_range_self y)

end GeometricAction
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace GeometricAction
variable {G X : Type*} [Group G] [MetricSpace X]

/-- An infinite group with a proper action cannot have zero displacement
energy on a finite generating tuple. -/
theorem energy_pos [Infinite G] {ι : Type*} [Fintype ι]
    (A : GeometricAction G X) (S : ι → G)
    (hgen : Subgroup.closure (Set.range S) = ⊤) (o : X) :
    0 < ∑ i, dist o (A.act (S i) o) ^ 2 := by
  classical
  have hn : 0 ≤ ∑ i, dist o (A.act (S i) o) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_contra hp
  have he : (∑ i, dist o (A.act (S i) o) ^ 2) = 0 := le_antisymm (not_lt.mp hp) hn
  have hs (i : ι) : A.act (S i) o = o := by
    have hi : dist o (A.act (S i) o) ^ 2 ≤ ∑ j, dist o (A.act (S j) o) ^ 2 :=
      Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
        sq_nonneg (dist o (A.act (S j) o))) (Finset.mem_univ i)
    rw [he] at hi
    exact (dist_eq_zero.mp (by nlinarith [dist_nonneg (x := o) (y := A.act (S i) o)])).symm
  have hfix (g : G) : A.act g o = o := by
    have hg : g ∈ Subgroup.closure (Set.range S) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction with
    | mem a ha => obtain ⟨i, rfl⟩ := ha; exact hs i
    | one => simp
    | mul a b _ _ ha hb => simp [map_mul, IsometryEquiv.mul_apply, ha, hb]
    | inv a _ ha =>
      have hh := congrArg (fun x => (A.act a)⁻¹ x) ha
      simpa using hh.symm
  have hf := A.proper {o} isCompact_singleton
  have hall : ({g : G | ∃ x ∈ ({o} : Set X), A.act g x ∈ ({o} : Set X)}) = Set.univ := by
    ext g
    simp [hfix g]
  rw [hall] at hf
  exact Set.infinite_univ hf

end GeometricAction
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators

/-- Splitting off the last coordinate of a uniform independent tuple. -/
theorem expect_snoc {ι : Type*} [Fintype ι] (n : ℕ) (f : (Fin (n + 1) → ι) → ℝ) :
    (𝔼 a, f a) = 𝔼 a : Fin n → ι, 𝔼 i : ι, f (Fin.snoc a i) := by
  calc
    _ = 𝔼 p : ι × (Fin n → ι), f (Fin.snoc p.2 p.1) := by
      apply Fintype.expect_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => ι)).symm
      intro a
      simp
    _ = 𝔼 i : ι, 𝔼 a : Fin n → ι, f (Fin.snoc a i) := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = _ := Finset.expect_comm _ _ _

namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

theorem normSq_segment_pairing (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    T.normSq (CATZero.segment h x y t) = (1 - t) ^ 2 * T.normSq x +
      t ^ 2 * T.normSq y + 2 * t * (1 - t) * T.pairing x y := by
  rw [T.normSq_segment h x y ht, T.dist_sq]
  ring

/-- The ordered inductive mean, with the harmless value vertex for an empty
list. For a list of length j+1, append its last point with weight 1/(j+1). -/
def inductiveMean (T : ConeData X) (h : CATZero X) : (n : ℕ) → (Fin n → X) → X
  | 0, _ => T.vertex
  | n + 1, v => CATZero.segment h
      (inductiveMean T h n (fun i => v i.castSucc)) (v (Fin.last n)) (1 / (n + 1 : ℝ))

theorem reciprocal_mem (n : ℕ) : 1 / (n + 1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · exact (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)

/-- Deterministic concavity for the ordered mean; no associative cone
addition is used. -/
theorem pairing_inductiveMean (h : CATZero X) (w : X) (n : ℕ) (v : Fin n → X) :
    (∑ i, T.pairing w (v i)) ≤ (n : ℝ) * T.pairing w (T.inductiveMean h n v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have hi := ih (fun i => v i.castSucc)
    have hc := T.pairing_segment h w (T.inductiveMean h n (fun i => v i.castSucc))
      (v (Fin.last n)) (reciprocal_mem n)
    have hh : (n : ℝ) * T.pairing w (T.inductiveMean h n (fun i => v i.castSucc)) +
        T.pairing w (v (Fin.last n)) ≤
        (n + 1 : ℝ) * T.pairing w (T.inductiveMean h (n + 1) v) := by
      calc
        _ = (n + 1 : ℝ) * ((1 - 1 / (n + 1 : ℝ)) *
          T.pairing w (T.inductiveMean h n (fun i => v i.castSucc)) +
          (1 / (n + 1 : ℝ)) * T.pairing w (v (Fin.last n))) := by
            field_simp
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
    push_cast
    linarith

/-- One genuinely independent averaging step, using the zero-barycenter
inequality rather than any linear ambient vector space. -/
theorem expected_step {ι : Type*} [Fintype ι] [Nonempty ι]
    (h : CATZero X) (v : ι → X)
    (hbar : ∀ u, (𝔼 i, T.pairing u (v i)) ≤ 0)
    (hen : (𝔼 i, T.normSq (v i)) = 1) (u : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (𝔼 i, T.normSq (CATZero.segment h u (v i) t)) ≤ (1 - t) ^ 2 * T.normSq u + t ^ 2 := by
  simp_rw [T.normSq_segment_pairing h u _ ht]
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const, hen, mul_one]
  have hh := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht.1) (sub_nonneg.mpr ht.2)) (hbar u)
  linarith

theorem expected_inductiveMean_step {ι : Type*} [Fintype ι] [Nonempty ι]
    (h : CATZero X) (v : ι → X)
    (hbar : ∀ u, (𝔼 i, T.pairing u (v i)) ≤ 0)
    (hen : (𝔼 i, T.normSq (v i)) = 1) (n : ℕ) :
    (𝔼 a : Fin (n + 1) → ι, T.normSq (T.inductiveMean h (n + 1) (v ∘ a))) ≤
      (1 - 1 / (n + 1 : ℝ)) ^ 2 *
        (𝔼 a : Fin n → ι, T.normSq (T.inductiveMean h n (v ∘ a))) +
          (1 / (n + 1 : ℝ)) ^ 2 := by
  rw [expect_snoc]
  simp only [inductiveMean, Function.comp_apply, Fin.snoc_castSucc, Fin.snoc_last]
  calc
    _ ≤ 𝔼 a : Fin n → ι, ((1 - 1 / (n + 1 : ℝ)) ^ 2 *
        T.normSq (T.inductiveMean h n (v ∘ a)) + (1 / (n + 1 : ℝ)) ^ 2) := by
      apply Finset.expect_le_expect
      intro a _
      exact T.expected_step h v hbar hen (T.inductiveMean h n (v ∘ a)) (reciprocal_mem n)
    _ = _ := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]

/-- The exact 1/t mean-square decay for t independent uniform samples. -/
theorem expected_inductiveMean {ι : Type*} [Fintype ι] [Nonempty ι]
    (h : CATZero X) (v : ι → X)
    (hbar : ∀ u, (𝔼 i, T.pairing u (v i)) ≤ 0)
    (hen : (𝔼 i, T.normSq (v i)) = 1) (n : ℕ) :
    (𝔼 a : Fin (n + 1) → ι, T.normSq (T.inductiveMean h (n + 1) (v ∘ a))) ≤
      1 / (n + 1 : ℝ) := by
  induction n with
  | zero =>
    have hh := T.expected_inductiveMean_step h v hbar hen 0
    simpa using hh
  | succ n ih =>
    calc
      _ ≤ (1 - 1 / ((n + 1 : ℕ) + 1 : ℝ)) ^ 2 *
          (𝔼 a : Fin (n + 1) → ι, T.normSq (T.inductiveMean h (n + 1) (v ∘ a))) +
          (1 / ((n + 1 : ℕ) + 1 : ℝ)) ^ 2 :=
        T.expected_inductiveMean_step h v hbar hen (n + 1)
      _ ≤ (1 - 1 / ((n + 1 : ℕ) + 1 : ℝ)) ^ 2 * (1 / (n + 1 : ℝ)) +
          (1 / ((n + 1 : ℕ) + 1 : ℝ)) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left ih (sq_nonneg _)) le_rfl
      _ = _ := by
        push_cast
        field_simp
        ring

end ConeData
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators

/-- A finite probability law, retaining real weights for the conditional
couplings. Uniform laws are exactly the table match distributions. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  sum_one : (∑ a, mass a) = 1

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

def expect (μ : FiniteLaw α) (f : α → ℝ) : ℝ := ∑ a, μ.mass a * f a

def uniform [Nonempty α] : FiniteLaw α where
  mass _ := 1 / (Fintype.card α : ℝ)
  nonneg _ := by positivity
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hh : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp [hh]

theorem expect_uniform [Nonempty α] (f : α → ℝ) :
    (uniform : FiniteLaw α).expect f = 𝔼 a, f a := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [expect, uniform, ← Finset.mul_sum]
  ring

theorem expect_const (μ : FiniteLaw α) (c : ℝ) : μ.expect (fun _ => c) = c := by
  rw [expect, ← Finset.sum_mul, μ.sum_one, one_mul]

theorem expect_add (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun a => f a + g a) = μ.expect f + μ.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun a => f a - g a) = μ.expect f - μ.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul (μ : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    μ.expect (fun a => c * f a) = c * μ.expect f := by
  simp [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expect_sum (μ : FiniteLaw α) {ι : Type*} [Fintype ι] (f : ι → α → ℝ) :
    μ.expect (fun a => ∑ i, f i a) = ∑ i, μ.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_mono (μ : FiniteLaw α) {f g : α → ℝ} (hle : ∀ a, f a ≤ g a) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hle a) (μ.nonneg a)

theorem expect_nonneg (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ μ.expect f := Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonneg a) (hf a)

def map (μ : FiniteLaw α) (f : α → β) : FiniteLaw β := by
  classical
  exact {
    mass := fun b => ∑ a, if f a = b then μ.mass a else 0
    nonneg := fun b => Finset.sum_nonneg fun a _ => by
      split
      · exact μ.nonneg a
      · exact le_rfl
    sum_one := by rw [Finset.sum_comm]; simpa using μ.sum_one }

theorem expect_map (μ : FiniteLaw α) (f : α → β) (g : β → ℝ) :
    (μ.map f).expect g = μ.expect (g ∘ f) := by
  classical
  unfold expect map
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

def totalVariation (μ ν : FiniteLaw α) : ℝ := (∑ a, |μ.mass a - ν.mass a|) / 2

theorem totalVariation_nonneg (μ ν : FiniteLaw α) : 0 ≤ μ.totalVariation ν := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

/-- Exact finite total-variation comparison, with the constant 2B. -/
theorem expect_sub_bound (μ ν : FiniteLaw α) (f : α → ℝ) {B : ℝ}
    (hB : ∀ a, |f a| ≤ B) :
    |μ.expect f - ν.expect f| ≤ 2 * B * μ.totalVariation ν := by
  have he : μ.expect f - ν.expect f = ∑ a, (μ.mass a - ν.mass a) * f a := by
    simp [expect, sub_mul, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ a, |(μ.mass a - ν.mass a) * f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |μ.mass a - ν.mass a| * B := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB a) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold totalVariation; ring

/-- Finite-probability Cauchy--Schwarz in the scalar form needed for cone
norms under arbitrary conditional couplings. -/
theorem expect_le_sqrt (μ : FiniteLaw α) (f : α → ℝ) :
    μ.expect f ≤ Real.sqrt (μ.expect (fun a => f a ^ 2)) := by
  have hn := μ.expect_nonneg (fun a => sq_nonneg (f a - μ.expect f))
  have he : μ.expect (fun a => (f a - μ.expect f) ^ 2) =
      μ.expect (fun a => f a ^ 2) - μ.expect f ^ 2 := by
    simp_rw [sub_sq, show ∀ a, 2 * f a * μ.expect f = (2 * μ.expect f) * f a by intro a; ring]
    rw [μ.expect_add, μ.expect_sub, μ.expect_mul, μ.expect_const]
    ring
  rw [he] at hn
  have hpos := μ.expect_nonneg (fun a => sq_nonneg (f a))
  have hs := Real.sq_sqrt hpos
  have hs' := Real.sqrt_nonneg (μ.expect (fun a => f a ^ 2))
  nlinarith

end FiniteLaw
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

end OAI
