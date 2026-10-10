import OAI.Combinatorics.SparsestCut.GaussianTools

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.FiniteNets

lemma euclidean_norm_le_sum_abs {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ ∑ i, |x i| := by
  classical
  have heq : x = ∑ i : Fin n, (PiLp.single 2 i (x i) : EuclideanSpace ℝ (Fin n)) := by
    ext j
    simp
  calc
    _ = ‖∑ i : Fin n, (PiLp.single 2 i (x i) : EuclideanSpace ℝ (Fin n))‖ := congrArg norm heq
    _ ≤ ∑ i : Fin n, ‖(PiLp.single 2 i (x i) : EuclideanSpace ℝ (Fin n))‖ := norm_sum_le _ _
    _ = _ := by simp [PiLp.norm_single, Real.norm_eq_abs]

lemma floor_coordinate_bound {n K : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ (K : ℝ) * δ) (i : Fin n) :
    ⌊x i / δ⌋ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
  have hcoord : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
  have hi : |x i| ≤ (K : ℝ) * δ := hcoord.trans hx
  rw [Finset.mem_Icc]
  constructor
  · apply Int.le_floor.mpr
    push_cast
    apply (le_div_iff₀ hδ).mpr
    linarith [neg_abs_le (x i)]
  · have hh : x i / δ ≤ (K : ℝ) := (div_le_iff₀ hδ).mpr ((le_abs_self _).trans hi)
    have h := Int.floor_mono hh
    simpa using h

lemma same_floor_distance {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {x y : EuclideanSpace ℝ (Fin n)} (hxy : ∀ i, ⌊x i / δ⌋ = ⌊y i / δ⌋) :
    ‖x - y‖ ≤ (n : ℝ) * δ := by
  have hc (i : Fin n) : |x i - y i| ≤ δ := by
    have hx1 := Int.floor_le (x i / δ)
    have hx2 := Int.lt_floor_add_one (x i / δ)
    have hy1 := Int.floor_le (y i / δ)
    have hy2 := Int.lt_floor_add_one (y i / δ)
    rw [hxy i] at hx1 hx2
    apply abs_le.mpr
    constructor
    · have hh : -1 ≤ (x i - y i) / δ := by rw [sub_div]; linarith
      have := (le_div_iff₀ hδ).mp hh
      linarith
    · have hh : (x i - y i) / δ ≤ 1 := by rw [sub_div]; linarith
      have := (div_le_iff₀ hδ).mp hh
      linarith
  calc
    ‖x-y‖ ≤ ∑ i, |(x-y) i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _ : Fin n, δ := Finset.sum_le_sum (fun i _ => hc i)
    _ = _ := by simp

theorem exists_coordinate_net {n K : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : ∀ x ∈ A, ‖x‖ ≤ (K : ℝ) * δ) :
    ∃ V : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ v ∈ V, v ∈ A) ∧ V.card ≤ (2*K+1)^n ∧
      ∀ x ∈ A, ∃ v ∈ V, ‖x-v‖ ≤ (n : ℝ)*δ := by
  classical
  let G := Fin n → ↥(Finset.Icc (-(K : ℤ)) (K : ℤ))
  let represented : G → Prop := fun g => ∃ x ∈ A, ∀ i, ⌊x i / δ⌋ = (g i).val
  let point : G → EuclideanSpace ℝ (Fin n) := fun g =>
    if h : represented g then h.choose else 0
  have hpoint (g : G) (hg : represented g) :
      point g ∈ A ∧ ∀ i, ⌊point g i / δ⌋ = (g i).val := by
    simpa [point, hg] using hg.choose_spec
  let V := (Finset.univ.filter represented).image point
  refine ⟨V, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
    exact (hpoint g (Finset.mem_filter.mp hg).2).1
  · calc
      V.card ≤ (Finset.univ.filter represented).card := Finset.card_image_le
      _ ≤ Fintype.card G := (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
      _ = (2*K+1)^n := by
        simp only [G, Fintype.card_fun, Fintype.card_coe, Int.card_Icc, Fintype.card_fin]
        congr 1
        omega
  · intro x hx
    let g : G := fun i => ⟨⌊x i / δ⌋, floor_coordinate_bound hδ (hA x hx) i⟩
    have hg : represented g := ⟨x, hx, fun _ => rfl⟩
    refine ⟨point g, Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩, rfl⟩, ?_⟩
    exact same_floor_distance hδ (fun i => ((hpoint g hg).2 i).symm)

lemma sphere_net_norm_bound {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {V : Finset E} {ρ B : ℝ}
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ V, ‖x-v‖ ≤ ρ)
    {z : E} (hz : ∀ v ∈ V, |inner ℝ z v| ≤ B) (hB : 0 ≤ B) :
    (1-ρ)*‖z‖ ≤ B := by
  by_cases hzero : z = 0
  · simpa [hzero] using hB
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hzero
  let x := ‖z‖⁻¹ • z
  have hx : ‖x‖ = 1 := by simp [x, norm_smul, hn.ne']
  obtain ⟨v, hv, hdist⟩ := hnet x hx
  have hinner : inner ℝ z x = ‖z‖ := by
    simp [x, inner_smul_right, sq, hn.ne']
  have heq : inner ℝ z x = inner ℝ z v + inner ℝ z (x-v) := by
    rw [inner_sub_right]
    ring
  have hbound : ‖z‖ ≤ B + ‖z‖ * ρ := by
    calc
      ‖z‖ = |inner ℝ z x| := by rw [hinner, abs_of_nonneg (norm_nonneg _)]
      _ ≤ |inner ℝ z v| + |inner ℝ z (x-v)| := by rw [heq]; exact abs_add_le _ _
      _ ≤ B + ‖z‖ * ρ := add_le_add (hz v hv)
        ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hdist (norm_nonneg _)))
  nlinarith

end UniformSparsestCut.FiniteNets

end

end OAI
