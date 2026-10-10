import Mathlib
import OAI.MathematicalPhysics.BFSS.PotentialSquares
import OAI.MathematicalPhysics.BFSS.ColorLie
import OAI.MathematicalPhysics.BFSS.NormalCocycle

namespace OAI

/-! Massive zero relations and positive normal quadratic forms. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset
variable {N : ℕ} (M : BFSSQuantum.AlgebraData N)

def spatialColor (x : Boson N) (i : SpaceIndex) : ColorVector N :=
  WithLp.toLp 2 (fun A => x (i,A))

lemma spatialColor_add (x z : Boson N) (i : SpaceIndex) :
    spatialColor (x+z) i = spatialColor x i + spatialColor z i := rfl
lemma spatialColor_smul (r : ℝ) (x : Boson N) (i : SpaceIndex) :
    spatialColor (r • x) i = r • spatialColor x i := rfl

lemma colorEmbed_normSq (a : ColorVector N) :
    BFSS.hsNormSq (M.colorEmbed a) = ‖a‖^2 := by
  rw [show M.colorEmbed a = M.colorCombination a from rfl, M.colorCombination_normSq,
    EuclideanSpace.real_norm_sq_eq]

lemma colorEmbed_spatial (x : Boson N) (i : SpaceIndex) :
    M.colorEmbed (spatialColor x i) = (M.matrixConfiguration x i).val := rfl

def ZeroRelations (q : Boson N) : Prop :=
  M.colorLie (spatialColor q 0) (spatialColor q 1) = (2:ℝ) • spatialColor q 2 ∧
  M.colorLie (spatialColor q 1) (spatialColor q 2) = (2:ℝ) • spatialColor q 0 ∧
  M.colorLie (spatialColor q 2) (spatialColor q 0) = (2:ℝ) • spatialColor q 1 ∧
  ∀ d : SpaceIndex, 3 ≤ d.val → spatialColor q d = 0

lemma residual_normSq (q : Boson N) (i j k : SpaceIndex) :
    BFSS.hsNormSq (BFSS.realBracket (M.matrixConfiguration q i).val
      (M.matrixConfiguration q j).val - (2:ℂ) • (M.matrixConfiguration q k).val) =
    ‖M.colorLie (spatialColor q i) (spatialColor q j) - (2:ℝ) • spatialColor q k‖^2 := by
  rw [←M.colorEmbed_normSq]
  simp only [map_sub,map_smul,M.colorEmbed_lie,M.colorEmbed_spatial]
  rfl

theorem potential_zero_relations (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0) : M.ZeroRelations q := by
  rw [M.deformedBosonicPotential_matrix] at hq
  obtain ⟨_,h01,h12,h20,ht⟩ := BFSS.massivePotential_bounds (M.matrixConfiguration q)
  rw [hq,mul_zero,M.residual_normSq] at h01 h12 h20
  have hz {v : ColorVector N} (h : ‖v‖^2 ≤ 0) : v = 0 := by
    have : ‖v‖ = 0 := by nlinarith [sq_nonneg ‖v‖]
    exact norm_eq_zero.mp this
  refine ⟨sub_eq_zero.mp (hz h01),sub_eq_zero.mp (hz h12),sub_eq_zero.mp (hz h20),?_⟩
  intro d hd
  have hh := ht d hd
  rw [hq,mul_zero,←M.colorEmbed_spatial,M.colorEmbed_normSq] at hh
  exact hz hh

def bracketLinearization (q z : Boson N) (i j : SpaceIndex) : ColorVector N :=
  M.colorLie (spatialColor q i) (spatialColor z j) +
    M.colorLie (spatialColor z i) (spatialColor q j)

def cyclicLinearization (q z : Boson N) (i j k : SpaceIndex) : ColorVector N :=
  M.bracketLinearization q z i j - (2:ℝ) • spatialColor z k

def normalQuadratic (q z : Boson N) : ℝ :=
  (‖M.cyclicLinearization q z 0 1 2‖^2 +
   ‖M.cyclicLinearization q z 1 2 0‖^2 +
   ‖M.cyclicLinearization q z 2 0 1‖^2 +
   (∑ i : SpaceIndex, ∑ j : SpaceIndex,
     if i < j ∧ 3 ≤ j.val then ‖M.bracketLinearization q z i j‖^2 else 0) +
   (∑ d : SpaceIndex, if 3 ≤ d.val then ‖spatialColor z d‖^2 else 0)) / 2

lemma normalQuadratic_nonneg (q z : Boson N) : 0 ≤ M.normalQuadratic q z := by
  unfold normalQuadratic
  positivity

lemma normalQuadratic_zero_components (q z : Boson N)
    (hz : M.normalQuadratic q z = 0) :
    M.cyclicLinearization q z 0 1 2 = 0 ∧
    M.cyclicLinearization q z 1 2 0 = 0 ∧
    M.cyclicLinearization q z 2 0 1 = 0 ∧
    (∀ d : SpaceIndex, 3 ≤ d.val → spatialColor z d = 0) := by
  have hs : 0 ≤ (∑ i : SpaceIndex, ∑ j : SpaceIndex,
      if i < j ∧ 3 ≤ j.val then ‖M.bracketLinearization q z i j‖^2 else 0) := by positivity
  have ht : 0 ≤ (∑ d : SpaceIndex, if 3 ≤ d.val then ‖spatialColor z d‖^2 else 0) := by positivity
  have h1 := sq_nonneg ‖M.cyclicLinearization q z 0 1 2‖
  have h2 := sq_nonneg ‖M.cyclicLinearization q z 1 2 0‖
  have h3 := sq_nonneg ‖M.cyclicLinearization q z 2 0 1‖
  unfold normalQuadratic at hz
  have ha : ‖M.cyclicLinearization q z 0 1 2‖ = 0 := by nlinarith
  have hb : ‖M.cyclicLinearization q z 1 2 0‖ = 0 := by nlinarith
  have hc : ‖M.cyclicLinearization q z 2 0 1‖ = 0 := by nlinarith
  refine ⟨norm_eq_zero.mp ha,norm_eq_zero.mp hb,norm_eq_zero.mp hc,?_⟩
  intro d hd
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun d : SpaceIndex => if 3 ≤ d.val then ‖spatialColor z d‖^2 else 0)
    (fun i _ => by positivity) (Finset.mem_univ d)
  rw [ite_eq_left hd] at hh
  have h0 : ‖spatialColor z d‖ = 0 := by nlinarith [sq_nonneg ‖spatialColor z d‖]
  exact norm_eq_zero.mp h0

def gaugeDivergence (q z : Boson N) : ColorVector N :=
  ∑ i : SpaceIndex, M.colorAd (spatialColor q i) (spatialColor z i)

lemma colorLie_zero_left (b : ColorVector N) : M.colorLie 0 b = 0 := by
  have h := M.colorLie_smul_left 0 (0:ColorVector N) b
  simpa only [zero_smul] using h
lemma colorLie_zero_right (a : ColorVector N) : M.colorLie a 0 = 0 := by
  have h := M.colorLie_smul_right 0 a (0:ColorVector N)
  simpa only [zero_smul] using h

lemma gaugeDivergence_first_three (q z : Boson N) (hq : M.ZeroRelations q) :
    M.gaugeDivergence q z =
      M.colorAd (spatialColor q 0) (spatialColor z 0) +
      M.colorAd (spatialColor q 1) (spatialColor z 1) +
      M.colorAd (spatialColor q 2) (spatialColor z 2) := by
  have ht (d : SpaceIndex) (hd : 3 ≤ d.val) :
      M.colorAd (spatialColor q d) (spatialColor z d) = 0 := by
    change M.colorLie (spatialColor q d) (spatialColor z d) = 0
    rw [hq.2.2.2 d hd, M.colorLie_zero_left]
  unfold gaugeDivergence
  simp only [Fin.sum_univ_succ]
  have h3 := ht 3 (by decide)
  have h4 := ht 4 (by decide)
  have h5 := ht 5 (by decide)
  have h6 := ht 6 (by decide)
  have h7 := ht 7 (by decide)
  have h8 := ht 8 (by decide)
  change M.colorAd (spatialColor q 0) (spatialColor z 0) +
    (M.colorAd (spatialColor q 1) (spatialColor z 1) +
    (M.colorAd (spatialColor q 2) (spatialColor z 2) +
    (M.colorAd (spatialColor q 3) (spatialColor z 3) +
    (M.colorAd (spatialColor q 4) (spatialColor z 4) +
    (M.colorAd (spatialColor q 5) (spatialColor z 5) +
    (M.colorAd (spatialColor q 6) (spatialColor z 6) +
    (M.colorAd (spatialColor q 7) (spatialColor z 7) +
    (M.colorAd (spatialColor q 8) (spatialColor z 8) + 0)))))))) = _
  simp only [h3,h4,h5,h6,h7,h8,add_zero]
  abel

theorem normalQuadratic_zero_of_normal (q z : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0)
    (hperp : M.gaugeDivergence q z = 0)
    (hz : M.normalQuadratic q z = 0) : z = 0 := by
  have hrel := M.potential_zero_relations q hq
  obtain ⟨h01,h12,h20,ht⟩ := M.normalQuadratic_zero_components q z hz
  have hcyc (i j k : SpaceIndex) (hh : M.cyclicLinearization q z i j k = 0) :
      M.colorAd (spatialColor q i) (spatialColor z j) -
      M.colorAd (spatialColor q j) (spatialColor z i) = (2:ℝ) • spatialColor z k := by
    unfold cyclicLinearization bracketLinearization at hh
    rw [M.colorLie_swap (spatialColor z i) (spatialColor q j)] at hh
    exact sub_eq_zero.mp hh
  have hcomm (i j k : SpaceIndex)
      (hh : M.colorLie (spatialColor q i) (spatialColor q j) = (2:ℝ) • spatialColor q k)
      (w : ColorVector N) :
      M.colorAd (spatialColor q i) (M.colorAd (spatialColor q j) w) -
      M.colorAd (spatialColor q j) (M.colorAd (spatialColor q i) w) =
      (2:ℝ) • M.colorAd (spatialColor q k) w := by
    rw [M.colorAd_commutator,hh]
    exact M.colorLie_smul_left 2 _ _
  rw [M.gaugeDivergence_first_three q z hrel] at hperp
  obtain ⟨ha,hb,hc⟩ := BFSSNormal.normal_cocycle_zero
    (M.colorAd (spatialColor q 0)) (M.colorAd (spatialColor q 1)) (M.colorAd (spatialColor q 2))
    (M.colorAd_skew _) (M.colorAd_skew _) (M.colorAd_skew _)
    (hcomm 0 1 2 hrel.1) (hcomm 1 2 0 hrel.2.1) (hcomm 2 0 1 hrel.2.2.1)
    (spatialColor z 0) (spatialColor z 1) (spatialColor z 2)
    (hcyc 0 1 2 h01) (hcyc 1 2 0 h12) (hcyc 2 0 1 h20) hperp
  ext p
  obtain ⟨i,A⟩ := p
  have hi : spatialColor z i = 0 := by
    by_cases hid : 3 ≤ i.val
    · exact ht i hid
    · have : i = 0 ∨ i = 1 ∨ i = 2 := by
        simp only [Fin.ext_iff]; omega
      rcases this with rfl|rfl|rfl
      · exact ha
      · exact hb
      · exact hc
  exact congrArg (fun a : ColorVector N => a A) hi
end
end BFSSQuantum.AlgebraData
namespace BFSSNormal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma positive_quadratic_lower (Q : E → ℝ) (hcont : Continuous Q)
    (hsmul : ∀ r x, Q (r • x) = r^2 * Q x)
    (hpos : ∀ x, x ≠ 0 → 0 < Q x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖^2 ≤ Q x := by
  have hzero : Q 0 = 0 := by
    simpa only [zero_smul,zero_pow (by decide : 2 ≠ 0),zero_mul]
      using (hsmul 0 (0:E))
  rcases subsingleton_or_nontrivial E with hs|hn
  · let := hs
    refine ⟨1,zero_lt_one,?_⟩
    intro x
    rw [Subsingleton.elim x 0,hzero,norm_zero]
    norm_num
  · let := hn
    obtain ⟨a,ha,hmin⟩ := (isCompact_sphere (0:E) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
    have ha_norm : ‖a‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using ha
    have ha_ne : a ≠ 0 := by intro h; simp only [h,norm_zero] at ha_norm; exact zero_ne_one ha_norm
    refine ⟨Q a,hpos a ha_ne,?_⟩
    intro x
    by_cases hx : x = 0
    · rw [hx,hzero,norm_zero]; norm_num
    let y := ‖x‖⁻¹ • x
    have hy : y ∈ Metric.sphere (0:E) 1 := by
      rw [Metric.mem_sphere,dist_zero_right]
      dsimp [y]
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg x)]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
    have he : x = ‖x‖ • y := by
      dsimp [y]
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]
    calc
      Q a * ‖x‖^2 ≤ Q y * ‖x‖^2 := mul_le_mul_of_nonneg_right (hmin hy) (sq_nonneg _)
      _ = Q (‖x‖ • y) := by rw [hsmul ‖x‖ y, mul_comm]
      _ = Q x := congrArg Q he.symm
end
end BFSSNormal

end OAI
