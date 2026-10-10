import Mathlib
import OAI.MathematicalPhysics.BFSS.NormalPotential

namespace OAI

/-! Gauge tangent slices, normal coercivity and Taylor squares. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset
variable {N : ℕ} (M : BFSSQuantum.AlgebraData N)

def spatialColorMap (i : SpaceIndex) : Boson N →ₗ[ℝ] ColorVector N where
  toFun x := spatialColor x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def gaugeTangent (q : Boson N) : ColorVector N →ₗ[ℝ] Boson N where
  toFun w := WithLp.toLp 2 (fun p => M.colorLie w (spatialColor q p.1) p.2)
  map_add' w v := by
    ext p
    exact congrArg (fun a : ColorVector N => a p.2) (M.colorLie_add_left w v (spatialColor q p.1))
  map_smul' r w := by
    ext p
    exact congrArg (fun a : ColorVector N => a p.2) (M.colorLie_smul_left r w (spatialColor q p.1))

def normalSlice (q : Boson N) : Submodule ℝ (Boson N) :=
  (LinearMap.range (M.gaugeTangent q))ᗮ

lemma spatialColor_gaugeTangent (q : Boson N) (w : ColorVector N) (i : SpaceIndex) :
    spatialColor (M.gaugeTangent q w) i = M.colorLie w (spatialColor q i) := rfl

lemma spatialColor_inner (x z : Boson N) :
    inner ℝ x z = ∑ i : SpaceIndex, inner ℝ (spatialColor x i) (spatialColor z i) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type]
  rfl

lemma gaugeTangent_pairing (q z : Boson N) (w : ColorVector N) :
    inner ℝ z (M.gaugeTangent q w) = inner ℝ (M.gaugeDivergence q z) w := by
  rw [spatialColor_inner]
  simp only [gaugeDivergence,sum_inner,spatialColor_gaugeTangent]
  apply Finset.sum_congr rfl
  intro i hi
  rw [M.colorLie_swap w (spatialColor q i),inner_neg_right]
  exact (M.colorAd_skew _ _ _).symm

lemma mem_normalSlice_iff (q z : Boson N) :
    z ∈ M.normalSlice q ↔ M.gaugeDivergence q z = 0 := by
  rw [normalSlice,Submodule.mem_orthogonal']
  constructor
  · intro hz
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [←M.gaugeTangent_pairing]
    exact hz _ ⟨M.gaugeDivergence q z,rfl⟩
  · intro hz u hu
    obtain ⟨w,rfl⟩ := hu
    rw [M.gaugeTangent_pairing,hz,inner_zero_left]

lemma bracketLinearization_eq (q z : Boson N) (i j : SpaceIndex) :
    M.bracketLinearization q z i j =
      M.colorAd (spatialColor q i) (spatialColor z j) -
      M.colorAd (spatialColor q j) (spatialColor z i) := by
  unfold bracketLinearization
  rw [M.colorLie_swap (spatialColor z i) (spatialColor q j)]
  rfl

def bracketLinearizationMap (q : Boson N) (i j : SpaceIndex) : Boson N →ₗ[ℝ] ColorVector N :=
  (M.colorAd (spatialColor q i)).comp (spatialColorMap j) -
    (M.colorAd (spatialColor q j)).comp (spatialColorMap i)

lemma bracketLinearizationMap_apply (q z : Boson N) (i j : SpaceIndex) :
    M.bracketLinearizationMap q i j z = M.bracketLinearization q z i j :=
  (M.bracketLinearization_eq q z i j).symm

def cyclicLinearizationMap (q : Boson N) (i j k : SpaceIndex) : Boson N →ₗ[ℝ] ColorVector N :=
  M.bracketLinearizationMap q i j - (2:ℝ) • spatialColorMap k

lemma cyclicLinearizationMap_apply (q z : Boson N) (i j k : SpaceIndex) :
    M.cyclicLinearizationMap q i j k z = M.cyclicLinearization q z i j k := by
  change M.bracketLinearizationMap q i j z - (2:ℝ) • spatialColor z k = _
  rw [M.bracketLinearizationMap_apply]
  rfl

lemma normalQuadratic_continuous (q : Boson N) : Continuous (M.normalQuadratic q) := by
  unfold normalQuadratic
  simp_rw [←M.cyclicLinearizationMap_apply, ←M.bracketLinearizationMap_apply,
    show ∀ z i, spatialColor z i = spatialColorMap i z from fun _ _ => rfl]
  have hc (i j k : SpaceIndex) : Continuous (fun z => ‖M.cyclicLinearizationMap q i j k z‖^2) :=
    (M.cyclicLinearizationMap q i j k).continuous_of_finiteDimensional.norm.pow 2
  have hb : Continuous (fun z => ∑ i : SpaceIndex, ∑ j : SpaceIndex,
      if i < j ∧ 3 ≤ j.val then ‖M.bracketLinearizationMap q i j z‖^2 else 0) := by
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
      split_ifs
      · exact (M.bracketLinearizationMap q i j).continuous_of_finiteDimensional.norm.pow 2
      · exact continuous_const
  have hs : Continuous (fun z : Boson N => ∑ d : SpaceIndex,
      if 3 ≤ d.val then ‖spatialColorMap d z‖^2 else 0) := by
    exact continuous_finsetSum _ fun d _ => by
      split_ifs
      · exact (spatialColorMap d).continuous_of_finiteDimensional.norm.pow 2
      · exact continuous_const
  exact (((((hc 0 1 2).add (hc 1 2 0)).add (hc 2 0 1)).add hb).add hs).div_const 2

lemma normalQuadratic_smul (q z : Boson N) (r : ℝ) :
    M.normalQuadratic q (r • z) = r^2 * M.normalQuadratic q z := by
  unfold normalQuadratic
  simp_rw [←M.cyclicLinearizationMap_apply, ←M.bracketLinearizationMap_apply]
  simp only [map_smul,spatialColor_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hif (P : Prop) [Decidable P] (a : ℝ) :
      (if P then r^2*a else 0) = r^2 * (if P then a else 0) := by split_ifs <;> simp
  simp_rw [hif]
  simp only [←Finset.mul_sum]
  ring

theorem normalQuadratic_coercive (q : Boson N) (hq : M.deformedBosonicPotential 1 1 q = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : Boson N, z ∈ M.normalSlice q →
      c * ‖z‖^2 ≤ M.normalQuadratic q z := by
  obtain ⟨c,hc,hbound⟩ := BFSSNormal.positive_quadratic_lower
    (fun z : M.normalSlice q => M.normalQuadratic q z)
    ((M.normalQuadratic_continuous q).comp continuous_subtype_val)
    (fun r z => M.normalQuadratic_smul q z r)
    (by
      intro z hz
      have hz' : (z:Boson N) ≠ 0 := by intro he; exact hz (Subtype.ext he)
      have hne : M.normalQuadratic q z ≠ 0 := by
        intro he
        exact hz' (M.normalQuadratic_zero_of_normal q z hq
          ((M.mem_normalSlice_iff q z).mp z.property) he)
      exact lt_of_le_of_ne (M.normalQuadratic_nonneg q z) hne.symm)
  exact ⟨c,hc,fun z hz => hbound ⟨z,hz⟩⟩
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset
variable {N : ℕ} (M : BFSSQuantum.AlgebraData N)

lemma colorLie_continuous : Continuous (fun p : ColorVector N × ColorVector N => M.colorLie p.1 p.2) := by
  unfold colorLie
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro A
  exact continuous_finsetSum _ fun B _ => continuous_finsetSum _ fun C _ =>
    ((continuous_const.mul ((EuclideanSpace.proj (𝕜 := ℝ) B).continuous.comp continuous_fst)).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) C).continuous.comp continuous_snd))

lemma spatialBracket_continuous (i j : SpaceIndex) :
    Continuous (fun x : Boson N => M.colorLie (spatialColor x i) (spatialColor x j)) :=
  M.colorLie_continuous.comp (((spatialColorMap i).continuous_of_finiteDimensional).prodMk
    ((spatialColorMap j).continuous_of_finiteDimensional))

lemma potential_color (x : Boson N) :
    M.deformedBosonicPotential 1 1 x =
    (‖M.colorLie (spatialColor x 0) (spatialColor x 1) - (2:ℝ) • spatialColor x 2‖^2 +
     ‖M.colorLie (spatialColor x 1) (spatialColor x 2) - (2:ℝ) • spatialColor x 0‖^2 +
     ‖M.colorLie (spatialColor x 2) (spatialColor x 0) - (2:ℝ) • spatialColor x 1‖^2 +
     (∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
       ‖M.colorLie (spatialColor x i) (spatialColor x j)‖^2 else 0) +
     (∑ d : SpaceIndex, if 3 ≤ d.val then ‖spatialColor x d‖^2 else 0))/2 := by
  have hc (i j k : SpaceIndex) :
      BFSS.hsNormSq (BFSS.realBracket (M.matrixConfiguration x i).val (M.matrixConfiguration x j).val -
        (2:ℝ) • (M.matrixConfiguration x k).val) =
      ‖M.colorLie (spatialColor x i) (spatialColor x j) - (2:ℝ) • spatialColor x k‖^2 := by
    have he : (2:ℝ) • (M.matrixConfiguration x k).val = (2:ℂ) • (M.matrixConfiguration x k).val := by
      ext a b
      simp [Matrix.smul_apply,Complex.real_smul]
    rw [he,M.residual_normSq]
  have hb : (∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
      BFSS.hsNormSq (BFSS.realBracket (M.matrixConfiguration x i).val (M.matrixConfiguration x j).val) else 0) =
      ∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
      ‖M.colorLie (spatialColor x i) (spatialColor x j)‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs
    · rw [←M.colorEmbed_spatial,←M.colorEmbed_spatial]
      change BFSS.hsNormSq (AlgebraData.bracket (M.colorEmbed (spatialColor x i))
        (M.colorEmbed (spatialColor x j))) = _
      rw [←M.colorEmbed_lie,M.colorEmbed_normSq]
    · rfl
  have hs : (∑ d : SpaceIndex, if 3 ≤ d.val then BFSS.hsNormSq (M.matrixConfiguration x d).val else 0) =
      ∑ d : SpaceIndex, if 3 ≤ d.val then ‖spatialColor x d‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs
    · rw [←M.colorEmbed_spatial,M.colorEmbed_normSq]
    · rfl
  rw [M.deformedBosonicPotential_matrix, BFSS.massivePotential]
  simp only [Complex.ofReal_one,one_smul,mul_one,one_pow,one_mul,hc,hb,hs]

lemma cyclicResidual_continuous (i j k : SpaceIndex) : Continuous (fun x : Boson N =>
      ‖M.colorLie (spatialColor x i) (spatialColor x j) - (2:ℝ) • spatialColor x k‖^2) := by
  have hk : Continuous (fun x : Boson N => spatialColor x k) :=
    (spatialColorMap k).continuous_of_finiteDimensional
  have hm : Continuous (fun x : Boson N => (2:ℝ) • spatialColor x k) :=
    (continuous_const : Continuous (fun _ : Boson N => (2:ℝ))).smul hk
  have hr : Continuous (fun x : Boson N =>
      M.colorLie (spatialColor x i) (spatialColor x j) - (2:ℝ) • spatialColor x k) :=
    (M.spatialBracket_continuous i j).sub hm
  exact hr.norm.pow 2

lemma potential_continuous : Continuous (M.deformedBosonicPotential 1 1) := by
  have hc := M.cyclicResidual_continuous
  have hb : Continuous (fun x : Boson N => ∑ i : SpaceIndex, ∑ j : SpaceIndex,
      if i < j ∧ 3 ≤ j.val then ‖M.colorLie (spatialColor x i) (spatialColor x j)‖^2 else 0) := by
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
      split_ifs
      · exact (M.spatialBracket_continuous i j).norm.pow 2
      · exact continuous_const
  have hs : Continuous (fun x : Boson N => ∑ d : SpaceIndex,
      if 3 ≤ d.val then ‖spatialColor x d‖^2 else 0) := by
    exact continuous_finsetSum _ fun d _ => by
      split_ifs
      · exact (spatialColorMap d).continuous_of_finiteDimensional.norm.pow 2
      · exact continuous_const
  have ht := (((((hc 0 1 2).add (hc 1 2 0)).add (hc 2 0 1)).add hb).add hs).div_const 2
  exact ht.congr (fun x => (M.potential_color x).symm)

lemma potential_nonneg (x : Boson N) : 0 ≤ M.deformedBosonicPotential 1 1 x := by
  rw [M.potential_color]
  positivity

lemma potential_zero_of_relations (q : Boson N) (hq : M.ZeroRelations q) :
    M.deformedBosonicPotential 1 1 q = 0 := by
  rw [M.potential_color,hq.1,hq.2.1,hq.2.2.1]
  simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add]
  have hb : (∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
      ‖M.colorLie (spatialColor q i) (spatialColor q j)‖^2 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs with hh
    · rw [hq.2.2.2 j hh.2,M.colorLie_zero_right,norm_zero]; norm_num
    · rfl
  have hs : (∑ d : SpaceIndex, if 3 ≤ d.val then ‖spatialColor q d‖^2 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    split_ifs with hh
    · rw [hq.2.2.2 d hh,norm_zero]; norm_num
    · rfl
  rw [hb,hs]; norm_num

lemma bracket_taylor (q z : Boson N) (i j : SpaceIndex) :
    M.colorLie (spatialColor (q+z) i) (spatialColor (q+z) j) =
    M.colorLie (spatialColor q i) (spatialColor q j) + M.bracketLinearization q z i j +
      M.colorLie (spatialColor z i) (spatialColor z j) := by
  simp only [spatialColor_add,M.colorLie_add_left,M.colorLie_add_right,bracketLinearization]
  abel

lemma cyclic_taylor (q z : Boson N) (i j k : SpaceIndex)
    (hq : M.colorLie (spatialColor q i) (spatialColor q j) = (2:ℝ) • spatialColor q k) :
    M.colorLie (spatialColor (q+z) i) (spatialColor (q+z) j) - (2:ℝ) • spatialColor (q+z) k =
      M.cyclicLinearization q z i j k + M.colorLie (spatialColor z i) (spatialColor z j) := by
  rw [M.bracket_taylor,hq,spatialColor_add,smul_add]
  unfold cyclicLinearization
  abel

theorem potential_taylor_squares (q z : Boson N) (hq : M.deformedBosonicPotential 1 1 q = 0) :
    M.deformedBosonicPotential 1 1 (q+z) =
    (‖M.cyclicLinearization q z 0 1 2 + M.colorLie (spatialColor z 0) (spatialColor z 1)‖^2 +
     ‖M.cyclicLinearization q z 1 2 0 + M.colorLie (spatialColor z 1) (spatialColor z 2)‖^2 +
     ‖M.cyclicLinearization q z 2 0 1 + M.colorLie (spatialColor z 2) (spatialColor z 0)‖^2 +
     (∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
       ‖M.bracketLinearization q z i j + M.colorLie (spatialColor z i) (spatialColor z j)‖^2 else 0) +
     (∑ d : SpaceIndex, if 3 ≤ d.val then ‖spatialColor z d‖^2 else 0))/2 := by
  have hr := M.potential_zero_relations q hq
  have hb : (∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
      ‖M.colorLie (spatialColor (q+z) i) (spatialColor (q+z) j)‖^2 else 0) =
      ∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
      ‖M.bracketLinearization q z i j + M.colorLie (spatialColor z i) (spatialColor z j)‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with hh
    · rw [M.bracket_taylor,hr.2.2.2 j hh.2,M.colorLie_zero_right,zero_add]
    · rfl
  have hs : (∑ d : SpaceIndex, if 3 ≤ d.val then ‖spatialColor (q+z) d‖^2 else 0) =
      ∑ d : SpaceIndex, if 3 ≤ d.val then ‖spatialColor z d‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs with hh
    · rw [spatialColor_add,hr.2.2.2 d hh,zero_add]
    · rfl
  rw [M.potential_color, M.cyclic_taylor q z 0 1 2 hr.1,
    M.cyclic_taylor q z 1 2 0 hr.2.1,M.cyclic_taylor q z 2 0 1 hr.2.2.1,hb,hs]

end
end BFSSQuantum.AlgebraData

end OAI
