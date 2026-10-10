import Mathlib
import OAI.MathematicalPhysics.BFSS.NormalLinearization

namespace OAI

/-! Uniform Taylor remainders and compact massive zero sets. -/

namespace BFSSNormal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma quartic_upper (Q : E → ℝ) (hcont : Continuous Q)
    (hsmul : ∀ r x, Q (r • x) = r^4 * Q x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, Q x ≤ C * ‖x‖^4 := by
  have hzero : Q 0 = 0 := by
    simpa only [zero_smul,zero_pow (by decide : 4 ≠ 0),zero_mul] using (hsmul 0 (0:E))
  rcases subsingleton_or_nontrivial E with hs|hn
  · let := hs
    refine ⟨1,zero_lt_one,?_⟩
    intro x
    rw [Subsingleton.elim x 0,hzero,norm_zero]
    norm_num
  · let := hn
    obtain ⟨a,ha,hmax⟩ := (isCompact_sphere (0:E) 1).exists_isMaxOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
    refine ⟨max 1 (Q a),lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
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
      Q x = ‖x‖^4 * Q y := by conv_lhs => rw [he]; exact hsmul ‖x‖ y
      _ ≤ ‖x‖^4 * max 1 (Q a) := mul_le_mul_of_nonneg_left
        ((hmax hy).trans (le_max_right _ _)) (by positivity)
      _ = max 1 (Q a) * ‖x‖^4 := mul_comm _ _

lemma norm_add_square_lower {F : Type*} [NormedAddCommGroup F] (a b : F) :
    ‖a‖^2 / 2 - ‖b‖^2 ≤ ‖a+b‖^2 := by
  have ht : ‖a‖ ≤ ‖a+b‖+‖b‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (a+b) b
  have hs := sq_le_sq₀ (norm_nonneg a) (by positivity : 0 ≤ ‖a+b‖+‖b‖) |>.mpr ht
  nlinarith [sq_nonneg (‖a+b‖-‖b‖)]
lemma sum_square_lower {F ι : Type*} [NormedAddCommGroup F] [Fintype ι]
    (P : ι → Prop) [DecidablePred P] (a b : ι → F) :
    (∑ i, if P i then ‖a i‖^2 else 0)/2 - (∑ i, if P i then ‖b i‖^2 else 0) ≤
      ∑ i, if P i then ‖a i+b i‖^2 else 0 := by
  have he (i : ι) : (if P i then ‖a i‖^2 else 0)/2 - (if P i then ‖b i‖^2 else 0) ≤
      (if P i then ‖a i+b i‖^2 else 0) := by
    split_ifs
    · exact norm_add_square_lower _ _
    · norm_num
  simpa only [Finset.sum_sub_distrib,Finset.sum_div] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => he i)

end
end BFSSNormal

namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset
variable {N : ℕ} (M : BFSSQuantum.AlgebraData N)

def quarticRemainder (z : Boson N) : ℝ :=
  (‖M.colorLie (spatialColor z 0) (spatialColor z 1)‖^2 +
   ‖M.colorLie (spatialColor z 1) (spatialColor z 2)‖^2 +
   ‖M.colorLie (spatialColor z 2) (spatialColor z 0)‖^2 +
   (∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
      ‖M.colorLie (spatialColor z i) (spatialColor z j)‖^2 else 0))/2

lemma quarticRemainder_continuous : Continuous M.quarticRemainder := by
  have hc (i j : SpaceIndex) := (M.spatialBracket_continuous i j).norm.pow 2
  have hb : Continuous (fun x : Boson N => ∑ i : SpaceIndex, ∑ j : SpaceIndex,
      if i < j ∧ 3 ≤ j.val then ‖M.colorLie (spatialColor x i) (spatialColor x j)‖^2 else 0) := by
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
      split_ifs
      · exact hc i j
      · exact continuous_const
  exact ((((hc 0 1).add (hc 1 2)).add (hc 2 0)).add hb).div_const 2

lemma quarticRemainder_smul (r : ℝ) (z : Boson N) :
    M.quarticRemainder (r • z) = r^4 * M.quarticRemainder z := by
  have he (i j : SpaceIndex) :
      ‖M.colorLie (spatialColor (r • z) i) (spatialColor (r • z) j)‖^2 =
      r^4 * ‖M.colorLie (spatialColor z i) (spatialColor z j)‖^2 := by
    rw [spatialColor_smul,spatialColor_smul,M.colorLie_smul_left,M.colorLie_smul_right]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  unfold quarticRemainder
  simp_rw [he]
  have hi (P : Prop) [Decidable P] (a : ℝ) :
      (if P then r^4*a else 0) = r^4 * (if P then a else 0) := by split_ifs <;> simp
  simp_rw [hi]
  simp only [←Finset.mul_sum]
  ring

lemma quarticRemainder_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : Boson N,
    M.quarticRemainder z ≤ C * ‖z‖^4 :=
  BFSSNormal.quartic_upper M.quarticRemainder M.quarticRemainder_continuous
    (fun r z => M.quarticRemainder_smul r z)

theorem potential_taylor_lower (q z : Boson N) (hq : M.deformedBosonicPotential 1 1 q = 0) :
    M.normalQuadratic q z / 2 - M.quarticRemainder z ≤ M.deformedBosonicPotential 1 1 (q+z) := by
  have h01 := BFSSNormal.norm_add_square_lower (M.cyclicLinearization q z 0 1 2)
    (M.colorLie (spatialColor z 0) (spatialColor z 1))
  have h12 := BFSSNormal.norm_add_square_lower (M.cyclicLinearization q z 1 2 0)
    (M.colorLie (spatialColor z 1) (spatialColor z 2))
  have h20 := BFSSNormal.norm_add_square_lower (M.cyclicLinearization q z 2 0 1)
    (M.colorLie (spatialColor z 2) (spatialColor z 0))
  have hb0 := BFSSNormal.sum_square_lower
    (fun p : SpaceIndex × SpaceIndex => p.1 < p.2 ∧ 3 ≤ p.2.val)
    (fun p => M.bracketLinearization q z p.1 p.2)
    (fun p => M.colorLie (spatialColor z p.1) (spatialColor z p.2))
  simp only [Fintype.sum_prod_type] at hb0
  have hs : 0 ≤ (∑ d : SpaceIndex, if 3 ≤ d.val then ‖spatialColor z d‖^2 else 0) := by
    apply Finset.sum_nonneg
    intro d _
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  rw [M.potential_taylor_squares q z hq]
  unfold normalQuadratic quarticRemainder
  linarith
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset
variable {N : ℕ} (M : BFSSQuantum.AlgebraData N)

def massiveZeros : Set (Boson N) := {q | M.deformedBosonicPotential 1 1 q = 0}

lemma zero_mem_massiveZeros : (0 : Boson N) ∈ M.massiveZeros := by
  apply M.potential_zero_of_relations
  have hz (i : SpaceIndex) : spatialColor (0 : Boson N) i = 0 := rfl
  unfold ZeroRelations
  simp [hz,M.colorLie_zero_left]

lemma massiveZeros_isClosed : IsClosed M.massiveZeros :=
  isClosed_eq M.potential_continuous continuous_const

lemma massiveZeros_isCompact (hN : 2 ≤ N) : IsCompact M.massiveZeros := by
  obtain ⟨c,hc,R,hR⟩ := M.deformedBosonicPotential_coercive hN
  apply (isCompact_closedBall (0 : Boson N) (max R 1)).of_isClosed_subset M.massiveZeros_isClosed
  intro q hq
  rw [Metric.mem_closedBall,dist_zero_right]
  by_contra hn
  have hqn : max R 1 < ‖q‖ := lt_of_not_ge hn
  have h1 : 1 < ‖q‖ := lt_of_le_of_lt (le_max_right _ _) hqn
  have hr := hR q ((le_max_left R 1).trans hqn.le)
  change M.deformedBosonicPotential 1 1 q = 0 at hq
  rw [hq] at hr
  exact (not_lt_of_ge hr) (mul_pos hc (sq_pos_of_pos (lt_trans zero_lt_one h1)))

lemma bracketLinearization_jointContinuous (i j : SpaceIndex) :
    Continuous (fun p : Boson N × Boson N => M.bracketLinearization p.1 p.2 i j) := by
  have hf (i : SpaceIndex) : Continuous (fun p : Boson N × Boson N => spatialColor p.1 i) :=
    (spatialColorMap i).continuous_of_finiteDimensional.comp continuous_fst
  have hs (i : SpaceIndex) : Continuous (fun p : Boson N × Boson N => spatialColor p.2 i) :=
    (spatialColorMap i).continuous_of_finiteDimensional.comp continuous_snd
  exact (M.colorLie_continuous.comp ((hf i).prodMk (hs j))).add
    (M.colorLie_continuous.comp ((hs i).prodMk (hf j)))

lemma cyclicLinearization_jointContinuous (i j k : SpaceIndex) :
    Continuous (fun p : Boson N × Boson N => M.cyclicLinearization p.1 p.2 i j k) := by
  have hs : Continuous (fun p : Boson N × Boson N => spatialColor p.2 k) :=
    (spatialColorMap k).continuous_of_finiteDimensional.comp continuous_snd
  have hh : Continuous (fun p : Boson N × Boson N => (2:ℝ) • spatialColor p.2 k) :=
    (continuous_const : Continuous (fun _ : Boson N × Boson N => (2:ℝ))).smul hs
  exact (M.bracketLinearization_jointContinuous i j).sub hh

lemma normalQuadratic_jointContinuous :
    Continuous (fun p : Boson N × Boson N => M.normalQuadratic p.1 p.2) := by
  have hc (i j k : SpaceIndex) := (M.cyclicLinearization_jointContinuous i j k).norm.pow 2
  have hb : Continuous (fun p : Boson N × Boson N => ∑ i : SpaceIndex, ∑ j : SpaceIndex,
      if i < j ∧ 3 ≤ j.val then ‖M.bracketLinearization p.1 p.2 i j‖^2 else 0) := by
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
      split_ifs
      · exact (M.bracketLinearization_jointContinuous i j).norm.pow 2
      · exact continuous_const
  have hs : Continuous (fun p : Boson N × Boson N => ∑ d : SpaceIndex,
      if 3 ≤ d.val then ‖spatialColor p.2 d‖^2 else 0) := by
    exact continuous_finsetSum _ fun d _ => by
      split_ifs
      · exact ((spatialColorMap d).continuous_of_finiteDimensional.comp continuous_snd).norm.pow 2
      · exact continuous_const
  exact (((((hc 0 1 2).add (hc 1 2 0)).add (hc 2 0 1)).add hb).add hs).div_const 2

lemma gaugeDivergence_jointContinuous :
    Continuous (fun p : Boson N × Boson N => M.gaugeDivergence p.1 p.2) := by
  unfold gaugeDivergence
  apply continuous_finsetSum
  intro i _
  have hf : Continuous (fun p : Boson N × Boson N => spatialColor p.1 i) :=
    (spatialColorMap i).continuous_of_finiteDimensional.comp continuous_fst
  have hs : Continuous (fun p : Boson N × Boson N => spatialColor p.2 i) :=
    (spatialColorMap i).continuous_of_finiteDimensional.comp continuous_snd
  exact M.colorLie_continuous.comp (hf.prodMk hs)

theorem normalQuadratic_uniform_coercive (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ q ∈ M.massiveZeros, ∀ z : Boson N,
      z ∈ M.normalSlice q → c * ‖z‖^2 ≤ M.normalQuadratic q z := by
  let K : Set (Boson N × Boson N) :=
    (M.massiveZeros ×ˢ Metric.sphere 0 1) ∩ {p | M.gaugeDivergence p.1 p.2 = 0}
  have hK : IsCompact K :=
    ((M.massiveZeros_isCompact hN).prod (isCompact_sphere (0 : Boson N) 1)).inter_right
      (isClosed_eq M.gaugeDivergence_jointContinuous continuous_const)
  have hp (p : Boson N × Boson N) (hp : p ∈ K) : 0 < M.normalQuadratic p.1 p.2 := by
    have hz : p.2 ≠ 0 := by
      have hn : ‖p.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hp.1.2
      intro he
      rw [he,norm_zero] at hn
      exact zero_ne_one hn
    have he : M.normalQuadratic p.1 p.2 ≠ 0 := by
      intro hh
      exact hz (M.normalQuadratic_zero_of_normal p.1 p.2 hp.1.1 hp.2 hh)
    exact lt_of_le_of_ne (M.normalQuadratic_nonneg p.1 p.2) he.symm
  have hu : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, c ≤ M.normalQuadratic p.1 p.2 := by
    rcases Set.eq_empty_or_nonempty K with he|hn
    · refine ⟨1,zero_lt_one,?_⟩
      intro p hp
      rw [he] at hp
      exact hp.elim
    · obtain ⟨a,ha,hmin⟩ := hK.exists_isMinOn hn M.normalQuadratic_jointContinuous.continuousOn
      exact ⟨M.normalQuadratic a.1 a.2,hp a ha,fun p hp => hmin hp⟩
  obtain ⟨c,hc,hbound⟩ := hu
  refine ⟨c,hc,?_⟩
  intro q hq z hz
  by_cases hzero : z = 0
  · subst z
    have he := M.normalQuadratic_smul q (0 : Boson N) 0
    simp only [zero_smul,zero_pow (by decide : 2 ≠ 0),zero_mul] at he
    rw [he,norm_zero]
    norm_num
  let y := ‖z‖⁻¹ • z
  have hy_norm : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg z)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzero)
  have hy_normal : y ∈ M.normalSlice q := (M.normalSlice q).smul_mem _ hz
  have hy : (q,y) ∈ K := by
    refine ⟨⟨hq,?_⟩,(M.mem_normalSlice_iff q y).mp hy_normal⟩
    simpa only [Metric.mem_sphere,dist_zero_right] using hy_norm
  have he : z = ‖z‖ • y := by
    dsimp [y]
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hzero),one_smul]
  calc
    c * ‖z‖^2 ≤ M.normalQuadratic q y * ‖z‖^2 :=
      mul_le_mul_of_nonneg_right (hbound (q,y) hy) (sq_nonneg _)
    _ = M.normalQuadratic q (‖z‖ • y) := by rw [M.normalQuadratic_smul q y ‖z‖,mul_comm]
    _ = M.normalQuadratic q z := congrArg (M.normalQuadratic q) he.symm
end
end BFSSQuantum.AlgebraData

end OAI
