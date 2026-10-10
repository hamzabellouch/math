import Mathlib

namespace OAI

/-! Deletion Deterministic Repair Smallness. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open scoped Topology BigOperators

namespace MicroscopicJamming

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

 

theorem exists_orthogonal_solution {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : W →ₗ[ℝ] V) (w : W) :
    ∃ z : W, f z = f w ∧ z ∈ (LinearMap.ker f)ᗮ ∧ ‖z‖ ≤ ‖w‖ := by
  obtain ⟨u, hu, z, hz, hw⟩ :=
    (LinearMap.ker f).exists_add_mem_mem_orthogonal w
  have hfu : f u = 0 := hu
  have hinner : inner ℝ u z = 0 :=
    ((LinearMap.ker f).mem_orthogonal z).mp hz u hu
  refine ⟨z, ?_, hz, ?_⟩
  · rw [hw, map_add, hfu, zero_add]
  · have he := norm_add_sq_real u z
    rw [hinner, mul_zero, add_zero, ← hw] at he
    nlinarith [sq_nonneg ‖u‖, norm_nonneg z, norm_nonneg w]

 
def rowRestriction {m : ℕ} (L : W →L[ℝ] EuclideanSpace ℝ (Fin m))
    (T : Finset (Fin m)) : W →ₗ[ℝ] (T → ℝ) where
  toFun x i := (L x) i
  map_add' := by intro x y; ext i; simp
  map_smul' := by intro r x; ext i; simp

omit [FiniteDimensional ℝ W] in
lemma rowRestriction_mem_ker {m : ℕ} (L : W →L[ℝ] EuclideanSpace ℝ (Fin m))
    (T : Finset (Fin m)) (x : W) :
    x ∈ LinearMap.ker (rowRestriction L T) ↔ ∀ j ∈ T, (L x) j = 0 := by
  simp only [LinearMap.mem_ker, rowRestriction, LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · intro h j hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact h j j.property

omit [FiniteDimensional ℝ W] in
 
lemma card_large_rows_bound {m : ℕ} (L : W →L[ℝ] EuclideanSpace ℝ (Fin m))
    (K η : ℝ) (hK : ‖L‖ ≤ K) (hη : 0 < η)
    (x : W) (J : Finset (Fin m)) (hJ : J.Nonempty)
    (hlarge : ∀ j ∈ J, η < |(L x) j|) :
    η ^ 2 * (J.card : ℝ) < K ^ 2 * ‖x‖ ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg L).trans hK
  have hsum : ∑ _j ∈ J, η ^ 2 < ∑ j ∈ J, ((L x) j) ^ 2 := by
    apply Finset.sum_lt_sum_of_nonempty hJ
    intro j hj
    have hh := hlarge j hj
    nlinarith [sq_abs ((L x) j)]
  have hsub : ∑ j ∈ J, ((L x) j) ^ 2 ≤ ‖L x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => sq_nonneg _)
  have hop : ‖L x‖ ≤ K * ‖x‖ := (L.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hK (norm_nonneg x))
  have hop2 : ‖L x‖ ^ 2 ≤ K ^ 2 * ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (K * ‖x‖ - ‖L x‖), norm_nonneg (L x), norm_nonneg x]
  simpa [mul_comm] using hsum.trans_le (hsub.trans hop2)

 

theorem exists_slack_correction {m : ℕ}
    (L : W →L[ℝ] EuclideanSpace ℝ (Fin m)) (S : Finset (Fin m))
    (r : Fin m → ℝ) (b : ℕ) (K R η q : ℝ)
    (hK : ‖L‖ ≤ K) (hKpos : 0 < K) (hR : 0 ≤ R) (hη : 0 < η) (hq : 0 < q)
    (hqeq : q * K ^ 2 = η ^ 2)
    (hcap : q * (S.card : ℝ) + 2 * R ^ 2 ≤ q * b)
    (hr : ∀ j, j ∉ S → r j = 0)
    (hsolve : ∀ T : Finset (Fin m), T.card ≤ b →
      ∃ x : W, (∀ j ∈ T, (L x) j = r j) ∧ ‖x‖ ≤ R) :
    ∃ T : Finset (Fin m), S ⊆ T ∧ T.card ≤ b ∧
      ∃ z : W, ‖z‖ ≤ R ∧ (∀ j ∈ T, (L z) j = r j) ∧
        ∀ j, j ∉ T → |(L z) j| ≤ η := by
  classical
  let F : Finset (Finset (Fin m)) := Finset.univ.filter fun T => S ⊆ T ∧ T.card ≤ b
  have hS : S ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, subset_refl, true_and]
    have : (S.card : ℝ) ≤ b := by nlinarith [sq_nonneg R]
    exact_mod_cast this
  have hf (T : Finset (Fin m)) (hT : T ∈ F) : S ⊆ T ∧ T.card ≤ b :=
    (Finset.mem_filter.mp hT).2
  have hchoose : ∀ T : Finset (Fin m), ∃ z : W,
      T ∈ F → ‖z‖ ≤ R ∧ (∀ j ∈ T, (L z) j = r j) ∧
        z ∈ (LinearMap.ker (rowRestriction L T))ᗮ := by
    intro T
    by_cases hT : T ∈ F
    · obtain ⟨x, hx, hxnorm⟩ := hsolve T (hf T hT).2
      obtain ⟨z, hzmap, hzortho, hznorm⟩ := exists_orthogonal_solution (rowRestriction L T) x
      refine ⟨z, fun _ => ⟨hznorm.trans hxnorm, ?_, hzortho⟩⟩
      intro j hj
      have hh := congrFun hzmap ⟨j, hj⟩
      exact hh.trans (hx j hj)
    · exact ⟨0, fun h => False.elim (hT h)⟩
  choose z hz using hchoose
  let objective (T : Finset (Fin m)) := ‖z T‖ ^ 2 - q * ((T \ S).card : ℝ)
  obtain ⟨T, hT, hmax⟩ := F.exists_max_image objective ⟨S, hS⟩
  have hTnorm := (hz T hT).1
  have hTmap := (hz T hT).2.1
  have hTortho := (hz T hT).2.2
  have hTS := (hf T hT).1
  have hTcard := (hf T hT).2
  have hobj : 0 ≤ objective T := by
    have hsobj : 0 ≤ objective S := by simp [objective]
    exact hsobj.trans (hmax S hS)
  have hadded : q * ((T \ S).card : ℝ) ≤ R ^ 2 := by
    dsimp [objective] at hobj
    have hnorm2 := (sq_le_sq₀ (norm_nonneg (z T)) hR).mpr hTnorm
    linarith
  refine ⟨T, hTS, hTcard, z T, hTnorm, hTmap, ?_⟩
  by_contra hbad
  let J := Finset.univ.filter fun j => j ∉ T ∧ η < |(L (z T)) j|
  have hJ : J.Nonempty := by
    push Not at hbad
    obtain ⟨j, hjT, hj⟩ := hbad
    exact ⟨j, by simp [J, hjT, hj]⟩
  have hj (j : Fin m) (hj : j ∈ J) : j ∉ T ∧ η < |(L (z T)) j| :=
    (Finset.mem_filter.mp hj).2
  have hdisj : Disjoint T J := Finset.disjoint_left.mpr fun j hjT hjJ => (hj j hjJ).1 hjT
  have hJbound : q * (J.card : ℝ) < R ^ 2 := by
    have hh := card_large_rows_bound L K η hK hη (z T) J hJ (fun j hjJ => (hj j hjJ).2)
    have hnorm2 := (sq_le_sq₀ (norm_nonneg (z T)) hR).mpr hTnorm
    rw [← hqeq] at hh
    have hK2 : 0 < K ^ 2 := sq_pos_of_pos hKpos
    nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hnorm2)]
  have hTsplit : T.card = S.card + (T \ S).card := by
    have he := Finset.card_sdiff_add_card_eq_card hTS
    omega
  have hTunioncard : (T ∪ J).card ≤ b := by
    rw [Finset.card_union_of_disjoint hdisj]
    have : ((T.card + J.card : ℕ) : ℝ) ≤ b := by
      push_cast
      rw [hTsplit]
      push_cast
      nlinarith
    exact_mod_cast this
  have hU : T ∪ J ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hTS.trans Finset.subset_union_left, hTunioncard⟩
  have hUmap := (hz (T ∪ J) hU).2.1
  have hdiff : z (T ∪ J) - z T ∈ LinearMap.ker (rowRestriction L T) := by
    rw [rowRestriction_mem_ker]
    intro j hjT
    simp [map_sub, hUmap j (Finset.mem_union_left J hjT), hTmap j hjT]
  have hinner : inner ℝ (z (T ∪ J) - z T) (z T) = 0 :=
    ((LinearMap.ker (rowRestriction L T)).mem_orthogonal (z T)).mp hTortho _ hdiff
  have hpyth : ‖z (T ∪ J)‖ ^ 2 = ‖z T‖ ^ 2 + ‖z (T ∪ J) - z T‖ ^ 2 := by
    have he := norm_add_sq_real (z (T ∪ J) - z T) (z T)
    rw [hinner, mul_zero, add_zero, sub_add_cancel] at he
    linarith
  have hdiffrows (j : Fin m) (hjJ : j ∈ J) :
      |(L (z (T ∪ J) - z T)) j| = |(L (z T)) j| := by
    have hjS : j ∉ S := fun hjS => (hj j hjJ).1 (hTS hjS)
    simp [map_sub, hUmap j (Finset.mem_union_right T hjJ), hr j hjS]
  have hgain : q * (J.card : ℝ) < ‖z (T ∪ J) - z T‖ ^ 2 := by
    have hh := card_large_rows_bound L K η hK hη (z (T ∪ J) - z T) J hJ
      (fun j hjJ => by rw [hdiffrows j hjJ]; exact (hj j hjJ).2)
    rw [← hqeq] at hh
    nlinarith [sq_pos_of_pos hKpos]
  have hUadded : ((T ∪ J) \ S).card = (T \ S).card + J.card := by
    have hjS : Disjoint J S := Finset.disjoint_left.mpr fun j hjJ hjS => (hj j hjJ).1 (hTS hjS)
    rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_self_iff_disjoint.mpr hjS]
    exact Finset.card_union_of_disjoint (hdisj.mono_left Finset.sdiff_subset)
  have hoptimal := hmax (T ∪ J) hU
  dsimp [objective] at hoptimal
  rw [hUadded, Nat.cast_add, hpyth] at hoptimal
  nlinarith

 

theorem active_slabs_card_ge {m : ℕ}
    (L : W →ₗ[ℝ] (Fin m → ℝ))
    (w : W)
    (hw : ∀ j, |L w j| ≤ 1)
    (hmax : ∀ x : W, (∀ j, |L x j| ≤ 1) → ‖x‖ ≤ ‖w‖) :
    Module.finrank ℝ W ≤ (Finset.univ.filter fun j => |L w j| = 1).card := by
  classical
  by_contra hc
  have hc' : (Finset.univ.filter fun j => |L w j| = 1).card < Module.finrank ℝ W := by omega
  let S := Finset.univ.filter fun j => |L w j| = 1
  let K : W →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun x j => L x j
      map_add' := by intro x y; ext j; simp
      map_smul' := by intro r x; ext j; simp }
  have hdim : Module.finrank ℝ (S → ℝ) <
      Module.finrank ℝ W := by
    calc
      Module.finrank ℝ (S → ℝ) = S.card := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      _ < Module.finrank ℝ W := by
        exact hc'
  obtain ⟨h, hker, hh⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := K) hdim)
  have hhactive : ∀ j, |L w j| = 1 → L h j = 0 := by
    intro j hj
    have hjS : j ∈ S := by simp [S, hj]
    exact congrFun (show K h = 0 from hker) ⟨j, hjS⟩
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ j, |L (w + t • h) j| ≤ 1 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : |L w j| = 1
    · filter_upwards [] with t
      simp [map_add, map_smul, hhactive j hj, hj]
    · have hjlt : |L w j| < 1 := lt_of_le_of_ne (hw j) hj
      have hcont : Continuous (fun t : ℝ => |L (w + t • h) j|) := by
        exact ((continuous_apply j).comp
          ((LinearMap.continuous_of_finiteDimensional L).comp
            (continuous_const.add (continuous_id.smul continuous_const)))).abs
      have htend : Tendsto (fun t : ℝ => |L (w + t • h) j|) (𝓝 0)
          (𝓝 |L w j|) := by
        simpa only [ContinuousAt, zero_smul, add_zero] using
          hcont.continuousAt (x := 0)
      have he := htend.eventually_lt_const hjlt
      filter_upwards [he] with t ht using ht.le
  obtain ⟨r, hr, he⟩ := Metric.eventually_nhds_iff.mp hev
  let t : ℝ := r / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hp := hmax (w + t • h) (he (by simpa [Real.dist_eq, abs_of_pos ht] using (show t < r by dsimp [t]; linarith)))
  have hm := hmax (w + (-t) • h) (he (by simpa [Real.dist_eq, abs_neg, abs_of_pos ht] using (show t < r by dsimp [t]; linarith)))
  have hp2 : ‖w + t • h‖ ^ 2 ≤ ‖w‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hp
  have hm2 : ‖w - t • h‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [sub_eq_add_neg, ← neg_smul]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hm
  have hpara := parallelogram_law_with_norm ℝ w (t • h)
  have hn : 0 < ‖t • h‖ := norm_pos_iff.mpr (smul_ne_zero ht.ne' hh)
  nlinarith [sq_pos_of_pos hn]

 

theorem slab_direction {m : ℕ} (hD : 0 < Module.finrank ℝ W)
    (L : W →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ∃ v : W, ‖v‖ = 1 ∧
      ∀ j, |(L v) j| ≤ ‖L‖ / Real.sqrt (Module.finrank ℝ W) := by
  classical
  by_cases hker : LinearMap.ker L.toLinearMap = ⊥
  · let Lp : W →ₗ[ℝ] (Fin m → ℝ) :=
      (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap.comp L.toLinearMap
    have hlp : LinearMap.ker Lp = ⊥ := by
      apply LinearMap.ker_eq_bot.mpr
      exact (EuclideanSpace.equiv (Fin m) ℝ).injective.comp
        (LinearMap.ker_eq_bot.mp hker)
    let Q := Lp ⁻¹' Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))
    have hQ : IsCompact Q :=
      (LinearMap.isClosedEmbedding_of_injective hlp).isCompact_preimage isCompact_Icc
    have hmem (x : W) :
        x ∈ Q ↔ ∀ j, |(L x) j| ≤ 1 := by
      change ((∀ j, -1 ≤ (L x) j) ∧ (∀ j, (L x) j ≤ 1)) ↔ _
      simp only [abs_le, forall_and]
    have hQ0 : (0 : W) ∈ Q := by
      rw [hmem]
      simp
    obtain ⟨w, hwQ, hwmax⟩ := hQ.exists_isMaxOn ⟨0, hQ0⟩ continuous_norm.continuousOn
    have hw := (hmem w).mp hwQ
    have hcard := active_slabs_card_ge Lp w hw
      (fun x hx => hwmax ((hmem x).mpr hx))
    let S := Finset.univ.filter fun j => |(L w) j| = 1
    have hdimnorm : (Module.finrank ℝ W : ℝ) ≤ ‖L w‖ ^ 2 := by
      calc
        (Module.finrank ℝ W : ℝ) ≤ S.card := by exact_mod_cast hcard
        _ = ∑ j ∈ S, ((L w) j) ^ 2 := by
          have heq : ∑ j ∈ S, ((L w) j) ^ 2 = ∑ _j ∈ S, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro j hj
            have ha : |(L w) j| = 1 := (Finset.mem_filter.mp hj).2
            nlinarith [sq_abs ((L w) j)]
          rw [heq]
          simp
        _ ≤ ∑ j, ((L w) j) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => sq_nonneg _)
        _ = ‖L w‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq _).symm
    have hDreal : (0 : ℝ) < Module.finrank ℝ W := Nat.cast_pos.mpr hD
    have hsqrt : 0 < Real.sqrt (Module.finrank ℝ W) := Real.sqrt_pos.mpr hDreal
    have hsqrteq : (Real.sqrt (Module.finrank ℝ W)) ^ 2 = Module.finrank ℝ W := Real.sq_sqrt hDreal.le
    have hroot : Real.sqrt (Module.finrank ℝ W) ≤ ‖L w‖ := by nlinarith [norm_nonneg (L w)]
    have hprod : Real.sqrt (Module.finrank ℝ W) ≤ ‖L‖ * ‖w‖ := hroot.trans (L.le_opNorm w)
    have hwn : 0 < ‖w‖ := by
      have hn := norm_nonneg w
      by_contra hn'
      have : ‖w‖ = 0 := le_antisymm (not_lt.mp hn') hn
      rw [this, mul_zero] at hprod
      linarith
    refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwn),
        inv_mul_cancel₀ hwn.ne']
    · intro j
      calc
        |(L (‖w‖⁻¹ • w)) j| = |(L w) j| / ‖w‖ := by
          simp [map_smul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hwn.le),
            div_eq_mul_inv, mul_comm]
        _ ≤ 1 / ‖w‖ := div_le_div_of_nonneg_right (hw j) hwn.le
        _ ≤ ‖L‖ / Real.sqrt (Module.finrank ℝ W) := (div_le_div_iff₀ hwn hsqrt).mpr (by simpa using hprod)
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hlw : L w = 0 := hw
    refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwn),
        inv_mul_cancel₀ hwn.ne']
    · intro j
      simp only [map_smul, hlw, smul_zero, PiLp.zero_apply, abs_zero]
      positivity

 

theorem orthogonal_kernel_slab_direction {m d : ℕ}
    (L : W →L[ℝ] EuclideanSpace ℝ (Fin m)) (T : Finset (Fin m)) (x : W)
    (hd : 0 < d) (hdim : T.card + d + 1 ≤ Module.finrank ℝ W) :
    ∃ v : W, ‖v‖ = 1 ∧ inner ℝ x v = 0 ∧
      (∀ j ∈ T, (L v) j = 0) ∧
      ∀ j, |(L v) j| ≤ ‖L‖ / Real.sqrt d := by
  classical
  let f : W →ₗ[ℝ] (T → ℝ) × ℝ :=
    (rowRestriction L T).prod (innerSL ℝ x).toLinearMap
  let U := LinearMap.ker f
  have hUdim : d ≤ Module.finrank ℝ U := by
    have hrank := f.finrank_range_add_finrank_ker
    have hle := (LinearMap.range f).finrank_le
    have htarget : Module.finrank ℝ ((T → ℝ) × ℝ) = T.card + 1 := by
      rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      simp
    rw [htarget] at hle
    dsimp [U]
    omega
  let LU : U →L[ℝ] EuclideanSpace ℝ (Fin m) := L.comp U.subtypeL
  obtain ⟨v, hvnorm, hvrows⟩ := slab_direction (lt_of_lt_of_le hd hUdim) LU
  have hvker : f (v : W) = 0 := v.property
  have hprod : (rowRestriction L T (v : W), inner ℝ x (v : W)) = 0 := hvker
  have hrestrict : ‖LU‖ ≤ ‖L‖ := by
    exact (L.opNorm_comp_le U.subtypeL).trans
      ((mul_le_mul_of_nonneg_left U.norm_subtypeL_le (norm_nonneg L)).trans_eq (mul_one _))
  have hden : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hsqrt : Real.sqrt (d : ℝ) ≤ Real.sqrt (Module.finrank ℝ U : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hUdim)
  refine ⟨(v : W), hvnorm, congrArg Prod.snd hprod, ?_, ?_⟩
  · have hh := congrArg Prod.fst hprod
    exact (rowRestriction_mem_ker L T (v : W)).mp hh
  · intro j
    have he : |(L (v : W)) j| ≤ ‖LU‖ / Real.sqrt (Module.finrank ℝ U) := hvrows j
    exact he.trans (div_le_div₀ (norm_nonneg L) hrestrict hden hsqrt)

section Adjoint
variable {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

 
theorem exists_solution_of_adjoint_lower_bound (L : W →ₗ[ℝ] V)
    (c : ℝ) (hc : 0 < c) (hL : ∀ v : V, c * ‖v‖ ≤ ‖L.adjoint v‖) (r : V) :
    ∃ x : W, L x = r ∧ ‖x‖ ≤ ‖r‖ / c := by
  have hinj : Function.Injective L.adjoint := by
    rw [← LinearMap.ker_eq_bot]
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hh := hL v
    rw [hv, norm_zero] at hh
    have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp this
  have hgraminj : Function.Injective (L.comp L.adjoint) :=
    L.self_comp_adjoint_injective_iff.mpr hinj
  have hgramsurj : Function.Surjective (L.comp L.adjoint) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hgraminj
  obtain ⟨v, hv⟩ := hgramsurj r
  change L (L.adjoint v) = r at hv
  refine ⟨L.adjoint v, hv, ?_⟩
  have hinner : inner ℝ (L.adjoint v) (L.adjoint v) = inner ℝ r v := by
    rw [L.adjoint_inner_right, hv]
  have hcs : ‖L.adjoint v‖ ^ 2 ≤ ‖r‖ * ‖v‖ := by
    rw [← real_inner_self_eq_norm_sq, hinner]
    exact real_inner_le_norm r v
  have hh := hL v
  apply (le_div_iff₀ hc).mpr
  by_cases hz : L.adjoint v = 0
  · simp [hz, norm_nonneg]
  · have hpos : 0 < ‖L.adjoint v‖ := norm_pos_iff.mpr hz
    nlinarith [mul_le_mul_of_nonneg_left hcs hc.le,
      mul_le_mul_of_nonneg_left hh (norm_nonneg r)]

end Adjoint

 

theorem complete_feasible_to_sphere {m d : ℕ}
    (L : W →L[ℝ] EuclideanSpace ℝ (Fin m)) (T : Finset (Fin m)) (x : W)
    (R u : ℝ) (_hR : 0 ≤ R) (hd : 0 < d)
    (hdim : T.card + d + 1 ≤ Module.finrank ℝ W)
    (hxnorm : 1 - R ≤ ‖x‖)
    (hfeas : ∀ j, 0 ≤ 1 + (L x) j)
    (hmargin : ∀ j, j ∉ T → u ≤ 1 + (L x) j)
    (hsmall : Real.sqrt (2 * R) * (‖L‖ / Real.sqrt d) ≤ u) :
    ∃ y : W, ‖y‖ = 1 ∧ ∀ j, 0 ≤ 1 + (L y) j := by
  classical
  by_cases hnorm : 1 ≤ ‖x‖
  · have hpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hnorm
    refine ⟨(‖x‖⁻¹ : ℝ) • x, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']
    · intro j
      have hinv : ‖x‖⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr hnorm
      have hn : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr hpos.le
      have hp := mul_nonneg hn (hfeas j)
      simpa only [map_smul, PiLp.smul_apply, smul_eq_mul] using
        (show 0 ≤ 1 + ‖x‖⁻¹ * (L x) j by nlinarith)
  · have hlt : ‖x‖ < 1 := lt_of_not_ge hnorm
    obtain ⟨v, hvnorm, hvortho, hvT, hvrows⟩ :=
      orthogonal_kernel_slab_direction L T x hd hdim
    have hrad : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    let t := Real.sqrt (1 - ‖x‖ ^ 2)
    have ht : 0 ≤ t := Real.sqrt_nonneg _
    have ht2 : t ^ 2 = 1 - ‖x‖ ^ 2 := Real.sq_sqrt hrad
    have hradle : 1 - ‖x‖ ^ 2 ≤ 2 * R := by nlinarith [sq_nonneg (1 - ‖x‖)]
    have htle : t ≤ Real.sqrt (2 * R) := Real.sqrt_le_sqrt hradle
    have hbound : ∀ j, |t * (L v) j| ≤ u := by
      intro j
      rw [abs_mul, abs_of_nonneg ht]
      calc
        t * |(L v) j| ≤ t * (‖L‖ / Real.sqrt d) := mul_le_mul_of_nonneg_left (hvrows j) ht
        _ ≤ Real.sqrt (2 * R) * (‖L‖ / Real.sqrt d) :=
          mul_le_mul_of_nonneg_right htle (div_nonneg (norm_nonneg L) (Real.sqrt_nonneg _))
        _ ≤ u := hsmall
    refine ⟨x + t • v, ?_, ?_⟩
    · have hi : inner ℝ x (t • v) = 0 := by rw [real_inner_smul_right, hvortho, mul_zero]
      have hn : ‖t • v‖ = t := by rw [norm_smul, hvnorm, mul_one, Real.norm_of_nonneg ht]
      have hh := norm_add_sq_real x (t • v)
      rw [hi, mul_zero, add_zero, hn, ht2] at hh
      nlinarith [norm_nonneg (x + t • v)]
    · intro j
      have he : (L (x + t • v)) j = (L x) j + t * (L v) j := by simp
      rw [he]
      by_cases hj : j ∈ T
      · simpa [hvT j hj] using hfeas j
      · have hh := hmargin j hj
        have hb := (abs_le.mp (hbound j)).1
        linarith

 

theorem deterministic_repair_of_small_solves {m D : ℕ}
    (L : W →L[ℝ] EuclideanSpace ℝ (Fin m)) (y : W) (S : Finset (Fin m))
    (b : ℕ) (K R u q : ℝ) (hy : ‖y‖ = 1)
    (hK : ‖L‖ ≤ K) (hKpos : 0 < K) (hR : 0 ≤ R) (hu : 0 < u)
    (hq : 0 < q) (hqeq : q * K ^ 2 = (u / 4) ^ 2)
    (hcap : q * (S.card : ℝ) + 2 * R ^ 2 ≤ q * b)
    (hD : 0 < D) (hdim : b + D + 1 ≤ Module.finrank ℝ W)
    (hmargin : ∀ j, j ∉ S → u < 1 + (L y) j)
    (hsmall : Real.sqrt (2 * R) * (‖L‖ / Real.sqrt D) ≤ 3 * u / 4)
    (hsolve : ∀ T : Finset (Fin m), T.card ≤ b →
      ∃ z : W, (∀ j ∈ T, (L z) j = max (-(1 + (L y) j)) 0) ∧ ‖z‖ ≤ R) :
    ∃ yhat : W, ‖yhat‖ = 1 ∧ ∀ j, 0 ≤ 1 + (L yhat) j := by
  classical
  let r : Fin m → ℝ := fun j => max (-(1 + (L y) j)) 0
  have hr : ∀ j, j ∉ S → r j = 0 := by
    intro j hj
    have hh := hmargin j hj
    exact max_eq_right (by linarith)
  obtain ⟨T, hST, hTcard, z, hznorm, hzT, hzrest⟩ :=
    exists_slack_correction L S r b K R (u / 4) q hK hKpos hR (by positivity)
      hq hqeq hcap hr hsolve
  have hdimT : T.card + D + 1 ≤ Module.finrank ℝ W := by omega
  have hnear : 1 - R ≤ ‖y + z‖ := by
    have hh := norm_sub_le (y + z) z
    rw [add_sub_cancel_right, hy] at hh
    linarith
  have hrest (j : Fin m) (hj : j ∉ T) : 3 * u / 4 ≤ 1 + (L (y + z)) j := by
    have hjS : j ∉ S := fun hh => hj (hST hh)
    have hgap := hmargin j hjS
    have hz := (abs_le.mp (hzrest j hj)).1
    have he : (L (y + z)) j = (L y) j + (L z) j := by simp
    rw [he]
    linarith
  have hfeas (j : Fin m) : 0 ≤ 1 + (L (y + z)) j := by
    by_cases hj : j ∈ T
    · have hh := hzT j hj
      have hrbound : -(1 + (L y) j) ≤ r j := le_max_left _ _
      have he : (L (y + z)) j = (L y) j + (L z) j := by simp
      rw [he, hh]
      linarith
    · exact (by positivity : 0 ≤ 3 * u / 4).trans (hrest j hj)
  exact complete_feasible_to_sphere L T (y + z) R (3 * u / 4) hR hD
    hdimT hnear hfeas hrest hsmall

 
def euclideanRows {m : ℕ} (L : W →L[ℝ] EuclideanSpace ℝ (Fin m))
    (T : Finset (Fin m)) : W →ₗ[ℝ] EuclideanSpace ℝ T :=
  (EuclideanSpace.equiv T ℝ).symm.toLinearMap.comp (rowRestriction L T)

 
lemma norm_euclidean_restrict {m : ℕ} (r : EuclideanSpace ℝ (Fin m))
    (T : Finset (Fin m)) :
    ‖(EuclideanSpace.equiv T ℝ).symm (fun j => r j)‖ ≤ ‖r‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg r)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ j : T, r j ^ 2) ≤ ∑ j : Fin m, r j ^ 2
  rw [Finset.sum_coe_sort T (fun j => r j ^ 2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => sq_nonneg _)

 

theorem small_row_solves_of_adjoint_lower_bound {m : ℕ}
    (L : W →L[ℝ] EuclideanSpace ℝ (Fin m)) (b : ℕ) (c : ℝ) (hc : 0 < c)
    (hL : ∀ T : Finset (Fin m), T.card ≤ b →
      ∀ v : EuclideanSpace ℝ T, c * ‖v‖ ≤ ‖(euclideanRows L T).adjoint v‖)
    (r : EuclideanSpace ℝ (Fin m)) :
    ∀ T : Finset (Fin m), T.card ≤ b →
      ∃ z : W, (∀ j ∈ T, (L z) j = r j) ∧ ‖z‖ ≤ ‖r‖ / c := by
  intro T hT
  obtain ⟨z, hz, hznorm⟩ := exists_solution_of_adjoint_lower_bound
    (euclideanRows L T) c hc (hL T hT)
    ((EuclideanSpace.equiv T ℝ).symm (fun j => r j))
  refine ⟨z, ?_, hznorm.trans (div_le_div_of_nonneg_right (norm_euclidean_restrict r T) hc.le)⟩
  intro j hj
  exact congrArg (fun v : EuclideanSpace ℝ T => v ⟨j, hj⟩) hz

 

theorem deterministic_repair_smallness {N m : ℕ}
    (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin N)) (K c u ρ d : ℝ)
    (hK : 0 < K) (hc : 0 < c) (hu : 0 < u) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hd : 0 < d) (hN : 2 ≤ ρ * N)
    (hy : ‖y‖ = 1) (hLnorm : ‖L‖ ≤ K * Real.sqrt N)
    (htrans : ∀ T : Finset (Fin m), (T.card : ℝ) ≤ (1 - ρ) * N →
      ∀ v : EuclideanSpace ℝ T,
        c * Real.sqrt N * ‖v‖ ≤ ‖(euclideanRows L T).adjoint v‖)
    (hres : ‖(EuclideanSpace.equiv (Fin m) ℝ).symm
      (fun j => max (-(1 + (L y) j)) 0)‖ ≤ d * Real.sqrt N)
    (hcount : ((Finset.univ.filter (fun j => 1 + (L y) j ≤ u)).card : ℝ) ≤
      (1 - 2 * ρ) * N)
    (_hsmall₁ : d / c ≤ 1 / 2)
    (hsmall₂ : 16 * K ^ 2 * d ^ 2 / (c ^ 2 * u ^ 2) ≤ ρ / 4)
    (hsmall₃ : K * Real.sqrt (4 * d / (c * ρ)) ≤ u / 2) :
    ∃ yhat : EuclideanSpace ℝ (Fin N), ‖yhat‖ = 1 ∧
      ∀ j, 0 ≤ 1 + (L yhat) j := by
  classical
  have hn : 0 < (N : ℝ) := by nlinarith only [hN, hρ, show (0 : ℝ) ≤ N by positivity]
  have hsqrtn : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  let b : ℕ := ⌊(1 - ρ) * N⌋₊
  have harg : 0 ≤ (1 - ρ) * (N : ℝ) := mul_nonneg (by linarith only [hρ1]) hn.le
  have hb : (b : ℝ) ≤ (1 - ρ) * N := Nat.floor_le harg
  have hbfloor : (1 - ρ) * N < (b : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbN : b + 2 ≤ N := by
    have : (b : ℝ) + 2 ≤ N := by nlinarith only [hb, hN]
    exact_mod_cast this
  let D := N - b - 1
  have hD : 0 < D := by dsimp [D]; omega
  have hDcast : (D : ℝ) = (N : ℝ) - b - 1 := by
    dsimp [D]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp
  have hDlower : ρ * N / 2 ≤ (D : ℝ) := by rw [hDcast]; nlinarith only [hb, hN]
  have hDpos : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  let S := Finset.univ.filter (fun j => 1 + (L y) j ≤ u)
  let R := d / c
  let KN := K * Real.sqrt N
  let q := (u / 4) ^ 2 / KN ^ 2
  have hR : 0 ≤ R := le_of_lt (div_pos hd hc)
  have hKN : 0 < KN := mul_pos hK hsqrtn
  have hq : 0 < q := div_pos (sq_pos_of_pos (by positivity)) (sq_pos_of_pos hKN)
  have hqeq : q * KN ^ 2 = (u / 4) ^ 2 := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hKN))
  have hKNeq : KN ^ 2 = K ^ 2 * N := by
    dsimp [KN]
    rw [mul_pow, Real.sq_sqrt hn.le]
  have hRratio : R ^ 2 / q =
      (16 * K ^ 2 * d ^ 2 / (c ^ 2 * u ^ 2)) * N := by
    dsimp [R, q]
    rw [hKNeq]
    field_simp
    ring
  have hcapR : 2 * R ^ 2 ≤ q * (ρ * N / 2) := by
    have hh := mul_le_mul_of_nonneg_right hsmall₂ hn.le
    rw [← hRratio] at hh
    have hh' := (div_le_iff₀ hq).mp hh
    nlinarith only [hh']
  have hcapS : (S.card : ℝ) + ρ * N / 2 ≤ b := by
    have hcS := hcount
    change (S.card : ℝ) ≤ (1 - 2 * ρ) * N at hcS
    nlinarith only [hcS, hbfloor, hN]
  have hcap : q * (S.card : ℝ) + 2 * R ^ 2 ≤ q * b := by
    have hh := mul_le_mul_of_nonneg_left hcapS hq.le
    nlinarith only [hh, hcapR]
  have hmargin : ∀ j, j ∉ S → u < 1 + (L y) j := by
    intro j hj
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hj
  let r : EuclideanSpace ℝ (Fin m) :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => max (-(1 + (L y) j)) 0)
  have hsolve : ∀ T : Finset (Fin m), T.card ≤ b →
      ∃ z : EuclideanSpace ℝ (Fin N),
        (∀ j ∈ T, (L z) j = max (-(1 + (L y) j)) 0) ∧ ‖z‖ ≤ R := by
    have ht : ∀ T : Finset (Fin m), T.card ≤ b →
        ∀ v : EuclideanSpace ℝ T,
          c * Real.sqrt N * ‖v‖ ≤ ‖(euclideanRows L T).adjoint v‖ := by
      intro T hT
      exact htrans T ((by exact_mod_cast hT : (T.card : ℝ) ≤ b).trans hb)
    intro T hT
    obtain ⟨z, hz, hznorm⟩ := small_row_solves_of_adjoint_lower_bound L b
      (c * Real.sqrt N) (mul_pos hc hsqrtn) ht r T hT
    refine ⟨z, hz, hznorm.trans ?_⟩
    have heq : d * Real.sqrt N / (c * Real.sqrt N) = R := by
      dsimp [R]; field_simp
    rw [← heq]
    exact div_le_div_of_nonneg_right hres (mul_pos hc hsqrtn).le
  have hsmall : Real.sqrt (2 * R) * (‖L‖ / Real.sqrt D) ≤ 3 * u / 4 := by
    have hratio : (N : ℝ) / D ≤ 2 / ρ := by
      apply (div_le_div_iff₀ hDpos hρ).mpr
      nlinarith only [hDlower]
    have hrad : (2 * R) * ((N : ℝ) / D) ≤ 4 * d / (c * ρ) := by
      have hh := mul_le_mul_of_nonneg_left hratio (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hR)
      have he : 2 * R * (2 / ρ) = 4 * d / (c * ρ) := by dsimp [R]; ring
      exact hh.trans_eq he
    calc
      Real.sqrt (2 * R) * (‖L‖ / Real.sqrt D) ≤
          Real.sqrt (2 * R) * (KN / Real.sqrt D) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hLnorm (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)
      _ = K * Real.sqrt ((2 * R) * ((N : ℝ) / D)) := by
        rw [Real.sqrt_mul (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hR), Real.sqrt_div hn.le]
        dsimp [KN]
        ring
      _ ≤ K * Real.sqrt (4 * d / (c * ρ)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) hK.le
      _ ≤ u / 2 := hsmall₃
      _ ≤ 3 * u / 4 := by linarith only [hu]
  have hdim : b + D + 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
    simp only [finrank_euclideanSpace_fin]
    dsimp [D]
    omega
  exact deterministic_repair_of_small_solves L y S b KN R u q hy hLnorm hKN hR hu
    hq hqeq hcap hD hdim hmargin hsmall hsolve

end MicroscopicJamming

end

end OAI
