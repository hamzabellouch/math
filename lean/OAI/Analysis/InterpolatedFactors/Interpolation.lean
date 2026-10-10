import OAI.Analysis.InterpolatedFactors.NormalTransport

namespace OAI

noncomputable section

universe u_1

namespace FreeGroupFactorMain.Interpolation
open Amplification
open scoped ENNReal

theorem selectedProjection_trace (a : ℝ) (ha : 0<a) :
    stabilizedProjectionTrace (selectedProjection a).val=ENNReal.ofReal a := by
  unfold selectedProjection
  apply Classical.epsilon_spec (p := fun p : RankTwoProjection => stabilizedProjectionTrace p.val=ENNReal.ofReal a)
  obtain ⟨p,hp,ht⟩ := (rankTwo_allPositiveScaling a ha).1
  exact ⟨⟨p,hp⟩,ht⟩

theorem interpolationScale_pos (r : ℝ) (hr : 1<r) : 0 < interpolationScale r :=
  inv_pos.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hr))

theorem Model.toRankTwo (m : Model) (hm : m.Valid) :
    Nonempty (NormalTracialEquiv m.trace (canonicalTrace (G := FreeGroupRank 2))
      m.topology (groupUltraweakTopology (FreeGroupRank 2))) := by
  cases m with
  | integer n => exact groupNormal_of_iso (finiteRank_to_two n hm)
  | continuous r =>
    exact (rankTwo_allPositiveScaling _ (interpolationScale_pos r hm)).2 _ _
      (selectedProjection_trace _ (interpolationScale_pos r hm))
  | infinity => exact groupNormal_of_iso (rankTwo.trans rankThreeInfinite).symm

theorem Model.allIsomorphic (m n : Model) (hm : m.Valid) (hn : n.Valid) :
    Nonempty (m.Iso n) := by
  obtain ⟨E⟩ := m.toRankTwo hm
  obtain ⟨F⟩ := n.toRankTwo hn
  exact ⟨E.trans F.symm⟩

theorem Model.projection_exists (m : Model) (hm : m.Valid) (t : ℝ) (ht : 0<t) :
    ∃p : m.Stabilization,IsStarProjection p ∧ m.projectionTrace p=ENNReal.ofReal t := by
  cases m with
  | integer n => exact (groupAllPositive_of_rankTwo (finiteRank_to_two n hm) t ht).1
  | infinity => exact (infinite_allPositiveScaling t ht).1
  | continuous r =>
    exact cornerStabilization_projection_exists
      (fun a ha => (rankTwo_allPositiveScaling a ha).2) rankTwo_smallScaling
      _ (interpolationScale_pos r hm) (selectedProjection (interpolationScale r)).val
      (selectedProjection (interpolationScale r)).property (selectedProjection_trace _ (interpolationScale_pos r hm)) t ht

theorem Model.allPositive (m : Model) (hm : m.Valid) (t : ℝ) (ht : 0<t)
    (p : m.Stabilization) (hp : IsStarProjection p) (hpτ : m.projectionTrace p=ENNReal.ofReal t) :
    Nonempty (m.AmplificationIso t p hp) := by
  cases m with
  | integer n => exact (groupAllPositive_of_rankTwo (finiteRank_to_two n hm) t ht).2 p hp hpτ
  | infinity => exact (infinite_allPositiveScaling t ht).2 p hp hpτ
  | continuous r =>
    exact cornerStabilization_allPositive (fun a ha => (rankTwo_allPositiveScaling a ha).2)
      _ (interpolationScale_pos r hm) _ _ (selectedProjection_trace _ (interpolationScale_pos r hm))
      t ht p hp hpτ

theorem Model.fundamentalGroup_eq (m : Model) (hm : m.Valid) : m.fundamentalGroup=Set.Ioi (0:ℝ) := by
  ext t
  constructor
  · exact fun h => h.1
  · intro ht
    obtain ⟨p,hp,hpτ⟩ := m.projection_exists hm t ht
    exact ⟨ht,p,hp,hpτ,m.allPositive hm t ht p hp hpτ⟩

@[simp] theorem parameterModel_top : parameterModel ⊤=Model.infinity := by
  classical
  simp [parameterModel]

@[simp] theorem parameterModel_nat (n : ℕ) : parameterModel (n:ℝ≥0∞)=Model.integer n := by
  classical
  have hn : ∃k : ℕ,(n:ℝ≥0∞)=(k:ℝ≥0∞) := ⟨n,rfl⟩
  simp only [parameterModel,ENNReal.natCast_ne_top,ite_false,dite_eq_left hn]
  congr 1
  exact_mod_cast hn.choose_spec.symm

theorem parameterModel_nonnatural (r : ℝ≥0∞) (hrtop : r≠⊤)
    (hrnat : ¬∃n : ℕ,r=(n:ℝ≥0∞)) : parameterModel r=Model.continuous r.toReal := by
  classical
  simp only [parameterModel,ite_eq_right hrtop,dite_eq_right hrnat]

theorem parameterModel_valid (r : ℝ≥0∞) (hr : 1<r) : (parameterModel r).Valid := by
  classical
  by_cases htop : r=⊤
  · rw [htop,parameterModel_top]
    trivial
  · by_cases hn : ∃n : ℕ,r=(n:ℝ≥0∞)
    · obtain ⟨n,rfl⟩ := hn
      rw [parameterModel_nat]
      change 2≤n
      have h : (1:ℕ)<n := by exact_mod_cast hr
      omega
    · rw [parameterModel_nonnatural r htop hn]
      change 1<r.toReal
      have h := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top htop).mpr hr
      simpa only [ENNReal.toReal_one] using h

theorem allInterpolatedIsomorphic (r s : ℝ≥0∞) (hr : 1<r) (hs : 1<s) :
    Nonempty (NormalTracialEquiv (interpolatedTrace r) (interpolatedTrace s)
      (interpolatedTopology r) (interpolatedTopology s)) :=
  Model.allIsomorphic _ _ (parameterModel_valid r hr) (parameterModel_valid s hs)

theorem allInterpolatedAmplifications (r : ℝ≥0∞) (hr : 1<r) (t : ℝ) (ht : 0<t)
    (p : interpolatedStabilization r) (hp : IsStarProjection p)
    (hpτ : interpolatedProjectionTrace r p=ENNReal.ofReal t) :
    Nonempty (NormalTracialEquiv
      (normalizedCornerTrace (interpolatedStabilizationTrace r) t p hp) (interpolatedTrace r)
      (cornerTopology (interpolatedStabilizationTopology r) p hp) (interpolatedTopology r)) :=
  Model.allPositive _ (parameterModel_valid r hr) t ht p hp hpτ

theorem allInterpolatedFundamentalGroups (r : ℝ≥0∞) (hr : 1<r) :
    fundamentalGroup r=Set.Ioi (0:ℝ) := Model.fundamentalGroup_eq _ (parameterModel_valid r hr)

end FreeGroupFactorMain.Interpolation

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_1} [Group G]

theorem double_corner_matrix_iff (p : stabilization G) (T : GroupOperator (ℕ × (ℕ × G))) :
    (T ∈ doubleStabilization G ∧
      productAmplification ℕ (ℕ × G) (p : GroupOperator (ℕ × G))*T=T ∧
      T*productAmplification ℕ (ℕ × G) (p : GroupOperator (ℕ × G))=T) ↔
    ∀i j : ℕ, matrixEntry T i j ∈ stabilization G ∧
      (p : GroupOperator (ℕ × G))*matrixEntry T i j=matrixEntry T i j ∧
      matrixEntry T i j*(p : GroupOperator (ℕ × G))=matrixEntry T i j := by
  rw [mem_doubleStabilization_iff_matrix]
  constructor
  · rintro ⟨hT,hl,hr⟩ i j
    refine ⟨hT i j,?_,?_⟩
    · simpa only [matrixEntry_diagonal_mul] using congrArg (fun S => matrixEntry S i j) hl
    · simpa only [matrixEntry_mul_diagonal] using congrArg (fun S => matrixEntry S i j) hr
  · intro h
    refine ⟨fun i j => (h i j).1,?_,?_⟩
    · apply matrixEntry_ext
      intro i j
      rw [matrixEntry_diagonal_mul]
      exact (h i j).2.1
    · apply matrixEntry_ext
      intro i j
      rw [matrixEntry_mul_diagonal]
      exact (h i j).2.2

variable [DecidableEq G]

theorem corner_weight_tensor_formula (a : ℝ) (p : stabilization G) (hp : IsStarProjection p)
    (x : CornerStabilization p hp) :
    cornerStabilizationProjectionTrace a p hp x =
      (ENNReal.ofReal a)⁻¹ * ∑' i : ℕ, ∑' j : ℕ,
        ENNReal.ofReal (‖(flattenStabilizationIso.symm x.val : GroupOperator (ℕ × (ℕ × G)))
          (lp.single 2 (i,j,1) (1:ℂ))‖^2) := by
  unfold cornerStabilizationProjectionTrace
  apply congrArg ((ENNReal.ofReal a)⁻¹ * ·)
  simpa only [StarAlgEquiv.apply_symm_apply] using
    (flatten_projectionTrace ((flattenStabilizationIso (G := G)).symm x.val))

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.Interpolation
open Amplification
open scoped ENNReal

theorem standardCornerScale_pos (n : ℕ) (hn : 2≤n) (r : ℝ) (hr : 1<r) :
    0 < standardCornerScale n r := by
  apply Real.sqrt_pos.mpr
  apply div_pos _ (sub_pos.mpr hr)
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  linarith

theorem standardCornerScale_parameter (n : ℕ) (hn : 2≤n) (r : ℝ) (hr : 1<r) :
    1+((n:ℝ)-1)/(standardCornerScale n r)^2=r := by
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have h0 : 0<((n:ℝ)-1)/(r-1) := div_pos (by linarith) (by linarith)
  rw [standardCornerScale,Real.sq_sqrt h0.le]
  have ha : (n:ℝ)-1≠0 := by linarith
  field_simp [ha]
  ring

theorem standardCornerScale_two (r : ℝ) : standardCornerScale 2 r=interpolationScale r := by
  norm_num [standardCornerScale,interpolationScale,Real.sqrt_inv]

theorem interpolationScale_parameter (r : ℝ) (hr : 1<r) :
    1+1/(interpolationScale r)^2=r := by
  have h := standardCornerScale_parameter 2 (by omega) r hr
  simpa only [standardCornerScale_two,Nat.cast_ofNat,show (2:ℝ)-1=1 by norm_num] using h

theorem ofReal_parameter_valid (r : ℝ) (hr : 1<r) : (1:ℝ≥0∞)<ENNReal.ofReal r := by
  rw [←ENNReal.ofReal_one]
  exact ENNReal.ofReal_lt_ofReal_iff (by linarith : 0<r) |>.mpr hr

theorem interpolatedFactor_nat (n : ℕ) :
    InterpolatedFactor (n:ℝ≥0∞)=groupVonNeumann (FreeGroupRank n) := by
  unfold InterpolatedFactor
  rw [parameterModel_nat]
  rfl

theorem interpolatedFactor_infinity : InterpolatedFactor ⊤=groupVonNeumann (FreeGroup ℕ) := by
  unfold InterpolatedFactor
  rw [parameterModel_top]
  rfl

theorem interpolatedTrace_one (r : ℝ≥0∞) (hr : 1<r) :
    interpolatedTrace r (1 : InterpolatedFactor r)=1 := by
  obtain ⟨E⟩ := Model.toRankTwo (parameterModel r) (parameterModel_valid r hr)
  have h := E.trace_eq 1
  rw [map_one,canonicalTrace_one] at h
  exact h.symm

theorem allInterpolatedProjections (r : ℝ≥0∞) (hr : 1<r) (t : ℝ) (ht : 0<t) :
    ∃p : interpolatedStabilization r,IsStarProjection p ∧
      interpolatedProjectionTrace r p=ENNReal.ofReal t :=
  Model.projection_exists _ (parameterModel_valid r hr) t ht

theorem standardIntegerBaseProjection (n : ℕ) (hn : 2≤n) (r : ℝ) (hr : 1<r) :
    ∃p : stabilization (FreeGroupRank n), IsStarProjection p ∧
      stabilizedProjectionTrace p=ENNReal.ofReal (standardCornerScale n r) :=
  (groupAllPositive_of_rankTwo (finiteRank_to_two n hn) _ (standardCornerScale_pos n hn r hr)).1

theorem standardIntegerBaseIdentification (n : ℕ) (hn : 2≤n) (r : ℝ) (hr : 1<r)
    (p : stabilization (FreeGroupRank n)) (hp : IsStarProjection p)
    (hpτ : stabilizedProjectionTrace p=ENNReal.ofReal (standardCornerScale n r)) :
    Nonempty (NormalTracialEquiv
      (normalizedCornerTrace stabilizedTrace (standardCornerScale n r) p hp)
      (interpolatedTrace (ENNReal.ofReal r))
      (cornerTopology (stabilizationTopology (FreeGroupRank n)) p hp)
      (interpolatedTopology (ENNReal.ofReal r))) := by
  obtain ⟨E⟩ := (groupAllPositive_of_rankTwo (finiteRank_to_two n hn) _
    (standardCornerScale_pos n hn r hr)).2 p hp hpτ
  obtain ⟨F⟩ := Model.allIsomorphic (.integer n) (parameterModel (ENNReal.ofReal r)) hn
    (parameterModel_valid _ (ofReal_parameter_valid r hr))
  exact ⟨E.trans F⟩

theorem interpolationAmplificationFormula (r : ℝ) (hr : 1<r) (t : ℝ) (ht : 0<t)
    (p : interpolatedStabilization (ENNReal.ofReal r)) (hp : IsStarProjection p)
    (hpτ : interpolatedProjectionTrace (ENNReal.ofReal r) p=ENNReal.ofReal t) :
    Nonempty (NormalTracialEquiv
      (normalizedCornerTrace (interpolatedStabilizationTrace (ENNReal.ofReal r)) t p hp)
      (interpolatedTrace (ENNReal.ofReal (1+(r-1)/t^2)))
      (cornerTopology (interpolatedStabilizationTopology (ENNReal.ofReal r)) p hp)
      (interpolatedTopology (ENNReal.ofReal (1+(r-1)/t^2)))) := by
  have hs : 1<1+(r-1)/t^2 := by
    have h : 0<(r-1)/t^2 := div_pos (sub_pos.mpr hr) (pow_pos ht 2)
    linarith
  obtain ⟨E⟩ := allInterpolatedAmplifications _ (ofReal_parameter_valid r hr) t ht p hp hpτ
  obtain ⟨F⟩ := allInterpolatedIsomorphic _ _ (ofReal_parameter_valid r hr) (ofReal_parameter_valid _ hs)
  exact ⟨E.trans F⟩

end FreeGroupFactorMain.Interpolation

end

end OAI
