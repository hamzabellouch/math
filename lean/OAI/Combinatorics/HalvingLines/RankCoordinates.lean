import OAI.Combinatorics.HalvingLines.Compactness

namespace OAI

open Filter Topology
namespace PlanarHalving.RankCoordinates

abbrev UnitOpen := Set.Ioo (0 : ℝ) 1

structure Coordinate (l u : ℝ) where
  value : ℝ × ℝ → ℝ
  continuous_value : Continuous value
  mem : ∀ p, value p ∈ Set.Ioo 0 1
  strict_vertical : ∀ x, StrictMono (fun y => value (x,y))
  onto_vertical : ∀ x (v : UnitOpen), ∃ y, value (x,y) = v
  translate_lower : ∀ x y h, 0 ≤ h → value (x+h,y+l*h) ≤ value (x,y)
  translate_upper : ∀ x y h, 0 ≤ h → value (x,y) ≤ value (x+h,y+u*h)

namespace Coordinate
variable {l u : ℝ} (R : Coordinate l u)

noncomputable def level (x : ℝ) (v : UnitOpen) : ℝ :=
  Classical.choose (R.onto_vertical x v)

lemma value_level (x : ℝ) (v : UnitOpen) : R.value (x,R.level x v) = v :=
  Classical.choose_spec (R.onto_vertical x v)

lemma level_value (x y : ℝ) : R.level x ⟨R.value (x,y), R.mem (x,y)⟩ = y :=
  (R.strict_vertical x).injective (R.value_level x _)

lemma lt_level_iff (x y : ℝ) (v : UnitOpen) : y < R.level x v ↔ R.value (x,y) < v := by
  rw [← R.value_level x v]
  exact (R.strict_vertical x).lt_iff_lt.symm

lemma level_lt_iff (x y : ℝ) (v : UnitOpen) : R.level x v < y ↔ (v : ℝ) < R.value (x,y) := by
  rw [← R.value_level x v]
  exact (R.strict_vertical x).lt_iff_lt.symm

lemma le_level_iff (x y : ℝ) (v : UnitOpen) : y ≤ R.level x v ↔ R.value (x,y) ≤ v := by
  rw [← R.value_level x v]
  exact (R.strict_vertical x).le_iff_le.symm

lemma level_le_iff (x y : ℝ) (v : UnitOpen) : R.level x v ≤ y ↔ (v : ℝ) ≤ R.value (x,y) := by
  rw [← R.value_level x v]
  exact (R.strict_vertical x).le_iff_le.symm

lemma continuous_level : Continuous (fun p : ℝ × UnitOpen => R.level p.1 p.2) := by
  refine continuous_iff_continuousAt.mpr fun p => tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    have h := (R.lt_level_iff p.1 a p.2).mp ha
    have hr : Continuous (fun q : ℝ × UnitOpen => R.value (q.1,a)) :=
      R.continuous_value.comp (continuous_fst.prodMk continuous_const)
    have hv : Continuous (fun q : ℝ × UnitOpen => (q.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    filter_upwards [hr.continuousAt.eventually_lt hv.continuousAt h] with q hq
    exact (R.lt_level_iff q.1 a q.2).mpr hq
  · intro a ha
    have h := (R.level_lt_iff p.1 a p.2).mp ha
    have hr : Continuous (fun q : ℝ × UnitOpen => R.value (q.1,a)) :=
      R.continuous_value.comp (continuous_fst.prodMk continuous_const)
    have hv : Continuous (fun q : ℝ × UnitOpen => (q.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    filter_upwards [hv.continuousAt.eventually_lt hr.continuousAt h] with q hq
    exact (R.level_lt_iff q.1 a q.2).mpr hq

lemma level_slope {x x' : ℝ} (h : x ≤ x') (v : UnitOpen) :
    l*(x'-x) ≤ R.level x' v - R.level x v ∧
    R.level x' v - R.level x v ≤ u*(x'-x) := by
  have h₁ := R.translate_lower x (R.level x v) (x'-x) (sub_nonneg.mpr h)
  have h₂ := R.translate_upper x (R.level x v) (x'-x) (sub_nonneg.mpr h)
  rw [R.value_level] at h₁ h₂
  have he : x + (x'-x) = x' := by ring
  rw [he] at h₁ h₂
  have hl := (R.le_level_iff x' (R.level x v + l*(x'-x)) v).mpr h₁
  have hu := (R.level_le_iff x' (R.level x v + u*(x'-x)) v).mpr h₂
  constructor <;> linarith

end Coordinate

lemma exists_zero_of_strongAnti {f : ℝ → ℝ} (hf : Continuous f) {d : ℝ}
    (hd : 0 < d) (hs : ∀ x x', x ≤ x' → f x' - f x ≤ -d*(x'-x)) :
    ∃ x, f x = 0 := by
  let t := (|f 0|+1)/d
  have ht : 0 < t := div_pos (by positivity) hd
  have htprod : d*t = |f 0|+1 := by dsimp [t]; field_simp
  have hleft := hs (-t) 0 (by linarith)
  have hright := hs 0 t ht.le
  have hzero : (0:ℝ) ∈ Set.Icc (f t) (f (-t)) := by
    constructor
    · have h := le_abs_self (f 0); nlinarith
    · have h := neg_abs_le (f 0); nlinarith
  exact intermediate_value_univ t (-t) hf hzero

variable {lA uA lB uB : ℝ} (A : Coordinate lA uA) (B : Coordinate lB uB)

noncomputable def levelDiff (v : UnitOpen × UnitOpen) (x : ℝ) : ℝ :=
  A.level x v.1 - B.level x v.2

lemma continuous_levelDiff : Continuous (fun p : (UnitOpen × UnitOpen) × ℝ =>
    levelDiff A B p.1 p.2) := by
  exact (A.continuous_level.comp (continuous_snd.prodMk continuous_fst.fst)).sub
    (B.continuous_level.comp (continuous_snd.prodMk continuous_fst.snd))

lemma levelDiff_decay (v : UnitOpen × UnitOpen) {x x' : ℝ} (h : x ≤ x') :
    levelDiff A B v x' - levelDiff A B v x ≤ -(lB-uA)*(x'-x) := by
  have ha := (A.level_slope h v.1).2
  have hb := (B.level_slope h v.2).1
  dsimp [levelDiff]
  nlinarith only [ha, hb]

lemma levelDiff_strictAnti (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    StrictAnti (levelDiff A B v) := by
  intro x x' h
  have hh := levelDiff_decay A B v h.le
  have hp : 0 < (lB-uA)*(x'-x) := mul_pos (sub_pos.mpr hgap) (sub_pos.mpr h)
  linarith

lemma exists_intersection (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    ∃ x, levelDiff A B v x = 0 := by
  exact exists_zero_of_strongAnti
    ((continuous_levelDiff A B).comp (continuous_const.prodMk continuous_id))
    (sub_pos.mpr hgap) (fun _ _ h => levelDiff_decay A B v h)

noncomputable def intersectionX (hgap : uA < lB) (v : UnitOpen × UnitOpen) : ℝ :=
  Classical.choose (exists_intersection A B hgap v)

lemma levelDiff_intersectionX (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    levelDiff A B v (intersectionX A B hgap v) = 0 :=
  Classical.choose_spec (exists_intersection A B hgap v)

lemma lt_intersectionX_iff (hgap : uA < lB) (v : UnitOpen × UnitOpen) (x : ℝ) :
    x < intersectionX A B hgap v ↔ 0 < levelDiff A B v x := by
  rw [← levelDiff_intersectionX A B hgap v]
  exact (levelDiff_strictAnti A B hgap v).lt_iff_gt.symm

lemma intersectionX_lt_iff (hgap : uA < lB) (v : UnitOpen × UnitOpen) (x : ℝ) :
    intersectionX A B hgap v < x ↔ levelDiff A B v x < 0 := by
  rw [← levelDiff_intersectionX A B hgap v]
  exact (levelDiff_strictAnti A B hgap v).lt_iff_gt.symm

lemma continuous_intersectionX (hgap : uA < lB) : Continuous (intersectionX A B hgap) := by
  refine continuous_iff_continuousAt.mpr fun v => tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    have h := (lt_intersectionX_iff A B hgap v a).mp ha
    have hc := (continuous_levelDiff A B).comp (continuous_id.prodMk (continuous_const : Continuous fun _ : UnitOpen × UnitOpen => a))
    filter_upwards [continuousAt_const.eventually_lt hc.continuousAt h] with w hw
    exact (lt_intersectionX_iff A B hgap w a).mpr hw
  · intro a ha
    have h := (intersectionX_lt_iff A B hgap v a).mp ha
    have hc := (continuous_levelDiff A B).comp (continuous_id.prodMk (continuous_const : Continuous fun _ : UnitOpen × UnitOpen => a))
    filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h] with w hw
    exact (intersectionX_lt_iff A B hgap w a).mpr hw

noncomputable def pairHomeomorph (hgap : uA < lB) :
    (ℝ × ℝ) ≃ₜ (UnitOpen × UnitOpen) where
  toFun p := (⟨A.value p,A.mem p⟩, ⟨B.value p,B.mem p⟩)
  invFun v := (intersectionX A B hgap v, A.level (intersectionX A B hgap v) v.1)
  left_inv p := by
    let v : UnitOpen × UnitOpen := (⟨A.value p,A.mem p⟩, ⟨B.value p,B.mem p⟩)
    have hz : levelDiff A B v p.1 = 0 := by
      dsimp [levelDiff,v]
      rw [A.level_value, B.level_value]
      ring
    have he : intersectionX A B hgap v = p.1 :=
      (levelDiff_strictAnti A B hgap v).injective
        ((levelDiff_intersectionX A B hgap v).trans hz.symm)
    change (intersectionX A B hgap v, A.level (intersectionX A B hgap v) v.1) = p
    rw [he]
    dsimp [v]
    rw [A.level_value]
  right_inv v := by
    have he : A.level (intersectionX A B hgap v) v.1 =
        B.level (intersectionX A B hgap v) v.2 :=
      sub_eq_zero.mp (levelDiff_intersectionX A B hgap v)
    apply Prod.ext <;> apply Subtype.ext
    · exact A.value_level _ _
    · change B.value (_, A.level _ v.1) = _
      rw [he, B.value_level]
  continuous_toFun := (A.continuous_value.subtype_mk _).prodMk (B.continuous_value.subtype_mk _)
  continuous_invFun := (continuous_intersectionX A B hgap).prodMk
    (A.continuous_level.comp ((continuous_intersectionX A B hgap).prodMk continuous_fst))

noncomputable def smoothed {m : ℕ} (g : Fin m → ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (∑ i, Real.sigmoid ((p.2 - g i p.1)/ε)) / m

lemma continuous_smoothed {m : ℕ} (g : Fin m → ℝ → ℝ) (ε : ℝ)
    (hg : ∀ i, Continuous (g i)) : Continuous (smoothed g ε) := by
  unfold smoothed
  fun_prop

lemma smoothed_mem {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) :
    smoothed g ε p ∈ Set.Ioo 0 1 := by
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hn : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0,hm⟩, Finset.mem_univ _⟩
  constructor
  · exact div_pos (Finset.sum_pos (fun i _ => Real.sigmoid_pos _) hn) hmR
  · apply (div_lt_iff₀ hmR).mpr
    have hs := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => Real.sigmoid ((p.2 - g i p.1)/ε)) (g := fun _ => (1:ℝ))
      (fun i _ => (Real.sigmoid_lt_one _).le)
      ⟨⟨0,hm⟩, Finset.mem_univ _, Real.sigmoid_lt_one _⟩
    simpa using hs

lemma strict_vertical_smoothed {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) : StrictMono (fun y => smoothed g ε (x,y)) := by
  intro y y' h
  apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr hm)
  apply Finset.sum_lt_sum
  · intro i _
    exact (Real.sigmoid_strictMono (div_lt_div_of_pos_right (sub_lt_sub_right h _) hε)).le
  · exact ⟨⟨0,hm⟩, Finset.mem_univ _,
      Real.sigmoid_strictMono (div_lt_div_of_pos_right (sub_lt_sub_right h _) hε)⟩

lemma onto_vertical_smoothed {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) (v : UnitOpen) :
    ∃ y, smoothed g ε (x,y) = v := by
  obtain ⟨t, ht⟩ : (v : ℝ) ∈ Set.range Real.sigmoid := by
    rw [Real.range_sigmoid]
    exact v.property
  let T : ℝ := ∑ i, |g i x + ε*t|
  have hT (i : Fin m) : |g i x+ε*t| ≤ T :=
    Finset.single_le_sum (fun j _ => abs_nonneg (g j x+ε*t)) (Finset.mem_univ i)
  have hlo (i : Fin m) : (-T - g i x)/ε ≤ t := by
    apply (div_le_iff₀ hε).mpr
    have h := (neg_abs_le (g i x+ε*t)).trans' (neg_le_neg (hT i))
    linarith
  have hhi (i : Fin m) : t ≤ (T - g i x)/ε := by
    apply (le_div_iff₀ hε).mpr
    have h := (le_abs_self (g i x+ε*t)).trans (hT i)
    linarith
  have hleft : smoothed g ε (x,-T) ≤ v := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hm)).mpr
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => Real.sigmoid_monotone (hlo i))
    simpa only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using h
  have hright : (v : ℝ) ≤ smoothed g ε (x,T) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hm)).mpr
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => Real.sigmoid_monotone (hhi i))
    simpa only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using h
  have hc : Continuous (fun y => smoothed g ε (x,y)) := by
    simp only [smoothed]
    fun_prop
  exact intermediate_value_univ (-T) T hc ⟨hleft,hright⟩

noncomputable def smoothedCoordinate {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    {ε l u : ℝ} (hε : 0 < ε) (hg : ∀ i, Continuous (g i))
    (hs : ∀ i x x', x ≤ x' → l*(x'-x) ≤ g i x'-g i x ∧ g i x'-g i x ≤ u*(x'-x)) :
    Coordinate l u where
  value := smoothed g ε
  continuous_value := continuous_smoothed g ε hg
  mem := smoothed_mem hm g ε
  strict_vertical := strict_vertical_smoothed hm g hε
  onto_vertical := onto_vertical_smoothed hm g hε
  translate_lower x y h hh := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
    apply Finset.sum_le_sum
    intro i _
    apply Real.sigmoid_monotone
    apply (div_le_div_iff_of_pos_right hε).mpr
    have he := (hs i x (x+h) (by linarith)).1
    dsimp
    linarith
  translate_upper x y h hh := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
    apply Finset.sum_le_sum
    intro i _
    apply Real.sigmoid_monotone
    apply (div_le_div_iff_of_pos_right hε).mpr
    have he := (hs i x (x+h) (by linarith)).2
    dsimp
    linarith

namespace Coordinate
variable {lR uR lS uS : ℝ} (R : Coordinate lR uR) (S : Coordinate lS uS)

lemma strictMono_along_level (hgap : uR < lS) (v : UnitOpen) :
    StrictMono (fun x => R.value (x,S.level x v)) := by
  intro x x' h
  have hh := R.translate_upper x (S.level x v) (x'-x) (sub_nonneg.mpr h.le)
  rw [show x+(x'-x) = x' by ring] at hh
  have hprod : uR*(x'-x) < lS*(x'-x) := mul_lt_mul_of_pos_right hgap (sub_pos.mpr h)
  have hs := (S.level_slope h.le v).1
  exact hh.trans_lt (R.strict_vertical x' (by linarith :
    S.level x v+uR*(x'-x) < S.level x' v))

lemma strictAnti_along_level (hgap : uS < lR) (v : UnitOpen) :
    StrictAnti (fun x => R.value (x,S.level x v)) := by
  intro x x' h
  have hh := R.translate_lower x (S.level x v) (x'-x) (sub_nonneg.mpr h.le)
  rw [show x+(x'-x) = x' by ring] at hh
  have hprod : uS*(x'-x) < lR*(x'-x) := mul_lt_mul_of_pos_right hgap (sub_pos.mpr h)
  have hs := (S.level_slope h.le v).2
  exact (R.strict_vertical x' (by linarith :
    S.level x' v < S.level x v+lR*(x'-x))).trans_le hh

end Coordinate

lemma value_pair_inverse_fst (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    A.value ((pairHomeomorph A B hgap).symm v) = v.1 :=
  congrArg (fun w : UnitOpen × UnitOpen => (w.1:ℝ)) ((pairHomeomorph A B hgap).apply_symm_apply v)

lemma value_pair_inverse_snd (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    B.value ((pairHomeomorph A B hgap).symm v) = v.2 :=
  congrArg (fun w : UnitOpen × UnitOpen => (w.2:ℝ)) ((pairHomeomorph A B hgap).apply_symm_apply v)

lemma pair_inverse_snd_levelA (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    ((pairHomeomorph A B hgap).symm v).2 = A.level ((pairHomeomorph A B hgap).symm v).1 v.1 := rfl

lemma pair_inverse_snd_levelB (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    ((pairHomeomorph A B hgap).symm v).2 = B.level ((pairHomeomorph A B hgap).symm v).1 v.2 := by
  apply (B.strict_vertical ((pairHomeomorph A B hgap).symm v).1).injective
  dsimp only
  rw [B.value_level]
  exact value_pair_inverse_snd A B hgap v

lemma inverseX_mono_left (hgap : uA < lB) (v : UnitOpen) :
    Monotone (fun u : UnitOpen => ((pairHomeomorph A B hgap).symm (u,v)).1) := by
  intro u u' huu
  apply (A.strictMono_along_level B hgap v).le_iff_le.mp
  have h₁ := value_pair_inverse_fst A B hgap (u,v)
  have h₂ := value_pair_inverse_fst A B hgap (u',v)
  conv_lhs at h₁ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u,v))]
  conv_lhs at h₂ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u',v))]
  rw [pair_inverse_snd_levelB] at h₁ h₂
  change A.value (_, B.level _ v) = (u:ℝ) at h₁
  change A.value (_, B.level _ v) = (u':ℝ) at h₂
  rw [h₁,h₂]
  exact huu

lemma inverseX_anti_right (hgap : uA < lB) (u : UnitOpen) :
    Antitone (fun v : UnitOpen => ((pairHomeomorph A B hgap).symm (u,v)).1) := by
  intro v v' hvv
  apply (B.strictAnti_along_level A hgap u).le_iff_ge.mp
  have h₁ := value_pair_inverse_snd A B hgap (u,v)
  have h₂ := value_pair_inverse_snd A B hgap (u,v')
  conv_lhs at h₁ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u,v))]
  conv_lhs at h₂ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u,v'))]
  rw [pair_inverse_snd_levelA] at h₁ h₂
  change B.value (_, A.level _ u) = (v:ℝ) at h₁
  change B.value (_, A.level _ u) = (v':ℝ) at h₂
  rw [h₁,h₂]
  exact hvv

noncomputable def inCoordinates {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (v : UnitOpen × UnitOpen) : ℝ :=
  C.value ((pairHomeomorph A B hgap).symm v)

lemma inCoordinates_eq_levelA {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (v : UnitOpen × UnitOpen) :
    inCoordinates A B hgap C v = C.value
      (((pairHomeomorph A B hgap).symm v).1,
       A.level ((pairHomeomorph A B hgap).symm v).1 v.1) := rfl

lemma inCoordinates_eq_levelB {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (v : UnitOpen × UnitOpen) :
    inCoordinates A B hgap C v = C.value
      (((pairHomeomorph A B hgap).symm v).1,
       B.level ((pairHomeomorph A B hgap).symm v).1 v.2) := by
  unfold inCoordinates
  conv_lhs => rw [← Prod.eta ((pairHomeomorph A B hgap).symm v)]
  rw [pair_inverse_snd_levelB]

lemma inCoordinates_monotone_left {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hCB : uC < lB) (v : UnitOpen) :
    Monotone (fun u : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro u u' h
  dsimp only
  rw [inCoordinates_eq_levelB, inCoordinates_eq_levelB]
  exact (C.strictMono_along_level B hCB v).monotone (inverseX_mono_left A B hgap v h)

lemma inCoordinates_antitone_left {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hBC : uB < lC) (v : UnitOpen) :
    Antitone (fun u : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro u u' h
  dsimp only
  rw [inCoordinates_eq_levelB, inCoordinates_eq_levelB]
  exact (C.strictAnti_along_level B hBC v).antitone (inverseX_mono_left A B hgap v h)

lemma inCoordinates_antitone_right {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hCA : uC < lA) (u : UnitOpen) :
    Antitone (fun v : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro v v' h
  dsimp only
  rw [inCoordinates_eq_levelA, inCoordinates_eq_levelA]
  exact (C.strictMono_along_level A hCA u).monotone (inverseX_anti_right A B hgap u h)

lemma inCoordinates_monotone_right {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hAC : uA < lC) (u : UnitOpen) :
    Monotone (fun v : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro v v' h
  dsimp only
  rw [inCoordinates_eq_levelA, inCoordinates_eq_levelA]
  exact (C.strictAnti_along_level A hAC u).antitone (inverseX_anti_right A B hgap u h)

end PlanarHalving.RankCoordinates

end OAI
