import OAI.Geometry.TranslativeCovering.SourcePatternTail

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace BodySelection
open Set Metric MeasureTheory Filter SourceParameters LocalizationRates PatternEnumeration SourceLocalization SphericalLaw
open scoped ENNReal Topology Classical
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def bad {n : ℕ} (R : ℝ) : Set (PoissonConfig.Config (Sphere n)) :=
  ⋃ P : Patterns n R,PatternTail.coverEvent (points P.val) a D
lemma union_bound {n : ℕ} [NeZero n] (e : Sphere n) {R t : ℝ} (ht : 0≤t)
    (hlist : (Fintype.card (LocalizationRounding.BoundedLists n (h n) (L n) (N n R)):ℝ)≤Real.exp (Real.exp ((1/10:ℝ)*n)))
    (hP : ∀ P : Patterns n R,(BodyVolume.law e a).real (PatternTail.coverEvent (points P.val) a D)≤t) :
    (BodyVolume.law e a).real (bad R) ≤ Real.exp (Real.exp ((1/10:ℝ)*n))*t := by
  have hc : (Fintype.card (Patterns n R):ℝ)≤Real.exp (Real.exp ((1/10:ℝ)*n)) :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hlist
  calc
    _ ≤ ∑ P : Patterns n R,(BodyVolume.law e a).real (PatternTail.coverEvent (points P.val) a D) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _P : Patterns n R,t := Finset.sum_le_sum (fun P _ => hP P)
    _ = (Fintype.card (Patterns n R):ℝ)*t := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc ht
lemma volume_lower {n : ℕ} [NeZero n] [Fact (2≤n)] (e : Sphere n)
    (hβ : 0<β n) (houter : (β n/a)^n≤3) :
    1/10 ≤ (BodyVolume.law e a).real {U | 2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U)} := by
  have ha := a_pos
  have hab : a≤b n := by dsimp [b]; nlinarith only [mul_nonneg ha.le (inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) n))]
  have hbβ : b n≤β n := by have he : 0≤RadialShell.η n := by unfold RadialShell.η; positivity
                           dsimp [β]; linarith only [he]
  have hvβ : volume (closedBall (0:Space n) (β n)) ≤ 3*volume (closedBall (0:Space n) a) := by
    rw [ball_scale ha hβ.le]
    gcongr
    simpa using ENNReal.ofReal_le_ofReal houter
  have hball : volume.real (closedBall (0:Space n) (b n))≤3*volume.real (closedBall (0:Space n) a) := by
    have hh := (measure_mono (closedBall_subset_closedBall hbβ)).trans hvβ
    have hf : 3*volume (closedBall (0:Space n) a)≠∞ := ENNReal.mul_ne_top (by norm_num) (isCompact_closedBall _ _).measure_ne_top
    have := ENNReal.toReal_mono hf hh
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,Measure.real] using this
  apply le_trans _ (BodyVolume.volume_probability e a_one hab (by norm_num [v]) hball)
  have he : (1:ℝ)/3<Real.exp (-1) := by
    rw [Real.exp_neg]
    have hexp : Real.exp 1<3 := Real.exp_one_lt_d9.trans (by norm_num)
    simpa only [one_div] using one_div_lt_one_div_of_lt (Real.exp_pos 1) hexp
  norm_num [v]
  norm_num [v] at he
  nlinarith only [he]

theorem uniform : ∃ c : ℝ,0<c ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
    ∀ [NeZero n] [Fact (2≤n)] (_e : Sphere n) (R : ℝ),
    1≤R → R≤c*(n:ℝ)*Real.log n → R≤(n:ℝ)^2 →
    ∃ U : PoissonConfig.Config (Sphere n),
      2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U) ∧
      U ∉ bad R := by
  obtain ⟨c,hc,n₁,hbound⟩ := SourcePatternTail.uniform
  have hdecay := CoveringGrowth.union_decay (α:=1/10) (β:=1/2) (C:=1) (by norm_num) (by norm_num) (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop,
      Real.exp (Real.exp ((1/10:ℝ)*n)-Real.exp ((1/2:ℝ)*n))<1/20 := by
    simpa only [one_mul] using hdecay.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20))
  have hd := LocalizationRates.dimension
  have hE := EntropyRates.list_rate
  obtain ⟨n₂,hn₂⟩ := eventually_atTop.mp (hevent.and (hd.and hE))
  refine ⟨c,hc,max n₁ n₂,?_⟩
  intro n hn _ _ e R hR hRc hRn
  have hdim := (hn₂ n (le_trans (le_max_right _ _) hn)).2.1
  have hlist := (hn₂ n (le_trans (le_max_right _ _) hn)).2.2 R (by linarith only [hR]) hRn
  have hP (P : Patterns n R) : (BodyVolume.law e a).real (PatternTail.coverEvent (points P.val) a D) ≤ Real.exp (-Real.exp ((1/2:ℝ)*n)) := by
    cases isEmpty_or_nonempty (Fin P.val.1.val) with
    | inl h =>
      have hem : PatternTail.coverEvent (points P.val) a D=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro U hU
        obtain ⟨i,_⟩ := hU 0 (mem_closedBall_self D_pos.le)
        exact isEmptyElim i
      rw [hem,measureReal_empty]
      positivity
    | inr h =>
      exact hbound n (le_trans (le_max_left _ _) hn) _ e _ R (by linarith only [hR]) hRc hRn (by simpa using (Nat.le_of_lt_succ P.val.1.isLt)) (pattern_good P)
  have hbad : (BodyVolume.law e a).real (bad R)<1/20 := by
    apply lt_of_le_of_lt (union_bound e (Real.exp_pos _).le hlist hP)
    rw [← Real.exp_add]
    exact (hn₂ n (le_trans (le_max_right _ _) hn)).1
  have hvol := volume_lower e hdim.2.2.1 hdim.2.2.2.1
  by_contra! hnone
  have hsub : {U : PoissonConfig.Config (Sphere n) | 2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U)} ⊆ bad R := by
    intro U hU
    exact hnone U hU
  have hh := measureReal_mono (μ:=BodyVolume.law e a) hsub (measure_ne_top _ _)
  linarith only [hbad,hvol,hh]
end BodySelection

end OAI
