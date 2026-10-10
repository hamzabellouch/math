import Mathlib
import OAI.Probability.Ballisticity.Crossings.GaussianBadCutoff
import OAI.Probability.Ballisticity.Walk.WienerPathMaximal

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma physical_shrinking_subset_path_norm {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x y : Lattice d) (θ r n T : ℝ) (hr : 0 < r) (hn : 0 < n) (hT : 0 < T)
    (hgap : |signedCoordinate f (x-y)| = r) :
    {P : Path d × Path d | ∃ h ≤ ⌊T*n⌋₊, |physicalFirstHitGap ℓ f x y h P| ≤ r/2} ⊆
      {P | 1/4 ≤ ‖recordLinearPath ℓ f θ r n T (fun j => P.1 j-x)‖} ∪
      {P | 1/4 ≤ ‖recordLinearPath ℓ f θ r n T (fun j => P.2 j-y)‖} := by
  rintro P ⟨h,hh,hsmall⟩
  by_contra hno
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hno
  have hTn : 0 < T*n := mul_pos hT hn
  have hhh : (h:ℝ) ≤ T*n := (show (h:ℝ) ≤ (⌊T*n⌋₊:ℝ) by exact_mod_cast hh).trans (Nat.floor_le hTn.le)
  let s : unitInterval := ⟨(h:ℝ)/(T*n), div_nonneg (Nat.cast_nonneg _) hTn.le,
    (div_le_one hTn).mpr hhh⟩
  have hs : T*n*(s:ℝ) = h := by dsimp [s]; field_simp
  let A := recordLinearPath ℓ f θ r n T (fun j => P.1 j-x)
  let B := recordLinearPath ℓ f θ r n T (fun j => P.2 j-y)
  have hA : |A s| < 1/4 := by
    exact (A.norm_coe_le_norm s).trans_lt hno.1
  have hB : |B s| < 1/4 := by
    exact (B.norm_coe_le_norm s).trans_lt hno.2
  have hAe : A s = (signedCoordinate f (recordIndexPosition ℓ h (fun j => P.1 j-x))-(h:ℝ)*θ)/r :=
    heightPolygon_grid _ r n T hTn.le h s hs
  have hBe : B s = (signedCoordinate f (recordIndexPosition ℓ h (fun j => P.2 j-y))-(h:ℝ)*θ)/r :=
    heightPolygon_grid _ r n T hTn.le h s hs
  have he : physicalFirstHitGap ℓ f x y h P = signedCoordinate f (x-y)+r*(A s-B s) := by
    rw [hAe,hBe]
    dsimp only [physicalFirstHitGap, firstHitPairGap]
    field_simp
    ring
  have hab : |A s-B s| < 1/2 := (abs_sub _ _).trans_lt (by linarith)
  have hg : r ≤ |physicalFirstHitGap ℓ f x y h P| + r*|A s-B s| := by
    rw [← hgap]
    have ht := abs_sub (physicalFirstHitGap ℓ f x y h P) (r*(A s-B s))
    rw [he,add_sub_cancel_right,abs_mul,abs_of_pos hr] at ht
    rw [hgap] at ht ⊢
    simpa only [he] using ht
  nlinarith

theorem shared_shrinking_gaussian {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    (hgap : ∀ i, |signedCoordinate f (x i-y i)| = r i)
    {t : ℝ} (ht : 0 < t) :
    let ℓ := realPosition (step e)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ)
      (commonIncrementProcess ℓ f 0) (r i)
    ∀ᶠ i in atTop,
      (sharedConditionedPairLaw ν ℓ (x i) (y i)).real
        {P | ∃ h ≤ ⌊t*n i⌋₊, |physicalFirstHitGap ℓ f (x i) (y i) h P| ≤ r i/2} ≤
          8*Real.exp (-commonMeanWidth ν ℓ/(16*t)) := by
  let ℓ := realPosition (step e)
  let m := commonMeanWidth ν ℓ
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ)
    (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
  let F := fun i (P : Path d × Path d) => recordLinearPath ℓ f (θ i) (r i) (n i) t (fun j => P.1 j-x i)
  let G := fun i (P : Path d × Path d) => recordLinearPath ℓ f (θ i) (r i) (n i) t (fun j => P.2 j-y i)
  have hFm (i : ℕ) : Measurable (F i) := (measurable_recordLinearPath _ _ _ _ _ _).comp (by fun_prop)
  have hGm (i : ℕ) : Measurable (G i) := (measurable_recordLinearPath _ _ _ _ _ _).comp (by fun_prop)
  have hm : 0 < m := zero_lt_one.trans_le (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e)
    (signedHeight_projection e) (signedHeight_step_le e))
  obtain ⟨W,hW,hlim⟩ := shared_path_marginal_limits ν hue e f hef htrans r hr ht.le
  have hV : 0 < t/(2*m) := by positivity
  have hF := distribution_path_norm_limsup μ F hFm W (hlim x y hxy).1
    (t/(2*m)) hV hW (1/4) (by norm_num)
  have hG := distribution_path_norm_limsup μ G hGm W (hlim x y hxy).2
    (t/(2*m)) hV hW (1/4) (by norm_num)
  have he : -(1/4:ℝ)^2/(2*(t/(2*m))) = -m/(16*t) := by field_simp; ring
  rw [he] at hF hG
  let c := Real.exp (-m/(16*t))
  have hc : 0 < c := Real.exp_pos _
  have hFb : IsBoundedUnder (· ≤ ·) atTop (fun i => (μ i).real {P | 1/4 ≤ ‖F i P‖}) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun i =>
      (show (μ i).real {P | 1/4 ≤ ‖F i P‖} ≤ 1 from measureReal_le_one))
  have hGb : IsBoundedUnder (· ≤ ·) atTop (fun i => (μ i).real {P | 1/4 ≤ ‖G i P‖}) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun i =>
      (show (μ i).real {P | 1/4 ≤ ‖G i P‖} ≤ 1 from measureReal_le_one))
  have hFe := eventually_lt_of_limsup_lt (hF.trans_lt (show 2*c < 3*c by linarith)) hFb
  have hGe := eventually_lt_of_limsup_lt (hG.trans_lt (show 2*c < 3*c by linarith)) hGb
  filter_upwards [hFe,hGe] with i hi hj
  have hni : 0 < n i := recordFluctuationScale_pos ν hue e f hef htrans (hrpos i)
  have hs := physical_shrinking_subset_path_norm ℓ f (x i) (y i) (θ i) (r i) (n i) t
    (hrpos i) hni ht (hgap i)
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans (by
    change (μ i).real {P | 1/4 ≤ ‖F i P‖} + (μ i).real {P | 1/4 ≤ ‖G i P‖} ≤ 8*c
    linarith))

theorem shared_uniform_good_shrinking {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {t : ℝ} (ht : 0 < t) :
    let ℓ := realPosition (step e)
    let μ := independentConditionedPairLaw ν ℓ
    let n := fluctuationScale μ (commonIncrementProcess ℓ f 0)
    ∃ l ε R : ℝ, 0 < l ∧ l < 1 ∧ 0 < ε ∧ 0 < R ∧
      ∀ u : ℝ, R ≤ u → n u * μ.real {P | l*u < |commonIncrementProcess ℓ f 0 P|} ≤ ε →
      ∀ x y : Lattice d, signedHeight e x = signedHeight e y → |signedCoordinate f (x-y)| = u →
      (sharedConditionedPairLaw ν ℓ x y).real
        {P | ∃ h ≤ ⌊t*n u⌋₊, |physicalFirstHitGap ℓ f x y h P| ≤ u/2} ≤
          8*Real.exp (-commonMeanWidth ν ℓ/(16*t)) := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let S := commonIncrementProcess ℓ f 0
  let n := fluctuationScale μ S
  let P := fun u (x y : Lattice d) =>
    (sharedConditionedPairLaw ν ℓ x y).real
      {Q | ∃ h ≤ ⌊t*n u⌋₊, |physicalFirstHitGap ℓ f x y h Q| ≤ u/2} ≤
        8*Real.exp (-commonMeanWidth ν ℓ/(16*t))
  change ∃ l ε R : ℝ, 0<l ∧ l<1 ∧ 0<ε ∧ 0<R ∧ ∀ u : ℝ, R≤u →
    n u*μ.real {Q | l*u< |S Q|}≤ε → ∀ x y : Lattice d,
    signedHeight e x=signedHeight e y → |signedCoordinate f (x-y)|=u → P u x y
  by_contra hn
  let a := fun i : ℕ => 1/((i:ℝ)+2)
  have ha (i : ℕ) : 0<a i ∧ a i<1 := by
    dsimp [a]
    have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr (by linarith)
  have hex (i : ℕ) : ∃ u : ℝ, (i:ℝ)+1≤u ∧ n u*μ.real {Q | a i*u< |S Q|}≤a i ∧
      ∃ x y : Lattice d, signedHeight e x=signedHeight e y ∧ |signedCoordinate f (x-y)|=u ∧ ¬P u x y := by
    by_contra hc
    push Not at hc
    apply hn
    refine ⟨a i,a i,(i:ℝ)+1,(ha i).1,(ha i).2,(ha i).1,by positivity,?_⟩
    exact hc
  choose r hr htail x y hxy hgap hbad using hex
  have hrpos (i : ℕ) : 0<r i := (by positivity : (0:ℝ)<(i:ℝ)+1).trans_le (hr i)
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa [a,Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (tendsto_add_atTop_nat 2)
  have hgauss : IsGaussianSequence μ S r := by
    constructor
    · exact tendsto_atTop_mono hr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    · intro δ hδ
      apply squeeze_zero' (Eventually.of_forall fun i =>
        mul_nonneg (fluctuationScale_nonneg μ S _) measureReal_nonneg) _ ha0
      filter_upwards [ha0.eventually_lt_const hδ] with i hi
      have htail' : μ.real {Q | δ*r i< |S Q|} ≤ μ.real {Q | a i*r i< |S Q|} := by
        apply measureReal_mono _ (measure_ne_top _ _)
        intro Q hQ
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hi.le (hrpos i).le) hQ
      exact (mul_le_mul_of_nonneg_left htail' (fluctuationScale_nonneg μ S _)).trans (htail i)
  obtain ⟨i,hi⟩ := (shared_shrinking_gaussian ν hue e f hef htrans r hrpos hgauss x y hxy hgap ht).exists
  exact hbad i hi

end DirectionalTransience

end

end

end OAI
