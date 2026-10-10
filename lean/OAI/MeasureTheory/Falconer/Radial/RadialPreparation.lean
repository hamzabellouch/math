import OAI.MeasureTheory.Falconer.Graphs.Energy
import Mathlib.MeasureTheory.Measure.Support

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem exists_frostman_above_one (E : Set Plane) (hE : IsCompact E)
    (hd : 1 < dimH E) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ζ : ProbabilityMeasure Plane,
      (ζ : Measure Plane) Eᶜ = 0 ∧ NullSingletonClass (ζ : Measure Plane) ∧
      ∃ C : ℝ, 0 < C ∧ BallBound ζ (1+δ) C ∧
        ∀ u : ℝ, 0 < u → u < 1+δ → rieszEnergy ζ u < ∞ := by
  obtain ⟨a,ha1,ha⟩ := exists_between (lt_min hd (by norm_num : (1 : ℝ≥0∞) < 2))
  have ha2 := ha.trans_le (min_le_right _ _)
  have hatop : a ≠ ∞ := ne_of_lt (ha2.trans_le (le_top))
  have har1 : 1 < a.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by simp) hatop).mpr ha1
  have har2 : a.toReal < 2 := by
    simpa using (ENNReal.toReal_lt_toReal hatop (by simp)).mpr ha2
  have has : 0 < a.toNNReal := ENNReal.toNNReal_pos (zero_lt_one.trans ha1).ne' hatop
  obtain ⟨ζ,hζ,C,hC,hb⟩ := frostman_probability E hE has
    (by rw [ENNReal.coe_toNNReal hatop]; exact ha.trans_le (min_le_left _ _))
  have hball : BallBound ζ (1+(a.toReal-1)) C := by
    simpa only [BallBound, add_sub_cancel, ENNReal.toReal] using hb
  refine ⟨a.toReal-1,by linarith,by linarith,ζ,hζ,
    noAtoms_of_ball_bound ζ (by linarith) hball,C,hC,hball,?_⟩
  intro u hu hus
  exact rieszEnergy_lt_top_of_ball_bound ζ hu hus hball

theorem normalized_restriction_ball_bound (μ : ProbabilityMeasure Plane)
    {s C : ℝ} (hb : BallBound μ s C) (hC : 0 < C)
    (A : Set Plane) (hA : MeasurableSet A) (hpos : 0 < (μ : Measure Plane) A) :
    ∃ ν : ProbabilityMeasure Plane, (ν : Measure Plane) Aᶜ = 0 ∧
      ∃ D : ℝ, 0 < D ∧ BallBound ν s D ∧
        (ν : Measure Plane) = (ENNReal.ofReal (((μ : Measure Plane) A).toReal))⁻¹ •
          (μ : Measure Plane).restrict A := by
  let m := ((μ : Measure Plane) A).toReal
  have hm : 0 < m := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hmass : (μ : Measure Plane).restrict A univ = ENNReal.ofReal m := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  let ν₀ := ENNReal.ofReal m⁻¹ • (μ : Measure Plane).restrict A
  have hprob : IsProbabilityMeasure ν₀ := by
    constructor
    dsimp [ν₀]
    rw [hmass,
      ← ENNReal.ofReal_mul (by positivity),inv_mul_cancel₀ hm.ne',ENNReal.ofReal_one]
  let ν : ProbabilityMeasure Plane := ⟨ν₀,hprob⟩
  refine ⟨ν,?_,m⁻¹*C,mul_pos (inv_pos.mpr hm) hC,?_,?_⟩
  · simp [ν,ν₀,Measure.smul_apply,Measure.restrict_apply hA.compl]
  · intro x r hr
    change ν₀ (ball x r) ≤ _
    dsimp [ν₀]
    rw [Measure.restrict_apply measurableSet_ball]
    calc
      _ ≤ ENNReal.ofReal m⁻¹ * ENNReal.ofReal (C*r^s) :=
        mul_le_mul_right ((measure_mono inter_subset_left).trans (hb x r hr)) _
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  · change ENNReal.ofReal m⁻¹ • _ = (ENNReal.ofReal m)⁻¹ • _
    rw [ENNReal.ofReal_inv_of_pos hm]

theorem support_subset_carrier (μ : Measure Plane) {E : Set Plane}
    (hE : IsClosed E) (hμ : μ Eᶜ = 0) : μ.support ⊆ E :=
  μ.support_subset_of_isClosed hE hμ

theorem exists_distinct_support_points (μ : ProbabilityMeasure Plane)
    [NullSingletonClass (μ : Measure Plane)] :
    ∃ x ∈ (μ : Measure Plane).support, ∃ y ∈ (μ : Measure Plane).support, x ≠ y := by
  obtain ⟨x,hx⟩ := (μ : Measure Plane).nonempty_support (by
    intro h; have := congrArg (fun ν : Measure Plane => ν univ) h; simp at this)
  have hcomp : (μ : Measure Plane) {x}ᶜ = 1 := by
    rw [measure_compl (measurableSet_singleton x) (measure_ne_top _ _)]
    simp
  obtain ⟨y,hy,hyS⟩ := (μ : Measure Plane).nonempty_inter_support_of_pos
    (by rw [hcomp]; exact zero_lt_one)
  exact ⟨x,hx,y,hyS,fun he => hy (by simp [he])⟩

theorem exists_separated_compact_pieces (E : Set Plane) (hE : IsCompact E)
    (μ : ProbabilityMeasure Plane) (hμ : (μ : Measure Plane) Eᶜ = 0)
    [NullSingletonClass (μ : Measure Plane)] :
    ∃ A B : Set Plane, IsCompact A ∧ IsCompact B ∧ A ⊆ E ∧ B ⊆ E ∧
      0 < (μ : Measure Plane) A ∧ 0 < (μ : Measure Plane) B ∧
      ∃ d : ℝ, 0 < d ∧ ∀ a ∈ A, ∀ b ∈ B, d/2 ≤ dist a b ∧ dist a b ≤ 2*d := by
  obtain ⟨x,hx,y,hy,hxy⟩ := exists_distinct_support_points μ
  let d := dist x y
  have hd : 0 < d := dist_pos.mpr hxy
  let A := E ∩ closedBall x (d/1000)
  let B := E ∩ closedBall y (d/1000)
  have hpositive (z : Plane) (hz : z ∈ (μ : Measure Plane).support) :
      0 < (μ : Measure Plane) (E ∩ closedBall z (d/1000)) := by
    have hball := ((μ : Measure Plane).mem_support_iff_forall z).mp hz
      (ball z (d/1000)) (ball_mem_nhds z (by positivity))
    have hsub : ball z (d/1000) ⊆ (E ∩ closedBall z (d/1000)) ∪ Eᶜ := by
      intro w hw
      by_cases he : w ∈ E
      · exact Or.inl ⟨he,ball_subset_closedBall hw⟩
      · exact Or.inr he
    have hle := (measure_mono hsub).trans (measure_union_le _ _ (μ := (μ : Measure Plane)))
    rw [hμ,add_zero] at hle
    exact hball.trans_le hle
  refine ⟨A,B,hE.inter_right isClosed_closedBall,hE.inter_right isClosed_closedBall,
    inter_subset_left,inter_subset_left,hpositive x hx,hpositive y hy,d,hd,?_⟩
  intro a ha b hb
  have hax : dist a x ≤ d/1000 := ha.2
  have hby : dist b y ≤ d/1000 := hb.2
  have hupper := dist_triangle4 a x y b
  have hlower := dist_triangle4 x a b y
  rw [dist_comm y b] at hupper
  rw [dist_comm x a] at hlower
  dsimp [d] at hd hax hby ⊢
  constructor <;> linarith

theorem radial_parameters {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 < 1+δ/2 ∧ 1+δ/2 < 2 ∧ 1 < 1+δ/8 ∧ 1+δ/8 < 2 ∧
      0 < 1-δ/4 ∧
      (1+δ/8)*(2-(1+δ/2)) < 1-δ/4 ∧
      1-δ/4 < 2-(1+δ/8) ∧ 1+δ/2 < 1+δ ∧ 1-δ/4 < 1+δ := by
  constructor <;> (try constructor) <;> (try constructor) <;>
    (try constructor) <;> (try constructor) <;> (try constructor) <;>
    (try constructor) <;> (try constructor) <;> nlinarith

theorem exists_separated_frostman_pair (E : Set Plane) (hE : IsCompact E)
    (hd : 1 < dimH E) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ μ ν : ProbabilityMeasure Plane,
      IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
      (μ : Measure Plane).support ⊆ E ∧ (ν : Measure Plane).support ⊆ E ∧
      ∃ C d : ℝ, 0 < C ∧ 0 < d ∧ BallBound μ (1+δ) C ∧ BallBound ν (1+δ) C ∧
        (∀ x ∈ (μ : Measure Plane).support, ∀ y ∈ (ν : Measure Plane).support,
          d/2 ≤ dist x y ∧ dist x y ≤ 2*d) ∧
        (∀ u : ℝ, 0 < u → u < 1+δ →
          rieszEnergy μ u < ∞ ∧ rieszEnergy ν u < ∞) := by
  obtain ⟨δ,hδ,hδ1,ζ,hζ,hna,C,hC,hball,_⟩ := exists_frostman_above_one E hE hd
  let := hna
  obtain ⟨A,B,hA,hB,hAE,hBE,hAp,hBp,d,hdp,hsep⟩ :=
    exists_separated_compact_pieces E hE ζ hζ
  obtain ⟨μ,hμ,Cμ,hCμ,hballμ,_⟩ := normalized_restriction_ball_bound ζ hball hC A hA.measurableSet hAp
  obtain ⟨ν,hν,Cν,_,hballν,_⟩ := normalized_restriction_ball_bound ζ hball hC B hB.measurableSet hBp
  have hsμ := support_subset_carrier μ hA.isClosed hμ
  have hsν := support_subset_carrier ν hB.isClosed hν
  have hmC : BallBound μ (1+δ) (max Cμ Cν) := by
    intro x r hr
    exact (hballμ x r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hnC : BallBound ν (1+δ) (max Cμ Cν) := by
    intro x r hr
    exact (hballν x r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  refine ⟨δ,hδ,hδ1,μ,ν,hA.of_isClosed_subset Measure.isClosed_support hsμ,
    hB.of_isClosed_subset Measure.isClosed_support hsν,hsμ.trans hAE,hsν.trans hBE,
    max Cμ Cν,d,hCμ.trans_le (le_max_left _ _),hdp,hmC,hnC,
    fun x hx y hy => hsep x (hsμ hx) y (hsν hy),?_⟩
  intro u hu hus
  exact ⟨rieszEnergy_lt_top_of_ball_bound μ hu hus hmC,
    rieszEnergy_lt_top_of_ball_bound ν hu hus hnC⟩

end PlanarFalconer

end OAI
