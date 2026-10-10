import Mathlib
import OAI.Probability.Ballisticity.Estimates.DensityTransfer

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def coordinateProfile {d : ℕ} (e : Direction d) (f : Fin d)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) : Kernel D ℤ :=
  w.map (fun x => x.1 f)

instance coordinateProfile_finite {d : ℕ} (e : Direction d) (f : Fin d)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w] :
    IsFiniteKernel (coordinateProfile e f w) := by
  unfold coordinateProfile
  infer_instance

lemma coordinateProfile_apply {d : ℕ} (e : Direction d) (f : Fin d)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) (z : D) :
    coordinateProfile e f w z = (w z).map (fun x => x.1 f) :=
  Kernel.map_apply _ (measurable_of_countable _) _

lemma profile_statistic_nonpos {d : ℕ} (e : Direction d) (f : Fin d)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (htotal : ∀ z, w z Set.univ ≤ 1) (z : D) (R : ℤ) :
    Real.log (TailGrowth.statistic (coordinateProfile e f w z) R) ≤ 0 := by
  have hnon : 0 ≤ TailGrowth.statistic (coordinateProfile e f w z) R := by
    apply le_trans _ (TailGrowth.score_le_statistic _ R 0)
    exact le_min (measureReal_nonneg) (measureReal_nonneg)
  apply Real.log_nonpos hnon
  apply (TailGrowth.statistic_le_mass _ _).trans
  rw [coordinateProfile_apply,Measure.real,
    Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using htotal z)

lemma iterate_identDistrib {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {F : Ω → Y} (hF : Measurable F) (n : ℕ) :
    IdentDistrib (fun ω => F (T^[n] ω)) F μ μ := by
  refine ⟨(hF.comp (hT.iterate n).measurable).aemeasurable,hF.aemeasurable,?_⟩
  change Measure.map (F ∘ T^[n]) μ = _
  rw [←Measure.map_map hF (hT.iterate n).measurable, (hT.iterate n).map_eq]

structure StationaryProfileSystem {d : ℕ} (ν : Measure (Row d))
    (e : Direction d) (f : Fin d)
    (Ω D : Type) [MeasurableSpace Ω] [MeasurableSpace D]
    (μ : Measure Ω) (w : Kernel D (HorizontalLayer e)) where
  T : Ω → Ω
  preserving : MeasurePreserving T μ μ
  data : Ω → D
  measurable_data : Measurable data
  full : ∀ z x, 0 < (w z).real {x}
  total : ∀ z, w z Set.univ ≤ 1
  c : Ω → ℝ
  measurable_c : Measurable c
  nonneg_c : ∀ᵐ ω ∂μ, 0 ≤ c ω
  integrable_c : Integrable c μ
  h : Ω → ℕ
  measurable_h : Measurable h
  positive_h : ∀ᵐ ω ∂μ, 1 ≤ h ω
  integrable_log_h : Integrable (fun ω => Real.log (1+(h ω:ℝ))) μ
  field : ℕ → Ω → Environment d
  measurable_field : ∀ n, Measurable (field n)
  finite_entropy : ∀ n : ℕ, 0 < n →
    ∃ g : D × Environment d → ℝ,
      Measurable g ∧ (∀ z, 0 ≤ g z) ∧
      Integrable g ((μ.map data).prod (environmentLaw ν)) ∧
      (∫ z, g z ∂(μ.map data).prod (environmentLaw ν)) = 1 ∧
      Integrable (fun z => TailDecorrelation.entropyPlus (g z))
        ((μ.map data).prod (environmentLaw ν)) ∧
      μ.map (fun ω => (data ω,field n ω)) =
        ((μ.map data).prod (environmentLaw ν)).withDensity (fun z => ENNReal.ofReal (g z))
  offset : ℕ → Ω → ℤ
  update : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ,
    ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, c (T^[i] ω))) •
      (horizontalCoordinateKernel e f (∑ i ∈ Finset.range n, h (T^[i] ω)) (field n ω) ∘ₘ
        w (data ω)) ≤
      (coordinateProfile e f w (data (T^[n] ω))).map (fun x => x+offset n ω)

theorem stationary_profile_mean_nonpos {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (Ω D : Type) [MeasurableSpace Ω] [MeasurableSpace D]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (S : StationaryProfileSystem ν e f Ω D μ w) :
    (∫ ω, S.c ω ∂μ) ≤ 0 := by
  classical
  obtain ⟨A,hA,hpoint,M,hM,hdec⟩ := actual_profile_tail_decorrelation ν hue e f hef htrans
  let δ := μ.map S.data
  let : IsProbabilityMeasure δ :=
    (Measure.isProbabilityMeasure_map_iff S.measurable_data.aemeasurable).2 inferInstance
  let X : ℕ → ℕ → Ω → ℝ := fun n R ω =>
    Real.log (TailGrowth.statistic (coordinateProfile e f w (S.data (S.T^[n] ω))) (R:ℤ))
  have hXa (R : ℕ) : Measurable (fun ω => X 0 R ω) := by
    exact Real.measurable_log.comp ((TailGrowth.measurable_statistic
      (coordinateProfile e f w) (R:ℤ)).comp S.measurable_data)
  have hXid (n R : ℕ) : IdentDistrib (X 0 R) (X n R) μ μ := by
    exact (iterate_identDistrib μ S.preserving (hXa R) n).symm
  have hXnon (n R : ℕ) : ∀ᵐ ω ∂μ, X n R ω ≤ 0 :=
    Eventually.of_forall fun ω => profile_statistic_nonpos e f w S.total _ _
  have hpos : ∀ᵐ ω ∂μ, ∀ i, 1 ≤ S.h (S.T^[i] ω) :=
    ae_all_iff.mpr fun i => (S.preserving.iterate i).quasiMeasurePreserving.ae S.positive_h
  have hwindow (n : ℕ) (hn : 0 < n) : ∃ Z : ℕ → Ω → ℝ,
      (∀ R, Integrable (Z R) μ) ∧
      (∀ᶠ R in atTop, (∫ ω, Z R ω ∂μ) ≤ M+1) ∧
      (∀ R, ∀ᵐ ω ∂μ,
        (∑ i ∈ Finset.range n, S.c (S.T^[i] ω)) -
          (2*A)*Real.log (1+∑ i ∈ Finset.range n, (S.h (S.T^[i] ω):ℝ)) -
          Z R ω - Real.log 2 ≤ X n R ω-X 0 R ω) := by
    obtain ⟨g,hgm,hg0,hgi,hg1,hgH,hLaw⟩ := S.finite_entropy n hn
    obtain ⟨j,hj,hmax,hsect,hint,hmean,hlim⟩ := hdec D δ w S.full g hgm hg0 hgi hg1 hgH
    let κ := fun R : ℕ => profilePairKernel e f w (R:ℤ) (j R) (hj R)
    let F : ℕ → D × Environment d → ℝ := fun R z =>
      ∫ p : ZeroHeightPair e, outwardCanonicalExcess e (f,true) A p.1 z.2 ∂κ R z.1
    let V : Ω → D × Environment d := fun ω => (S.data ω,S.field n ω)
    have hVm : Measurable V := S.measurable_data.prodMk (S.measurable_field n)
    have hFi (R : ℕ) := TailDecorrelation.controlled_integral μ
      (δ.prod (environmentLaw ν)) hVm hgm hg0 hLaw (hint R)
    refine ⟨fun R ω => F R (V ω),fun R => (hFi R).1,?_,?_⟩
    · filter_upwards [hmean 1 (by norm_num)] with R hR
      exact ((hFi R).2).trans_le hR
    · intro R
      have hs := TailDecorrelation.controlled_ae μ (δ.prod (environmentLaw ν))
        hVm hgm hLaw (hsect R)
      have hp : ∀ᵐ ω ∂μ,
          ∀ x : Lattice d × Lattice d,
            dot (realPosition x.1) (realPosition (step e)) =
              dot (realPosition x.2) (realPosition (step e)) →
            ∀ t : ℕ, 0 < outwardKernelMass e (f,true) (t+1) x (S.field n ω) ∧
              -Real.log (outwardKernelMass e (f,true) (t+1) x (S.field n ω)) ≤
                2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e (f,true) A x (S.field n ω) := by
        have hpref := (Measure.quasiMeasurePreserving_snd (μ := δ) (ν := environmentLaw ν)).ae hpoint
        exact TailDecorrelation.controlled_ae μ (δ.prod (environmentLaw ν)) hVm hgm hLaw
          (hpref.mono fun _ hz _ => hz)
      filter_upwards [S.update n hn,hs,hp,hpos] with ω hupdate hsec hpω hhω
      have hH : 0 < ∑ i ∈ Finset.range n, S.h (S.T^[i] ω) := by
        exact lt_of_lt_of_le (Nat.succ_le_iff.mp (hhω 0))
          (Finset.single_le_sum (s := Finset.range n) (f := fun i => S.h (S.T^[i] ω))
            (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hn))
      have hsec' := (profilePairKernel_integrable e f hef w S.full (R:ℤ)
        (j R) (hj R) (S.data ω)
        (fun p : ZeroHeightPair e => outwardCanonicalExcess e (f,true) A p.1 (S.field n ω))).mp hsec
      have hgrowth := actual_profile_tail_growth e f hef A (S.field n ω) hpω
        (∑ i ∈ Finset.range n, S.h (S.T^[i] ω)) hH (w (S.data ω)) (S.full _)
        ((coordinateProfile e f w (S.data (S.T^[n] ω))).map (fun x => x+S.offset n ω))
        (R:ℤ) (j R (S.data ω)) (hmax (S.data ω) R)
        (∑ i ∈ Finset.range n, S.c (S.T^[i] ω)) hupdate hsec'
      rw [TailGrowth.statistic_translate] at hgrowth
      have heq := profilePairKernel_integral e f hef w S.full (R:ℤ)
        (j R) (hj R) (S.data ω)
        (fun p : ZeroHeightPair e => outwardCanonicalExcess e (f,true) A p.1 (S.field n ω))
      dsimp only [horizontalPair] at heq
      rw [←heq] at hgrowth
      simpa only [Nat.cast_sum, X, Function.iterate_zero, id_eq, coordinateProfile_apply,
        F,V,κ] using hgrowth
  choose W hWi hWmean hWgrowth using fun n => hwindow (n+1) (Nat.succ_pos n)
  let Z : ℕ → ℕ → Ω → ℝ := fun n => match n with
    | 0 => fun _ _ => 0
    | k+1 => W k
  have hZint (n R : ℕ) : Integrable (Z n R) μ := by
    cases n with
    | zero => exact integrable_const 0
    | succ k => exact hWi k R
  have hZmean (n : ℕ) : ∀ᶠ R in atTop, (∫ ω, Z n R ω ∂μ) ≤ M+1 := by
    cases n with
    | zero => exact Eventually.of_forall fun R => by simp only [Z,integral_zero]; linarith
    | succ k => exact hWmean k
  have hgrowth (n R : ℕ) : ∀ᵐ ω ∂μ,
      (∑ i ∈ Finset.range n, S.c (S.T^[i] ω)) -
        (2*A)*Real.log (1+∑ i ∈ Finset.range n, (S.h (S.T^[i] ω):ℝ)) -
        Z n R ω-Real.log 2 ≤ X n R ω-X 0 R ω := by
    cases n with
    | zero =>
      apply Eventually.of_forall
      intro ω
      simp only [Finset.range_zero,Finset.sum_empty,add_zero,Real.log_one,mul_zero,
        Z,zero_sub,sub_self]
      exact neg_nonpos.mpr (Real.log_nonneg (by norm_num))
    | succ k => exact hWgrowth k R
  apply stationary_tail_growth_obstruction μ (c := fun i ω => S.c (S.T^[i] ω))
    (h := fun i ω => (S.h (S.T^[i] ω):ℝ)) (X := X) (Z := Z)
    S.integrable_c (fun i => iterate_identDistrib μ S.preserving S.measurable_c i)
    (Eventually.of_forall fun ω i => Nat.cast_nonneg _) (fun i => ?_)
    S.integrable_log_h hXid hXnon hZint (2*A) (M+1) hZmean hgrowth
  exact iterate_identDistrib μ S.preserving ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp S.measurable_h) i

end DirectionalTransience

end

end OAI
