import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Components.SliceRectangleNonsingular

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoundedSubadditive

namespace ContinuousBirkhoffCode

lemma measurableSet_atom {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {T S : X → X} {μ : Measure X} [IsFiniteMeasure μ]
    (C : ContinuousBirkhoffCode T S μ) (c : ℕ → ℝ) :
    MeasurableSet {x | C.value x=c} := measurableSet_eq_fun C.measurable measurable_const
lemma invariant_atom {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {T S : X → X} {μ : Measure X} [IsFiniteMeasure μ]
    (C : ContinuousBirkhoffCode T S μ) (c : ℕ → ℝ) :
    T ⁻¹' {x | C.value x=c}={x | C.value x=c} := by
  ext x
  simp only [mem_preimage,mem_ofPred_eq,C.invariant]

lemma integral_on_subset_atom {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {T S : X → X} {μ : Measure X} [IsFiniteMeasure μ]
    (C : ContinuousBirkhoffCode T S μ) (c : ℕ → ℝ)
    {A : Set X} (hA : MeasurableSet A) (hTA : T ⁻¹' A=A) (hAc : A⊆{x | C.value x=c}) (j : ℕ) :
    ∫ x in A,C.observation j x ∂μ=(μ A).toReal*c j := by
  rw [←C.integral A hA hTA j]
  have he : (fun x => C.value x j)=ᵐ[μ.restrict A] (fun _ => c j) :=
    (ae_restrict_mem hA).mono fun x hx => congrFun (hAc hx) j
  rw [integral_congr_ae he,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {T S : X → X} {μ : Measure X} [IsFiniteMeasure μ]

theorem ergodic_atom (C : ContinuousBirkhoffCode T S μ) (hT : MeasurePreserving T μ μ)
    {c : ℕ → ℝ} (hc : 0<μ {x | C.value x=c}) :
    Ergodic T ((μ {x | C.value x=c})⁻¹ • μ.restrict {x | C.value x=c}) := by
  let E := {x | C.value x=c}
  have hE : MeasurableSet E := C.measurableSet_atom c
  have hTE : T ⁻¹' E=E := C.invariant_atom c
  have hET : MeasurePreserving T (μ.restrict E) (μ.restrict E) := by
    simpa only [hTE] using hT.restrict_preimage hE
  have hEr : (μ E).toReal≠0 := ne_of_gt (ENNReal.toReal_pos hc.ne' (measure_ne_top μ E))
  let ν := (μ E)⁻¹ • μ.restrict E
  have hν : IsProbabilityMeasure ν := ⟨by
    dsimp only [ν]
    rw [Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hc.ne' (measure_ne_top μ E)⟩
  let := hν
  refine ⟨hET.smul_measure _,?_⟩
  constructor
  intro A hA hTA
  by_cases hzero : μ (A∩E)=0
  · apply eventuallyEmptyOrUniv_iff'.mpr
    left
    have hz : ν A=0 := by
      dsimp only [ν]
      rw [Measure.smul_apply,Measure.restrict_apply hA,hzero,smul_zero]
    change A =ᵐ[ν] (∅ : Set X)
    simpa only [ae_eq_empty] using hz
  · have hAE : MeasurableSet (A∩E) := hA.inter hE
    have hTAE : T ⁻¹' (A∩E)=A∩E := by rw [preimage_inter,hTA,hTE]
    let η := (μ (A∩E))⁻¹ • μ.restrict (A∩E)
    have hη : IsProbabilityMeasure η := ⟨by
      dsimp only [η]
      rw [Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
      exact ENNReal.inv_mul_cancel hzero (measure_ne_top μ _)⟩
    let := hη
    have hiE (j : ℕ) : (∫ x,C.observation j x ∂ν)=c j := by
      dsimp only [ν]
      rw [integral_smul_measure,C.integral_on_subset_atom c hE hTE Subset.rfl j,
        ENNReal.toReal_inv,smul_eq_mul,←mul_assoc,inv_mul_cancel₀ hEr,one_mul]
    have hiAE (j : ℕ) : (∫ x,C.observation j x ∂η)=c j := by
      dsimp only [η]
      have hr : (μ (A∩E)).toReal≠0 := ne_of_gt (ENNReal.toReal_pos hzero (measure_ne_top μ _))
      rw [integral_smul_measure,C.integral_on_subset_atom c hAE hTAE inter_subset_right j,
        ENNReal.toReal_inv,smul_eq_mul,←mul_assoc,inv_mul_cancel₀ hr,one_mul]
    have hην : η=ν := measure_eq_of_dense_continuous_integrals C.dense (fun j => (hiAE j).trans (hiE j).symm)
    have hz : ν Aᶜ=0 := by
      rw [←hην]
      dsimp only [η]
      rw [Measure.smul_apply,Measure.restrict_apply hA.compl]
      have he : Aᶜ∩(A∩E)=∅ := by ext x; simp only [mem_inter_iff,mem_compl_iff,mem_empty_iff_false]; tauto
      rw [he,measure_empty,smul_zero]
    apply eventuallyEmptyOrUniv_iff'.mpr
    right
    change A =ᵐ[ν] univ
    simpa only [ae_eq_univ] using hz

end ContinuousBirkhoffCode
end BoundedSubadditive

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable BoundedSubadditive
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B} (R : ReversibleGraphRectangle F)
noncomputable def torusPoint (p : B.coordinateCarrier×B.coordinateCarrier) : Torus := complexProjection (B.chart (R.point p))
lemma stable_representation (p : B.coordinateCarrier×B.coordinateCarrier) :
    B.chart (R.point p)=fineStableCurve k χ B.ε B.δ B.δ_pos B.contraction (B.label p.1)
      (B.regular (B.label p.1) (B.label p.1).property) (F.stableParameter (B.label p.1) (R.point p).1) := by
  calc
    B.chart (R.point p)=B.chart ((R.point p).1,F.G (B.label p.1) (R.point p).1) := congrArg B.chart (Prod.ext rfl (R.stable p))
    _ = _ := F.stable_representation _ _ ((R.x_bound p).trans (by linarith [B.ρ_small,B.r_pos]))
lemma unstable_representation (p : B.coordinateCarrier×B.coordinateCarrier) :
    B.chart (R.point p)=fineUnstableCurve k χ B.ε B.δ B.δ_pos B.contraction (B.label p.2)
      (B.reversed (B.label p.2) (B.label p.2).property) (F.unstableParameter (B.label p.2) (R.point p).2) := by
  calc
    B.chart (R.point p)=B.chart (F.U (B.label p.2) (R.point p).2,(R.point p).2) := congrArg B.chart (Prod.ext (R.unstable p) rfl)
    _ = _ := F.unstable_representation _ _ ((R.y_bound p).trans (by linarith [B.ρ_reverse,B.ρ_pos]))
lemma torus_nonsingular : QuasiMeasurePreserving R.torusPoint ((volume : Measure B.coordinateCarrier).prod volume) area :=
  complexProjection_quasiMeasurePreserving.comp (B.chart_quasiMeasurePreserving.comp R.nonsingular)
lemma spectrum_positive {p : B.coordinateCarrier×B.coordinateCarrier} {l : ℝ}
    (hl : LyapunovSpectrumAt k (R.torusPoint p) l) : 0<l := by
  apply fineStableCurve_spectrum_positive k χ B.ε B.δ B.δ_pos B.contraction (B.label p.1)
    (B.regular (B.label p.1) (B.label p.1).property)
    (s := F.stableParameter (B.label p.1) (R.point p).1)
    (lt_of_le_of_lt (F.stable_bound _ _) (by linarith [B.r_small]))
  simpa only [torusPoint,R.stable_representation] using hl
end ReversibleGraphRectangle

theorem actual_rectangle_hopf_atom {k χ : ℝ} (hk : 0≤k) {B : ReversibleRectangleBlock k χ}
    {F : ReversibleGraphFamilies B} (R : ReversibleGraphRectangle F)
    (C : ContinuousBirkhoffCode (standardMap k) (inverseMap k) area) :
    ∃ c : ℕ → ℝ,0<area ({z | C.value z=c}∩{z | 0<standardLyapunov k hk z}) := by
  let ν : Measure B.coordinateCarrier := ((volume : Measure B.coordinateCarrier) univ)⁻¹ • volume
  have hmpos : 0<(volume : Measure B.coordinateCarrier) univ := by
    rw [B.volume_coordinate_univ]
    exact B.positive_coordinateCarrier
  let _ : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := B.finite_coordinate_volume
  have hν : IsProbabilityMeasure ν := ⟨by
    dsimp only [ν]
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmpos.ne' (measure_ne_top _ _)⟩
  let _ := hν
  have hνac : ν≪(volume : Measure B.coordinateCarrier) := smul_absolutelyContinuous
  have hπ : QuasiMeasurePreserving R.torusPoint (ν.prod ν) area := R.torus_nonsingular.mono_left (hνac.prod hνac)
  let P (z : Torus) : Prop := (∀ j : ℕ,
      Tendsto (fun n : ℕ => birkhoffSum (standardMap k) (C.observation j) n z/(n : ℝ)) atTop (𝓝 (C.value z j)) ∧
      Tendsto (fun n : ℕ => birkhoffSum (inverseMap k) (C.observation j) n z/(n : ℝ)) atTop (𝓝 (C.value z j))) ∧
    LyapunovSpectrumAt k z (standardLyapunov k hk z)
  have hP : ∀ᵐ z ∂area,P z := C.generic.and (ae_standardLyapunov_spectrum k hk)
  have hrow (a b b' : B.coordinateCarrier) (ha : P (R.torusPoint (a,b))) (hb : P (R.torusPoint (a,b'))) :
      C.value (R.torusPoint (a,b))=C.value (R.torusPoint (a,b')) := by
    funext j
    apply fineStableCurve_birkhoff_eq k χ B.ε B.δ B.δ_pos B.contraction (B.label a)
      (B.regular (B.label a) (B.label a).property)
      (s := F.stableParameter (B.label a) (R.point (a,b)).1)
      (t := F.stableParameter (B.label a) (R.point (a,b')).1)
      ((F.stable_bound _ _).trans (by linarith [B.r_small]))
      ((F.stable_bound _ _).trans (by linarith [B.r_small])) (C.observation j)
    · simpa only [ReversibleGraphRectangle.torusPoint,R.stable_representation] using (ha.1 j).1
    · simpa only [ReversibleGraphRectangle.torusPoint,R.stable_representation] using (hb.1 j).1
  have hcol (a a' b : B.coordinateCarrier) (ha : P (R.torusPoint (a,b))) (hb : P (R.torusPoint (a',b))) :
      C.value (R.torusPoint (a,b))=C.value (R.torusPoint (a',b)) := by
    funext j
    apply fineUnstableCurve_birkhoff_eq k χ B.ε B.δ B.δ_pos B.contraction (B.label b)
      (B.reversed (B.label b) (B.label b).property)
      (s := F.unstableParameter (B.label b) (R.point (a,b)).2)
      (t := F.unstableParameter (B.label b) (R.point (a',b)).2)
      ((F.unstable_bound _ _).trans (by linarith [B.r'_small]))
      ((F.unstable_bound _ _).trans (by linarith [B.r'_small])) (C.observation j)
    · simpa only [ReversibleGraphRectangle.torusPoint,R.unstable_representation] using (ha.1 j).2
    · simpa only [ReversibleGraphRectangle.torusPoint,R.unstable_representation] using (hb.1 j).2
  obtain ⟨c,hc⟩ := ae_constant_of_product_rows_columns (F := fun p => C.value (R.torusPoint p)) (hπ.ae hP) hrow hcol
  refine ⟨c,?_⟩
  by_contra hn
  have hz : area ({z | C.value z=c}∩{z | 0<standardLyapunov k hk z})=0 := le_antisymm (not_lt.mp hn) (bot_le)
  have he : ∀ᵐ z ∂area,z∉({z | C.value z=c}∩{z | 0<standardLyapunov k hk z}) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hz
  obtain ⟨p,hpc,hpP,hpn⟩ := (hc.and ((hπ.ae hP).and (hπ.ae he))).exists
  exact hpn ⟨hpc,R.spectrum_positive hpP.2⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open BoundedSubadditive
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

lemma row_asymptotic (a b b' : B.coordinateCarrier) :
    Tendsto (fun n : ℕ => dist ((standardMap k)^[n] (R.torusPoint (a,b)))
      ((standardMap k)^[n] (R.torusPoint (a,b')))) atTop (𝓝 0) := by
  have h := fineStableCurve_asymptotic k χ B.ε B.δ B.δ_pos B.contraction (B.label a)
    (B.regular (B.label a) (B.label a).property)
    ((F.stable_bound (B.label a) (R.point (a,b)).1).trans (by linarith [B.r_small]))
    ((F.stable_bound (B.label a) (R.point (a,b')).1).trans (by linarith [B.r_small]))
  simpa only [torusPoint,R.stable_representation] using h

lemma column_asymptotic (a a' b : B.coordinateCarrier) :
    Tendsto (fun n : ℕ => dist ((inverseMap k)^[n] (R.torusPoint (a,b)))
      ((inverseMap k)^[n] (R.torusPoint (a',b)))) atTop (𝓝 0) := by
  have h := fineUnstableCurve_asymptotic k χ B.ε B.δ B.δ_pos B.contraction (B.label b)
    (B.reversed (B.label b) (B.label b).property)
    ((F.unstable_bound (B.label b) (R.point (a,b)).2).trans (by linarith [B.r'_small]))
    ((F.unstable_bound (B.label b) (R.point (a',b)).2).trans (by linarith [B.r'_small]))
  simpa only [torusPoint,R.unstable_representation] using h
end ReversibleGraphRectangle

lemma asymptotic_iterate {X : Type*} [PseudoMetricSpace X] {T : X → X} {x y : X}
    (h : Tendsto (fun n : ℕ => dist (T^[n] x) (T^[n] y)) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => dist ((T^[m])^[n] x) ((T^[m])^[n] y)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => m*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ m*n; nlinarith) tendsto_id
  simpa only [Function.comp_def,Function.iterate_mul] using h.comp ht

theorem exists_powerBirkhoffCodes (k : ℝ) :
    Nonempty (∀ m : ℕ,ContinuousBirkhoffCode ((standardMap k)^[m+1]) ((inverseMap k)^[m+1]) area) := by
  have h (m : ℕ) := exists_continuousBirkhoffCode ((measurePreserving_standardMap k).iterate (m+1))
    ((measurePreserving_inverseMap k).iterate (m+1))
    ((show Function.LeftInverse (inverseMap k) (standardMap k) from inverseMap_standardMap k).iterate (m+1))
    ((show Function.LeftInverse (standardMap k) (inverseMap k) from standardMap_inverseMap k).iterate (m+1))
  exact ⟨fun m => Classical.choice (h m)⟩

theorem actual_rectangle_all_powers_atom {k χ : ℝ} (hk : 0≤k) {B : ReversibleRectangleBlock k χ}
    {F : ReversibleGraphFamilies B} (R : ReversibleGraphRectangle F)
    (C : ∀ m : ℕ,ContinuousBirkhoffCode ((standardMap k)^[m+1]) ((inverseMap k)^[m+1]) area) :
    ∃ c : ℕ → ℕ → ℝ,0<area ({z | ∀ m,(C m).value z=c m}∩{z | 0<standardLyapunov k hk z}) := by
  let ν : Measure B.coordinateCarrier := ((volume : Measure B.coordinateCarrier) univ)⁻¹ • volume
  have hmpos : 0<(volume : Measure B.coordinateCarrier) univ := by
    rw [B.volume_coordinate_univ]
    exact B.positive_coordinateCarrier
  let _ : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := B.finite_coordinate_volume
  have hν : IsProbabilityMeasure ν := ⟨by
    dsimp only [ν]
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmpos.ne' (measure_ne_top _ _)⟩
  let _ := hν
  have hνac : ν≪(volume : Measure B.coordinateCarrier) := smul_absolutelyContinuous
  have hπ := R.torus_nonsingular.mono_left (hνac.prod hνac)
  let P (z : Torus) : Prop := (∀ m j : ℕ,
      Tendsto (fun n : ℕ => birkhoffSum ((standardMap k)^[m+1]) ((C m).observation j) n z/(n : ℝ)) atTop (𝓝 ((C m).value z j)) ∧
      Tendsto (fun n : ℕ => birkhoffSum ((inverseMap k)^[m+1]) ((C m).observation j) n z/(n : ℝ)) atTop (𝓝 ((C m).value z j))) ∧
    LyapunovSpectrumAt k z (standardLyapunov k hk z)
  have hP : ∀ᵐ z ∂area,P z := (ae_all_iff.mpr (fun m => (C m).generic)).and (ae_standardLyapunov_spectrum k hk)
  have hrow (a b b' : B.coordinateCarrier) (ha : P (R.torusPoint (a,b))) (hb : P (R.torusPoint (a,b'))) :
      (fun m => (C m).value (R.torusPoint (a,b)))=(fun m => (C m).value (R.torusPoint (a,b'))) := by
    funext m j
    exact birkhoff_limit_eq_of_asymptotic (CompactSpace.uniformContinuous_of_continuous ((C m).observation j).continuous)
      (asymptotic_iterate (R.row_asymptotic a b b') (Nat.succ_pos m)) (ha.1 m j).1 (hb.1 m j).1
  have hcol (a a' b : B.coordinateCarrier) (ha : P (R.torusPoint (a,b))) (hb : P (R.torusPoint (a',b))) :
      (fun m => (C m).value (R.torusPoint (a,b)))=(fun m => (C m).value (R.torusPoint (a',b))) := by
    funext m j
    exact birkhoff_limit_eq_of_asymptotic (CompactSpace.uniformContinuous_of_continuous ((C m).observation j).continuous)
      (asymptotic_iterate (R.column_asymptotic a a' b) (Nat.succ_pos m)) (ha.1 m j).2 (hb.1 m j).2
  obtain ⟨c,hc⟩ := ae_constant_of_product_rows_columns
    (F := fun p => fun m => (C m).value (R.torusPoint p)) (hπ.ae hP) hrow hcol
  refine ⟨c,?_⟩
  by_contra hn
  have hz : area ({z | ∀ m,(C m).value z=c m}∩{z | 0<standardLyapunov k hk z})=0 := le_antisymm (not_lt.mp hn) bot_le
  have he : ∀ᵐ z ∂area,z∉({z | ∀ m,(C m).value z=c m}∩{z | 0<standardLyapunov k hk z}) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hz
  obtain ⟨p,hpc,hpP,hpn⟩ := (hc.and ((hπ.ae hP).and (hπ.ae he))).exists
  exact hpn ⟨fun m => congrFun hpc m,R.spectrum_positive hpP.2⟩

end StandardMapEntropy

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace AEPeriod
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def setoid : Setoid (Set X) where
  r A B := A =ᵐ[μ] B
  iseqv := ⟨fun _ => EventuallyEq.rfl,fun h => h.symm,fun h h' => h.trans h'⟩

abbrev Class := Quotient (setoid μ)
def ofSet (A : Set X) : Class μ := Quotient.mk _ A
lemma ofSet_eq_iff (A B : Set X) : ofSet μ A=ofSet μ B ↔ A =ᵐ[μ] B := Quotient.eq

variable {μ} {T : X → X}
def act (hT : QuasiMeasurePreserving T μ μ) : Class μ → Class μ :=
  Quotient.map (fun A => T ⁻¹' A) (fun _ _ h => hT.preimage_ae_eq h)

lemma act_ofSet (hT : QuasiMeasurePreserving T μ μ) (A : Set X) :
    act hT (ofSet μ A)=ofSet μ (T ⁻¹' A) := rfl
lemma iterate_act (hT : QuasiMeasurePreserving T μ μ) (A : Set X) (n : ℕ) :
    (act hT)^[n] (ofSet μ A)=ofSet μ ((T^[n]) ⁻¹' A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,act_ofSet]
    congr 1

lemma periodic_iff (hT : QuasiMeasurePreserving T μ μ) (A : Set X) (n : ℕ) :
    Function.IsPeriodicPt (act hT) n (ofSet μ A) ↔ (T^[n]) ⁻¹' A =ᵐ[μ] A := by
  change (act hT)^[n] (ofSet μ A)=ofSet μ A ↔ _
  rw [iterate_act,ofSet_eq_iff]

lemma period_pos (hT : QuasiMeasurePreserving T μ μ) {A : Set X} {n : ℕ}
    (hn : 0 < n) (hinv : (T^[n]) ⁻¹' A =ᵐ[μ] A) :
    0<Function.minimalPeriod (act hT) (ofSet μ A) :=
  ((periodic_iff hT A n).mpr hinv).minimalPeriod_pos hn

lemma period_dvd (hT : QuasiMeasurePreserving T μ μ) {A : Set X} {n : ℕ}
    (hinv : (T^[n]) ⁻¹' A =ᵐ[μ] A) : Function.minimalPeriod (act hT) (ofSet μ A) ∣ n :=
  ((periodic_iff hT A n).mpr hinv).minimalPeriod_dvd

lemma period_preimage (hT : QuasiMeasurePreserving T μ μ) (A : Set X) :
    (T^[Function.minimalPeriod (act hT) (ofSet μ A)]) ⁻¹' A =ᵐ[μ] A :=
  (periodic_iff hT A _).mp (Function.isPeriodicPt_minimalPeriod _ _)

lemma preimage_mod (hT : QuasiMeasurePreserving T μ μ) (A : Set X) (j : ℕ) :
    (T^[j%Function.minimalPeriod (act hT) (ofSet μ A)]) ⁻¹' A =ᵐ[μ] (T^[j]) ⁻¹' A := by
  apply (ofSet_eq_iff μ _ _).mp
  rw [←iterate_act,←iterate_act]
  exact Function.iterate_mod_minimalPeriod_eq

lemma preimage_ne (hT : QuasiMeasurePreserving T μ μ) (A : Set X) {i j : ℕ}
    (hi : i<Function.minimalPeriod (act hT) (ofSet μ A))
    (hj : j<Function.minimalPeriod (act hT) (ofSet μ A)) (hij : i≠j) :
    ¬ ((T^[i]) ⁻¹' A =ᵐ[μ] (T^[j]) ⁻¹' A) := by
  intro he
  apply hij
  apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp
  rw [iterate_act,iterate_act]
  exact (ofSet_eq_iff μ _ _).mpr he

end AEPeriod

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {T : X → X} {A B : Set X}

lemma ergodic_restrict_of_normalized [IsFiniteMeasure μ] (hA : 0<μ A)
    (h : Ergodic T ((μ A)⁻¹ • μ.restrict A)) : Ergodic T (μ.restrict A) := by
  have hh := h.smul_measure (μ A)
  simpa only [smul_smul,ENNReal.mul_inv_cancel hA.ne' (measure_ne_top μ A),one_smul] using hh

lemma ergodic_restrict_subset_of_inter [IsFiniteMeasure μ] (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : PreErgodic T (μ.restrict A)) (hBInv : T ⁻¹' B=B) (hpos : 0<μ (A∩B)) :
    A ≤ᵐ[μ] B := by
  rcases h.ae_mem_or_ae_notMem hB hBInv with hh|hh
  · exact (ae_restrict_iff' hA).mp hh
  · have hz : μ.restrict A B=0 := by
      simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hh
    rw [Measure.restrict_apply hB,inter_comm] at hz
    exact (hpos.ne' hz).elim

lemma ergodic_restrict_disjoint_or_eq [IsFiniteMeasure μ] (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : PreErgodic T (μ.restrict A)) (hBInv : T ⁻¹' B=B) (hmass : μ A=μ B) :
    μ (A∩B)=0 ∨ A =ᵐ[μ] B := by
  by_cases hz : μ (A∩B)=0
  · exact Or.inl hz
  · exact Or.inr (ae_eq_of_ae_subset_of_measure_ge
      (ergodic_restrict_subset_of_inter hA hB h hBInv (pos_iff_ne_zero.mpr hz))
      hmass.symm.le hA.nullMeasurableSet (measure_ne_top μ B))

lemma measurePreserving_restrict_of_ae [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (hInv : T ⁻¹' A =ᵐ[μ] A) : MeasurePreserving T (μ.restrict A) (μ.restrict A) := by
  have h := hT.restrict_preimage hA
  rwa [Measure.restrict_congr_set hInv] at h

lemma ergodic_restrict_congr [IsFiniteMeasure μ] {V : X → X} (h : Ergodic V (μ.restrict A)) (hAB : A =ᵐ[μ] B) :
    Ergodic V (μ.restrict B) := by
  rwa [Measure.restrict_congr_set hAB] at h

lemma preimage_iterate_symm_eq (e : X ≃ᵐ X) {n : ℕ} (hA : (e^[n]) ⁻¹' A=A) :
    (e.symm^[n]) ⁻¹' A=A := by
  ext x
  have hh := congrArg (fun U : Set X => (e.symm^[n] x)∈U) hA
  have hi : Function.LeftInverse (e : X → X) e.symm := e.apply_symm_apply
  simpa only [mem_preimage,hi.iterate n x] using Iff.of_eq hh.symm

lemma translate_invariant (e : X ≃ᵐ X) {n : ℕ} (hA : (e^[n]) ⁻¹' A=A) (j : ℕ) :
    (e^[n]) ⁻¹' ((e.symm^[j]) ⁻¹' A)=((e.symm^[j]) ⁻¹' A) := by
  have hc : Function.Commute (e : X → X) e.symm := fun x => by simp
  ext x
  change (e.symm^[j] (e^[n] x)∈A) ↔ (e.symm^[j] x∈A)
  rw [←(hc.iterate_iterate n j).eq]
  exact Iff.of_eq (congrArg (fun U : Set X => e.symm^[j] x∈U) hA)

lemma measurePreserving_translate [IsFiniteMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (hA : MeasurableSet A) (j : ℕ) :
    MeasurePreserving (e^[j]) (μ.restrict A) (μ.restrict ((e.symm^[j]) ⁻¹' A)) := by
  have hB : MeasurableSet ((e.symm^[j]) ⁻¹' A) := hA.preimage (e.symm.measurable.iterate j)
  have h := (he.iterate j).restrict_preimage hB
  have hi : Function.LeftInverse (e.symm : X → X) e := e.symm_apply_apply
  have hh : (e^[j]) ⁻¹' ((e.symm^[j]) ⁻¹' A)=A := by
    ext x
    simp only [mem_preimage,hi.iterate j x]
  rwa [hh] at h

lemma ergodic_translate [IsFiniteMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (hA : MeasurableSet A) {n : ℕ} (h : Ergodic (e^[n]) (μ.restrict A)) (j : ℕ) :
    Ergodic (e^[n]) (μ.restrict ((e.symm^[j]) ⁻¹' A)) := by
  exact (measurePreserving_translate e he hA j).ergodic_of_ergodic_semiconj h
    (e.measurable.iterate n) (Function.Commute.iterate_iterate_self e j n)

end BoundedSubadditive

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

structure CyclicAtom (e : X ≃ᵐ X) (μ : Measure X) (E A : Set X) (n : ℕ) where
  period : ℕ
  positive : 0<period
  divides : period ∣ n
  periodic : (e.symm^[period]) ⁻¹' A =ᵐ[μ] A
  disjoint : ∀ i j : Fin period,i≠j → μ (((e.symm^[i.val]) ⁻¹' A)∩((e.symm^[j.val]) ⁻¹' A))=0
  cover : (⋃ j : Fin period,(e.symm^[j.val]) ⁻¹' A) =ᵐ[μ] E
  mass : (period : ℝ≥0∞)*μ A=μ E
  forward : ∀ j : Fin period,e '' ((e.symm^[j.val]) ⁻¹' A) =ᵐ[μ]
    (e.symm^[(j.val+1)%period]) ⁻¹' A
  ergodic : ∀ j : Fin period,Ergodic (e^[period]) (μ.restrict ((e.symm^[j.val]) ⁻¹' A))

lemma inverse_preimage_ae [IsFiniteMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {A : Set X} (p : ℕ)
    (hp : (e.symm^[p]) ⁻¹' A =ᵐ[μ] A) : (e^[p]) ⁻¹' A =ᵐ[μ] A := by
  have hh := (he.iterate p).quasiMeasurePreserving.preimage_ae_eq hp
  have hi : Function.LeftInverse (e.symm : X → X) e := e.symm_apply_apply
  have hx : (e^[p]) ⁻¹' ((e.symm^[p]) ⁻¹' A)=A := by
    ext x
    simp only [mem_preimage,hi.iterate p x]
  rw [hx] at hh
  exact hh.symm

theorem finite_cycle_of_ergodic_atom [IsFiniteMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {E A : Set X} (hE : MeasurableSet E) (hA : MeasurableSet A) (hApos : 0<μ A)
    (hAE : A ≤ᵐ[μ] E) (hEInv : e ⁻¹' E=E) (hErgE : Ergodic e (μ.restrict E))
    {n : ℕ} (hn : 0 < n) (hAInv : (e^[n]) ⁻¹' A=A) (hErgA : Ergodic (e^[n]) (μ.restrict A)) :
    Nonempty (CyclicAtom e μ E A n) := by
  let hs := (he.symm e).quasiMeasurePreserving
  let p := Function.minimalPeriod (AEPeriod.act hs) (AEPeriod.ofSet μ A)
  have haS : (e.symm^[n]) ⁻¹' A =ᵐ[μ] A := Eventually.of_forall fun x =>
    congrArg (fun U : Set X => x∈U) (preimage_iterate_symm_eq e hAInv)
  have hp : 0 < p := AEPeriod.period_pos hs hn haS
  have hpd : p ∣ n := AEPeriod.period_dvd hs haS
  have hpp : (e.symm^[p]) ⁻¹' A =ᵐ[μ] A := AEPeriod.period_preimage hs A
  let P (j : ℕ) : Set X := (e.symm^[j]) ⁻¹' A
  have hPm (j : ℕ) : MeasurableSet (P j) := hA.preimage (e.symm.measurable.iterate j)
  have hPmass (j : ℕ) : μ (P j)=μ A := ((he.symm e).iterate j).measure_preimage hA.nullMeasurableSet
  have hPInv (j : ℕ) : (e^[n]) ⁻¹' (P j)=P j := translate_invariant e hAInv j
  have hPdisj (i j : Fin p) (hij : i≠j) : μ (P i.val∩P j.val)=0 := by
    rcases ergodic_restrict_disjoint_or_eq (hPm _) (hPm _)
      (ergodic_translate e he hA hErgA i.val).toPreErgodic (hPInv j.val)
      ((hPmass _).trans (hPmass _).symm) with hh|hh
    · exact hh
    · exact (AEPeriod.preimage_ne hs A i.isLt j.isLt (fun hv => hij (Fin.ext hv)) hh).elim
  have hnext (j : Fin p) : e.symm ⁻¹' P j.val =ᵐ[μ] P ((j.val+1)%p) := by
    have heq : e.symm ⁻¹' P j.val=P (j.val+1) := by
      ext x
      simp only [P,mem_preimage,Function.iterate_succ_apply]
    rw [heq]
    exact (AEPeriod.preimage_mod hs A (j.val+1)).symm
  let U : Set X := ⋃ j : Fin p,P j.val
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun j => hPm j.val
  have hUsub : U ≤ᵐ[μ] E := by
    have hh (j : Fin p) : P j.val ≤ᵐ[μ] E := by
      have hh := ((he.symm e).iterate j.val).quasiMeasurePreserving.preimage_mono_ae hAE
      rwa [preimage_iterate_symm_eq e (Function.IsFixedPt.preimage_iterate hEInv j.val)] at hh
    filter_upwards [ae_all_iff.mpr hh] with x hx
    intro hxU
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxU
    exact hx j hj
  have hUInv : e.symm ⁻¹' U =ᵐ[μ] U := by
    have hnxt (j : Fin p) : e.symm ⁻¹' P j.val =ᵐ[μ] P (finRotate p j).val := by
      have hrot : (finRotate p j).val=(j.val+1)%p := by
        let : NeZero p := ⟨hp.ne'⟩
        rw [finRotate_apply]
        rw [Fin.val_add]
        change (j.val+1%p)%p=(j.val+1)%p
        exact Nat.add_mod_mod _ _ _
      simpa only [hrot] using hnext j
    filter_upwards [ae_all_iff.mpr hnxt] with x hx
    apply propext
    change (e.symm x ∈ U) ↔ x ∈ U
    simp only [U,mem_iUnion]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨finRotate p j,Eq.mp (hx j) hj⟩
    · rintro ⟨j,hj⟩
      refine ⟨(finRotate p).symm j,?_⟩
      apply (Iff.of_eq (hx ((finRotate p).symm j))).mpr
      simpa only [Equiv.apply_symm_apply] using hj
  have hUpos : 0<μ U := hApos.trans_le (measure_mono (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨0,hp⟩,hx⟩))
  have hEU : E ≤ᵐ[μ] U := by
    have hInvR : e.symm ⁻¹' U =ᵐ[μ.restrict E] U :=
      Measure.absolutelyContinuous_restrict.ae_eq hUInv
    rcases hErgE.symm.quasiErgodic.ae_mem_or_ae_notMem₀ hUm.nullMeasurableSet hInvR with h|h
    · exact (ae_restrict_iff' hE).mp h
    · have hz : μ.restrict E U=0 := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using h
      rw [Measure.restrict_apply hUm] at hz
      have hei : (U∩E : Set X) =ᵐ[μ] U := by
        filter_upwards [hUsub] with x hx
        apply propext
        exact ⟨fun h => h.1,fun h => ⟨h,hx h⟩⟩
      rw [measure_congr hei] at hz
      exact (hUpos.ne' hz).elim
  have hcover : U =ᵐ[μ] E := eventuallyLE_antisymm_iff.mpr ⟨hUsub,hEU⟩
  have hmass : (p : ℝ≥0∞)*μ A=μ E := by
    rw [←measure_congr hcover]
    dsimp only [U]
    rw [measure_iUnion₀ (fun i j hij => hPdisj i j hij) (fun j => (hPm j.val).nullMeasurableSet),tsum_fintype]
    simp only [hPmass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hbaseErg : Ergodic (e^[p]) (μ.restrict A) := by
    refine ⟨measurePreserving_restrict_of_ae (he.iterate p) hA (inverse_preimage_ae e he p hpp),?_⟩
    obtain ⟨q,hq⟩ := hpd
    apply PreErgodic.of_iterate q
    simpa only [hq,Function.iterate_mul] using hErgA.toPreErgodic
  refine ⟨{
    period := p
    positive := hp
    divides := hpd
    periodic := hpp
    disjoint := hPdisj
    cover := hcover
    mass := hmass
    forward := ?_
    ergodic := ?_ }⟩
  · intro j
    rw [e.image_eq_preimage_symm]
    exact hnext j
  · intro j
    exact ergodic_translate e he hA hbaseErg j.val

end BoundedSubadditive

end
end

end OAI
