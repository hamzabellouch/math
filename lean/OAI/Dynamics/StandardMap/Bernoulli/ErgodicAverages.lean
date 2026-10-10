import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Components.BirkhoffAtoms

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}

theorem ae_bounded_ergodic_mean (hT : Ergodic T μ) {g : X → ℝ} (hg : Measurable g)
    (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    ∀ᵐ x ∂μ,Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)) atTop (𝓝 (∫ y,g y ∂μ)) := by
  obtain ⟨G,hGm,hGb,hGT,hGc,hGi⟩ := exists_bounded_birkhoff_limit hT.toMeasurePreserving hg h0 h1
  obtain ⟨c,hc⟩ := hT.toPreErgodic.ae_eq_const_of_ae_eq_comp hGm (funext hGT)
  have hi : c=∫ y,g y ∂μ := by
    calc
      c = ∫ y,G y ∂μ := by rw [integral_congr_ae hc]; simp
      _ = _ := by simpa only [Measure.restrict_univ] using hGi univ MeasurableSet.univ (preimage_univ)
  filter_upwards [hGc,hc] with x hx hxc
  simpa only [hxc,Function.const_apply,hi] using hx

end BoundedSubadditive

end
section
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace HyperbolicCoding

noncomputable def hammingAverage {X A : Type*} (T : X → X) (α : X → A)
    (x y : X) (n : ℕ) : ℝ := by
  classical
  exact (∑ i ∈ Finset.range n, if α (T^[i] x)=α (T^[i] y) then (0 : ℝ) else 1)/(n : ℝ)

lemma hammingAverage_nonneg {X A : Type*} (T : X → X) (α : X → A) (x y : X) (n : ℕ) :
    0≤hammingAverage T α x y n := by
  classical
  unfold hammingAverage
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    split <;> norm_num
  · positivity

lemma nat_eq_of_dist_lt_one {a b : ℕ} (h : dist a b<1) : a=b := by
  rw [Nat.dist_eq,abs_lt] at h
  by_contra hn
  rcases lt_or_gt_of_ne hn with hl|hl
  · have hb : a+1≤b := hl
    have hc : (a : ℝ)+1≤b := by exact_mod_cast hb
    linarith [h.1]
  · have hb : b+1≤a := hl
    have hc : (b : ℝ)+1≤a := by exact_mod_cast hb
    linarith [h.2]

variable {X : Type*} [MetricSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

lemma compact_label_block {α : X → ℕ} (hα : Measurable α)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ K : Set X, IsCompact K ∧ ContinuousOn α K ∧ μ.real Kᶜ<ε := by
  have hr : ENNReal.ofReal (1-ε)<μ univ := by
    rw [measure_univ]
    exact ENNReal.ofReal_lt_one.mpr (by linarith)
  obtain ⟨K,_,hK,hc,hm⟩ := StandardMapEntropy.measurable_compact_continuity_block μ hα
    MeasurableSet.univ hr
  have hmr : 1-ε<μ.real K := by
    rw [measureReal_def]
    have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (measure_ne_top μ K)).mpr hm
    simpa only [ENNReal.toReal_ofReal (by linarith : 0≤1-ε)] using hh
  refine ⟨K,hK,hc,?_⟩
  rw [measureReal_compl hK.measurableSet]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one]
  change 1-μ.real K<ε
  linarith

theorem full_set_asymptotic_names {T : X → X} (hT : Ergodic T μ)
    {α : X → ℕ} (hα : Measurable α) :
    ∃ G : Set X,MeasurableSet G ∧ (∀ᵐ x ∂μ,x∈G) ∧
      ∀ x∈G,∀ y∈G,
        Tendsto (fun n : ℕ => dist (T^[n] x) (T^[n] y)) atTop (𝓝 0) →
        Tendsto (hammingAverage T α x y) atTop (𝓝 0) := by
  classical
  let ε (m : ℕ) : ℝ := 1/((m : ℝ)+1)
  have hε (m : ℕ) : 0<ε m := by unfold ε; positivity
  have hε1 (m : ℕ) : ε m≤1 := by
    unfold ε
    exact (div_le_one (by positivity)).mpr (by linarith [show 0≤(m : ℝ) from Nat.cast_nonneg m])
  choose K hK hKc hKμ using fun m => compact_label_block (μ := μ) hα (hε m) (hε1 m)
  let g (m : ℕ) : X → ℝ := (K m)ᶜ.indicator (fun _ => 1)
  have hgm (m : ℕ) : Measurable (g m) := measurable_const.indicator (hK m).measurableSet.compl
  have hg0 (m : ℕ) (x : X) : 0≤g m x := by simp only [g,Set.indicator_apply]; split_ifs <;> norm_num
  have hg1 (m : ℕ) (x : X) : g m x≤1 := by simp only [g,Set.indicator_apply]; split_ifs <;> norm_num
  have hgi (m : ℕ) : (∫ x,g m x ∂μ)=μ.real (K m)ᶜ := by
    simpa only [g,smul_eq_mul,mul_one] using integral_indicator_const (μ := μ) (1 : ℝ) (hK m).measurableSet.compl
  have hgeneric : ∀ᵐ x ∂μ,∀ m : ℕ,
      Tendsto (fun n : ℕ => birkhoffSum T (g m) n x/(n : ℝ)) atTop (𝓝 (μ.real (K m)ᶜ)) := by
    rw [ae_all_iff]
    intro m
    simpa only [hgi] using BoundedSubadditive.ae_bounded_ergodic_mean hT (hgm m) (hg0 m) (hg1 m)
  obtain ⟨G,hGae,hGm,hG⟩ := IsMeasurablyGenerated.exists_measurable_subset hgeneric
  refine ⟨G,hGm,hGae,?_⟩
  intro x hx y hy hxy
  apply Metric.tendsto_nhds.mpr
  intro r hr
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (show 0<r/4 by positivity)
  have hm' : ε m<r/4 := hm
  obtain ⟨δ,hδ,hδK⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK m).uniformContinuousOn_of_continuous (hKc m)) 1 (by norm_num)
  let b (i : ℕ) : ℝ := if dist (T^[i] x) (T^[i] y)<δ then 0 else 1
  have hbe : b =ᶠ[atTop] fun _ => (0 : ℝ) := by
    filter_upwards [hxy.eventually (eventually_lt_nhds hδ)] with i hi
    simp [b,hi]
  have hb : Tendsto b atTop (𝓝 0) := tendsto_const_nhds.congr' hbe.symm
  have hbound (n : ℕ) : hammingAverage T α x y n≤
      birkhoffSum T (g m) n x/(n : ℝ)+birkhoffSum T (g m) n y/(n : ℝ)+
        (∑ i ∈ Finset.range n,b i)/(n : ℝ) := by
    rw [←add_div,←add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    simp only [birkhoffSum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hbi : 0≤b i := by dsimp [b]; split_ifs <;> norm_num
    by_cases he : α (T^[i] x)=α (T^[i] y)
    · simp only [ite_eq_left he]
      linarith [hg0 m (T^[i] x),hg0 m (T^[i] y)]
    · simp only [ite_eq_right he]
      by_cases hxK : T^[i] x∈K m
      · by_cases hyK : T^[i] y∈K m
        · have hd : ¬dist (T^[i] x) (T^[i] y)<δ := by
            intro hh
            exact he (nat_eq_of_dist_lt_one (hδK _ hxK _ hyK hh))
          simp only [b,ite_eq_right hd]
          linarith [hg0 m (T^[i] x),hg0 m (T^[i] y)]
        · have hgy : g m (T^[i] y)=1 := by simp [g,hyK]
          linarith [hg0 m (T^[i] x)]
      · have hgx : g m (T^[i] x)=1 := by simp [g,hxK]
        linarith [hg0 m (T^[i] y)]
  have hlim := ((hG hx m).add (hG hy m)).add hb.cesaro
  have hrr : μ.real (K m)ᶜ+μ.real (K m)ᶜ+0<r := by linarith [hKμ m]
  filter_upwards [hlim.eventually (eventually_lt_nhds hrr)] with n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hammingAverage_nonneg T α x y n)]
  exact (hbound n).trans_lt (by simpa only [div_eq_mul_inv,mul_comm] using hn)

end HyperbolicCoding

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology ENNReal BigOperators

namespace HyperbolicCoding

lemma hammingAverage_le_one {X A : Type*} (T : X → X) (α : X → A) (x y : X) (n : ℕ) :
    hammingAverage T α x y n≤1 := by
  classical
  unfold hammingAverage
  by_cases hn : n=0
  · simp [hn]
  · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
    calc
      _ ≤ ∑ i ∈ Finset.range n,(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> norm_num
      _ = _ := by simp

lemma measurable_hammingAverage {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableEq A]
    {T : X → X} (hT : Measurable T) {α : X → A} (hα : Measurable α) (n : ℕ) :
    Measurable (fun p : X×X => hammingAverage T α p.1 p.2 n) := by
  classical
  unfold hammingAverage
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite (measurableSet_eq_fun ((hα.comp (hT.iterate i)).comp measurable_fst)
    ((hα.comp (hT.iterate i)).comp measurable_snd)) measurable_const measurable_const

theorem integral_hamming_asymptotic {X Ω : Type*}
    [MetricSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X} (hT : Ergodic T μ)
    {α : X → ℕ} (hα : Measurable α) (κ : Measure Ω) [IsFiniteMeasure κ]
    {p q : Ω → X} (hp : QuasiMeasurePreserving p κ μ) (hq : QuasiMeasurePreserving q κ μ)
    (hasym : ∀ᵐ w ∂κ,Tendsto (fun n : ℕ => dist (T^[n] (p w)) (T^[n] (q w))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ w,hammingAverage T α (p w) (q w) n ∂κ) atTop (𝓝 0) := by
  obtain ⟨G,hGm,hGae,hG⟩ := full_set_asymptotic_names hT hα
  have hlim : ∀ᵐ w ∂κ,Tendsto (fun n : ℕ => hammingAverage T α (p w) (q w) n) atTop (𝓝 0) := by
    filter_upwards [hp.ae hGae,hq.ae hGae,hasym] with w hw₁ hw₂ hw₃
    exact hG _ hw₁ _ hw₂ hw₃
  have hm (n : ℕ) : Measurable (fun w => hammingAverage T α (p w) (q w) n) :=
    (measurable_hammingAverage hT.toMeasurePreserving.measurable hα n).comp (hp.measurable.prodMk hq.measurable)
  have hh := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (fun n => (hm n).aestronglyMeasurable) (integrable_const 1) (fun n => ae_of_all _ (fun w => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hammingAverage_nonneg T α (p w) (q w) n)]
      exact hammingAverage_le_one T α (p w) (q w) n)) hlim
  simpa only [integral_zero] using hh

end HyperbolicCoding

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open BoundedSubadditive HyperbolicCoding
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

noncomputable def carrierProbability : Measure B.coordinateCarrier :=
  ((volume : Measure B.coordinateCarrier) univ)⁻¹ • volume

instance carrierProbability_probability : IsProbabilityMeasure B.carrierProbability := by
  let _ : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := B.finite_coordinate_volume
  have hp : 0<(volume : Measure B.coordinateCarrier) univ := by
    rw [B.volume_coordinate_univ]
    exact B.positive_coordinateCarrier
  constructor
  simp only [carrierProbability,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp.ne' (measure_ne_top _ _)

lemma carrierProbability_ac : B.carrierProbability≪(volume : Measure B.coordinateCarrier) :=
  smul_absolutelyContinuous
end ReversibleRectangleBlock

lemma quasiMeasurePreserving_normalizedArea {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {p : Ω → Torus} (hp : QuasiMeasurePreserving p ν area)
    {E : Set Torus} (hE : MeasurableSet E) (hmem : ∀ᵐ w ∂ν,p w∈E) :
    QuasiMeasurePreserving p ν (normalizedArea E) := by
  have hae : ∀ᵐ z ∂ν.map p,z∈E := (ae_map_iff hp.measurable.aemeasurable hE).mpr hmem
  have hac := hp.absolutelyContinuous.restrict E
  rw [Measure.restrict_eq_self_of_ae_mem hae] at hac
  exact ⟨hp.measurable,hac.trans (absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr (measure_ne_top area E)))⟩

namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

lemma carrier_nonsingular :
    QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) area := by
  let _ : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := B.finite_coordinate_volume
  exact R.torus_nonsingular.mono_left (B.carrierProbability_ac.prod B.carrierProbability_ac)

lemma component_for_power {N : ℕ} (hN : 0<N)
    (C : ContinuousBirkhoffCode ((standardMap k)^[N]) ((inverseMap k)^[N]) area) :
    ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧ ((standardMap k)^[N] ⁻¹' E=E) ∧
      Ergodic ((standardMap k)^[N]) (normalizedArea E) ∧
      QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) (normalizedArea E) := by
  have hrow (a b b' : B.coordinateCarrier)
      (ha : ∀ j : ℕ,
        Tendsto (fun n : ℕ => birkhoffSum ((standardMap k)^[N]) (C.observation j) n (R.torusPoint (a,b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b)) j)) ∧
        Tendsto (fun n : ℕ => birkhoffSum ((inverseMap k)^[N]) (C.observation j) n (R.torusPoint (a,b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b)) j)))
      (hb : ∀ j : ℕ,
        Tendsto (fun n : ℕ => birkhoffSum ((standardMap k)^[N]) (C.observation j) n (R.torusPoint (a,b'))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b')) j)) ∧
        Tendsto (fun n : ℕ => birkhoffSum ((inverseMap k)^[N]) (C.observation j) n (R.torusPoint (a,b'))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b')) j))) :
      C.value (R.torusPoint (a,b))=C.value (R.torusPoint (a,b')) := by
    funext j
    exact birkhoff_limit_eq_of_asymptotic (CompactSpace.uniformContinuous_of_continuous (C.observation j).continuous)
      (asymptotic_iterate (R.row_asymptotic a b b') hN) (ha j).1 (hb j).1
  have hcol (a a' b : B.coordinateCarrier)
      (ha : ∀ j : ℕ,
        Tendsto (fun n : ℕ => birkhoffSum ((standardMap k)^[N]) (C.observation j) n (R.torusPoint (a,b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b)) j)) ∧
        Tendsto (fun n : ℕ => birkhoffSum ((inverseMap k)^[N]) (C.observation j) n (R.torusPoint (a,b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b)) j)))
      (hb : ∀ j : ℕ,
        Tendsto (fun n : ℕ => birkhoffSum ((standardMap k)^[N]) (C.observation j) n (R.torusPoint (a',b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a',b)) j)) ∧
        Tendsto (fun n : ℕ => birkhoffSum ((inverseMap k)^[N]) (C.observation j) n (R.torusPoint (a',b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a',b)) j))) :
      C.value (R.torusPoint (a,b))=C.value (R.torusPoint (a',b)) := by
    funext j
    exact birkhoff_limit_eq_of_asymptotic (CompactSpace.uniformContinuous_of_continuous (C.observation j).continuous)
      (asymptotic_iterate (R.column_asymptotic a a' b) hN) (ha j).2 (hb j).2
  obtain ⟨c,hc⟩ := ae_constant_of_product_rows_columns (F := fun p => C.value (R.torusPoint p)) (R.carrier_nonsingular.ae C.generic) hrow hcol
  let E := {z | C.value z=c}
  have hE : MeasurableSet E := C.measurableSet_atom c
  have hEpos : 0<area E := by
    by_contra hn
    have hz : area E=0 := le_antisymm (not_lt.mp hn) bot_le
    have ha : ∀ᵐ z ∂area,z∉E := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hz
    obtain ⟨p,hp,hp'⟩ := (hc.and (R.carrier_nonsingular.ae ha)).exists
    exact hp' hp
  exact ⟨E,hE,hEpos,C.invariant_atom c,C.ergodic_atom ((measurePreserving_standardMap k).iterate N) hEpos,
    quasiMeasurePreserving_normalizedArea R.carrier_nonsingular hE hc⟩

theorem name_coupling_cost {N : ℕ} (hN : 0<N)
    (C : ContinuousBirkhoffCode ((standardMap k)^[N]) ((inverseMap k)^[N]) area) :
    ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧ ((standardMap k)^[N] ⁻¹' E=E) ∧
      Ergodic ((standardMap k)^[N]) (normalizedArea E) ∧
      QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) (normalizedArea E) ∧
      ∀ α : Torus → ℕ,Measurable α →
        Tendsto (fun n : ℕ => ∫ p : (B.coordinateCarrier×B.coordinateCarrier)×B.coordinateCarrier,
          hammingAverage ((standardMap k)^[N]) α (R.torusPoint p.1) (R.torusPoint (p.1.1,p.2)) n
            ∂(B.carrierProbability.prod B.carrierProbability).prod B.carrierProbability) atTop (𝓝 0) := by
  obtain ⟨E,hE,hEp,hInv,hErg,hπ⟩ := R.component_for_power hN C
  let _ := normalizedArea_probability hEp
  refine ⟨E,hE,hEp,hInv,hErg,hπ,?_⟩
  intro α hα
  have hp : MeasurePreserving (Prod.fst : (B.coordinateCarrier×B.coordinateCarrier)×B.coordinateCarrier → _)
      ((B.carrierProbability.prod B.carrierProbability).prod B.carrierProbability)
      (B.carrierProbability.prod B.carrierProbability) := measurePreserving_fst
  have hq : MeasurePreserving (fun p : (B.coordinateCarrier×B.coordinateCarrier)×B.coordinateCarrier => (p.1.1,p.2))
      ((B.carrierProbability.prod B.carrierProbability).prod B.carrierProbability)
      (B.carrierProbability.prod B.carrierProbability) :=
    (measurePreserving_fst (μ := B.carrierProbability) (ν := B.carrierProbability)).prod (MeasurePreserving.id B.carrierProbability)
  exact integral_hamming_asymptotic hErg hα _ (hπ.comp hp.quasiMeasurePreserving)
    (hπ.comp hq.quasiMeasurePreserving) (ae_of_all _ (fun p =>
      asymptotic_iterate (R.row_asymptotic p.1.1 p.1.2 p.2) hN))

end ReversibleGraphRectangle
end StandardMapEntropy

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology ENNReal NNReal BigOperators

namespace HyperbolicCoding

theorem ae_threshold_avoids_exponential {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X} (hT : Measurable T)
    {g : X → ℝ} (hg : Measurable g) {ρ : ℝ} (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    ∀ᵐ r : ℝ ∂volume,∀ᵐ x ∂μ,∀ C : ℕ,∀ᶠ n : ℕ in atTop,
      (C : ℝ)*ρ^n < |g (T^[n] x)-r| := by
  have hC (C : ℕ) : ∀ᵐ r : ℝ ∂volume,∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,
      (C : ℝ)*ρ^n < |g (T^[n] x)-r| := by
    let S (n : ℕ) : Set (ℝ×X) := {p | |g (T^[n] p.2)-p.1|≤(C : ℝ)*ρ^n}
    have hSm (n : ℕ) : MeasurableSet (S n) :=
      measurableSet_le (((hg.comp (hT.iterate n)).comp measurable_snd).sub measurable_fst).abs measurable_const
    have hm (n : ℕ) : ((volume : Measure ℝ).prod μ) (S n)=ENNReal.ofReal (2*(C : ℝ)*ρ^n) := by
      rw [Measure.prod_apply_symm (hSm n)]
      calc
        _ = ∫⁻ x : X,ENNReal.ofReal (2*(C : ℝ)*ρ^n) ∂μ := by
          apply lintegral_congr
          intro x
          have he : (fun r : ℝ => (r,x)) ⁻¹' S n=
              Icc (g (T^[n] x)-(C : ℝ)*ρ^n) (g (T^[n] x)+(C : ℝ)*ρ^n) := by
            ext r
            simp only [S,mem_preimage,mem_ofPred_eq,mem_Icc,abs_le]
            constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
          rw [he,Real.volume_Icc]
          congr 1
          ring
        _ = _ := by simp
    have hsum : (∑' n : ℕ,((volume : Measure ℝ).prod μ) (S n))≠⊤ := by
      simp only [hm,ENNReal.ofReal_mul (by positivity : 0≤2*(C : ℝ)),ENNReal.ofReal_pow hρ0,
        ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr hρ1)))
    have ha := ae_eventually_notMem hsum
    have hh := ae_ae_of_ae_prod ha
    filter_upwards [hh] with r hr
    filter_upwards [hr] with x hx
    filter_upwards [hx] with n hn
    exact lt_of_not_ge hn
  filter_upwards [ae_all_iff.mpr hC] with r hr
  exact ae_all_iff.mpr hr

theorem ae_threshold_exponential_tail {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : Measurable T) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {ρ : ℝ} (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    ∀ᵐ r : ℝ ∂volume,∀ᵐ x ∂μ,∀ y : X,∀ C : ℝ,
      (∀ᶠ n : ℕ in atTop,dist (T^[n] x) (T^[n] y)≤C*ρ^n) →
      ∀ᶠ n : ℕ in atTop,(g (T^[n] x)<r ↔ g (T^[n] y)<r) := by
  filter_upwards [ae_threshold_avoids_exponential μ hT hg.continuous.measurable hρ0 hρ1] with r hr
  filter_upwards [hr] with x hx
  intro y C hxy
  obtain ⟨M,hM⟩ := exists_nat_gt ((K : ℝ)*C)
  filter_upwards [hx M,hxy] with n hn hdist
  have hdiff : |g (T^[n] x)-g (T^[n] y)|≤(M : ℝ)*ρ^n := by
    calc
      _ ≤ (K : ℝ)*dist (T^[n] x) (T^[n] y) := by simpa only [Real.dist_eq] using hg.dist_le_mul (T^[n] x) (T^[n] y)
      _ ≤ (K : ℝ)*(C*ρ^n) := mul_le_mul_of_nonneg_left hdist K.coe_nonneg
      _ ≤ (M : ℝ)*ρ^n := by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right hM.le (pow_nonneg hρ0 n)
  rcases abs_le.mp hdiff with ⟨hlo,hhi⟩
  by_cases hxr : g (T^[n] x)<r
  · have habs : |g (T^[n] x)-r|=r-g (T^[n] x) := by rw [abs_of_neg (by linarith)]; ring
    rw [habs] at hn
    exact iff_of_true hxr (by linarith)
  · have habs : |g (T^[n] x)-r|=g (T^[n] x)-r := abs_of_nonneg (sub_nonneg.mpr (not_lt.mp hxr))
    rw [habs] at hn
    exact iff_of_false hxr (by linarith)

def ExponentiallyAsymptotic {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (x y : X) : Prop :=
  ∃ ρ : ℝ,0≤ρ ∧ ρ<1 ∧ ∃ C : ℝ,
    ∀ᶠ n : ℕ in atTop,dist (T^[n] x) (T^[n] y)≤C*ρ^n

theorem ae_threshold_all_exponential_tails {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : Measurable T) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    ∀ᵐ r : ℝ ∂volume,∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic T x y →
      ∀ᶠ n : ℕ in atTop,(g (T^[n] x)<r ↔ g (T^[n] y)<r) := by
  have hq (q : ℚ) : ∀ᵐ r : ℝ ∂volume,∀ᵐ x ∂μ,
      0≤(q : ℝ) → (q : ℝ)<1 → ∀ y : X,∀ C : ℝ,
      (∀ᶠ n : ℕ in atTop,dist (T^[n] x) (T^[n] y)≤C*(q : ℝ)^n) →
      ∀ᶠ n : ℕ in atTop,(g (T^[n] x)<r ↔ g (T^[n] y)<r) := by
    by_cases hq0 : 0≤(q : ℝ)
    · by_cases hq1 : (q : ℝ)<1
      · exact (ae_threshold_exponential_tail μ hT hg hq0 hq1).mono
          (fun r hr => hr.mono (fun x hx _ _ => hx))
      · exact ae_of_all _ (fun _ => ae_of_all _ (fun _ _ h => (hq1 h).elim))
    · exact ae_of_all _ (fun _ => ae_of_all _ (fun _ h => (hq0 h).elim))
  filter_upwards [ae_all_iff.mpr hq] with r hr
  filter_upwards [ae_all_iff.mpr hr] with x hx
  intro y ⟨ρ,hρ0,hρ1,C,hxy⟩
  obtain ⟨q,hρq,hq1⟩ := exists_rat_btwn hρ1
  apply hx q (hρ0.trans hρq.le) hq1 y (max C 0)
  filter_upwards [hxy] with n hn
  exact hn.trans (mul_le_mul (le_max_left C 0) (pow_le_pow_left₀ hρ0 hρq.le n)
    (pow_nonneg hρ0 n) (le_max_right C 0))

end HyperbolicCoding

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal ENNReal

namespace HyperbolicCoding

def joinedBinary {X : Type*} (α : ℕ → ℕ → X → Bool) (N : ℕ) (x : X) :
    (Fin N × Fin N) → Bool := fun p => α p.1 p.2 x

lemma measurable_joinedBinary {X : Type*} [MeasurableSpace X]
    {α : ℕ → ℕ → X → Bool} (hα : ∀ i j,Measurable (α i j)) (N : ℕ) :
    Measurable (joinedBinary α N) :=
  Measurable.of_eval (fun p => hα p.1 p.2)

theorem exists_good_binary_partitions {X : Type*} [MetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (μ : Measure X) [IsProbabilityMeasure μ] {T S : X → X}
    (hT : Measurable T) (hS : Measurable S) :
    ∃ α : ℕ → ℕ → X → Bool,
      (∀ i j,Measurable (α i j)) ∧
      Function.Injective (fun x => fun i j => α i j x) ∧
      (∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic T x y → ∀ N : ℕ,
        ∀ᶠ n : ℕ in atTop,joinedBinary α N (T^[n] x)=joinedBinary α N (T^[n] y)) ∧
      (∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic S x y → ∀ N : ℕ,
        ∀ᶠ n : ℕ in atTop,joinedBinary α N (S^[n] x)=joinedBinary α N (S^[n] y)) := by
  classical
  let c := TopologicalSpace.denseSeq X
  have hd : DenseRange c := TopologicalSpace.denseRange_denseSeq X
  have hgood (i j : ℕ) : ∃ r : ℝ,
      r∈Ioo (1/((j : ℝ)+1)) (2/((j : ℝ)+1)) ∧
      (∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic T x y →
        ∀ᶠ n : ℕ in atTop,(dist (T^[n] x) (c i)<r ↔ dist (T^[n] y) (c i)<r)) ∧
      (∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic S x y →
        ∀ᶠ n : ℕ in atTop,(dist (S^[n] x) (c i)<r ↔ dist (S^[n] y) (c i)<r)) := by
    have ha := (ae_threshold_all_exponential_tails μ hT (LipschitzWith.dist_left (c i))).and
      (ae_threshold_all_exponential_tails μ hS (LipschitzWith.dist_left (c i)))
    have hv : volume (Ioo (1/((j : ℝ)+1)) (2/((j : ℝ)+1)))≠0 := by
      rw [Real.volume_Ioo,ne_eq,ENNReal.ofReal_eq_zero]
      have hp : (0 : ℝ)<(j : ℝ)+1 := by positivity
      push Not
      exact sub_pos.mpr (div_lt_div_of_pos_right (by norm_num) hp)
    exact exists_mem_of_measure_ne_zero_of_ae hv (ae_restrict_of_ae ha)
  choose r hr hTf hSb using hgood
  let α (i j : ℕ) (x : X) : Bool := if dist x (c i)<r i j then true else false
  have hm (i j : ℕ) : Measurable (α i j) :=
    measurable_const.ite (measurableSet_lt (continuous_id.dist continuous_const).measurable measurable_const) measurable_const
  have hinj : Function.Injective (fun x => fun i j => α i j x) := by
    intro x y h
    by_contra hxy
    have hdpos : 0<dist x y := dist_pos.mpr hxy
    obtain ⟨j,hj⟩ := exists_nat_one_div_lt (by linarith : 0<dist x y/3)
    obtain ⟨i,hi⟩ := hd.exists_dist_lt x (by positivity : 0<1/((j : ℝ)+1))
    have hx : dist x (c i)<r i j := hi.trans (hr i j).1
    have hy : ¬dist y (c i)<r i j := by
      intro hy
      have ht := dist_triangle x (c i) y
      rw [dist_comm (c i) y] at ht
      have ht' : 2/((j : ℝ)+1)=2*(1/((j : ℝ)+1)) := by ring
      have hh := (hr i j).2
      rw [ht'] at hh
      linarith
    have hh := congrFun (congrFun h i) j
    simp only [α,ite_eq_left hx,ite_eq_right hy] at hh
    exact Bool.noConfusion hh
  have forward : ∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic T x y → ∀ N : ℕ,
      ∀ᶠ n : ℕ in atTop,joinedBinary α N (T^[n] x)=joinedBinary α N (T^[n] y) := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hTf i))] with x hx
    intro y hxy N
    have hp (p : Fin N × Fin N) : ∀ᶠ n : ℕ in atTop,
        α p.1 p.2 (T^[n] x)=α p.1 p.2 (T^[n] y) := by
      filter_upwards [hx p.1 p.2 y hxy] with n hn
      dsimp only [α]
      simp only [hn]
    filter_upwards [Filter.eventually_all.mpr hp] with n hn
    exact funext hn
  have backward : ∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic S x y → ∀ N : ℕ,
      ∀ᶠ n : ℕ in atTop,joinedBinary α N (S^[n] x)=joinedBinary α N (S^[n] y) := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hSb i))] with x hx
    intro y hxy N
    have hp (p : Fin N × Fin N) : ∀ᶠ n : ℕ in atTop,
        α p.1 p.2 (S^[n] x)=α p.1 p.2 (S^[n] y) := by
      filter_upwards [hx p.1 p.2 y hxy] with n hn
      dsimp only [α]
      simp only [hn]
    filter_upwards [Filter.eventually_all.mpr hp] with n hn
    exact funext hn
  exact ⟨α,hm,hinj,forward,backward⟩

end HyperbolicCoding

end
end

end OAI
