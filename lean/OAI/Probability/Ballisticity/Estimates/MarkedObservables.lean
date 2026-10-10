import Mathlib
import OAI.Probability.Ballisticity.Stationary.StationaryProfile
import OAI.Probability.Ballisticity.Stationary.ArrayMarkedIterate
import OAI.Probability.Ballisticity.Estimates.ProfileMeasureUpdate
import OAI.Probability.Ballisticity.Entropy.EntropyDensity

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

noncomputable def arrayNatHeight {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : ℕ :=
  (Y.1 0).1.toNat
lemma arrayNatHeight_measurable {d : ℕ} (e : Direction d) : Measurable (arrayNatHeight e) :=
  (measurable_of_countable ENat.toNat).comp (by fun_prop)
lemma arrayNatHeight_positive {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h0 : 0<(Y.1 0).1) (ht : (Y.1 0).1<⊤) : 1≤arrayNatHeight e Y := by
  have he := ENat.natCast_toNat ht.ne
  rw [←he] at h0
  exact_mod_cast h0

lemma markedArrayLaw_integrable {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) (hE : μ E≠0)
    (F : ActualEpisodeArray e → ℝ) (hF : Measurable F) (hFi : Integrable F μ) :
    Integrable (fun p : MarkedArray e => F p.1) (markedArrayLaw e μ E) := by
  have hi : Integrable F μ[|E] := hFi.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hE)
  apply (integrable_map_measure hF.aestronglyMeasurable measurable_fst.aemeasurable).mp
  change Integrable F (markedArrayLaw e μ E).fst
  rwa [markedArrayLaw_fst]

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma marked_proper_entropy (L : StationaryArrayLaw ν e)
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e)))
    (w₀ : ProperProfile e) (n : ℕ) :
    let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
    let data := fun p => properData e w₀ (markedData e p)
    klDiv (μ.map (fun p => (data p,markedUpper e n p)))
      ((μ.map data).prod (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)))≠∞ := by
  let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
  have := markedArrayLaw_probability e (L.law : Measure (ActualEpisodeArray e)) G.event G.positive_event.ne'
  let U := Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)
  have hk := L.marked_upper_entropy G n
  dsimp only at hk ⊢
  rw [Measure.fst_map_prodMk (markedData_measurable e) (markedUpper_measurable e n)] at hk
  have h := klDiv_map_le (μ.map (fun p => (markedData e p,markedUpper e n p)))
    ((μ.map (markedData e)).prod U) ((properData_measurable e w₀).prodMap measurable_id)
  have hprod := Measure.map_prod_map (μ.map (markedData e)) U (properData_measurable e w₀) measurable_id
  rw [Measure.map_id] at hprod
  rw [←hprod,Measure.map_map (properData_measurable e w₀) (markedData_measurable e),
    Measure.map_map ((properData_measurable e w₀).prodMap measurable_id)
      ((markedData_measurable e).prodMk (markedUpper_measurable e n))] at h
  exact ne_top_of_le_ne_top hk h

lemma marked_full_entropy (L : StationaryArrayLaw ν e)
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e)))
    (w₀ : ProperProfile e) (n : ℕ) :
    let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
    let data := fun p : MarkedArray e × Environment d => properData e w₀ (markedData e p.1)
    let field := fun p : MarkedArray e × Environment d => fillUpper e (markedUpper e n p.1,p.2)
    ∃ g : ProperProfile e × Environment d → ℝ, Measurable g ∧ (∀ z,0≤g z) ∧
      Integrable g (((μ.prod (environmentLaw ν)).map data).prod (environmentLaw ν)) ∧
      (∫ z, g z ∂((μ.prod (environmentLaw ν)).map data).prod (environmentLaw ν))=1 ∧
      Integrable (fun z => TailDecorrelation.entropyPlus (g z))
        (((μ.prod (environmentLaw ν)).map data).prod (environmentLaw ν)) ∧
      (μ.prod (environmentLaw ν)).map (fun p => (data p,field p))=
        (((μ.prod (environmentLaw ν)).map data).prod (environmentLaw ν)).withDensity (fun z => ENNReal.ofReal (g z)) := by
  let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
  have := markedArrayLaw_probability e (L.law : Measure (ActualEpisodeArray e)) G.event G.positive_event.ne'
  let data := fun p : MarkedArray e => properData e w₀ (markedData e p)
  have hd : Measurable data := (properData_measurable e w₀).comp (markedData_measurable e)
  have hf : Measurable (fun p : MarkedArray e × Environment d => fillUpper e (markedUpper e n p.1,p.2)) :=
    (fillUpper_measurable e).comp (((markedUpper_measurable e n).comp measurable_fst).prodMk measurable_snd)
  have hkl := fillUpper_finite_entropy e ν μ data hd (markedUpper e n) (markedUpper_measurable e n)
    (L.marked_proper_entropy G w₀ n)
  have hdata : (μ.prod (environmentLaw ν)).map (fun p => data p.1)=μ.map data := by
    rw [show (fun p : MarkedArray e × Environment d => data p.1)=data ∘ Prod.fst from rfl,
      ←Measure.map_map hd measurable_fst,Measure.map_fst_prod,measure_univ,one_smul]
  have : IsProbabilityMeasure ((μ.prod (environmentLaw ν)).map
      (fun p => (data p.1,fillUpper e (markedUpper e n p.1,p.2)))) :=
    (Measure.isProbabilityMeasure_map_iff
      ((hd.comp measurable_fst).prodMk hf).aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (μ.map data) :=
    (Measure.isProbabilityMeasure_map_iff hd.aemeasurable).mpr inferInstance
  have h := Entropy.density_of_finite_kl _ _ hkl
  dsimp only [μ,data] at hdata h ⊢
  simpa only [hdata] using h

end StationaryArrayLaw
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma arrayProfileMeasure_translation {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hp : ArrayProfilesConsistent e Y) (j : ℤ) (p q : StationaryCompact.Label)
    (v : HorizontalSpace e) (hv : Y.2.1 (p,q)=(v:OnePoint (HorizontalSpace e))) :
    (arrayProfileMeasure e j q Y).map (fun x => x+v)=arrayProfileMeasure e j p Y := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : (fun y : HorizontalSpace e => y+v) ⁻¹' {x}={x-v} := by
    ext y
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    exact eq_sub_iff_add_eq.symm
  rw [he,arrayProfileMeasure_atom,arrayProfileMeasure_atom]
  unfold arrayProfileMass
  rw [←hp.1 j p q v (x-v) hv]
  congr 2
  abel_nf

lemma arrayProfileMeasure_iterate {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (n a : ℕ) : arrayProfileMeasure e 0 (0,a) (StationaryCompact.shift^[n] Y)=
      arrayProfileMeasure e n (n,a) Y := by
  apply Measure.ext_of_singleton
  intro z
  simp only [arrayProfileMeasure_atom,arrayProfileMass,arrayProfile_iterate,zero_add]

lemma arrayHeight_sum {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hf : ∀ j, (Y.1 j).1<⊤) (n : ℕ) :
    arrayWindowHeight e 0 n Y=(∑ i∈Finset.range n, arrayNatHeight e (StationaryCompact.shift^[i] Y):ℕ) := by
  simp only [arrayWindowHeight,Nat.cast_sum,arrayNatHeight,arrayMark_iterate,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  exact (ENat.natCast_toNat (hf j).ne).symm

lemma exp_sum_discount {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hf : ∀ j, (Y.1 j).2.2≠⊤) (n : ℕ) :
    ENNReal.ofReal (Real.exp (∑ i∈Finset.range n, arrayRealCost e (StationaryCompact.shift^[i] Y))) *
      expNeg (arrayWindowCost e 0 n Y)=1 := by
  have hc : arrayWindowCost e 0 n Y≠⊤ := ENNReal.sum_ne_top.mpr fun j _ => hf _
  rw [←ENNReal.ofReal_toReal (expNeg_ne_top _),expNeg_toReal_of_ne_top _ hc,
    arrayWindowCost_toReal e Y hf,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
  simp

lemma markedCoordinateProfile_eq {d : ℕ} (e : Direction d) (f : Fin d) (w₀ : ProperProfile e)
    (p : MarkedArray e) (hp : IsProperProfile e (markedProfile e (markedData e p))) :
    coordinateProfile e f (properProfileKernel e) (properData e w₀ (markedData e p))=
      (arrayProfileMeasure e 0 (0,p.2) p.1).map (fun x => x.1 f) := by
  rw [coordinateProfile_apply,properData_kernel_eq e w₀ p hp,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

lemma markedProfile_update {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1≠f)
    (w₀ : ProperProfile e) (p : MarkedArray e) (ω : Environment d) (n : ℕ)
    (hp : ArrayProfilesConsistent e p.1) (hc : ArrayContinuation e p.1)
    (hh : ∀ j, (p.1.1 j).1<⊤) (hcost : ∀ j, (p.1.1 j).2.2≠⊤)
    (hrel : ArrayRelated e p.1 (0,p.2) (n,((markedShift e)^[n] p).2))
    (h0 : IsProperProfile e (markedProfile e (markedData e p)))
    (hn : IsProperProfile e (markedProfile e (markedData e ((markedShift e)^[n] p)))) :
    ENNReal.ofReal (Real.exp (∑ i∈Finset.range n, arrayRealCost e (((markedShift e)^[i] p).1))) •
      (horizontalCoordinateKernel e f (∑ i∈Finset.range n, arrayNatHeight e (((markedShift e)^[i] p).1))
        (fillUpper e (markedUpper e n p,ω)) ∘ₘ properProfileKernel e (properData e w₀ (markedData e p))) ≤
      (coordinateProfile e f (properProfileKernel e) (properData e w₀ (markedData e ((markedShift e)^[n] p)))).map
        (fun x => x+(markedDisplacement e n p).val f) := by
  simp only [markedShift_iterate_fst]
  rw [properData_kernel_eq e w₀ p h0,horizontalProfileImage_fill e f hef]
  have hu := arrayProfile_measure_update e 0 n p.2 _ p.1 hc (arrayHeight_sum e p.1 hh n)
  have hu' := smul_le_smul_left (ENNReal.ofReal (Real.exp (∑ i∈Finset.range n, arrayRealCost e (StationaryCompact.shift^[i] p.1)))) hu
  rw [smul_smul,exp_sum_discount e p.1 hcost n,one_smul] at hu'
  have hu'' := Measure.map_mono hu' (measurable_of_countable (fun x : HorizontalSpace e => x.1 f))
  rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable] at hu''
  change _≤(arrayProfileMeasure e (0+n) (0,p.2) p.1).map (fun x => x.1 f) at hu''
  simp only [zero_add] at hu''
  refine hu''.trans_eq ?_
  rw [markedCoordinateProfile_eq e f w₀ _ hn,markedShift_iterate_fst,arrayProfileMeasure_iterate]
  rw [←arrayProfileMeasure_translation e p.1 hp n (0,p.2) (n,((markedShift e)^[n] p).2)
    (markedDisplacement e n p) (markedDisplacement_spec e n p hrel)]
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

end DirectionalTransience

end

end OAI
