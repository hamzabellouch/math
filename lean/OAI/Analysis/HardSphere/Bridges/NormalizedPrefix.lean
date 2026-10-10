import Mathlib
import OAI.Analysis.HardSphere.Bridges.PrefixMap
import OAI.Analysis.HardSphere.Geometry.ConfigurationPath

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
namespace Wiener

def normalizedPrefix (u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  (Real.sqrt (u:ℝ))⁻¹ • prefixMap u

def normalizedSuffix (u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  (Real.sqrt (1-(u:ℝ)))⁻¹ • suffixMap u

lemma normalized_split_preserving (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) :
    MeasurePreserving (fun w : C(Time,ℝ) ↦ (normalizedPrefix u w,normalizedSuffix u w))
      wiener (wiener.prod wiener) := by
  have hm : Measurable (fun w : C(Time,ℝ) ↦ (prefixMap u w,suffixMap u w)) := by fun_prop
  have heq : wiener.map (fun w : C(Time,ℝ) ↦ (prefixMap u w,suffixMap u w)) =
      (wiener.map (fun f ↦ Real.sqrt (u:ℝ) • f)).prod
        (wiener.map (fun f ↦ Real.sqrt (1-(u:ℝ)) • f)) := by
    rw [wiener,Measure.map_map hm measurable_path]
    exact split_path_law u
  refine ⟨by fun_prop,?_⟩
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)] at heq
  have hh := congrArg (fun μ : Measure (C(Time,ℝ) × C(Time,ℝ)) ↦ μ.map
    (fun p ↦ ((Real.sqrt (u:ℝ))⁻¹ • p.1,(Real.sqrt (1-(u:ℝ)))⁻¹ • p.2))) heq
  rw [Measure.map_map (by fun_prop) hm, Measure.map_map (by fun_prop) (by fun_prop)] at hh
  simpa only [normalizedPrefix,normalizedSuffix,smul_apply,
    Function.comp_def,Prod.map,smul_smul,
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hu)),
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hu'))),
    one_smul,Prod.mk.eta,Measure.map_id'] using hh

end Wiener

open Wiener

def splitTime (s t : ℝ) (hs : 0<s) (ht : 0<t) : Time :=
  ⟨s/(s+t), (div_pos hs (add_pos hs ht)).le, (div_le_one (add_pos hs ht)).mpr (by linarith)⟩

lemma splitTime_pos (s t : ℝ) (hs : 0<s) (ht : 0<t) : 0<(splitTime s t hs ht:ℝ) :=
  div_pos hs (add_pos hs ht)

lemma splitTime_lt_one (s t : ℝ) (hs : 0<s) (ht : 0<t) : (splitTime s t hs ht:ℝ)<1 :=
  (div_lt_one (add_pos hs ht)).mpr (by linarith)

lemma sqrt_split_left (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    Real.sqrt (2*s) * (Real.sqrt (splitTime s t hs ht:ℝ))⁻¹ = Real.sqrt (2*(s+t)) := by
  have h : Real.sqrt (2*(s+t)) * Real.sqrt (splitTime s t hs ht:ℝ) = Real.sqrt (2*s) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    change 2*(s+t)*(s/(s+t))=2*s
    field_simp
  rw [← h,mul_assoc,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (splitTime_pos s t hs ht))),mul_one]

lemma sqrt_split_right (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    Real.sqrt (2*t) * (Real.sqrt (1-(splitTime s t hs ht:ℝ)))⁻¹ = Real.sqrt (2*(s+t)) := by
  have h : Real.sqrt (2*(s+t)) * Real.sqrt (1-(splitTime s t hs ht:ℝ)) = Real.sqrt (2*t) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    change 2*(s+t)*(1-s/(s+t))=2*t
    field_simp
    ring
  rw [← h,mul_assoc,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (splitTime_lt_one s t hs ht)))),mul_one]

def configurationPrefix (N : ℕ) (L : Length) (u : Time) (ω : ConfigurationPath N L) :
    ConfigurationPath N L := ω.comp (prefixTime u)

def configurationSuffix (N : ℕ) (L : Length) (u : Time) (ω : ConfigurationPath N L) :
    ConfigurationPath N L := ω.comp (suffixTime u)

lemma configurationPrefix_continuous (N : ℕ) (L : Length) (u : Time) :
    Continuous (configurationPrefix N L u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath N L × Time ↦ p.1 (prefixTime u p.2))
  fun_prop

lemma configurationSuffix_continuous (N : ℕ) (L : Length) (u : Time) :
    Continuous (configurationSuffix N L u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath N L × Time ↦ p.1 (suffixTime u p.2))
  fun_prop

lemma coordinateSplit_preserving (N : ℕ) (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) :
    MeasurePreserving (fun w : CoordinatePaths N ↦
      (fun p ↦ normalizedPrefix u (w p), fun p ↦ normalizedSuffix u (w p)))
      (coordinateWiener N) ((coordinateWiener N).prod (coordinateWiener N)) := by
  have hm : Measurable (fun w : CoordinatePaths N ↦
      fun p ↦ (normalizedPrefix u (w p),normalizedSuffix u (w p))) := by fun_prop
  have h : MeasurePreserving (fun w : CoordinatePaths N ↦
      fun p ↦ (normalizedPrefix u (w p),normalizedSuffix u (w p)))
      (coordinateWiener N) (Measure.pi fun _ : Direction N ↦ wiener.prod wiener) := by
    refine ⟨hm,?_⟩
    unfold coordinateWiener
    rw [Measure.pi_map_pi (fun _ ↦ (normalized_split_preserving u hu hu').measurable.aemeasurable)]
    simp_rw [(normalized_split_preserving u hu hu').map_eq]
  exact (measurePreserving_arrowProdEquivProdArrow C(Time,ℝ) C(Time,ℝ) (Direction N)
    (fun _ ↦ wiener) (fun _ ↦ wiener)).comp h

lemma prefix_freeTrajectory (N : ℕ) (L : Length) (s t : ℝ) (hs : 0<s) (ht : 0<t)
    (w : CoordinatePaths N) (X : Configuration N L) :
    configurationPrefix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X) =
      freeTrajectory N L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X := by
  ext v i j
  change X i j + ((Real.sqrt (2*(s+t))*w (i,j) (prefixTime _ v):ℝ):AddCircle L.val)=
    X i j + ((Real.sqrt (2*s)*((Real.sqrt (_:ℝ))⁻¹*w (i,j) (prefixTime _ v)):ℝ):AddCircle L.val)
  rw [← mul_assoc,sqrt_split_left]

lemma suffix_freeTrajectory (N : ℕ) (L : Length) (s t : ℝ) (hs : 0<s) (ht : 0<t)
    (w : CoordinatePaths N) (X : Configuration N L) :
    configurationSuffix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X) =
      freeTrajectory N L t (fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p))
        (freeTrajectory N L (s+t) w X (splitTime s t hs ht)) := by
  ext v i j
  change X i j + ((Real.sqrt (2*(s+t))*w (i,j) (suffixTime _ v):ℝ):AddCircle L.val)=
    (X i j + ((Real.sqrt (2*(s+t))*w (i,j) _ :ℝ):AddCircle L.val))+
      ((Real.sqrt (2*t)*((Real.sqrt (1-(_:ℝ)))⁻¹*(w (i,j) (suffixTime _ v)-w (i,j) _)):ℝ):AddCircle L.val)
  rw [← mul_assoc,sqrt_split_right,mul_sub,AddCircle.coe_sub]
  abel

@[simp] lemma prefixTime_one (u : Time) : prefixTime u 1=u := by
  apply Subtype.ext
  simp [prefixTime]

@[simp] lemma prefixTime_zero (u : Time) : prefixTime u 0=0 := by
  apply Subtype.ext
  simp [prefixTime]

@[simp] lemma suffixTime_zero (u : Time) : suffixTime u 0=u := by
  apply Subtype.ext
  simp [suffixTime]

@[simp] lemma suffixTime_one (u : Time) : suffixTime u 1=1 := by
  apply Subtype.ext
  simp [suffixTime]

lemma staysAllowed_split (N : ℕ) (L : Length) (a : ℝ) (u : Time)
    (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) (ω : ConfigurationPath N L) :
    ω∈staysAllowed N L a ↔
      configurationPrefix N L u ω ∈ staysAllowed N L a ∧
      configurationSuffix N L u ω ∈ staysAllowed N L a := by
  simp only [staysAllowed,Set.mem_ofPred_eq,Set.range_subset_iff]
  change (∀ v,ω v∈allowed N L a) ↔
    (∀ v,ω (prefixTime u v)∈allowed N L a) ∧ (∀ v,ω (suffixTime u v)∈allowed N L a)
  constructor
  · intro h
    exact ⟨fun v ↦ h _,fun v ↦ h _⟩
  · rintro ⟨h₁,h₂⟩ v
    by_cases hv : (v:ℝ)≤u
    · let z : Time := ⟨(v:ℝ)/(u:ℝ),div_nonneg v.property.1 hu.le,(div_le_one hu).mpr hv⟩
      have hz : prefixTime u z=v := by
        apply Subtype.ext
        change (u:ℝ)*((v:ℝ)/(u:ℝ))=(v:ℝ)
        field_simp
      simpa only [hz] using h₁ z
    · let z : Time := ⟨((v:ℝ)-(u:ℝ))/(1-(u:ℝ)),
          div_nonneg (sub_nonneg.mpr (le_of_not_ge hv)) (sub_pos.mpr hu').le,
          (div_le_one (sub_pos.mpr hu')).mpr (by linarith [v.property.2])⟩
      have hz : suffixTime u z=v := by
        apply Subtype.ext
        change (u:ℝ)+(1-(u:ℝ))*(((v:ℝ)-(u:ℝ))/(1-(u:ℝ)))=(v:ℝ)
        field_simp [ne_of_gt (sub_pos.mpr hu')]
        ring
      simpa only [hz] using h₂ z

lemma split_freePathLaw (N : ℕ) (L : Length) (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    (freePathLaw N L (s+t)).map (fun ω ↦
      (configurationPrefix N L (splitTime s t hs ht) ω,
        configurationSuffix N L (splitTime s t hs ht) ω)) =
      (((coordinateWiener N).prod (coordinateWiener N)).prod
        (volume : Measure (Configuration N L))).map (fun p ↦
          (freeTrajectory N L s p.1.1 p.2,
            freeTrajectory N L t p.1.2 (freeTrajectory N L s p.1.1 p.2 1))) := by
  have h := (coordinateSplit_preserving N (splitTime s t hs ht)
    (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht)).prod (MeasurePreserving.id (volume : Measure (Configuration N L)))
  have hm : Measurable (fun p : ((CoordinatePaths N × CoordinatePaths N) × Configuration N L) ↦
      (freeTrajectory N L s p.1.1 p.2,
        freeTrajectory N L t p.1.2 (freeTrajectory N L s p.1.1 p.2 1))) := by
    exact ((freeTrajectory_continuous N L s |>.comp (continuous_fst.fst.prodMk continuous_snd)).prodMk
      (freeTrajectory_continuous N L t |>.comp (continuous_fst.snd.prodMk
        ((freeTrajectory_continuous N L s |>.comp (continuous_fst.fst.prodMk continuous_snd)).eval continuous_const)))).measurable
  rw [freePathLaw,Measure.map_map
    ((configurationPrefix_continuous N L _).prodMk (configurationSuffix_continuous N L _)).measurable
    (freeTrajectory_continuous N L (s+t)).measurable,← h.map_eq,Measure.map_map hm h.measurable]
  congr 1
  funext p
  apply Prod.ext
  · exact prefix_freeTrajectory N L s t hs ht p.1 p.2
  · dsimp only [Function.comp_def,Prod.map,id_eq]
    rw [suffix_freeTrajectory N L s t hs ht]
    congr 1
    have heq := congrArg (fun ω : ConfigurationPath N L ↦ ω 1)
      (prefix_freeTrajectory N L s t hs ht p.1 p.2)
    simpa only [configurationPrefix,ContinuousMap.comp_apply,prefixTime_one] using heq

end HardSphere

end

end OAI
