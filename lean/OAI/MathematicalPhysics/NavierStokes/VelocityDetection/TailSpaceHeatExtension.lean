import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceRestrictRestrict
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TimeIntegral

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

def heatExtension {a : ℕ} (ν s : ℝ) (J : compatibleJets 2 (a + 2)) : compatibleJets 2 a :=
  heat ν s (restrict (by omega : a ≤ a + 2) J) + min s 0 • (ν • laplaceJet J)

@[simp] theorem heatExtension_of_nonneg {a : ℕ} (ν : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (J : compatibleJets 2 (a + 2)) :
    heatExtension ν s J = heat ν s (restrict (by omega : a ≤ a + 2) J) := by
  simp only [heatExtension, min_eq_right hs, zero_smul, add_zero]

theorem heat_of_nonpos {a : ℕ} {ν s : ℝ} (hν : 0 ≤ ν) (hs : s ≤ 0)
    (J : compatibleJets 2 a) : heat ν s J = J := by
  have he : Real.sqrt (2 * ν * s) = 0 := Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hs)
  simpa only [heat, he, mul_zero, Real.sqrt_zero, neg_zero] using heat_zero ν J

theorem heatExtension_of_nonpos {a : ℕ} {ν s : ℝ} (hν : 0 ≤ ν) (hs : s ≤ 0)
    (J : compatibleJets 2 (a + 2)) :
    heatExtension ν s J = restrict (by omega : a ≤ a + 2) J + s • (ν • laplaceJet J) := by
  rw [heatExtension, heat_of_nonpos hν hs, min_eq_left hs]

theorem continuous_heatExtension {a : ℕ} (ν : ℝ) :
    Continuous (fun p : ℝ × compatibleJets 2 (a + 2) => heatExtension ν p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × compatibleJets 2 (a + 2) =>
      (p.1, restrict (by omega : a ≤ a + 2) p.2)) := by
    have hr := (restrictL (n := 2) (a := a) (b := a + 2) (by omega : a ≤ a + 2)).continuous
    exact continuous_fst.prodMk (hr.comp continuous_snd)
  have hh := (continuous_heat_joint (a := a) ν).comp hc
  have hl : Continuous (fun p : ℝ × compatibleJets 2 (a + 2) => laplaceJet p.2) :=
    (laplaceL 2 a).continuous.comp continuous_snd
  have hm : Continuous (fun p : ℝ × compatibleJets 2 (a + 2) => min p.1 0) :=
    continuous_fst.min continuous_const
  have hg := hh.add (hm.smul (hl.const_smul ν))
  convert hg using 1
  rfl

theorem continuous_heatExtension_derivative {a : ℕ} (ν : ℝ) :
    Continuous (fun p : ℝ × compatibleJets 2 (a + 2) => ν • heat ν p.1 (laplaceJet p.2)) := by
  have hc : Continuous (fun p : ℝ × compatibleJets 2 (a + 2) => (p.1, laplaceJet p.2)) :=
    continuous_fst.prodMk ((laplaceL 2 a).continuous.comp continuous_snd)
  have hh := ((continuous_heat_joint (a := a) ν).comp hc).const_smul ν
  convert hh using 1
  rfl

theorem hasDerivAt_heatExtension {a : ℕ} {ν : ℝ} (hν : 0 < ν)
    (J : compatibleJets 2 (a + 2)) (s : ℝ) :
    HasDerivAt (fun r => heatExtension ν r J) (ν • heat ν s (laplaceJet J)) s := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have he : (fun r => heatExtension ν r J) =ᶠ[𝓝 s]
        (fun r => restrict (by omega : a ≤ a + 2) J + r • (ν • laplaceJet J)) := by
      filter_upwards [Iio_mem_nhds hs] with r hr
      exact heatExtension_of_nonpos hν.le hr.le J
    rw [heat_of_nonpos hν.le hs.le]
    apply HasDerivAt.congr_of_eventuallyEq _ he
    have hh := ((hasDerivAt_id s).smul_const (ν • laplaceJet J)).const_add
      (restrict (by omega : a ≤ a + 2) J)
    simp only [one_smul, id_eq] at hh
    convert hh using 1
  · rw [heat_zero]
    have hl : HasDerivWithinAt (fun r => heatExtension ν r J) (ν • laplaceJet J) (Iic (0 : ℝ)) 0 := by
      have hh : HasDerivAt (fun r : ℝ => restrict (by omega : a ≤ a + 2) J + r • (ν • laplaceJet J))
          (ν • laplaceJet J) 0 := by
        have he := ((hasDerivAt_id (0 : ℝ)).smul_const (ν • laplaceJet J)).const_add
          (restrict (by omega : a ≤ a + 2) J)
        simp only [one_smul, id_eq] at he
        convert he using 1
      exact hh.hasDerivWithinAt.congr_of_mem (fun r hr => heatExtension_of_nonpos hν.le hr J) (by simp)
    have hr : HasDerivWithinAt (fun r => heatExtension ν r J) (ν • laplaceJet J) (Ici (0 : ℝ)) 0 :=
      (hasDerivWithinAt_heat_zero hν J).congr_of_mem (fun r hr => heatExtension_of_nonneg ν hr J) (by simp)
    have hh := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at hh
  · have he : (fun r => heatExtension ν r J) =ᶠ[𝓝 s]
        (fun r => heat ν r (restrict (by omega : a ≤ a + 2) J)) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      exact heatExtension_of_nonneg ν hr.le J
    exact (hasDerivAt_heat hν hs J).congr_of_eventuallyEq he

def duhamel {a : ℕ} (ν : ℝ) (F : ℝ → compatibleJets 2 (a + 2)) (t : ℝ) :
    compatibleJets 2 a := ∫ r in (0 : ℝ)..t, heat ν (t-r) (restrict (by omega : a ≤ a + 2) (F r))

def extendedDuhamel {a : ℕ} (ν : ℝ) (F : ℝ → compatibleJets 2 (a + 2)) (t : ℝ) :
    compatibleJets 2 a := ∫ r in (0 : ℝ)..t, heatExtension ν (t-r) (F r)

theorem extendedDuhamel_eq {a : ℕ} (ν : ℝ) (F : ℝ → compatibleJets 2 (a + 2))
    {t : ℝ} (ht : 0 ≤ t) : extendedDuhamel ν F t = duhamel ν F t := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht] at hr
  exact heatExtension_of_nonneg ν (sub_nonneg.mpr hr.2) (F r)

theorem hasDerivAt_extendedDuhamel {a : ℕ} {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → compatibleJets 2 (a + 2)} (hF : Continuous F) (t : ℝ) :
    HasDerivAt (extendedDuhamel ν F)
      ((∫ r in (0 : ℝ)..t, ν • heat ν (t-r) (laplaceJet (F r))) +
        restrict (by omega : a ≤ a + 2) (F t)) t := by
  have hc : Continuous (fun p : ℝ × ℝ => (p.1-p.2, F p.2)) :=
    (continuous_fst.sub continuous_snd).prodMk (hF.comp continuous_snd)
  have hK := (continuous_heatExtension (a := a) ν).comp hc
  have hL := (continuous_heatExtension_derivative (a := a) ν).comp hc
  have hd (s r : ℝ) : HasDerivAt (fun t => heatExtension ν (t-r) (F r))
      (ν • heat ν (s-r) (laplaceJet (F r))) s := by
    have hh := (hasDerivAt_heatExtension hν (F r) (s-r)).scomp s ((hasDerivAt_id s).sub_const r)
    simpa only [one_smul, comp_def, id_eq] using hh
  have hh := TimeIntegral.hasDerivAt_diagonal
    (K := fun s r => heatExtension ν (s-r) (F r))
    (L := fun s r => ν • heat ν (s-r) (laplaceJet (F r))) hK hL hd 0 t
  simp only [sub_self, heatExtension_of_nonneg ν le_rfl, heat_zero] at hh
  convert hh using 1
  rfl

theorem hasDerivWithinAt_duhamel {a : ℕ} {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → compatibleJets 2 (a + 2)} (hF : Continuous F) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (duhamel ν F)
      ((∫ r in (0 : ℝ)..t, ν • heat ν (t-r) (laplaceJet (F r))) +
        restrict (by omega : a ≤ a + 2) (F t)) (Ici (0 : ℝ)) t := by
  exact (hasDerivAt_extendedDuhamel hν hF t).hasDerivWithinAt.congr_of_mem
    (fun r hr => (extendedDuhamel_eq ν F hr).symm) ht

end VelocityDetection.TailSpace.Jets
end

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

@[simp] theorem differentiateL_apply {n a : ℕ} (i : Fin n)
    (J : compatibleJets n (a+1)) : differentiateL i J = differentiate i J := rfl

@[simp] theorem differentiate_translate {n a : ℕ} (i : Fin n) (Y : Coord n)
    (J : compatibleJets n (a+1)) :
    differentiate i (translate Y J) = translate Y (differentiate i J) := by
  apply Subtype.ext
  rfl

@[simp] theorem differentiate_average {n a : ℕ} (i : Fin n) {k : Coord n → ℝ}
    (hk : Integrable k) (s : ℝ) (J : compatibleJets n (a+1)) :
    differentiate i (average k s J) = average k s (differentiate i J) := by
  have hh := (differentiateL (n := n) (a := a) i).integral_comp_comm
    (integrable_average (a := a+1) hk s J)
  simpa only [map_smul, differentiateL_apply, differentiate_translate, average] using hh.symm

@[simp] theorem differentiate_heat {a : ℕ} (i : Fin 2) (ν t : ℝ)
    (J : compatibleJets 2 (a+1)) :
    differentiate i (heat ν t J) = heat ν t (differentiate i J) :=
  differentiate_average i (HeatKernels.integrable_normal 2) _ J

@[simp] theorem laplace_heat {a : ℕ} (ν t : ℝ) (J : compatibleJets 2 (a+2)) :
    laplaceJet (heat ν t J) = heat ν t (laplaceJet J) := by
  simp only [laplaceJet, differentiate_heat, map_sum]

@[simp] theorem restrict_laplace {n a b : ℕ} (hab : a ≤ b)
    (J : compatibleJets n (b+2)) :
    restrict hab (laplaceJet J) = laplaceJet (restrict (Nat.add_le_add_right hab 2) J) := by
  change restrictL hab (∑ i : Fin n, differentiate i (differentiate i J)) = _
  rw [map_sum]
  simp only [restrictL_apply, restrict_differentiate, laplaceJet]

theorem laplace_integral_heat {a : ℕ} {F : ℝ → compatibleJets 2 (a+2)}
    (hF : Continuous F) (ν t : ℝ) :
    laplaceJet (∫ r in (0:ℝ)..t, heat ν (t-r) (F r)) =
      ∫ r in (0:ℝ)..t, heat ν (t-r) (laplaceJet (F r)) := by
  have hc : Continuous (fun r : ℝ => (t-r,F r)) :=
    (continuous_const.sub continuous_id).prodMk hF
  have hh := (continuous_heat_joint (a := a+2) ν).comp hc
  have he := (laplaceL 2 a).intervalIntegral_comp_comm (μ := volume) (hh.intervalIntegrable 0 t)
  simpa only [comp_def, laplaceL_apply, laplace_heat] using he.symm

end VelocityDetection.TailSpace.Jets
end

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

theorem hasDerivAt_of_evaluations {a : ℕ} {F G : ℝ → compatibleJets 2 a}
    (hG : Continuous G)
    (hd : ∀ t X, HasDerivAt (fun s => value (F s) X) (value (G t) X) t) (t : ℝ) :
    HasDerivAt F (G t) t := by
  have he (s : ℝ) : F s = F 0 + ∫ r in (0:ℝ)..s, G r := by
    apply value_injective
    funext X
    change value (F s) X = evaluate X (F 0 + ∫ r in (0:ℝ)..s, G r)
    rw [map_add]
    have hh := (evaluate (a := a) X).intervalIntegral_comp_comm (μ := volume)
      (hG.intervalIntegrable 0 s)
    rw [← hh]
    simp only [evaluate_apply]
    have hc : Continuous (fun r : ℝ => value (G r) X) := (evaluate X).continuous.comp hG
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r X)
      (hc.intervalIntegrable 0 s)]
    ring
  let : SecondCountableTopologyEither ℝ (compatibleJets 2 a) :=
    secondCountableTopologyEither_of_left _ _
  have hh := (intervalIntegral.integral_hasDerivAt_right (E := compatibleJets 2 a)
    (hG.intervalIntegrable 0 t) hG.stronglyMeasurable.stronglyMeasurableAtFilter
    hG.continuousAt).const_add (F 0)
  exact hh.congr_of_eventuallyEq (Eventually.of_forall he)

end VelocityDetection.TailSpace.Jets
end

end OAI
