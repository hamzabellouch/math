import Mathlib
import OAI.Probability.SKFluctuations.ScalarTwoClockPressure

namespace OAI

/-! Scalar Weighted Jet. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

noncomputable def scalarWeightedJet : HeatJet 0 where
  F := fun x => Scalar.logCosh (x 0)
  A := fun x => Real.tanh (x 0)
  G := fun _ x => Real.tanh (x 0)
  H := fun _ x => Scalar.curvature (x 0)
  A₁ := fun _ x => Scalar.curvature (x 0)
  A₂ := fun _ x => Scalar.third (x 0)
  C := 1
  lipschitz := by
    simpa only [one_mul,Function.comp_def] using Scalar.logCosh_lipschitz.comp (LipschitzWith.eval (0 : Fin 1))
  smoothA := scalarTanh_bddSmooth
  smoothG _ := scalarTanh_bddSmooth
  smoothH _ := scalarCurvature_bddSmooth
  smoothA₁ _ := scalarCurvature_bddSmooth
  smoothA₂ _ := scalarThird_bddSmooth
  derivF x v t := by
    change HasDerivAt (fun s => Scalar.logCosh ((x+s • v) 0))
      (∑ i : Fin 1, v i*Real.tanh ((x+t • v) 0)) t
    have hd := (Scalar.logCosh_derivative (x 0+t*v 0)).comp t
      (((hasDerivAt_id t).mul_const (v 0)).const_add (x 0))
    simpa only [Fin.sum_univ_one,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Function.comp_def,id_eq,one_mul,mul_comm] using hd
  derivG i x t := by
    have hi : i = 0 := (show Subsingleton (Fin 1) from inferInstance).elim _ _
    subst i
    have hd := (Scalar.tanh_derivative (x 0+t)).comp t ((hasDerivAt_id t).const_add (x 0))
    simpa only [Pi.add_apply,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one,Function.comp_def,id_eq] using hd
  derivA := scalarTanh_derivative
  derivA₁ := scalarCurvature_derivative

 theorem scalarWeightedJet_F : scalarWeightedJet.F = scalarTerminal.F := by
  funext x
  exact (scalarTerminal_F x).symm

 theorem scalarWeightedJet_mass_one {t : ℝ} (ht : 0 ≤ t) (x : Fin 1 → ℝ) :
    clockContinuation 1 scalarWeightedJet.F t x = scalarWeightedJet.F x+t/2 := by
  have hh := scalarTerminal_mass_one (Real.toNNReal t) x
  rw [Real.coe_toNNReal _ ht,← scalarWeightedJet_F] at hh
  exact hh

 

theorem scalarWeightedSquare_derivative_zero (a : ℝ) (x : Fin 1 → ℝ) :
    HasDerivWithinAt (fun t => clockTest a scalarWeightedJet.F scalarWeightedJet.square.A t x)
      ((Scalar.curvature (x 0))^2+2*(a-1)*(Real.tanh (x 0))^2*Scalar.curvature (x 0))
      (Ici 0) 0 := by
  let J := scalarWeightedJet.square
  have hh := hasDerivWithinAt_clockTest J.lipschitz J.smoothA J.smoothG J.smoothH J.smoothA₁ J.smoothA₂
    J.derivF J.derivG J.derivA J.derivA₁ a x (show (0:ℝ) ≤ 0 from le_rfl)
  apply hh.congr_deriv
  simp only [clockTest_zero,potentialHeatTrace,testedHeatTrace,
    J,HeatJet.square,scalarWeightedJet,Scalar.third]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  norm_num only [nsmul_eq_mul,Nat.cast_add,Nat.cast_zero,Nat.cast_one,zero_add,one_mul]
  ring

 theorem scalarWeightedSquare_initial (a : ℝ) (x : Fin 1 → ℝ) :
    clockTest a scalarWeightedJet.F scalarWeightedJet.square.A 0 x = (Real.tanh (x 0))^2 :=
  clockTest_zero a x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 

theorem integral_hasDerivWithinAt_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f df : ℝ → Ω → ℝ}
    (hi : ∀ t ∈ Ici (0:ℝ), Integrable (f t) μ)
    (hd : ∀ x t, 0 ≤ t → HasDerivWithinAt (fun s => f s x) (df t x) (Ici 0) t)
    {C : ℝ≥0} (hb : ∀ x t, 0 ≤ t → |df t x| ≤ C) :
    HasDerivWithinAt (fun t => ∫ x, f t x ∂μ) (∫ x, df 0 x ∂μ) (Ici 0) 0 := by
  have hL : ∀ x, LipschitzOnWith C (fun t => f t x) (Ici (0:ℝ)) := by
    intro x
    apply (convex_Ici (0:ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => hd x t ht)
    intro t ht
    exact_mod_cast (show ‖df t x‖ ≤ (C:ℝ) by simpa only [Real.norm_eq_abs] using hb x t ht)
  have hB : ∀ t ∈ Ioi (0:ℝ), ∀ x, ‖slope (fun s => f s x) 0 t‖ ≤ C := by
    intro t ht x
    have hh := (hL x).dist_le_mul t (mem_Ici.mpr (mem_Ioi.mp ht).le) 0 (by simp)
    simp only [Real.dist_eq,sub_zero] at hh
    rw [slope_def_field,sub_zero,norm_div,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (mem_Ioi.mp ht),div_le_iff₀ (mem_Ioi.mp ht)]
    simpa only [abs_of_pos (mem_Ioi.mp ht)] using hh
  have hM : ∀ t ∈ Ioi (0:ℝ), Integrable (fun x => slope (fun s => f s x) 0 t) μ := by
    intro t ht
    simpa only [slope_def_field,sub_zero,Pi.sub_apply] using ((hi t (mem_Ici.mpr (mem_Ioi.mp ht).le)).sub (hi 0 (by simp))).div_const t
  have hD := tendsto_integral_filter_of_norm_le_const (μ := μ) (l := 𝓝[>] (0:ℝ))
    (F := fun t x => slope (fun s => f s x) 0 t)
    (f := fun x => df 0 x)
    ((show ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Ioi 0 from self_mem_nhdsWithin).mono fun t ht => (hM t ht).aestronglyMeasurable)
    ⟨(C:ℝ), (show ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Ioi 0 from self_mem_nhdsWithin).mono fun t ht => Eventually.of_forall (hB t ht)⟩
    (Eventually.of_forall fun x =>
      (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).mp
        ((hd x 0 (by simp)).mono Ioi_subset_Ici_self))
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).mpr
  apply hD.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [slope_def_field,sub_zero]
  rw [integral_div,integral_sub (hi t (mem_Ici.mpr (mem_Ioi.mp ht).le)) (hi 0 (by simp))]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

noncomputable def scalarInsertedOverlap (a : ℝ) (v : ℝ≥0) (t : ℝ) : ℝ :=
  ∫ z, clockTest a scalarWeightedJet.F scalarWeightedJet.square.A t (fun _ => z) ∂gaussianReal 0 v

 theorem scalarInsertedOverlap_zero (a : ℝ) (v : ℝ≥0) :
    scalarInsertedOverlap a v 0 = ∫ z, (Real.tanh z)^2 ∂gaussianReal 0 v := by
  unfold scalarInsertedOverlap
  simp only [scalarWeightedSquare_initial]

 theorem scalarInsertedOverlap_derivative_zero (a : ℝ) (v : ℝ≥0) :
    HasDerivWithinAt (scalarInsertedOverlap a v)
      (∫ z, (Scalar.curvature z)^2+2*(a-1)*(Real.tanh z)^2*Scalar.curvature z ∂gaussianReal 0 v)
      (Ici 0) 0 := by
  let J := scalarWeightedJet.square
  obtain ⟨C,hC,hb⟩ := clockTestDerivative_absBounded J.lipschitz J.smoothA J.smoothG J.smoothH J.smoothA₁ J.smoothA₂ a
  have hd := integral_hasDerivWithinAt_zero (μ := gaussianReal 0 v)
    (f := fun t z => clockTest a J.F J.A t (fun _ => z))
    (df := fun t z => clockTestDerivative a J.F J.G J.H J.A J.A₁ J.A₂ t (fun _ => z))
    (C := NNReal.mk C hC)
    (fun t _ => by
      obtain ⟨B,_,hB⟩ := (clockTest_bddSmooth J.regular J.smoothA a t).bound
      exact Integrable.of_bound
        (((clockTest_bddSmooth J.regular J.smoothA a t).continuous.comp
          (continuous_pi fun _ => continuous_id)).aestronglyMeasurable) B
        (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hB (fun _ => z)))
    (fun z t ht => hasDerivWithinAt_clockTest J.lipschitz J.smoothA J.smoothG J.smoothH J.smoothA₁ J.smoothA₂
      J.derivF J.derivG J.derivA J.derivA₁ a (fun _ => z) ht)
    (fun z t _ => hb (t,fun _ => z))
  apply hd.congr_deriv
  apply integral_congr_ae
  filter_upwards [] with z
  apply UniqueDiffWithinAt.eq_deriv (Ici 0) (uniqueDiffWithinAt_Ici (0:ℝ))
  · exact hasDerivWithinAt_clockTest J.lipschitz J.smoothA J.smoothG J.smoothH J.smoothA₁ J.smoothA₂
      J.derivF J.derivG J.derivA J.derivA₁ a (fun _ => z) (show (0:ℝ) ≤ 0 from le_rfl)
  · exact scalarWeightedSquare_derivative_zero a (fun _ => z)

 theorem scalarInsertedSlope_continuous (v : ℝ≥0) :
    Continuous (fun a : ℝ => ∫ z, (Scalar.curvature z)^2+
      2*(a-1)*(Real.tanh z)^2*Scalar.curvature z ∂gaussianReal 0 v) := by
  have h₁ : Integrable (fun z => (Scalar.curvature z)^2) (gaussianReal 0 v) := by
    exact Integrable.of_bound (Scalar.curvature_continuous.pow 2).aestronglyMeasurable 1
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Scalar.curvature z))] using
          (sq_le_one_iff_abs_le_one (Scalar.curvature z)).mpr (by simpa only [abs_of_nonneg (Scalar.curvature_bounds z).1] using (Scalar.curvature_bounds z).2))
  have h₂ : Integrable (fun z => (Real.tanh z)^2*Scalar.curvature z) (gaussianReal 0 v) := by
    exact Integrable.of_bound ((Scalar.tanh_continuous.pow 2).mul Scalar.curvature_continuous).aestronglyMeasurable 1
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonneg (Scalar.curvature_bounds z).1]
        exact (mul_le_mul ((sq_le_one_iff_abs_le_one _).mpr (Real.abs_tanh_lt_one z).le)
          (Scalar.curvature_bounds z).2 (Scalar.curvature_bounds z).1 (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul 1))
  have he (a : ℝ) : (∫ z, (Scalar.curvature z)^2+2*(a-1)*(Real.tanh z)^2*Scalar.curvature z ∂gaussianReal 0 v) =
      (∫ z, (Scalar.curvature z)^2 ∂gaussianReal 0 v)+2*(a-1)*(∫ z, (Real.tanh z)^2*Scalar.curvature z ∂gaussianReal 0 v) := by
    have heq : (fun z => (Scalar.curvature z)^2+2*(a-1)*(Real.tanh z)^2*Scalar.curvature z) =
        (fun z => (Scalar.curvature z)^2+(2*(a-1))*((Real.tanh z)^2*Scalar.curvature z)) := by funext z; ring
    rw [heq,integral_add h₁ (h₂.const_mul _),integral_const_mul]
  simp_rw [he]
  fun_prop

 

theorem scalarInsertedSlope_supercritical {T q : ℝ} (hT : 0 < T) (hq : 0 < q)
    (hfix : q = ∫ z, (Real.tanh z)^2 ∂gaussianReal 0 (Real.toNNReal (T*q))) :
    ∃ a ∈ Ioo (0:ℝ) 1, 1/T <
      ∫ z, (Scalar.curvature z)^2+2*(a-1)*(Real.tanh z)^2*Scalar.curvature z
        ∂gaussianReal 0 (Real.toNNReal (T*q)) := by
  have hr := Scalar.rs_replicon_strict hT hq hfix
  have hp : 1/T < ∫ z, (Scalar.curvature z)^2 ∂gaussianReal 0 (Real.toNNReal (T*q)) :=
    (div_lt_iff₀ hT).mpr (by simpa only [mul_comm] using hr)
  have hp1 : 1/T < ∫ z, (Scalar.curvature z)^2+2*((1:ℝ)-1)*(Real.tanh z)^2*Scalar.curvature z
      ∂gaussianReal 0 (Real.toNNReal (T*q)) := by simpa only [sub_self,mul_zero,zero_mul,add_zero] using hp
  have he := ((scalarInsertedSlope_continuous (Real.toNNReal (T*q))).continuousAt (x := 1)).tendsto.eventually
    (lt_mem_nhds hp1)
  have he' : ∀ᶠ a in 𝓝[<] (1:ℝ), 1/T <
      ∫ z, (Scalar.curvature z)^2+2*(a-1)*(Real.tanh z)^2*Scalar.curvature z
        ∂gaussianReal 0 (Real.toNNReal (T*q)) := nhdsWithin_le_nhds he
  have hn : ∀ᶠ a in 𝓝[<] (1:ℝ), 0 < a :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0:ℝ) < 1))
  obtain ⟨a,ha,hp,hl⟩ := (he'.and (hn.and self_mem_nhdsWithin)).exists
  exact ⟨a,⟨hp,hl⟩,ha⟩

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem integral_fin_one {f : (Fin 1 → ℝ) → ℝ} (hf : Continuous f) (v : ℝ≥0) :
    (∫ z, f z ∂Measure.pi fun _ : Fin 1 => gaussianReal 0 v) =
      ∫ y, f (fun _ => y) ∂gaussianReal 0 v := by
  have hh := integral_gaussian_eval (0 : Fin 1) v (hf.comp (continuous_pi fun _ => continuous_id))
  simp only [Function.comp_apply,id_eq] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  funext i
  exact congrArg z (Subsingleton.elim _ _)

 theorem scalar_clockDerivative (a t : ℝ) (x : Fin 1 → ℝ) :
    clockDerivative a scalarWeightedJet.F scalarWeightedJet.G scalarWeightedJet.H t x =
      (1+(a-1)*clockTest a scalarWeightedJet.F scalarWeightedJet.square.A t x)/2 := by
  have he : (fun y : Fin 1 → ℝ => Scalar.curvature (y 0)) =
      (fun y => (1:ℝ)+(-1)*scalarWeightedJet.square.A y) := by
    funext y
    simp only [Scalar.curvature,HeatJet.square,scalarWeightedJet]
    ring
  have hconst : clockTest a scalarWeightedJet.F (fun _ => (1:ℝ)) t x = 1 :=
    shiftedMean_const 1 ((exponentialIncrement_gaussian (fun _ : Fin 1 => Real.toNNReal t)).integrable_shift scalarWeightedJet.lipschitz a x)
  change (1/2:ℝ)*((∑ _ : Fin 1, clockTest a scalarWeightedJet.F (fun y => Scalar.curvature (y 0)) t x)+
      a*∑ _ : Fin 1, clockTest a scalarWeightedJet.F (fun y => (Real.tanh (y 0))^2) t x) = _
  rw [Fin.sum_univ_one,Fin.sum_univ_one,he,
    clockTest_add_test scalarWeightedJet.lipschitz (BddSmooth.const 0 1)
      (scalarWeightedJet.square.smoothA.const_mul (-1)),clockTest_const_mul,hconst]
  change (1/2:ℝ)*(1+(-1)*clockTest a scalarWeightedJet.F scalarWeightedJet.square.A t x+
    a*clockTest a scalarWeightedJet.F scalarWeightedJet.square.A t x) = _
  ring

noncomputable def scalarInsertedPotential (a : ℝ) (v : ℝ≥0) (t : ℝ) : ℝ :=
  zeroContinuation (Measure.pi fun _ : Fin 1 => gaussianReal 0 v)
    (clockContinuation a scalarWeightedJet.F t) 0

 theorem scalarInsertedPotential_continuous {a : ℝ} (ha : 0 < a) (v : ℝ≥0) :
    Continuous (scalarInsertedPotential a v) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [← continuousWithinAt_univ]
  exact continuousWithinAt_zeroContinuation (exponentialIncrement_gaussian (fun _ : Fin 1 => v))
    (fun s _ => (scalarWeightedJet.evolve ha s).lipschitz)
    (fun y => ((clockContinuation_continuous scalarWeightedJet.lipschitz a).comp
      (continuous_id.prodMk continuous_const)).continuousAt.continuousWithinAt) 0

 theorem scalarInsertedPotential_derivative {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (v : ℝ≥0) :
    HasDerivAt (scalarInsertedPotential a v) ((1+(a-1)*scalarInsertedOverlap a v t)/2) t := by
  obtain ⟨K,hK⟩ := parametric_clock scalarWeightedJet.lipschitz scalarWeightedJet.smoothG scalarWeightedJet.smoothH
    scalarWeightedJet.derivF scalarWeightedJet.derivG ha
  have hd := ((hK (t+1)).root (fun _ : Fin 1 => v)).derivative t ⟨ht,by linarith⟩ 0
  apply hd.congr_deriv
  unfold zeroContinuation
  simp only [zero_add,scalar_clockDerivative]
  have hA := clockTest_bddSmooth scalarWeightedJet.regular scalarWeightedJet.square.smoothA a t
  obtain ⟨C,_,hC⟩ := hA.bound
  have hi : Integrable (clockTest a scalarWeightedJet.F scalarWeightedJet.square.A t)
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 v) :=
    Integrable.of_bound hA.continuous.aestronglyMeasurable C
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  rw [integral_div,integral_add (integrable_const _) (hi.const_mul _),integral_const_mul,
    integral_fin_one hA.continuous v]
  simp only [integral_const,probReal_univ,one_smul,scalarInsertedOverlap]

noncomputable def scalarRSBIncrement (T a q t : ℝ) : ℝ :=
  scalarInsertedPotential a (Real.toNNReal (T*q)) t-scalarInsertedPotential a (Real.toNNReal (T*q)) 0-
    t/2+(1-a)/2*q*t+(1-a)/(4*T)*t^2

 theorem scalarRSBIncrement_zero (T a q : ℝ) : scalarRSBIncrement T a q 0 = 0 := by
  simp [scalarRSBIncrement]

 theorem scalarRSBIncrement_continuous {a : ℝ} (ha : 0 < a) (T q : ℝ) :
    Continuous (scalarRSBIncrement T a q) := by
  unfold scalarRSBIncrement
  have hc := scalarInsertedPotential_continuous ha (Real.toNNReal (T*q))
  fun_prop

 theorem scalarRSBIncrement_derivative {T a t : ℝ} (hT : T ≠ 0) (ha : 0 < a) (ht : 0 < t) (q : ℝ) :
    HasDerivAt (scalarRSBIncrement T a q)
      ((a-1)/2*(scalarInsertedOverlap a (Real.toNNReal (T*q)) t-q-t/T)) t := by
  have hd := ((((scalarInsertedPotential_derivative ha ht (Real.toNNReal (T*q))).sub_const (scalarInsertedPotential a (Real.toNNReal (T*q)) 0)).sub
    ((hasDerivAt_id t).div_const 2)).add ((hasDerivAt_id t).const_mul ((1-a)/2*q))).add
    (((hasDerivAt_id t).pow 2).const_mul ((1-a)/(4*T)))
  apply hd.congr_deriv
  simp only [id_eq]
  field_simp [hT]
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 

theorem scalarRSB_descent {T q : ℝ} (hT : 0 < T) (hq : q ∈ Ioo (0:ℝ) 1)
    (hfix : q = ∫ z, (Real.tanh z)^2 ∂gaussianReal 0 (Real.toNNReal (T*q))) :
    ∃ a ∈ Ioo (0:ℝ) 1, ∃ t ∈ Ioo (0:ℝ) (T*(1-q)), scalarRSBIncrement T a q t < 0 := by
  obtain ⟨a,ha,hs⟩ := scalarInsertedSlope_supercritical hT hq.1 hfix
  let g : ℝ → ℝ := fun t => scalarInsertedOverlap a (Real.toNNReal (T*q)) t-q-t/T
  have hg0 : g 0 = 0 := by
    dsimp [g]
    rw [scalarInsertedOverlap_zero,← hfix]
    ring
  have hd := ((scalarInsertedOverlap_derivative_zero a (Real.toNNReal (T*q))).sub_const q).sub
    ((hasDerivWithinAt_id (0:ℝ) (Ici 0)).div_const T)
  have hp := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp
    (hd.mono (show Ioi (0:ℝ) ⊆ Ici (0:ℝ) from fun x h => by
      change (0:ℝ) ≤ x
      exact le_of_lt h))
  have he := hp.eventually (lt_mem_nhds (sub_pos.mpr hs))
  change ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < slope g 0 t at he
  obtain ⟨b,hb,hb'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  have hb0 : 0 < b := hb
  have hg (t : ℝ) (ht : t ∈ Ioo (0:ℝ) b) : 0 < g t := by
    have hh : 0 < slope g 0 t := hb' ht
    rw [slope_def_field,hg0,sub_zero,sub_zero] at hh
    exact (div_pos_iff.mp hh).resolve_right (fun h => (not_lt.mpr ht.1.le) h.2) |>.1
  let d : ℝ := min b (T*(1-q))/2
  have hd0 : 0 < d := div_pos (lt_min hb (mul_pos hT (sub_pos.mpr hq.2))) (by norm_num)
  have hdb : d < b := by
    dsimp [d]
    linarith [min_le_left b (T*(1-q)),hb0]
  have hdq : d < T*(1-q) := by
    dsimp [d]
    have hpos := mul_pos hT (sub_pos.mpr hq.2)
    linarith [min_le_right b (T*(1-q))]
  have hant : StrictAntiOn (scalarRSBIncrement T a q) (Icc 0 d) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 d) (scalarRSBIncrement_continuous ha.1 T q).continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(scalarRSBIncrement_derivative hT.ne' ha.1 ht.1 q).deriv]
    exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (sub_neg.mpr ha.2) (by norm_num))
      (hg t ⟨ht.1,ht.2.trans hdb⟩)
  refine ⟨a,ha,d,⟨hd0,hdq⟩,?_⟩
  simpa only [scalarRSBIncrement_zero] using hant ⟨le_rfl,hd0.le⟩ ⟨hd0.le,le_rfl⟩ hd0

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem scalarInsertedPotential_zero {a : ℝ} (ha : a ≠ 0) (v : ℝ≥0) :
    scalarInsertedPotential a v 0 = Scalar.rsHeat v := by
  have h1 : clockContinuation 1 scalarTerminal.F 0 = scalarTerminal.F := by
    funext x
    exact clockContinuation_zero (by norm_num : (1:ℝ) ≠ 0) x
  have h0 : clockContinuation a scalarWeightedJet.F 0 = scalarTerminal.F := by
    rw [scalarWeightedJet_F]
    funext x
    exact clockContinuation_zero ha x
  have hh := scalarRoot_mass_one v 0
  simp only [NNReal.coe_zero,h1,zero_div,add_zero] at hh
  change zeroContinuation (Measure.pi fun _ : Fin 1 => gaussianReal 0 v)
    (clockContinuation a scalarWeightedJet.F 0) 0 = _
  rw [h0]
  exact hh

 theorem scalarTwoClockPressure_collapse {T a q r : ℝ} (ha : 0 < a) (htr : 0 ≤ T-T*r) :
    scalarTwoClockPressure T a q r = scalarInsertedPotential a (Real.toNNReal (T*q)) (T*r-T*q)+(T-T*r)/2 := by
  have hF : clockContinuation 1 scalarTerminal.F (T-T*r) =
      fun x => scalarWeightedJet.F x+(T-T*r)/2 := by
    rw [← scalarWeightedJet_F]
    funext x
    exact scalarWeightedJet_mass_one htr x
  have hshift : clockContinuation a (fun x => scalarWeightedJet.F x+(T-T*r)/2) (T*r-T*q) =
      fun x => clockContinuation a scalarWeightedJet.F (T*r-T*q) x+(T-T*r)/2 := by
    funext x
    exact shiftedContinuation_add_const ha.ne'
      ((exponentialIncrement_gaussian (fun _ : Fin 1 => Real.toNNReal (T*r-T*q))).integrable_shift
        scalarWeightedJet.lipschitz a) _ x
  unfold scalarTwoClockPressure
  rw [hF,hshift]
  unfold scalarInsertedPotential zeroContinuation
  have hi : Integrable (fun z : Fin 1 → ℝ => clockContinuation a scalarWeightedJet.F (T*r-T*q) (0+z))
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 (Real.toNNReal (T*q))) :=
    (exponentialIncrement_gaussian (fun _ : Fin 1 => Real.toNNReal (T*q))).integrable_lipschitz
      (scalarWeightedJet.evolve ha (T*r-T*q)).lipschitz 0
  rw [integral_add hi (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Scalar
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 theorem gaussian_integral_rescale {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    (∫ y, f y ∂gaussianReal 0 (Real.toNNReal t)) =
      ∫ z, f (Real.sqrt t*z) ∂gaussianReal 0 1 := by
  have hh := integral_map_of_stronglyMeasurable (μ := gaussianReal 0 1) (φ := fun z : ℝ => Real.sqrt t*z)
    (measurable_const.mul measurable_id) hf.stronglyMeasurable
  rw [gaussianReal_map_const_mul] at hh
  have he : (NNReal.mk ((Real.sqrt t)^2) (sq_nonneg _))*1 = Real.toNNReal t := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk,mul_one,Real.sq_sqrt ht,Real.coe_toNNReal _ ht]
  simpa only [mul_zero,he] using hh

 theorem rsHeatSlope_gaussian {t : ℝ} (ht : 0 ≤ t) :
    rsHeatSlope t = (1/2:ℝ)*(1-∫ z, (Real.tanh z)^2 ∂gaussianReal 0 (Real.toNNReal t)) := by
  unfold rsHeatSlope
  rw [← gaussian_integral_rescale curvature_continuous ht]
  have hi : Integrable (fun z => (Real.tanh z)^2) (gaussianReal 0 (Real.toNNReal t)) :=
    Integrable.of_bound (tanh_continuous.pow 2).aestronglyMeasurable 1
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.tanh z))] using
          (sq_le_one_iff_abs_le_one _).mpr (Real.abs_tanh_lt_one z).le)
  simp only [curvature,integral_sub (integrable_const (1:ℝ)) hi,integral_const,probReal_univ,one_smul]

 theorem rsVariationSlope_gaussian {T q : ℝ} (hT : 0 ≤ T) (hq : 0 ≤ q) :
    rsVariationSlope T q = T/2*(q-∫ z, (Real.tanh z)^2 ∂gaussianReal 0 (Real.toNNReal (T*q))) := by
  unfold rsVariationSlope
  rw [rsHeatSlope_gaussian (mul_nonneg hT hq)]
  ring

 theorem rs_minimizer_fixed_point {T q : ℝ} (hT : 0 < T) (hq : q ∈ Ioo (0:ℝ) 1)
    (hmin : ∀ r ∈ Icc (0:ℝ) 1, rsVariation T q ≤ rsVariation T r) :
    q = ∫ z, (Real.tanh z)^2 ∂gaussianReal 0 (Real.toNNReal (T*q)) := by
  have hmn : IsMinOn (rsVariation T) (Icc (0:ℝ) 1) q := hmin
  have hh := (hmn.isLocalMin (Icc_mem_nhds hq.1 hq.2)).hasDerivAt_eq_zero
    ((rsVariation_derivative hT.le hq.1.le).hasDerivAt (Ici_mem_nhds hq.1))
  rw [rsVariationSlope_gaussian hT.le hq.1.le] at hh
  have : T/2 ≠ 0 := ne_of_gt (by positivity)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left this)

 theorem curvature_pos (z : ℝ) : 0 < curvature z := by
  have hh := (sq_lt_one_iff_abs_lt_one _).mpr (Real.abs_tanh_lt_one z)
  exact sub_pos.mpr hh

 theorem rsVariationSlope_one_pos {T : ℝ} (hT : 0 < T) : 0 < rsVariationSlope T 1 := by
  have hi : Integrable (fun z => curvature (Real.sqrt T*z)) (gaussianReal 0 1) := by
    simpa only [zero_add] using curvature_expBounded.affine_integrable 0 (Real.sqrt T)
  have hp : 0 < ∫ z, curvature (Real.sqrt T*z) ∂gaussianReal 0 1 := by
    apply (integral_pos_iff_support_of_nonneg (fun z => (curvature_pos _).le) hi).2
    have hs : Function.support (fun z => curvature (Real.sqrt T*z)) = univ := by
      ext z
      simp only [Function.mem_support,mem_univ,iff_true]
      exact (curvature_pos _).ne'
    rw [hs]
    simp
  unfold rsVariationSlope rsHeatSlope
  simp only [mul_one]
  nlinarith

 

theorem rs_one_not_minimizer {T : ℝ} (hT : 0 < T) :
    ¬ (∀ r ∈ Icc (0:ℝ) 1, rsVariation T 1 ≤ rsVariation T r) := by
  intro hm
  have hd := (rsVariation_derivative hT.le (by norm_num : (0:ℝ) ≤ 1)).hasDerivAt
    (Ici_mem_nhds (by norm_num : (0:ℝ) < 1))
  have he := (hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (1:ℝ))).eventually
    (lt_mem_nhds (rsVariationSlope_one_pos hT))
  have hn : ∀ᶠ r in 𝓝[<] (1:ℝ), 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0:ℝ) < 1))
  obtain ⟨r,hr,hp,hs⟩ := (he.and (hn.and self_mem_nhdsWithin)).exists
  have hm' := hm r ⟨hp.le,hs.le⟩
  rw [slope_def_field] at hr
  have hh := (div_pos_iff.mp hr)
  rcases hh with hh | hh
  · linarith [hh.2]
  · linarith [hh.1]

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 

theorem scalarParisiDiracMinimizer_replicon {T q : ℝ} (hT : 1 < T) (hq : q ∈ Icc (0:ℝ) 1)
    (hmin : ∀ α ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) (diracMassProfile q) ≤
      scalarParisiValue (by linarith : 0 < T) α) :
    0 < q ∧ q < 1 ∧
      q = ∫ z, (Real.tanh z)^2 ∂gaussianReal 0 (Real.toNNReal (T*q)) ∧
      1 < T*(∫ z, (Scalar.curvature z)^2 ∂gaussianReal 0 (Real.toNNReal (T*q))) := by
  have hT0 : 0 < T := by linarith
  have hm : ∀ r ∈ Icc (0:ℝ) 1, Scalar.rsVariation T q ≤ Scalar.rsVariation T r := by
    intro r hr
    simpa only [scalarParisiValue_dirac hT0 hq,scalarParisiValue_dirac hT0 hr] using
      hmin (diracMassProfile r) (diracMassProfile_mem hr)
  have hq0 : 0 < q := by
    by_contra hn
    have he : q = 0 := le_antisymm (not_lt.mp hn) hq.1
    have hh := scalarParisiMinimum_neg hT hmin
    rw [he,scalarParisiValue_dirac hT0 ⟨le_rfl,by norm_num⟩,Scalar.rsVariation_zero] at hh
    exact lt_irrefl _ hh
  have hq1 : q < 1 := by
    by_contra hn
    have he : q = 1 := le_antisymm hq.2 (not_lt.mp hn)
    rw [he] at hm
    exact Scalar.rs_one_not_minimizer hT0 hm
  have hfix := Scalar.rs_minimizer_fixed_point hT0 ⟨hq0,hq1⟩ hm
  exact ⟨hq0,hq1,hfix,Scalar.rs_replicon_strict hT0 hq0 hfix⟩

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem scalarParisiValue_twoAtom_increment {T a q t : ℝ} (hT : 0 < T)
    (ha : a ∈ Ioc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1)
    (ht : t ∈ Icc (0:ℝ) (T*(1-q))) :
    scalarParisiValue hT (twoAtomMassProfile q (q+t/T) ⟨ha.1.le,ha.2⟩)-
      scalarParisiValue hT (diracMassProfile q) = scalarRSBIncrement T a q t := by
  have hqr : q ≤ q+t/T := le_add_of_nonneg_right (div_nonneg ht.1 hT.le)
  have hr : q+t/T ∈ Icc (0:ℝ) 1 := by
    refine ⟨hq.1.trans hqr,?_⟩
    have hh : t/T ≤ 1-q := (div_le_iff₀ hT).2 (by nlinarith [ht.2])
    linarith
  have he : T*(q+t/T)-T*q = t := by field_simp; ring
  have htt : 0 ≤ T-T*(q+t/T) := sub_nonneg.mpr (by nlinarith [hr.2])
  erw [scalarParisiValue_twoAtom hT ha hq hr hqr,scalarParisiValue_dirac hT hq,
    scalarTwoClockPressure_collapse ha.1 htt,he]
  unfold scalarRSBIncrement Scalar.rsVariation
  rw [scalarInsertedPotential_zero ha.1.ne',Real.coe_toNNReal _ (mul_nonneg hT.le hq.1)]
  field_simp
  ring

 

theorem scalarParisi_no_dirac_minimizer {T q : ℝ} (hT : 1 < T) (hq : q ∈ Icc (0:ℝ) 1) :
    ¬ (∀ α ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) (diracMassProfile q) ≤
      scalarParisiValue (by linarith : 0 < T) α) := by
  intro hmin
  have hT0 : 0 < T := by linarith
  obtain ⟨hq0,hq1,hfix,_⟩ := scalarParisiDiracMinimizer_replicon hT hq hmin
  obtain ⟨a,ha,t,ht,hneg⟩ := scalarRSB_descent hT0 ⟨hq0,hq1⟩ hfix
  have hqr : q ≤ q+t/T := le_add_of_nonneg_right (div_nonneg ht.1.le hT0.le)
  have hr : q+t/T ∈ Icc (0:ℝ) 1 := by
    refine ⟨hq0.le.trans hqr,?_⟩
    have hh : t/T < 1-q := (div_lt_iff₀ hT0).2 (by nlinarith [ht.2])
    linarith
  have hm := hmin (twoAtomMassProfile q (q+t/T) ⟨ha.1.le,ha.2.le⟩)
    (twoAtomMassProfile_mem hq hr ⟨ha.1.le,ha.2.le⟩)
  have hh := scalarParisiValue_twoAtom_increment hT0 ⟨ha.1,ha.2.le⟩ hq ⟨ht.1.le,ht.2.le⟩
  linarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.GaussianCalculus
open Filter Asymptotics
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

theorem LipschitzWith.hasDerivAt_curve {F : E → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) {g : ℝ → E} {v : E} {d t : ℝ}
    (hg : HasDerivAt g v t)
    (hd : HasDerivAt (fun r : ℝ => F (g t+r • v)) d 0) :
    HasDerivAt (fun r => F (g r)) d t := by
  have hd' : HasDerivAt (fun r : ℝ => F (g t+r • v)) d (id t-t) := by simpa using hd
  have hl := HasDerivAt.comp (h := fun s : ℝ => s-t) t hd' ((hasDerivAt_id t).sub_const t)
  simp only [mul_one] at hl
  have he : (fun s => F (g s)-F (g t+(s-t) • v)) =O[𝓝 t]
      (fun s => g s-g t-(s-t) • v) := by
    apply IsBigO.of_bound (C:ℝ)
    exact Eventually.of_forall fun s => by
      simpa only [dist_eq_norm,sub_add_eq_sub_sub] using hF.dist_le_mul (g s) (g t+(s-t) • v)
  have hh := (he.trans_isLittleO hg.isLittleO).add hl.isLittleO
  apply HasDerivAt.of_isLittleO
  convert hh using 1; try rfl
  funext s
  simp only [Function.comp_apply,sub_self,zero_smul,add_zero,smul_eq_mul]
  ring

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

theorem exp_scaledSource_bound {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) (x a z : ι → ℝ) {A : ℝ} (ha : ‖a‖ ≤ A) :
    Real.exp (m*F (x+a*z)) ≤ Real.exp (|m| *|F x|)*Real.exp (|m| *C*A*‖z‖) := by
  have hd : |F (x+a*z)-F x| ≤ (C:ℝ)*A*‖z‖ := by
    have hh := hF.dist_le_mul (x+a*z) x
    rw [Real.dist_eq,dist_eq_norm,add_sub_cancel_left] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left ((norm_mul_le a z).trans
      (mul_le_mul_of_nonneg_right ha (norm_nonneg z))) C.coe_nonneg).trans_eq (by ring))
  have hf : |F (x+a*z)| ≤ |F x|+(C:ℝ)*A*‖z‖ := by
    have hh := abs_add_le (F (x+a*z)-F x) (F x)
    rw [sub_add_cancel] at hh
    linarith
  rw [← Real.exp_add,Real.exp_le_exp]
  have hm := le_abs_self (m*F (x+a*z))
  rw [abs_mul] at hm
  nlinarith [mul_le_mul_of_nonneg_left hf (abs_nonneg m)]

theorem integrable_exp_scaledSource {ν : Measure (ι → ℝ)} (hν : ExponentialIncrement ν)
    {F : (ι → ℝ) → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (m : ℝ) (x a : ι → ℝ) :
    Integrable (fun z => Real.exp (m*F (x+a*z))) ν := by
  apply ((hν (|m| *C*‖a‖)).const_mul (Real.exp (|m| *|F x|))).mono'
    ((hF.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).const_mul m).rexp.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact exp_scaledSource_bound hF m x a z le_rfl

 

theorem hasDerivAt_integral_exp_scaledSource {ν : Measure (ι → ℝ)} (hν : ExponentialIncrement ν)
    {F : (ι → ℝ) → ℝ} {G : ι → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, Continuous (G i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    {a a' : ℝ → (ι → ℝ)} {l r A B t : ℝ} (ht : t ∈ Ioo l r)
    (ha : ∀ s ∈ Ioo l r, HasDerivAt a (a' s) s)
    (hA : ∀ s ∈ Ioo l r, ‖a s‖ ≤ A) (hB : ∀ s ∈ Ioo l r, ‖a' s‖ ≤ B)
    (m : ℝ) (x : ι → ℝ) :
    HasDerivAt (fun s => ∫ z, Real.exp (m*F (x+a s*z)) ∂ν)
      (∫ z, m*(∑ i, (a' t*z) i*G i (x+a t*z))*Real.exp (m*F (x+a t*z)) ∂ν) t := by
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB t ht)
  have hd (s) (hs : s ∈ Ioo l r) (z : ι → ℝ) :
      HasDerivAt (fun u => F (x+a u*z)) (∑ i, (a' s*z) i*G i (x+a s*z)) s := by
    apply LipschitzWith.hasDerivAt_curve hF (HasDerivAt.const_add x ((ha s hs).mul_const z))
    simpa only [zero_smul,add_zero] using hdF (x+a s*z) (a' s*z) 0
  have hb (s) (hs : s ∈ Ioo l r) (z : ι → ℝ) :
      |∑ i, (a' s*z) i*G i (x+a s*z)| ≤ (C:ℝ)*B*‖z‖ := by
    have hl : HasLineDerivAt ℝ F (∑ i, (a' s*z) i*G i (x+a s*z)) (x+a s*z) (a' s*z) := by
      simpa only [HasLineDerivAt,zero_smul,add_zero] using hdF (x+a s*z) (a' s*z) 0
    have hh := norm_lineDeriv_le_of_lipschitz ℝ (x₀ := x+a s*z) (v := a' s*z) hF
    rw [hl.lineDeriv,Real.norm_eq_abs] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hB s hs) (norm_nonneg z))) C.coe_nonneg).trans_eq (by ring))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo l r) (bound := fun z => |m| *C*B*Real.exp (|m| *|F x|)*Real.exp ((|m| *C*A+1)*‖z‖))
    (Ioo_mem_nhds ht.1 ht.2) _ (integrable_exp_scaledSource hν hF m x (a t)) _ _ _ _).2
  · exact Eventually.of_forall fun s =>
      ((hF.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).const_mul m).rexp.aestronglyMeasurable
  · exact ((continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).const_mul (a' t i)).mul
        ((hG i).comp (continuous_const.add (continuous_const.mul continuous_id)))).const_mul m).mul
      (((hF.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).const_mul m).rexp) |>.aestronglyMeasurable
  · exact Eventually.of_forall fun z s hs => by
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
      have hE := exp_scaledSource_bound hF m x (a s) z (hA s hs)
      have hz : ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
      calc
        _ ≤ |m| *((C:ℝ)*B*‖z‖)*(Real.exp (|m| *|F x|)*Real.exp (|m| *C*A*‖z‖)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hb s hs z) (abs_nonneg m)) hE (Real.exp_nonneg _) (by positivity)
        _ ≤ |m| *((C:ℝ)*B*Real.exp ‖z‖)*(Real.exp (|m| *|F x|)*Real.exp (|m| *C*A*‖z‖)) := by gcongr
        _ = _ := by rw [show (|m| *C*A+1)*‖z‖ = ‖z‖+|m| *C*A*‖z‖ by ring,Real.exp_add]; ring
  · exact (hν _).const_mul _
  · exact Eventually.of_forall fun z s hs =>
      (((hd s hs z).const_mul m).exp).congr_deriv (by ring)

end SKFluctuations.GaussianCalculus

end

end OAI
