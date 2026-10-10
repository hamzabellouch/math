import Mathlib
import OAI.Analysis.Conductivity.Flux.TorusFluxDecay
import OAI.Analysis.Conductivity.Flux.LinearTensorEllipticity

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma coordinateDivergence_C1_continuous {F : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F) : Continuous (coordinateDivergence F) := by
  apply continuous_finsetSum
  intro i _
  exact (((contDiff_pi.mp hF) i).continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem coordinateDivergence_C1_weak {F : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F)
    (ψ : Coord3 → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hc : HasCompactSupport ψ) :
    (∫ x,fderiv ℝ ψ x (F x))= -(∫ x,ψ x*coordinateDivergence F x) := by
  have hFi (i : Fin 3) : ContDiff ℝ 1 (fun x => F x i) :=
    contDiff_pi.mp hF i
  have hdψ (i : Fin 3) : Continuous (fun x => fderiv ℝ ψ x (Pi.single i 1)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdF (i : Fin 3) : Continuous (fun x => fderiv ℝ (fun y => F y i) x (Pi.single i 1)) :=
    ((hFi i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi₁ (i : Fin 3) : Integrable (fun x => F x i*fderiv ℝ ψ x (Pi.single i 1)) :=
    ((hFi i).continuous.mul (hdψ i)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ _).mul_left
  have hi₂ (i : Fin 3) : Integrable (fun x => ψ x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)) :=
    (hψ.continuous.mul (hdF i)).integrable_of_hasCompactSupport hc.mul_right
  have he (i : Fin 3) : (∫ x,F x i*fderiv ℝ ψ x (Pi.single i 1))=
      -(∫ x,ψ x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)) := by
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure Coord3))
      (f := ψ) (g := fun x => F x i) (v := Pi.single i 1)
      (by simpa only [mul_comm] using hi₁ i) (hi₂ i)
      ((hψ.continuous.mul (hFi i).continuous).integrable_of_hasCompactSupport hc.mul_right)
      (fun x _ => hψ.differentiable (by norm_num) x)
      (fun x _ => (hFi i).differentiable (by norm_num) x)
    have hh' : (∫ x,fderiv ℝ ψ x (Pi.single i 1)*F x i)=
        (∫ x,F x i*fderiv ℝ ψ x (Pi.single i 1)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
    rw [hh'] at hh
    linarith
  have hex : (fun x => fderiv ℝ ψ x (F x))=
      (fun x => ∑ i : Fin 3,F x i*fderiv ℝ ψ x (Pi.single i 1)) := by
    funext x
    exact coordinate_fderiv_expansion ψ x (F x)
  rw [hex]
  simp only [coordinateDivergence,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi₁ i),integral_finsetSum _ (fun i _ => hi₂ i)]
  simp_rw [he]
  simp only [Finset.sum_neg_distrib]

lemma C1_flux_divergence_zero {F : Coord3 → Coord3} {U : Set Coord3}
    (hF : ContDiff ℝ 1 F) (hU : IsOpen U)
    (hw : ∀ (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x (F x))=0) :
    ∀ x∈U,coordinateDivergence F x=0 := by
  have hd := coordinateDivergence_C1_continuous hF
  have hz : ∀ᵐ x : Coord3,x∈U → coordinateDivergence F x=0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hd.locallyIntegrable.locallyIntegrableOn U) (by
        intro ψ hψ hc hs
        have hh := coordinateDivergence_C1_weak hF ψ hψ hc
        have he := hw ⟨ψ,hψ⟩ hc hs
        change (∫ x,ψ x*coordinateDivergence F x)=0
        change (∫ x,fderiv ℝ ψ x (F x))=0 at he
        linarith)
  have he : coordinateDivergence F=ᵐ[volume.restrict U] (fun _ => (0:ℝ)) :=
    (ae_restrict_iff' hU.measurableSet).mpr hz
  exact Measure.eqOn_open_of_ae_eq he hU hd.continuousOn continuous_const.continuousOn

namespace WeakFiniteTensorPair

lemma flux_periodic {U : Set Coord3} (w : WeakFiniteTensorPair U) {T : ℝ}
    (hv : AngularPeriodic T w.v) (hE : AngularPeriodic T w.E) : AngularPeriodic T w.G := by
  intro n
  have hae : (fun x => w.G (x+angularShift T n))=ᵐ[volume] w.G := by
    filter_upwards [w.constitution,
      (measurePreserving_add_right volume (angularShift T n)).quasiMeasurePreserving.ae w.constitution]
      with x hx hxn
    rw [←hx,←hxn,hE n x,hv.fderiv n x]
  exact fun x => congrFun (Measure.eq_of_ae_eq hae
    (w.flux_C1.continuous.comp (continuous_id.add continuous_const)) w.flux_C1.continuous) x

lemma flux_divergence {U : Set Coord3} (w : WeakFiniteTensorPair U) (hU : IsOpen U)
    (j : Fin 2) : ∀ x∈U,coordinateDivergence (fun y => (w.G y).col j) x=0 := by
  apply C1_flux_divergence_zero _ hU (w.weak j)
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp w.flux_C1)

end WeakFiniteTensorPair
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

theorem torus_band_divergence_C1 {T a b : ℝ} (hT : 0≤T) (hab : a≤b)
    {F : Coord3 → Coord3} (hF : ContDiff ℝ 1 F) (hp : AngularPeriodic T F) :
    (∫ t in a..b,torusCellIntegral T (coordinateDivergence F) t)=
      torusCellIntegral T (fun x => F x 0) b-torusCellIntegral T (fun x => F x 0) a := by
  let A : Coord3 := ![a,0,0]
  let B : Coord3 := ![b,T,T]
  have hAB : A≤B := by intro i; fin_cases i; exact hab; exact hT; exact hT
  have hc := coordinateDivergence_C1_continuous hF
  have hfd := hF.differentiable (by norm_num)
  have hh := integral_divergence_of_hasFDerivAt_off_countable A B hAB F (fderiv ℝ F)
    ∅ countable_empty hF.continuous.continuousOn (fun x _ => (hfd x).hasFDerivAt)
    (by simpa only [←coordinateDivergence_eq_trace hfd] using (hc.continuousOn.integrableOn_compact
      (μ:=volume) (isCompact_Icc : IsCompact (Icc A B))))
  simp_rw [←coordinateDivergence_eq_trace hfd] at hh
  rw [integral_coord3_Icc hAB hc] at hh
  have h1 (q : Fin 2 → ℝ) : F ((1:Fin 3).insertNth T q) 1=F ((1:Fin 3).insertNth 0 q) 1 := by
    have he : ((1:Fin 3).insertNth 0 q)+angularShift T ![1,0]=(1:Fin 3).insertNth T q := by
      ext i; fin_cases i <;> simp [angularShift,Fin.insertNth,Fin.succAboveCases]
    have hh := hp ![1,0] ((1:Fin 3).insertNth 0 q)
    rw [he] at hh
    exact congrFun hh 1
  have h2 (q : Fin 2 → ℝ) : F ((2:Fin 3).insertNth T q) 2=F ((2:Fin 3).insertNth 0 q) 2 := by
    have he : ((2:Fin 3).insertNth 0 q)+angularShift T ![0,1]=(2:Fin 3).insertNth T q := by
      ext i; fin_cases i <;> simp [angularShift,Fin.insertNth,Fin.succAboveCases]
    have hh := hp ![0,1] ((2:Fin 3).insertNth 0 q)
    rw [he] at hh
    exact congrFun hh 2
  rw [Fin.sum_univ_succ] at hh
  simp only [Fin.sum_univ_two,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] at hh
  simp only [A,B,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at hh
  simp_rw [h1,h2] at hh
  simp only [sub_self,add_zero] at hh
  have hf0 (c : ℝ) :
      (∫ q in Icc (A ∘ (0:Fin 3).succAbove) (B ∘ (0:Fin 3).succAbove),
        F ((0:Fin 3).insertNth c q) 0)=torusCellIntegral T (fun x => F x 0) c := by
    have hc0 : Continuous (fun q : Fin 2 → ℝ => F ((0:Fin 3).insertNth c q) 0) :=
      (continuous_apply 0).comp (hF.continuous.comp (by fun_prop))
    refine (integral_coord2_Icc (a:=A ∘ (0:Fin 3).succAbove) (b:=B ∘ (0:Fin 3).succAbove) (fun i => hAB ((0:Fin 3).succAbove i)) hc0).trans ?_
    change (∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,F ((0:Fin 3).insertNth c ![y,z]) 0)=_
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    have hi : (0:Fin 3).insertNth c ![y,z]=![c,y,z] := by
      ext i
      fin_cases i <;> simp [Fin.insertNth,Fin.succAboveCases]
    exact congrArg (fun x : Coord3 => F x 0) hi
  exact hh.trans (congrArg₂ (· - ·) (hf0 b) (hf0 a))

lemma coordinateDivergence_smul_scalar {F : Coord3 → Coord3} {φ : Coord3 → ℝ}
    {x : Coord3} (hF : DifferentiableAt ℝ F x) (hφ : DifferentiableAt ℝ φ x) :
    coordinateDivergence (fun y => φ y • F y) x=
      fderiv ℝ φ x (F x)+φ x*coordinateDivergence F x := by
  rw [coordinateDivergence_smul_at hφ hF]
  ring

theorem torus_band_green_C1 {T a b : ℝ} (hT : 0≤T) (hab : a≤b)
    {F : Coord3 → Coord3} {φ : Coord3 → ℝ}
    (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ)
    (hp : AngularPeriodic T F) (hφp : AngularPeriodic T φ)
    (hd : ∀ x,x 0∈Icc a b → coordinateDivergence F x=0) :
    (∫ t in a..b,torusCellIntegral T (fun x => fderiv ℝ φ x (F x)) t)=
      torusCellIntegral T (fun x => φ x*F x 0) b-
        torusCellIntegral T (fun x => φ x*F x 0) a := by
  have hprod : AngularPeriodic T (fun x => φ x • F x) := by
    intro n x
    change φ (x+angularShift T n) • F (x+angularShift T n)=φ x • F x
    rw [hφp n x,hp n x]
  have he := torus_band_divergence_C1 hT hab (hφ.smul hF) hprod
  refine Eq.trans ?_ he
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t∈Icc a b := by simpa only [uIcc_of_le hab] using ht
  unfold torusCellIntegral
  apply intervalIntegral.integral_congr
  intro y _
  apply intervalIntegral.integral_congr
  intro z _
  change fderiv ℝ φ ![t,y,z] (F ![t,y,z])=
    coordinateDivergence (fun x => φ x • F x) ![t,y,z]
  rw [coordinateDivergence_smul_scalar (hF.differentiable (by norm_num) _) (hφ.differentiable (by norm_num) _),
    hd _ ht',mul_zero,add_zero]

end ScalarConductivity

end
end

end OAI
