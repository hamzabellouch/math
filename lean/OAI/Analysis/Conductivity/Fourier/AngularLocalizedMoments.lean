import Mathlib
import OAI.Analysis.Conductivity.Sources.AngularLocalizedSources

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

lemma continuous_angular_integral {T : ℝ} (hT : 0≤T) {f : Coord3 → ℝ}
    (hf : Continuous f) (t : ℝ) :
    Continuous (fun y => ∫ z in (0:ℝ)..T,f ![t,y,z]) := by
  simp_rw [intervalIntegral.integral_of_le hT,←integral_Icc_eq_integral_Ioc]
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  exact hf.comp (by fun_prop)

lemma integral_coord3_iterated {f : Coord3 → ℝ} (hf : Integrable f) :
    (∫ x,f x)=∫ t,∫ y,∫ z,f ![t,y,z] := by
  have hi : Integrable (fun x : ℝ×(ℝ×ℝ) => f (threeArrow.symm x)) :=
    (threeArrow_volume.symm.integrable_comp hf.aestronglyMeasurable).mpr hf
  rw [←threeArrow_volume.symm.integral_comp' f]
  change (∫ x,f (threeArrow.symm x) ∂volume.prod volume)=_
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with t ht
  change (∫ x,f (threeArrow.symm (t,x)) ∂volume.prod volume)=_
  rw [integral_prod _ ht]
  simp only [threeArrow_symm_apply]

theorem angularCutoff_integral {T a b : ℝ} (hT : 0<T) {f : Coord3 → ℝ}
    (hf : Continuous f) (hp : AngularPeriodic T f)
    (hs : tsupport f⊆{x | x 0∈Icc a b}) :
    (∫ x,angularCutoff T x*f x)=∫ t,∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,f ![t,y,z] := by
  have hi : Integrable (fun x => angularCutoff T x*f x) :=
    ((angularCutoff_smooth T).continuous.mul hf).integrable_of_hasCompactSupport
      (angularCutoff_compact hT hs)
  rw [integral_coord3_iterated hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have hz (y : ℝ) :
      (∫ z,angularCutoff T ![t,y,z]*f ![t,y,z])=
        periodCutoff T y*(∫ z in (0:ℝ)..T,f ![t,y,z]) := by
    change (∫ z,periodCutoff T y*periodCutoff T z*f ![t,y,z])=_
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    exact periodCutoff_integral hT (hf.comp (by fun_prop)) (hp.coordinate_two t y)
  simp_rw [hz]
  apply periodCutoff_integral hT (continuous_angular_integral hT.le hf t)
  intro y
  apply intervalIntegral.integral_congr
  intro z _
  exact hp.coordinate_one t z y

def periodicSourceMoment (T : ℝ) (u : Coord3 → Fin 2 → ℝ) (r : PhysicalSourcePair) : Coord3 :=
  ![∫ t,∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,r 0 ![t,y,z],
    ∫ t,∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,r 1 ![t,y,z],
    ∫ t,∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,u ![t,y,z] 1*r 0 ![t,y,z]-u ![t,y,z] 0*r 1 ![t,y,z]]

theorem physicalSourceMoment_angularCutoff {T a b : ℝ} (hT : 0<T)
    {u : Coord3 → Fin 2 → ℝ} {r : PhysicalSourcePair}
    (hu : Continuous u) (hur : AngularPeriodic T u)
    (hr : ∀ j,Continuous (r j)) (hrp : ∀ j,AngularPeriodic T (r j))
    (hrs : ∀ j,tsupport (r j)⊆{x | x 0∈Icc a b}) :
    physicalSourceMoment u (fun j x => angularCutoff T x*r j x)=periodicSourceMoment T u r := by
  have ht : Continuous (fun x => u x 1*r 0 x-u x 0*r 1 x) := by fun_prop
  have htp : AngularPeriodic T (fun x => u x 1*r 0 x-u x 0*r 1 x) := by
    intro n x
    dsimp only
    rw [hur n x,hrp 0 n x,hrp 1 n x]
  have hts : tsupport (fun x => u x 1*r 0 x-u x 0*r 1 x)⊆{x | x 0∈Icc a b} :=
    (tsupport_sub _ _).trans (union_subset
      ((tsupport_mul_subset_right).trans (hrs 0)) ((tsupport_mul_subset_right).trans (hrs 1)))
  ext i
  fin_cases i
  · exact angularCutoff_integral hT (hr 0) (hrp 0) (hrs 0)
  · exact angularCutoff_integral hT (hr 1) (hrp 1) (hrs 1)
  · change (∫ x,u x 1*(angularCutoff T x*r 0 x)-u x 0*(angularCutoff T x*r 1 x))=_
    have he : (fun x => u x 1*(angularCutoff T x*r 0 x)-u x 0*(angularCutoff T x*r 1 x))=
        (fun x => angularCutoff T x*(u x 1*r 0 x-u x 0*r 1 x)) := by funext x; ring
    rw [he]
    exact angularCutoff_integral hT ht htp hts

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem angularPeriodize_uniform_bound {T : ℝ} (hT : 0<T) (R : ℝ) :
    ∃ M : ℕ,0<M ∧ ∀ (f : Coord3 → E) (C : ℝ),0≤C →
      (∀ x,f x≠0 → ‖x‖≤R) → (∀ x,‖f x‖≤C) →
      ∀ x,‖angularPeriodize T f x‖≤M*C := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt (2*R/T)
  let s : Finset (Fin 2 → ℤ) := Finset.Icc (fun _ => -(N:ℤ)) (fun _ => (N:ℤ))
  have hs0 : (0 : Fin 2 → ℤ)∈s := by
    simp only [s,Finset.mem_Icc]
    constructor <;> intro i <;> simp
  refine ⟨s.card,Finset.card_pos.mpr ⟨0,hs0⟩,?_⟩
  intro f C hC hf hbound x
  by_cases hn : ∃ n : Fin 2 → ℤ,f (x+angularShift T n)≠0
  · obtain ⟨n0,hn0⟩ := hn
    let e : (Fin 2 → ℤ) ↪ (Fin 2 → ℤ) := (Equiv.addRight n0).toEmbedding
    have hsub : Function.support (fun n => f (x+angularShift T n))⊆↑(s.map e) := by
      intro n hn
      have hdiff : angularShift T (n-n0)=(x+angularShift T n)-(x+angularShift T n0) := by
        have ha := angularShift_add T (n-n0) n0
        rw [sub_add_cancel] at ha
        rw [ha]
        abel
      have hnorm : ‖angularShift T (n-n0)‖≤2*R := by
        rw [hdiff]
        exact (norm_sub_le _ _).trans (by linarith [hf _ hn,hf _ hn0])
      have hi (i : Fin 2) : |((n-n0) i:ℝ)|<(N:ℝ) := by
        have hh := (norm_le_pi_norm (angularShift T (n-n0)) i.succ).trans hnorm
        rw [angularShift_succ,Real.norm_eq_abs,abs_mul,abs_of_pos hT] at hh
        exact ((le_div_iff₀ hT).mpr (by simpa only [mul_comm] using hh)).trans_lt hN
      have hin : n-n0∈s := by
        change _∈Finset.Icc _ _
        rw [Finset.mem_Icc]
        constructor <;> intro i
        · exact_mod_cast (abs_lt.mp (hi i)).1.le
        · exact_mod_cast (abs_lt.mp (hi i)).2.le
      exact Finset.mem_map.mpr ⟨n-n0,hin,by simp [e]⟩
    rw [angularPeriodize,finsum_eq_sum_of_support_subset _ hsub]
    calc
      _ ≤ ∑ n∈s.map e,‖f (x+angularShift T n)‖ := norm_sum_le _ _
      _ ≤ ∑ _n∈s.map e,C := Finset.sum_le_sum (fun n _ => hbound _)
      _ = s.card*C := by simp
  · have hz : (fun n : Fin 2 → ℤ => f (x+angularShift T n))=0 := by
      funext n
      exact not_ne_iff.mp (fun h => hn ⟨n,h⟩)
    rw [angularPeriodize,hz]
    have he : finsum (0 : (Fin 2 → ℤ) → E)=0 := finsum_zero
    rw [he,norm_zero]
    positivity

omit [NormedSpace ℝ E] in
lemma angularPeriodize_axial_support {T a b : ℝ} {f : Coord3 → E}
    (hs : tsupport f⊆{x | x 0∈Icc a b}) :
    tsupport (angularPeriodize T f)⊆{x | x 0∈Icc a b} := by
  apply closure_minimal _ (isClosed_Icc.preimage (continuous_apply 0))
  intro x hx
  by_contra hx0
  apply hx
  unfold angularPeriodize
  have hz : (fun n : Fin 2 → ℤ => f (x+angularShift T n))=0 := by
    funext n
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hh := hs h
    change (x 0+0)∈Icc a b at hh
    apply hx0
    change x 0∈Icc a b
    simpa only [add_zero] using hh
  rw [hz]
  exact finsum_zero

end ScalarConductivity

end

end OAI
