import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactPhysicalCorrections
import OAI.Analysis.Conductivity.Walls.ParametricWallTensors

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

def angularShift (T : ℝ) (n : Fin 2 → ℤ) : Coord3 := ![0,T*(n 0:ℝ),T*(n 1:ℝ)]

lemma angularShift_zero (T : ℝ) : angularShift T 0=0 := by ext i; fin_cases i <;> simp [angularShift]
lemma angularShift_add (T : ℝ) (n m : Fin 2 → ℤ) :
    angularShift T (n+m)=angularShift T n+angularShift T m := by
  ext i
  fin_cases i <;> simp [angularShift,mul_add]
lemma angularShift_succ (T : ℝ) (n : Fin 2 → ℤ) (i : Fin 2) :
    angularShift T n i.succ=T*(n i:ℝ) := by fin_cases i <;> rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def angularPeriodize (T : ℝ) (f : Coord3 → E) (x : Coord3) : E :=
  ∑ᶠ n : Fin 2 → ℤ,f (x+angularShift T n)

def AngularPeriodic (T : ℝ) (f : Coord3 → E) : Prop :=
  ∀ n x,f (x+angularShift T n)=f x

omit [NormedSpace ℝ E] in
lemma angularPeriodize_periodic (T : ℝ) (f : Coord3 → E) :
    AngularPeriodic T (angularPeriodize T f) := by
  intro n x
  unfold angularPeriodize
  calc
    _ = ∑ᶠ m : Fin 2 → ℤ,f (x+angularShift T (m+n)) := by
      congr 1
      funext m
      rw [angularShift_add]
      congr 1
      abel
    _ = _ := finsum_comp_equiv (Equiv.addRight n) (f := fun m => f (x+angularShift T m))

omit [NormedSpace ℝ E] in
lemma angular_translates_locallyFinite {T : ℝ} (hT : 0<T)
    {f : Coord3 → E} (hc : HasCompactSupport f) :
    LocallyFinite (fun n : Fin 2 → ℤ => Function.support (fun x => f (x+angularShift T n))) := by
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  intro x
  obtain ⟨N,hN⟩ := exists_nat_gt ((R+‖x‖+1)/T)
  refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,?_⟩
  apply (Set.finite_Icc (fun _ : Fin 2 => -(N:ℤ)) (fun _ => (N:ℤ))).subset
  rintro n ⟨z,hz,hzx⟩
  have hzs : z+angularShift T n∈tsupport f := subset_tsupport f hz
  have hzn : ‖z‖<‖x‖+1 := by
    have hh : ‖z‖ ≤ ‖x‖+dist z x := by
      simpa only [dist_eq_norm,add_comm,norm_sub_rev] using norm_le_norm_add_norm_sub x z
    linarith [Metric.mem_ball.mp hzx]
  have hsn : ‖angularShift T n‖<R+‖x‖+1 := by
    have he : angularShift T n=(z+angularShift T n)-z := by abel
    rw [he]
    exact lt_of_le_of_lt (norm_sub_le _ _) (by linarith [hR _ hzs])
  have hi (i : Fin 2) : |(n i:ℝ)|<(N:ℝ) := by
    have hh := (norm_le_pi_norm (angularShift T n) i.succ).trans_lt hsn
    rw [angularShift_succ,Real.norm_eq_abs,abs_mul,abs_of_pos hT] at hh
    exact (lt_div_iff₀ hT).mpr (by simpa only [mul_comm] using hh) |>.trans hN
  constructor
  · intro i
    have hh := (abs_lt.mp (hi i)).1.le
    exact_mod_cast hh
  · intro i
    have hh := (abs_lt.mp (hi i)).2.le
    exact_mod_cast hh

lemma angularPeriodize_smooth {T : ℝ} (hT : 0<T)
    {f : Coord3 → E} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (angularPeriodize T f) := by
  rw [←contMDiff_iff_contDiff]
  exact contMDiff_finsum (fun n => (contMDiff_iff_contDiff).mpr
    (hf.comp (contDiff_id.add contDiff_const))) (angular_translates_locallyFinite hT hc)

omit [NormedSpace ℝ E] in
lemma angularPeriodize_local_sum {T : ℝ} (hT : 0<T)
    {f : Coord3 → E} (hc : HasCompactSupport f) (x : Coord3) :
    ∃ s : Finset (Fin 2 → ℤ),∀ᶠ y in 𝓝 x,
      angularPeriodize T f y=∑ n∈s,f (y+angularShift T n) ∧
      ∀ n,n∉s → f (y+angularShift T n)=0 := by
  classical
  obtain ⟨N,hN,hfin⟩ := angular_translates_locallyFinite hT hc x
  refine ⟨hfin.toFinset,?_⟩
  filter_upwards [hN] with y hy
  have hz (n) (hn : n∉hfin.toFinset) : f (y+angularShift T n)=0 := by
    by_contra h
    exact hn (hfin.mem_toFinset.mpr ⟨y,h,hy⟩)
  exact ⟨finsum_eq_sum_of_support_subset _ (by
    intro n hn
    by_contra h
    exact hn (hz n h)),hz⟩

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma angularPeriodize_finite {T : ℝ} (hT : 0<T)
    {f : Coord3 → E} (hc : HasCompactSupport f) (x : Coord3) :
    Function.HasFiniteSupport (fun n => f (x+angularShift T n)) :=
  (angular_translates_locallyFinite hT hc).point_finite x

lemma angularPeriodize_fderiv {T : ℝ} (hT : 0<T)
    {f : Coord3 → E} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f) (x : Coord3) :
    fderiv ℝ (angularPeriodize T f) x=angularPeriodize T (fderiv ℝ f) x := by
  classical
  obtain ⟨s,hs⟩ := angularPeriodize_local_sum hT hc x
  have he : angularPeriodize T f=ᶠ[𝓝 x] (fun y => ∑ n∈s,f (y+angularShift T n)) :=
    hs.mono (fun _ h => h.1)
  rw [he.fderiv_eq]
  have hn : (fun y => ∑ n∈s,f (y+angularShift T n))=∑ n∈s,(fun y => f (y+angularShift T n)) := by
    funext y; simp only [Finset.sum_apply]
  rw [hn,fderiv_sum (A:=fun n y => f (y+angularShift T n)) (fun n _ =>
    (hf.comp (contDiff_id.add (contDiff_const (c:=angularShift T n)))).differentiable (by simp) x)]
  simp only [fderiv_comp_add_right]
  symm
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra hns
  have hz : (fun y => f (y+angularShift T n))=ᶠ[𝓝 x] (fun _ => 0) :=
    hs.mono (fun _ h => h.2 n hns)
  have hh := hz.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp_add_right] at hh
  exact hn (hh.trans (fderiv_const_apply (𝕜:=ℝ) (0:E)))

lemma AngularPeriodic.fderiv {T : ℝ} {f : Coord3 → E} (hf : AngularPeriodic T f) :
    AngularPeriodic T (fderiv ℝ f) := by
  intro n x
  have he : (fun y => f (y+angularShift T n))=f := funext (hf n)
  rw [←fderiv_comp_add_right,he]

lemma coordinateDivergence_comp_add (F : Coord3 → Coord3) (a x : Coord3) :
    coordinateDivergence (fun y => F (y+a)) x=coordinateDivergence F (x+a) := by
  unfold coordinateDivergence
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_comp_add_right (f:=fun y => F y i)]

lemma symmetricSource_congr_nhds {H K : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    {x : Coord3} (h : H=ᶠ[𝓝 x] K) (j : Fin 2) :
    symmetricSource H u j x=symmetricSource K u j x := by
  unfold symmetricSource coordinateDivergence
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => (H y*gradientColumns (fderiv ℝ u y)).col j i)=ᶠ[𝓝 x]
      (fun y => (K y*gradientColumns (fderiv ℝ u y)).col j i) := by
    filter_upwards [h] with y hy
    rw [hy]
  rw [he.fderiv_eq]

lemma symmetricSource_finset_sum {ι : Type*} (s : Finset ι) (H : ι → Coord3 → Mat3)
    (hH : ∀ i∈s,ContDiff ℝ (↑(⊤:ℕ∞)) (H i))
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (j : Fin 2) :
    symmetricSource (∑ i∈s,H i) u j=∑ i∈s,symmetricSource (H i) u j := by
  classical
  induction s using Finset.induction with
  | empty => simp [symmetricSource_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hsum : ContDiff ℝ (↑(⊤:ℕ∞)) (∑ i∈s,H i) := by
      convert (ContDiff.sum (fun i hi => hH i (Finset.mem_insert_of_mem hi))) using 1
      funext y; simp only [Finset.sum_apply]
    rw [symmetricSource_add (hH a (Finset.mem_insert_self _ _)) hsum hu j,
      ih (fun i hi => hH i (Finset.mem_insert_of_mem hi))]

lemma symmetricSource_angular_translate {T : ℝ} {u : Coord3 → Fin 2 → ℝ}
    (hu : AngularPeriodic T u) (H : Coord3 → Mat3) (j : Fin 2) (n : Fin 2 → ℤ) (x : Coord3) :
    symmetricSource (fun y => H (y+angularShift T n)) u j x=
      symmetricSource H u j (x+angularShift T n) := by
  have he : (fun y => (H (y+angularShift T n)*gradientColumns (fderiv ℝ u y)).col j)=
      (fun y => (H (y+angularShift T n)*gradientColumns (fderiv ℝ u (y+angularShift T n))).col j) := by
    funext y
    rw [hu.fderiv n y]
  unfold symmetricSource
  rw [he]
  exact coordinateDivergence_comp_add (fun y => (H y*gradientColumns (fderiv ℝ u y)).col j) _ _

theorem symmetricSource_angularPeriodize {T : ℝ} (hT : 0<T)
    {H : Coord3 → Mat3} (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hc : HasCompactSupport H)
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (hp : AngularPeriodic T u)
    (j : Fin 2) (x : Coord3) :
    symmetricSource (angularPeriodize T H) u j x=angularPeriodize T (symmetricSource H u j) x := by
  classical
  obtain ⟨s,hs⟩ := angularPeriodize_local_sum hT hc x
  have he : angularPeriodize T H=ᶠ[𝓝 x] ∑ n∈s,(fun y => H (y+angularShift T n)) := by
    filter_upwards [hs] with y hy
    simpa only [Finset.sum_apply] using hy.1
  rw [symmetricSource_congr_nhds he j,
    symmetricSource_finset_sum s (fun n y => H (y+angularShift T n))
      (fun n _ => hH.comp (contDiff_id.add (contDiff_const (c:=angularShift T n)))) hu j]
  simp only [Finset.sum_apply,symmetricSource_angular_translate hp]
  symm
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra hns
  have hz : (fun y => H (y+angularShift T n))=ᶠ[𝓝 x] (0 : Coord3 → Mat3) :=
    hs.mono (fun _ h => h.2 n hns)
  have hh := symmetricSource_congr_nhds (u:=u) hz j
  rw [symmetricSource_angular_translate hp,symmetricSource_zero] at hh
  exact hn hh

lemma angularPeriodize_symmetric {T : ℝ} (hT : 0<T) {H : Coord3 → Mat3}
    (hc : HasCompactSupport H) (hs : ∀ x,(H x).IsSymm) (x : Coord3) :
    (angularPeriodize T H x).IsSymm := by
  obtain ⟨s,h⟩ := angularPeriodize_local_sum hT hc x
  rw [(h.self_of_nhds).1]
  classical
  change (∑ n∈s,H (x+angularShift T n))ᵀ=∑ n∈s,H (x+angularShift T n)
  rw [Matrix.transpose_sum]
  exact Finset.sum_congr rfl (fun n _ => hs _)

end ScalarConductivity

end

end OAI
