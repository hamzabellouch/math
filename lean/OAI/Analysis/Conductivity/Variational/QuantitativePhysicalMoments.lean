import Mathlib
import OAI.Analysis.Conductivity.Variational.UniformC1Bounds
import OAI.Analysis.Conductivity.Variational.GlobalRegularCorrection

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma CompactSmoothPair.smul {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (a : ℝ) :
    CompactSmoothPair (a • r) := by
  intro j
  change ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => a*r j x) ∧ HasCompactSupport (fun x => a*r j x)
  exact ⟨contDiff_const.mul (hr j).1,(hr j).2.mul_left⟩

lemma PairSupported.smul {r : PhysicalSourcePair} {U : Set Coord3} (hr : PairSupported r U) (a : ℝ) :
    PairSupported (a • r) U := by
  intro j
  change tsupport (fun x => a*r j x)⊆U
  exact tsupport_mul_subset_right.trans (hr j)

lemma physicalSourceMoment_smul {u : Coord3 → Fin 2 → ℝ} (r : PhysicalSourcePair) (a : ℝ) :
    physicalSourceMoment u (a • r)=a • physicalSourceMoment u r := by
  have he : (fun x => u x 1*(a • r) 0 x-u x 0*(a • r) 1 x)=
      (fun x => a*(u x 1*r 0 x-u x 0*r 1 x)) := by
    funext x; simp only [Pi.smul_apply,smul_eq_mul]; ring
  ext i
  fin_cases i
  · exact integral_const_mul a (r 0)
  · exact integral_const_mul a (r 1)
  · change (∫ x,u x 1*(a • r) 0 x-u x 0*(a • r) 1 x)=_
    rw [he,integral_const_mul]; rfl

theorem bounded_physical_moments_in_open
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {U O : Set Coord3} (hO : IsOpen O) (hne : O.Nonempty) (hOU : O⊆U)
    (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p)) :
    ∃ (Q : Coord3 → PhysicalSourcePair) (L : ℝ),0<L ∧
      (∀ m,CompactSmoothPair (Q m)) ∧ (∀ m,PairSupported (Q m) O) ∧
      (∀ m,physicalSourceMoment u (Q m)=m) ∧
      ∀ m j,UniformC1Bound (Q m j) (L*‖m‖) := by
  classical
  choose g hg hs hm using fun i : Fin 3 =>
    exists_physical_moments_in_open hu hO hne hOU hD (Pi.single i 1)
  let Q : Coord3 → PhysicalSourcePair := fun m => ∑ i,m i • g i
  have hq (m) : CompactSmoothPair (Q m) :=
    CompactSmoothPair.sum _ _ (fun i _ => (hg i).smul (m i))
  have hqs (m) : PairSupported (Q m) O :=
    PairSupported.sum _ _ (fun i _ => (hs i).smul (m i))
  have hqm (m) : physicalSourceMoment u (Q m)=m := by
    change physicalSourceMoment u (∑ i,m i • g i)=m
    rw [physicalSourceMoment_sum _ _ hu.continuous (fun i _ => (hg i).smul (m i))]
    simp_rw [physicalSourceMoment_smul,hm]
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  choose B hB hb using fun j : Fin 2 => fun n : Fin 2 =>
    fixed_smooth_tests_bound (fun i : Fin 3 => g i j) (fun i => (hg i j).1) (fun i => (hg i j).2) n.val
  let L := ∑ j : Fin 2,∑ n : Fin 2,B j n
  have hL : 0<L := Finset.sum_pos (fun j _ => Finset.sum_pos (fun n _ => hB j n) Finset.univ_nonempty)
    Finset.univ_nonempty
  have hBL (j n) : B j n≤L :=
    (Finset.single_le_sum (fun k _ => (hB j k).le) (Finset.mem_univ n)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => (hB k l).le)) (Finset.mem_univ j))
  refine ⟨Q,L,hL,hq,hqs,hqm,?_⟩
  intro m j x
  have h0 := hb j 0 m ‖m‖ (norm_nonneg _) (norm_le_pi_norm m) x
  have h1 := hb j 1 m ‖m‖ (norm_nonneg _) (norm_le_pi_norm m) x
  simp only [Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h0
  simp only [Fin.val_one,norm_iteratedFDeriv_one] at h1
  have he : Q m j=(fun x => ∑ i,m i • g i j x) := by funext x; simp [Q,Finset.sum_apply]
  rw [he]
  exact ⟨h0.trans (mul_le_mul_of_nonneg_right (hBL j 0) (norm_nonneg _)),
    h1.trans (mul_le_mul_of_nonneg_right (hBL j 1) (norm_nonneg _))⟩

lemma integral_bound_on_compact {K : Set Coord3} (hK : IsCompact K) {f : Coord3 → ℝ}
    (hs : Function.support f⊆K) {C : ℝ} (hb : ∀ x∈K,|f x|≤C) :
    |∫ x,f x|≤C*volume.real K := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => Function.notMem_support.mp (fun h => hx (hs h)))]
  have he := norm_integral_le_of_norm_le_const (μ := volume.restrict K) (f := f) (C := C)
    (ae_restrict_of_forall_mem hK.measurableSet (fun x hx => by simpa only [Real.norm_eq_abs] using hb x hx))
  simpa only [Real.norm_eq_abs,Measure.real,Measure.restrict_apply_univ] using he

theorem physical_source_moment_bound
    {u : Coord3 → Fin 2 → ℝ} (hu : Continuous u) {V : Set Coord3}
    (hV : Bornology.IsBounded V) :
    ∃ L : ℝ,0<L ∧ ∀ r : PhysicalSourcePair,PairSupported r V →
      ∀ M : ℝ,0≤M → (∀ j x,|r j x|≤M) → ‖physicalSourceMoment u r‖≤L*M := by
  let K := closure V
  have hK : IsCompact K := hV.isCompact_closure
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
  let A := |B|+1
  let W := volume.real K
  have hA : 0<A := by dsimp [A]; positivity
  have hW : 0≤W := ENNReal.toReal_nonneg
  have huB (x) (hx : x∈K) (j : Fin 2) : |u x j|≤A :=
    (norm_le_pi_norm (u x) j).trans ((hB x hx).trans (by dsimp [A]; linarith [le_abs_self B]))
  refine ⟨(1+2*A)*(W+1),by positivity,fun r hs M hM hb => ?_⟩
  have hrK (j) : tsupport (r j)⊆K := (hs j).trans subset_closure
  have hi (j) : |∫ x,r j x|≤M*W :=
    integral_bound_on_compact hK ((subset_tsupport _).trans (hrK j)) (fun x _ => hb j x)
  have htK : Function.support (fun x => u x 1*r 0 x-u x 0*r 1 x)⊆K := by
    intro x hx
    by_contra hn
    have h0 := image_eq_zero_of_notMem_tsupport (fun h => hn (hrK 0 h))
    have h1 := image_eq_zero_of_notMem_tsupport (fun h => hn (hrK 1 h))
    exact hx (by simp [h0,h1])
  have ht : |∫ x,u x 1*r 0 x-u x 0*r 1 x|≤(2*A*M)*W := by
    apply integral_bound_on_compact hK htK
    intro x hx
    calc
      _ ≤ |u x 1*r 0 x|+|u x 0*r 1 x| := abs_sub _ _
      _ ≤ A*M+A*M := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul (huB x hx 1) (hb 0 x) (abs_nonneg _) hA.le)
          (mul_le_mul (huB x hx 0) (hb 1 x) (abs_nonneg _) hA.le)
      _ = _ := by ring
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
  intro j
  have hmass : M*W≤((1+2*A)*(W+1))*M := by
    nlinarith [mul_nonneg hM hW,mul_nonneg hA.le (mul_nonneg hM hW),mul_nonneg hA.le hM]
  have htorque : (2*A*M)*W≤((1+2*A)*(W+1))*M := by
    nlinarith [mul_nonneg hM hW,mul_nonneg hA.le hM]
  fin_cases j
  · exact (hi 0).trans hmass
  · exact (hi 1).trans hmass
  · exact ht.trans htorque

end ScalarConductivity

end
end

end OAI
