import Mathlib

namespace OAI
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ProfileDecay
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
def spaceJet (F : ℝ × V → E) (n : ℕ) (p : ℝ × V) := iteratedFDeriv ℝ n (fun z => F (p.1,z)) p.2
lemma spaceJet_smooth (F : ℝ × V → E) (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (spaceJet F n) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ V E).symm.contDiff.comp hF
  | succ n ih =>
    have hm : ContDiff ℝ ∞ (fun p : (ℝ × V) × V => spaceJet F n (p.1.1,p.2)) :=
      ih.comp ((contDiff_fst.fst).prodMk contDiff_snd)
    have hd : ContDiff ℝ ∞ (fun p : ℝ × V => fderiv ℝ (fun z => spaceJet F n (p.1,z)) p.2) :=
      hm.fderiv contDiff_snd (by simp)
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => V) E).symm.contDiff.comp hd

def timeD (F : ℝ × V → E) (p : ℝ × V) := fderiv ℝ F p (1,0)
lemma timeD_smooth (F : ℝ × V → E) (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (timeD F) := by
  exact (hF.fderiv_right (by simp)).clm_apply contDiff_const
lemma timeD_deriv (F : ℝ × V → E) (hF : ContDiff ℝ ∞ F) (s : ℝ) (z : V) :
    HasDerivAt (fun t => F (t,z)) (timeD F (s,z)) s := by
  exact ((hF.differentiable (by simp) (s,z)).hasFDerivAt).comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))
lemma even_timeD_zero (F : ℝ × V → E) (hF : ContDiff ℝ ∞ F)
    (he : ∀ s z, F (-s,z)=F (s,z)) (z : V) : timeD F (0,z)=0 := by
  have hd := timeD_deriv F hF 0 z
  have hd' : HasDerivAt (fun t => F (t,z)) (timeD F (0,z)) (-0) := by simpa only [neg_zero] using hd
  have hn := hd'.scomp 0 (hasDerivAt_neg (0:ℝ))
  simp only [Function.comp_def,neg_one_smul] at hn
  have heq : (fun s : ℝ => F (-s,z))=(fun s => F (s,z)) := funext (fun s => he s z)
  rw [heq] at hn
  have hh := hn.unique hd
  have hzero : (2:ℝ) • timeD F (0,z)=0 := by
    rw [two_smul]
    calc
      _ = -timeD F (0,z)+timeD F (0,z) := congrArg (fun q => q+timeD F (0,z)) hh.symm
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)

variable [FiniteDimensional ℝ V]

theorem parameter_decay (F : ℝ × V → E) (hF : ContDiff ℝ ∞ F)
    (he : ∀ s z, F (-s,z)=F (s,z)) (hz : ∀ z, F (0,z)=0) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℝ, s∈Icc (0:ℝ) 1 → ∀ z : V, ‖z‖≤3 →
      ‖spaceJet F n (s,z)‖≤C*s^2 := by
  let J := spaceJet F n
  have hJ : ContDiff ℝ ∞ J := spaceJet_smooth F hF n
  have hJe : ∀ s z, J (-s,z)=J (s,z) := by
    intro s z
    dsimp [J,spaceJet]
    congr 1
    exact funext (he s)
  have hJ0 : ∀ z, J (0,z)=0 := by
    intro z
    dsimp [J,spaceJet]
    rw [show (fun z => F (0,z))=(fun _ => (0:E)) from funext hz]
    simp
  have hD := timeD_smooth J hJ
  have hDD := timeD_smooth (timeD J) hD
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_closedBall (0:V) 3)).exists_bound_of_continuousOn hDD.continuous.continuousOn
  let C := max B 0
  have hC : 0≤C := le_max_right _ _
  have hb (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (z : V) (hz : ‖z‖≤3) : ‖timeD (timeD J) (s,z)‖≤C :=
    (hB (s,z) ⟨hs,by simpa [mem_closedBall,dist_zero_right] using hz⟩).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro s hs z hz
  have hdB (r : ℝ) (hr : r∈Icc (0:ℝ) s) : ‖timeD J (r,z)‖≤C*s := by
    have H := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t (_ : t∈Icc (0:ℝ) s) => (timeD_deriv (timeD J) hD t z).hasDerivWithinAt)
      (fun t ht => hb t ⟨ht.1,ht.2.le.trans hs.2⟩ z hz) r hr
    rw [even_timeD_zero J hJ hJe z,sub_zero,sub_zero] at H
    exact H.trans (mul_le_mul_of_nonneg_left hr.2 hC)
  have H := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t (_ : t∈Icc (0:ℝ) s) => (timeD_deriv J hJ t z).hasDerivWithinAt)
    (fun t ht => hdB t ⟨ht.1,ht.2.le⟩) s ⟨hs.1,le_rfl⟩
  simpa only [hJ0 z,sub_zero,pow_two,mul_assoc] using H
end ProfileDecay

end

end OAI
