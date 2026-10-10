import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.PicardCurvature

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma lorentzField_same_point_bound (E B E' B' : Field) (p : ℝ × Phase) :
    ‖lorentzField E B p-lorentzField E' B' p‖≤
      ‖E (p.1,p.2.1)-E' (p.1,p.2.1)‖+‖B (p.1,p.2.1)-B' (p.1,p.2.1)‖ := by
  have he : E (p.1,p.2.1)+cross (velocity p.2.2) (B (p.1,p.2.1))-
      (E' (p.1,p.2.1)+cross (velocity p.2.2) (B' (p.1,p.2.1)))=
      E (p.1,p.2.1)-E' (p.1,p.2.1)+cross (velocity p.2.2) (B (p.1,p.2.1)-B' (p.1,p.2.1)) := by
    rw [cross_sub_right]; abel
  have hb := (norm_cross_le (velocity p.2.2) (B (p.1,p.2.1)-B' (p.1,p.2.1))).trans
    (mul_le_mul_of_nonneg_right (norm_velocity_lt_one p.2.2).le (norm_nonneg _))
  change max ‖velocity p.2.2-velocity p.2.2‖
    ‖E (p.1,p.2.1)+cross (velocity p.2.2) (B (p.1,p.2.1))-
      (E' (p.1,p.2.1)+cross (velocity p.2.2) (B' (p.1,p.2.1)))‖≤_
  rw [sub_self,norm_zero,he]
  exact max_le (by positivity) ((norm_add_le _ _).trans (add_le_add le_rfl (by simpa only [one_mul] using hb)))

lemma uniform_lorentzField {E B : ℕ → Field} {e b : Field} {T : ℝ}
    (hE : TendstoUniformlyOn E e atTop {p | p.1∈Icc 0 T})
    (hB : TendstoUniformlyOn B b atTop {p | p.1∈Icc 0 T}) :
    TendstoUniformlyOn (fun n => lorentzField (E n) (B n)) (lorentzField e b) atTop {p | p.1∈Icc 0 T} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hE (ε/2) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp hB (ε/2) (by positivity)] with n hnE hnB p hp
  have he := hnE (p.1,p.2.1) hp
  have hb := hnB (p.1,p.2.1) hp
  rw [dist_comm,dist_eq_norm] at he hb ⊢
  exact (lorentzField_same_point_bound _ _ _ _ p).trans_lt (by linarith)

lemma lorentzField_norm_bound {E B : Field} {T L : ℝ}
    (hL : 0≤L) (hb : GlobalFieldBound T L E B) (p : ℝ × Phase) (hp : p.1∈Icc 0 T) :
    ‖lorentzField E B p‖≤1+2*L := by
  have hh := hb p.1 hp p.2.1
  have hc := (norm_cross_le (velocity p.2.2) (B (p.1,p.2.1))).trans
    (mul_le_mul (norm_velocity_lt_one p.2.2).le hh.2 (norm_nonneg _) zero_le_one)
  change max ‖velocity p.2.2‖ ‖E (p.1,p.2.1)+cross (velocity p.2.2) (B (p.1,p.2.1))‖≤_
  exact max_le ((norm_velocity_lt_one p.2.2).le.trans (by linarith))
    ((norm_add_le _ _).trans (by linarith))

lemma picard_particle_full_derivative_limit {d : Datum} {S : ℕ → Solution}
    {E B : Field} {f : Particle} {T H M L : ℝ} (hH : 0≤H) (hM : 0≤M) (hL : 0≤L)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (htransport : ∀ n, TransportFor (S (n+1)) (S n).E (S n).B)
    (hc : ∀ n, PhaseParticleCurvature T H (S (n+1)).f)
    (hlip : ∀ n, PhaseParticleLip T M (S (n+1)).f)
    (hlb : GlobalFieldBound T L E B)
    (hfl : TendstoUniformlyOn (fun n => (S (n+1)).f) f atTop {p | p.1∈Icc 0 T})
    (hEl : TendstoUniformlyOn (fun n => (S n).E) E atTop {p | p.1∈Icc 0 T})
    (hBl : TendstoUniformlyOn (fun n => (S n).B) B atTop {p | p.1∈Icc 0 T}) :
    ∃ Z : ℝ × Phase → (Phase →L[ℝ] ℝ),
      TendstoUniformlyOn (fun n p => fderiv ℝ (fun z => (S (n+1)).f (p.1,z)) p.2) Z atTop {p | p.1∈Icc 0 T} ∧
      (∀ t∈Icc 0 T, ∀ z, HasFDerivAt (fun w => f (t,w)) (Z (t,z)) z) ∧
      TendstoUniformlyOn (fun n p => fderiv ℝ (S (n+1)).f p)
        (fun p => assembleDerivative (-Z p (lorentzField E B p)) (Z p)) atTop {p | p.1∈Icc 0 T} := by
  have hs (n : ℕ) (t : ℝ) : Differentiable ℝ (fun z => (S (n+1)).f (t,z)) :=
    ((hr n).smooth_f.differentiable (by simp)).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨Z,hZ,hdZ⟩ := uniform_spatial_derivative_limit hH (fun n t ht => hs n t) hc hfl
  have hbZ (n : ℕ) (p : ℝ × Phase) (hp : p.1∈Icc 0 T) :
      ‖fderiv ℝ (fun z => (S (n+1)).f (p.1,z)) p.2‖≤M := by
    apply norm_fderiv_le_of_lip' ℝ hM
    exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hlip n p.1 hp z p.2
  have heval := uniform_clm_apply_bounded hM (show 0≤1+2*L by positivity)
    hZ (uniform_lorentzField hEl hBl) hbZ (lorentzField_norm_bound hL hlb)
  have hh := uniform_assembleDerivative heval.neg hZ
  refine ⟨Z,hZ,hdZ,hh.congr (Eventually.of_forall fun n p hp => ?_)⟩
  symm
  change fderiv ℝ (S (n+1)).f p=assembleDerivative
    (-fderiv ℝ (fun z => (S (n+1)).f (p.1,z)) p.2 (lorentzField (S n).E (S n).B p))
    (fderiv ℝ (fun z => (S (n+1)).f (p.1,z)) p.2)
  rw [fderiv_eq_assemble ((hr n).smooth_f.differentiable (by simp))]
  congr 1
  have ht := htransport n p.1 p.2
  change fderiv ℝ (S (n+1)).f p (1,lorentzField (S n).E (S n).B p)=0 at ht
  have he : ((1 : ℝ),lorentzField (S n).E (S n).B p)=(1,0)+(0,lorentzField (S n).E (S n).B p) := by simp
  rw [he,map_add] at ht
  rw [fderiv_spatial_slice ((hr n).smooth_f.differentiable (by simp))]
  exact eq_neg_of_add_eq_zero_left ht

end RVM
end

end OAI
