import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TFResponseMargins
import OAI.Analysis.CoulombRadii.Propagation.WeakLocality
import OAI.Analysis.CoulombRadii.RadialBounds.NearActive

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma WeakLaplacianGE.congr_on {f g q r : Position → ℝ} {U : Set Position}
    (hw : WeakLaplacianGE f U q) (he : ∀ x∈U, f x=g x) (hq : ∀ x∈U, q x=r x) :
    WeakLaplacianGE g U r := by
  intro φ hφ hc ht hp
  have H := hw φ hφ hc ht hp
  have hleft : (fun x => q x*φ x)=(fun x => r x*φ x) := by
    funext x
    by_cases hx : x∈tsupport φ
    · rw [hq x (ht hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hright : (fun x => f x*coordinateLaplacian φ x)=(fun x => g x*coordinateLaplacian φ x) := by
    funext x
    by_cases hx : x∈tsupport φ
    · rw [he x (ht hx)]
    · simp [coordinateLaplacian_eq_zero_of_notMem_tsupport hx]
  simpa only [hleft,hright] using H

lemma WeakLaplacianGE.mono_domain {f q : Position → ℝ} {U V : Set Position}
    (hw : WeakLaplacianGE f U q) (hVU : V⊆U) : WeakLaplacianGE f V q :=
  fun φ hφ hc ht hp => hw φ hφ hc (ht.trans hVU) hp

theorem WeakNuclearSubsolution.near_active_cutoffTF {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f q : ι → Position → ℝ)
    {b : Position → ℝ} {a Z η : ℝ} {U : Set Position}
    (ha : 0<a) (hη : 0<η) (hU : IsOpen U)
    (hf : ∀ i∈s, Continuous (f i)) (hq : ∀ i∈s, LocallyIntegrable (q i) volume)
    (hb : Measurable b)
    (hbb : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |b x| ≤ C)
    (hw : ∀ i∈s, WeakNuclearSubsolution (fun x => Z*coulombKernel x+f i x) Z U (q i))
    (hcompare : ∀ i∈s, ∀ x∈U, s.sup' hs (fun j => f j x)-f i x<2*η →
      b x+cutoffReaction a (fun y => Z*coulombKernel y+f i y) x≤q i x) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+s.sup' hs (fun i => f i x)) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+s.sup' hs (fun i => f i y)) x) := by
  classical
  let M : Position → ℝ := fun x => s.sup' hs (fun i => f i x)
  have hM : Continuous M := Continuous.finset_sup'_apply hs hf
  have hbi : LocallyIntegrable b volume := locallyIntegrable_of_ball_bounds hb hbb
  apply (weakNuclearSubsolution_offset_iff hM).2
  apply WeakLaplacianGE.of_local hM.locallyIntegrable
    (hbi.add (cutoffReaction_offset_locallyIntegrable ha hM))
  intro x₀ hx₀
  obtain ⟨t,ht,hts,_,V,hxV,hV,hVU,hmax,hnear⟩ :=
    finite_max_near_active s hs f hf hU hx₀ hη
  have hft (i) (hi : i∈t) : Continuous (f i) := hf i (hts hi)
  have hwt (i) (hi : i∈t) : WeakNuclearSubsolution (fun x => Z*coulombKernel x+f i x) Z V
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+f i y) x) := by
    apply (weakNuclearSubsolution_offset_iff (hft i hi)).2
    apply (((weakNuclearSubsolution_offset_iff (hft i hi)).1 (hw i (hts hi))).mono_domain hVU).mono_source_on
      (hq i (hts hi)) (hbi.add (cutoffReaction_offset_locallyIntegrable ha (hft i hi)))
    exact Eventually.of_forall (fun x hx => hcompare i (hts hi) x (hVU hx) (hnear i hi x hx))
  have H := WeakNuclearSubsolution.finset_max_cutoffTF t ht f ha hV hft hb hbb hwt
  have H' := (weakNuclearSubsolution_offset_iff (Continuous.finset_sup'_apply ht hft)).1 H
  refine ⟨V,hxV,hV,H'.congr_on (fun x hx => (hmax x hx).symm) ?_⟩
  intro x hx
  dsimp only [M]
  unfold cutoffReaction
  by_cases haX : a ≤ ‖x‖
  · simp [Pi.add_apply, Set.indicator, haX, hmax x hx]
  · simp [Pi.add_apply, Set.indicator, haX]

def propagationBarrier (B r : ℝ) (x : Position) : ℝ :=
  B*(radialPower (-2) x-r/8*radialPower (-(5/2:ℝ)) x)

lemma radialPower_half_nat (n : ℕ) (x : Position) :
    radialPower (-((n:ℝ)/2)) x=(‖x‖^n)⁻¹ := by
  unfold radialPower
  rw [←Real.rpow_natCast ‖x‖ 2,←Real.rpow_mul (norm_nonneg x)]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*-((n:ℝ)/2)=-(n:ℝ) by ring]
  rw [Real.rpow_neg (norm_nonneg x),Real.rpow_natCast]

lemma propagationBarrier_eq (B r : ℝ) (x : Position) :
    propagationBarrier B r x=B/‖x‖^4*(1-r/(8*‖x‖)) := by
  unfold propagationBarrier
  rw [show (-2:ℝ)=-(((4:ℕ):ℝ)/2) by norm_num,
    show (-(5/2:ℝ))=-(((5:ℕ):ℝ)/2) by norm_num]
  rw [radialPower_half_nat,radialPower_half_nat]
  by_cases hn : ‖x‖=0
  · simp [hn]
  · field_simp

lemma contDiffOn_propagationBarrier (B r : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (propagationBarrier B r) punctured :=
  contDiffOn_const.mul ((contDiffOn_radialPower (-2) n).sub
    (contDiffOn_const.mul (contDiffOn_radialPower (-(5/2:ℝ)) n)))

lemma laplacian_propagationBarrier {x : Position} (hx : x≠0) (B r : ℝ) :
    coordinateLaplacian (propagationBarrier B r) x=
      B/‖x‖^6*(12-5*r/(2*‖x‖)) := by
  have hcp (p : ℝ) : ContDiffAt ℝ 2 (radialPower p) x :=
    (contDiffOn_radialPower p 2).contDiffAt (isOpen_punctured.mem_nhds hx)
  unfold propagationBarrier
  rw [coordinateLaplacian_const_mul]
  have he : (fun y => radialPower (-2) y-r/8*radialPower (-(5/2:ℝ)) y)=
      (fun y => radialPower (-2) y+(-r/8)*radialPower (-(5/2:ℝ)) y) := by
    funext y
    ring
  rw [he,coordinateLaplacian_add_at (hcp (-2)) (contDiffAt_const.mul (hcp (-(5/2:ℝ)))),
    coordinateLaplacian_const_mul]
  simp only [coordinateLaplacian_radialPower hx]
  have h7 : (‖x‖^2)^(-(7/2:ℝ))=(‖x‖^7)⁻¹ := by
    exact radialPower_half_nat 7 x
  norm_num [show (-(5/2:ℝ))-1=-(7/2:ℝ) by ring,Real.rpow_neg_natCast,h7]
  have hn := norm_ne_zero_iff.mpr hx
  field_simp
  ring

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma tfScalarDensity_eq_kTF (v : ℝ) :
    Coulomb.tfScalarDensity v=kTF*(max v 0)^(3/2:ℝ) := by
  have hπ : 0<3*Real.pi^2 := by positivity
  have hcf : Coulomb.thomasFermiKineticConstant*(5/3:ℝ)=(3*Real.pi^2)^(2/3:ℝ)/2 := by
    unfold Coulomb.thomasFermiKineticConstant
    ring
  unfold Coulomb.tfScalarDensity
  rw [hcf,Real.div_rpow (le_max_right _ _) (by positivity),
    Real.div_rpow (Real.rpow_nonneg hπ.le _) (by norm_num),←Real.rpow_mul hπ.le]
  norm_num
  unfold kTF
  field_simp

lemma tfReaction_eq_scalar (v : ℝ) : tfReaction v=4*Real.pi*Coulomb.tfScalarDensity v := by
  rw [tfScalarDensity_eq_kTF]
  unfold tfReaction
  ring

lemma tfReaction_normalized {d : ℝ} (hd : 0<d) (v : ℝ) :
    d^6*tfReaction v=4*Real.pi*Coulomb.tfScalarDensity (d^4*v) := by
  have H := Coulomb.tfScalarDensity_scale (d^4*v) hd
  have he : d^4*v/d^4=v := by field_simp
  rw [he] at H
  rw [tfReaction_eq_scalar,H]
  field_simp

lemma normalized_density_le_reaction_iff {d μ v : ℝ} (hd : 0<d) :
    d^6*μ≤Coulomb.tfScalarDensity (d^4*v) ↔ 4*Real.pi*μ≤tfReaction v := by
  have H := tfReaction_normalized hd v
  have hp : 0<4*Real.pi := by positivity
  constructor
  · intro h
    have HH := mul_le_mul_of_nonneg_left h hp.le
    have h' : d^6*(4*Real.pi*μ)≤d^6*tfReaction v := by nlinarith only [HH,H]
    exact (mul_le_mul_iff_right₀ (pow_pos hd 6)).mp h'
  · intro h
    have HH := mul_le_mul_of_nonneg_left h (pow_pos hd 6).le
    have h' : (4*Real.pi)*(d^6*μ)≤(4*Real.pi)*Coulomb.tfScalarDensity (d^4*v) := by nlinarith only [HH,H]
    exact (mul_le_mul_iff_right₀ hp).mp h'

lemma normalized_reaction_le_density_iff {d μ v : ℝ} (hd : 0<d) :
    Coulomb.tfScalarDensity (d^4*v)≤d^6*μ ↔ tfReaction v≤4*Real.pi*μ := by
  have H := tfReaction_normalized hd v
  have hp : 0<4*Real.pi := by positivity
  constructor
  · intro h
    have HH := mul_le_mul_of_nonneg_left h hp.le
    have h' : d^6*tfReaction v≤d^6*(4*Real.pi*μ) := by nlinarith only [HH,H]
    exact (mul_le_mul_iff_right₀ (pow_pos hd 6)).mp h'
  · intro h
    have HH := mul_le_mul_of_nonneg_left h (pow_pos hd 6).le
    have h' : (4*Real.pi)*Coulomb.tfScalarDensity (d^4*v)≤(4*Real.pi)*(d^6*μ) := by nlinarith only [HH,H]
    exact (mul_le_mul_iff_right₀ hp).mp h'

lemma propagation_gain_density {d R u H μ l1 l2 e ξ hl hh : ℝ}
    (hd : 0<d) (hR : 0<R) (hdR : R/2≤d) (hξ : 0≤ξ)
    (hgap : 16*ξ+2*e<l1-l2)
    (hu : hl≤d^4*u ∧ d^4*u≤hh)
    (hinv : ∀ h∈Icc hl hh,Coulomb.tfScalarDensity h≤d^6*μ → h-ξ≤d^4*H)
    (hnear : H≤u-(l1-l2-2*e)/R^4) : 4*Real.pi*μ≤tfReaction u := by
  by_contra hh'
  have hm : Coulomb.tfScalarDensity (d^4*u)≤d^6*μ :=
    (normalized_reaction_le_density_iff hd).mpr (le_of_not_ge hh')
  have hI := hinv _ hu hm
  have hp : R^4≤16*d^4 := by
    have := pow_le_pow_left₀ (by positivity : 0≤R/2) hdR 4
    nlinarith only [this]
  have hgap' : 16*ξ<l1-l2-2*e := by linarith only [hgap]
  have hd4 : 0<d^4 := pow_pos hd 4
  have hR4 : 0<R^4 := pow_pos hR 4
  have hnear' : H*R^4≤u*R^4-(l1-l2-2*e) := by
    have h := mul_le_mul_of_nonneg_right hnear hR4.le
    field_simp at h
    linarith only [h]
  have hgg : ξ*R^4<(l1-l2-2*e)*d^4 := by
    calc
      _≤ξ*(16*d^4) := mul_le_mul_of_nonneg_left hp hξ
      _<(l1-l2-2*e)*d^4 := by nlinarith only [mul_lt_mul_of_pos_right hgap' hd4]
  have h1 := mul_le_mul_of_nonneg_right hI hR4.le
  have h2 := mul_le_mul_of_nonneg_right hnear' hd4.le
  nlinarith only [h1,h2,hgg]

lemma propagation_outer_reaction {d R H μ l2 ξ hl hh : ℝ}
    (hR : 0<R) (hRd : R≤d) (hξ : 0≤ξ) (hξl : ξ<l2)
    (hv : hl≤d^4*(H-l2/R^4) ∧ d^4*(H-l2/R^4)≤hh)
    (hinv : ∀ h∈Icc hl hh,d^6*μ≤Coulomb.tfScalarDensity h → d^4*H≤h+ξ) :
    tfReaction (H-l2/R^4)≤4*Real.pi*μ := by
  have hd : 0<d := hR.trans_le hRd
  by_contra hh'
  have hm : d^6*μ≤Coulomb.tfScalarDensity (d^4*(H-l2/R^4)) :=
    (normalized_density_le_reaction_iff hd).mpr (le_of_not_ge hh')
  have hI := hinv _ hv hm
  have hp := pow_le_pow_left₀ hR.le hRd 4
  have hR4 := pow_pos hR 4
  have h1 := mul_le_mul_of_nonneg_right hI hR4.le
  have he : (d^4*(H-l2/R^4)+ξ)*R^4=d^4*H*R^4-l2*d^4+ξ*R^4 := by field_simp
  rw [he] at h1
  have h2 := mul_le_mul_of_nonneg_left hp hξ
  have h3 := mul_lt_mul_of_pos_right hξl (pow_pos hd 4)
  nlinarith only [h1,h2,h3]
end NeutralAtom

end

end OAI
