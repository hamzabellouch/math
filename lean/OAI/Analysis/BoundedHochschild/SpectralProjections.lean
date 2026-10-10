import Mathlib
import OAI.Analysis.BoundedHochschild.MonotoneLimits

namespace OAI

/-! Support projections, power limits and density of projection spans. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildUltrapower
open BoundedHochschild
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (hω : (ω : Filter ℕ) ≤ atTop)
include hω

 
theorem exists_power_projection (b : Ultrapower τ h1 ω htr) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ p : Ultrapower τ h1 ω htr, IsStarProjection p ∧ GNSTendsto (quotientTrace τ h1 ω htr) (fun n : ℕ => b^n) atTop p ∧
      b*p=p ∧ ∀ x : Ultrapower τ h1 ω htr, b*x=x → p*x=x := by
  let a : ℕ → Ultrapower τ h1 ω htr := fun n => 1-b^n
  have ha0 : ∀ n, 0 ≤ a n := fun n => sub_nonneg.mpr (by
    simpa only [pow_zero] using CStarAlgebra.pow_antitone hb1 hb0 (Nat.zero_le n))
  have ha1 : ∀ n, a n ≤ 1 := fun n => sub_le_self _ (CStarAlgebra.pow_nonneg b n hb0)
  have ham : Monotone a := fun n m hnm => sub_le_sub_left
    (CStarAlgebra.pow_antitone hb1 hb0 hnm) 1
  obtain ⟨c,_hc,ht⟩ := exists_bounded_GNS_limit τ h1 ω htr hω a 1
    (fun n => (CStarAlgebra.norm_le_one_iff_of_nonneg _ (ha0 n)).mpr (ha1 n))
    (monotone_contractions_preGNS_cauchy (quotientTrace τ h1 ω htr) a ha0 ha1 ham)
  let p : Ultrapower τ h1 ω htr := 1-c
  have hp : GNSTendsto (quotientTrace τ h1 ω htr) (fun n : ℕ => b^n) atTop p := by
    simpa only [a,sub_sub_cancel] using (GNSTendsto.const (quotientTrace τ h1 ω htr) (1:Ultrapower τ h1 ω htr) (atTop : Filter ℕ)).sub (quotientTrace τ h1 ω htr) ht
  have hpstar : star p=p := by
    apply GNSTendsto.unique (quotientTrace τ h1 ω htr) (quotientTrace_faithful τ h1 ω htr) (hp.star (quotientTrace τ h1 ω htr) (quotientTrace_tracial τ h1 ω htr))
    simpa only [star_pow,(IsSelfAdjoint.of_nonneg hb0).star_eq] using hp
  have htimes : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hpp : p*p=p := by
    apply GNSTendsto.unique (quotientTrace τ h1 ω htr) (quotientTrace_faithful τ h1 ω htr) (hp.mul (quotientTrace τ h1 ω htr) (quotientTrace_tracial τ h1 ω htr) hp 1 (norm_pow_pos_contraction b hb0 hb1))
    simpa only [GNSTendsto,Function.comp_def,two_mul,pow_add] using
      (show Tendsto (fun n : ℕ => ‖(quotientTrace τ h1 ω htr).toPreGNS (b^(2*n)-p)‖) atTop (𝓝 0) from hp.comp htimes)
  have hbp : b*p=p := by
    apply GNSTendsto.unique (quotientTrace τ h1 ω htr) (quotientTrace_faithful τ h1 ω htr)
      ((GNSTendsto.const (quotientTrace τ h1 ω htr) b (atTop : Filter ℕ)).mul (quotientTrace τ h1 ω htr) (quotientTrace_tracial τ h1 ω htr) hp ‖b‖ (fun _ => le_rfl))
    simpa only [GNSTendsto,Function.comp_def,pow_succ'] using hp.comp (tendsto_add_atTop_nat 1)
  refine ⟨p,⟨hpp,hpstar⟩,hp,hbp,?_⟩
  intro x hx
  have hpow (n : ℕ) : b^n*x=x := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_assoc,ih,hx]
  apply GNSTendsto.unique (quotientTrace τ h1 ω htr) (quotientTrace_faithful τ h1 ω htr)
    (hp.mul (quotientTrace τ h1 ω htr) (quotientTrace_tracial τ h1 ω htr) (GNSTendsto.const (quotientTrace τ h1 ω htr) x atTop) 1 (norm_pow_pos_contraction b hb0 hb1))
  simpa only [hpow] using GNSTendsto.const (quotientTrace τ h1 ω htr) x (atTop : Filter ℕ)

lemma exists_support_contraction (a : Ultrapower τ h1 ω htr) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ p : Ultrapower τ h1 ω htr, IsSupportProjection a p ∧
      GNSTendsto (quotientTrace τ h1 ω htr) (fun n : ℕ => 1-(1-a)^n) atTop p := by
  obtain ⟨q,hq,ht,hbq,hqx⟩ := exists_power_projection τ h1 ω htr hω (1-a)
    (sub_nonneg.mpr ha1) (sub_le_self _ ha0)
  have haq : a*q=0 := by
    have hh := hbq
    rw [sub_mul,one_mul] at hh
    exact sub_eq_self.mp hh
  have hqa : q*a=0 := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg ha0).star_eq,star_zero]
      using congrArg Star.star haq
  refine ⟨1-q,⟨hq.one_sub,?_,?_,?_⟩,?_⟩
  · simp only [sub_mul,one_mul,hqa,sub_zero]
  · simp only [mul_sub,mul_one,haq,sub_zero]
  · intro x hx
    have hbx : (1-a)*x=x := by simp only [sub_mul,one_mul,hx,sub_zero]
    simp only [sub_mul,one_mul,hqx x hbx,sub_self]
  · exact (GNSTendsto.const (quotientTrace τ h1 ω htr) 1 (atTop : Filter ℕ)).sub (quotientTrace τ h1 ω htr) ht

 

theorem exists_support_projection (a : Ultrapower τ h1 ω htr) (ha : 0 ≤ a) :
    ∃ p : Ultrapower τ h1 ω htr, IsSupportProjection a p := by
  let r : ℝ := ‖a‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hi : 0 < r⁻¹ := inv_pos.mpr hr
  have hn : ‖r⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hi]
    exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
  have hsa : 0 ≤ r⁻¹ • a := smul_nonneg hi.le ha
  obtain ⟨p,hp,_⟩ := exists_support_contraction τ h1 ω htr hω (r⁻¹ • a) hsa
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hsa).mp hn)
  refine ⟨p,hp.proj,?_,?_,?_⟩
  · have hh := congrArg (fun z : Ultrapower τ h1 ω htr => r • z) hp.left
    simpa only [mul_smul_comm,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · have hh := congrArg (fun z : Ultrapower τ h1 ω htr => r • z) hp.right
    simpa only [smul_mul_assoc,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · intro x hx
    apply hp.annihilate x
    simp only [smul_mul_assoc,hx,smul_zero]

end HochschildUltrapower

 

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma norm_add_smul_sq_of_star_mul_zero (x y : M) (hxy : star y*x=0) (t : ℝ) :
    ‖y+t • x‖^2 ≤ ‖y‖^2+t^2*‖x‖^2 := by
  have hyx : star x*y=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hxy
  rw [pow_two, ← CStarRing.norm_star_mul_self]
  have he : star (y+t • x)*(y+t • x)=star y*y+(t^2) • (star x*x) := by
    simp only [star_add,star_smul,star_trivial,add_mul,mul_add,mul_smul_comm,
      smul_mul_assoc,smul_smul,hxy,hyx,smul_zero,add_zero,zero_add,pow_two]
  rw [he]
  apply (norm_add_le _ _).trans_eq
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg t),
    CStarRing.norm_star_mul_self,CStarRing.norm_star_mul_self]
  ring

 

theorem projection_range_limit (p : M) (hp : IsStarProjection p)
    {a : I → M} {l : Filter I} [l.NeBot] {b : M}
    (C : ℝ) (_hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (hpa : ∀ i, p*a i=a i) (ht : PredualTendsto e a l b) : p*b=b := by
  let q := 1-p
  have hq : IsStarProjection q := hp.one_sub
  let y := q*b
  have hqy : q*y=y := by dsimp [y]; rw [← mul_assoc,hq.isIdempotentElem.eq]
  have hy (i : I) : star y*a i=0 := by
    have hqa : q*a i=0 := by dsimp [q]; rw [sub_mul,one_mul,hpa i,sub_self]
    dsimp [y]
    rw [star_mul,hq.isSelfAdjoint.star_eq,mul_assoc,hqa,mul_zero]
  have hbound (t : ℝ) : ‖y+t • b‖^2 ≤ ‖y‖^2+t^2*C^2 := by
    have hpos : 0 ≤ ‖y‖^2+t^2*C^2 := by positivity
    have hn (i : I) : ‖y+t • a i‖ ≤ Real.sqrt (‖y‖^2+t^2*C^2) := by
      apply (Real.le_sqrt (norm_nonneg _) hpos).mpr
      exact (norm_add_smul_sq_of_star_mul_zero (a i) y (hy i) t).trans (by gcongr; exact ha i)
    have ht' : PredualTendsto e (fun i => y+t • a i) l (y+t • b) := by
      simp only [← Complex.coe_smul]
      exact predual_tendsto_add e (predual_tendsto_const e y l) (predual_tendsto_smul e ht (t:ℂ))
    exact (Real.le_sqrt (norm_nonneg _) hpos).mp
      (predual_norm_le e _ (Real.sqrt_nonneg _) (Eventually.of_forall hn) ht')
  have hzero : ‖y‖=0 := by
    by_contra hy0
    have hyp : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
    let t : ℝ := ‖y‖^2/(C^2+1)
    have ht0 : 0 < t := div_pos (sq_pos_of_pos hyp) (by positivity)
    have hlow : (1+t)*‖y‖ ≤ ‖y+t • b‖ := by
      calc
        (1+t)*‖y‖ = ‖(1+t) • y‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
        _ = ‖q*(y+t • b)‖ := by rw [mul_add,mul_smul_comm,hqy]; congr 1; module
        _ ≤ ‖q‖*‖y+t • b‖ := norm_mul_le _ _
        _ ≤ 1*‖y+t • b‖ := by gcongr; exact hq.norm_le
        _ = ‖y+t • b‖ := one_mul _
    have hs := hbound t
    have hs' : ((1+t)*‖y‖)^2 ≤ ‖y+t • b‖^2 := by gcongr
    have hte : t*(C^2+1)=‖y‖^2 := by dsimp [t]; field_simp
    nlinarith [sq_nonneg (t*‖y‖)]
  have hqb : q*b=0 := norm_eq_zero.mp hzero
  dsimp [q] at hqb
  simpa only [sub_mul,one_mul,sub_eq_zero,eq_comm] using hqb

 

theorem predual_tendsto_projection_mul_bounded (p : M) (hp : IsStarProjection p)
    {a : I → M} {l : Filter I} {b : M}
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (ht : PredualTendsto e a l b) :
    PredualTendsto e (fun i => p*a i) l (p*b) := by
  intro z
  rw [Filter.tendsto_iff_ultrafilter]
  intro u hu
  have htu : PredualTendsto e a (u : Filter I) b := fun x => (ht x).mono_left hu
  have hpa (i : I) : ‖p*a i‖ ≤ C :=
    (norm_mul_le _ _).trans (by simpa using (mul_le_mul hp.norm_le (ha i) (norm_nonneg _) zero_le_one))
  obtain ⟨c,_,hc⟩ := exists_predual_ultralimit e u (fun i => p*a i) C hpa
  have hpc : p*c=c := projection_range_limit e p hp C hC hpa
    (fun i => by rw [← mul_assoc,hp.isIdempotentElem.eq]) hc
  have hq : IsStarProjection (1-p) := hp.one_sub
  have hqa (i : I) : ‖(1-p)*a i‖ ≤ C :=
    (norm_mul_le _ _).trans (by simpa using (mul_le_mul hq.norm_le (ha i) (norm_nonneg _) zero_le_one))
  have hqt : PredualTendsto e (fun i => (1-p)*a i) (u : Filter I) (b-c) := by
    simpa only [sub_mul,one_mul] using predual_tendsto_sub e htu hc
  have hqc := projection_range_limit e (1-p) hq C hC hqa
    (fun i => by rw [← mul_assoc,hq.isIdempotentElem.eq]) hqt
  have hcb : c=p*b := by
    rw [sub_mul,one_mul,mul_sub,hpc] at hqc
    have hh : p*b-c=0 := sub_eq_self.mp hqc
    exact (sub_eq_zero.mp hh).symm
  exact hcb ▸ hc z

 
theorem projection_mul_hasPreadjoint [CompleteSpace X] (p : M)
    (hp : IsStarProjection p) : HasPreadjoint e (ContinuousLinearMap.mul ℂ M p) := by
  intro z
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let L : StrongDual ℂ X →ₗ[ℂ] ℂ :=
    { toFun := fun f => e.symm (p*e f) z
      map_add' := by intro f g; simp [mul_add]
      map_smul' := by intro r f; simp [map_smulₛₗ] }
  have hb (f : StrongDual ℂ X) : ‖L f‖ ≤ (‖p‖*‖z‖)*‖f‖ := by
    change ‖e.symm (p*e f) z‖ ≤ _
    calc
      _ ≤ ‖e.symm (p*e f)‖*‖z‖ := (e.symm (p*e f)).le_opNorm z
      _ = ‖p*e f‖*‖z‖ := by rw [e.symm.norm_map]
      _ ≤ (‖p‖*‖e f‖)*‖z‖ := by gcongr; exact norm_mul_le _ _
      _ = (‖p‖*‖z‖)*‖f‖ := by rw [e.norm_map]; ring
  let F := L.mkContinuous (‖p‖*‖z‖) hb
  have hF (a : Finset X → StrongDual ℂ X) (ha : ∀ s, ‖a s‖ ≤ 1)
      (hta : ∀ x, Tendsto (fun s => a s x) atTop (𝓝 0)) :
      Tendsto (fun s => F (a s)) atTop (𝓝 0) := by
    have ht : PredualTendsto e (fun s => e (a s)) atTop 0 := by
      intro x
      simpa using hta x
    have hh := predual_tendsto_projection_mul_bounded e p hp 1 zero_le_one
      (fun s => by simpa only [e.norm_map] using ha s) ht
    simpa [F,L] using hh z
  obtain ⟨w,hw⟩ := mem_predual_of_bounded_weak_continuity F hF
  refine ⟨w,fun a => ?_⟩
  simpa [F,L] using hw (e.symm a)

end HochschildSakai

 

open Filter Topology

namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma isGLB_of_antitone_predual_limit [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (a : I → M) (hm : Antitone a) {p : M} (ht : PredualTendsto e a atTop p)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) : IsGLB (Set.range a) p := by
  constructor
  · rintro _ ⟨i,rfl⟩
    apply le_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ ht
    exact (eventually_ge_atTop i).mono fun j hj => hm hj
  · intro d hd
    apply ge_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ ht
    exact Eventually.of_forall fun i => hd (Set.mem_range_self i)

lemma exists_antitone_predual_limit [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (a : I → M) (hm : Antitone a) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ p : M, ‖p‖ ≤ C ∧ IsGLB (Set.range a) p ∧ PredualTendsto e a atTop p := by
  obtain ⟨b,hb,_,ht⟩ := exists_monotone_predual_limit e (fun i => -a i)
    (fun i j hij => neg_le_neg (hm hij)) C hC
    (fun i => by simpa only [norm_neg] using ha i)
  have ht' : PredualTendsto e a atTop (-b) := by
    simpa only [neg_neg] using predual_tendsto_neg e ht
  exact ⟨-b,by simpa only [norm_neg] using hb,
    isGLB_of_antitone_predual_limit e a hm ht' C hC ha,ht'⟩

lemma isGLB_star_conjugate {a : I → M} {p : M} (hp : IsGLB (Set.range a) p)
    (u : Mˣ) : IsGLB (Set.range (fun i => star (u:M)*a i*u)) (star (u:M)*p*u) := by
  constructor
  · rintro _ ⟨i,rfl⟩
    exact star_left_conjugate_le_conjugate (hp.1 (Set.mem_range_self i)) _
  · intro d hd
    have hx : star (↑(u⁻¹):M)*d*(↑(u⁻¹):M) ≤ p := by
      apply hp.2
      rintro _ ⟨i,rfl⟩
      have hh := star_left_conjugate_le_conjugate (hd (Set.mem_range_self i)) (↑(u⁻¹):M)
      simpa [← mul_assoc,← star_mul] using hh
    have hh := star_left_conjugate_le_conjugate hx (u:M)
    simpa [← mul_assoc,← star_mul] using hh

 

lemma le_of_positive_fixed (a b : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hba : b*a=a) : a ≤ b := by
  have hab : a*b=a := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg ha0).star_eq,
      (IsSelfAdjoint.of_nonneg hb0).star_eq] using congrArg star hba
  have hcomm : Commute b (1-a) := by
    change b*(1-a)=(1-a)*b
    rw [mul_sub,sub_mul,mul_one,one_mul,hba,hab]
  have hh := hcomm.mul_nonneg hb0 (sub_nonneg.mpr ha1)
  simpa only [mul_sub,mul_one,hba,sub_nonneg] using hh

 

theorem power_limit_fixed (b p : M) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hp : IsGLB (Set.range (fun n : ℕ => b^n)) p)
    (ht : PredualTendsto e (fun n : ℕ => b^n) atTop p) : b*p=p := by
  have hbsa := IsSelfAdjoint.of_nonneg hb0
  have hnorm (n : ℕ) : ‖b^n‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (CStarAlgebra.pow_nonneg b n hb0)).mpr
      (by simpa only [pow_zero] using CStarAlgebra.pow_antitone hb1 hb0 (Nat.zero_le n))
  have ht1 : PredualTendsto e (fun n : ℕ => b^(n+1)) atTop p :=
    fun z => (ht z).comp (tendsto_add_atTop_nat 1)
  have ht2 : PredualTendsto e (fun n : ℕ => b^(n+2)) atTop p :=
    fun z => (ht z).comp (tendsto_add_atTop_nat 2)
  have hconj (t : ℝ) (ht0 : 0 ≤ t) :
      (1+t • b)*p*(1+t • b)=(1+t)^2 • p := by
    let c : M := 1+t • b
    have hc0 : 1 ≤ c := le_add_of_nonneg_right (smul_nonneg ht0 hb0)
    have hcu : IsUnit c := CStarAlgebra.isUnit_of_le 1 hc0
    obtain ⟨u,hu⟩ := hcu
    have hcsa : IsSelfAdjoint c := (IsSelfAdjoint.of_nonneg (zero_le_one.trans hc0))
    have hgl : IsGLB (Set.range (fun n : ℕ => c*b^n*c)) (c*p*c) := by
      simpa only [hu,hcsa.star_eq] using isGLB_star_conjugate hp u
    have heq (n : ℕ) : c*b^n*c = b^n+(2*t) • b^(n+1)+(t^2) • b^(n+2) := by
      dsimp [c]
      rw [show n+2=(n+1)+1 by omega,pow_succ,pow_succ]
      simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,
        ← pow_succ',← pow_succ]
      module
    have htc : PredualTendsto e (fun n : ℕ => c*b^n*c) atTop ((1+t)^2 • p) := by
      have hh := predual_tendsto_add e
        (predual_tendsto_add e ht (predual_tendsto_smul e ht1 ((2*t:ℝ):ℂ)))
        (predual_tendsto_smul e ht2 ((t^2:ℝ):ℂ))
      simp only [Complex.coe_smul] at hh
      have he : p+(2*t) • p+t^2 • p=(1+t)^2 • p := by module
      simpa only [heq,he] using hh
    have hant : Antitone (fun n : ℕ => c*b^n*c) := by
      intro n m hnm
      simpa only [hcsa.star_eq] using
        star_left_conjugate_le_conjugate (CStarAlgebra.pow_antitone hb1 hb0 hnm) c
    have hbound (n : ℕ) : ‖c*b^n*c‖ ≤ ‖c‖^2 := by
      calc
        ‖c*b^n*c‖ ≤ (‖c‖*‖b^n‖)*‖c‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
        _ ≤ (‖c‖*1)*‖c‖ := by gcongr; exact hnorm n
        _ = ‖c‖^2 := by ring
    exact hgl.unique (isGLB_of_antitone_predual_limit e _ hant htc _ (sq_nonneg _) hbound)
  have h1 := hconj 1 zero_le_one
  have h2 := hconj 2 (by norm_num)
  have hppos : 0 ≤ p := hp.2 (by rintro _ ⟨n,rfl⟩; exact CStarAlgebra.pow_nonneg b n hb0)
  have hpsa := IsSelfAdjoint.of_nonneg hppos
  have hbp : b*p*b=p := by
    have hid : (1+(2:ℝ) • b)*p*(1+(2:ℝ) • b) - (2:ℝ) • ((1+b)*p*(1+b)) =
        (2:ℝ) • (b*p*b) - p := by
      simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm]
      module
    have h1' : (1+b)*p*(1+b)=(4:ℝ) • p := by norm_num at h1 ⊢; exact h1
    have h2' : (1+(2:ℝ) • b)*p*(1+(2:ℝ) • b)=(9:ℝ) • p := by norm_num at h2 ⊢; exact h2
    rw [h1',h2'] at hid
    have hh : (2:ℝ) • (b*p*b-p)=0 := by
      calc
        _ = ((2:ℝ) • (b*p*b)-p)-((9:ℝ) • p-(2:ℝ) • ((4:ℝ) • p)) := by module
        _ = 0 := sub_eq_zero.mpr hid.symm
    exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_left (by norm_num))
  have hab : b*p+p*b=(2:ℝ) • p := by
    have h1' : (1+b)*p*(1+b)=(4:ℝ) • p := by norm_num at h1 ⊢; exact h1
    have he : (1+b)*p*(1+b)=p+(b*p+p*b)+b*p*b := by noncomm_ring
    rw [he,hbp] at h1'
    calc
      b*p+p*b = (p+(b*p+p*b)+p)-(2:ℝ) • p := by module
      _ = (4:ℝ) • p-(2:ℝ) • p := by rw [h1']
      _ = (2:ℝ) • p := by module
  have hz : (1-b)*p*(1-b)=0 := by
    have he : (1-b)*p*(1-b)=p-(b*p+p*b)+b*p*b := by noncomm_ring
    rw [he,hbp,hab]
    module
  let s := CFC.sqrt p
  have hs : s*s=p := CFC.sqrt_mul_sqrt_self p
  have hssa : star s=s := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq
  have hx : s*(1-b)=0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    simpa only [star_mul,hssa,star_sub,star_one,hbsa.star_eq,mul_assoc,← hs] using hz
  have hpx : p*(1-b)=0 := by rw [← hs,mul_assoc,hx,mul_zero]
  have hxp : (1-b)*p=0 := by
    simpa only [star_mul,star_sub,star_one,hbsa.star_eq,hpsa.star_eq,star_zero]
      using congrArg star hpx
  simpa only [sub_mul,one_mul,sub_eq_zero,eq_comm] using hxp

 
theorem exists_power_projection (b : M) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ p : M, IsStarProjection p ∧ PredualTendsto e (fun n : ℕ => b^n) atTop p ∧
      b*p=p ∧ ∀ x : M, b*x=x → p*x=x := by
  have hbn (n : ℕ) : ‖b^n‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (CStarAlgebra.pow_nonneg b n hb0)).mpr
      (by simpa only [pow_zero] using CStarAlgebra.pow_antitone hb1 hb0 (Nat.zero_le n))
  obtain ⟨p,_,hp,ht⟩ := exists_antitone_predual_limit e (fun n : ℕ => b^n)
    (CStarAlgebra.pow_antitone hb1 hb0) 1 zero_le_one hbn
  have hp0 : 0 ≤ p := hp.2 (by rintro _ ⟨n,rfl⟩; exact CStarAlgebra.pow_nonneg b n hb0)
  have hp1 : p ≤ 1 := by simpa only [pow_zero] using hp.1 (Set.mem_range_self 0)
  have hbp := power_limit_fixed e b p hb0 hb1 hp ht
  have hpsq : p*p ≤ p := by
    simpa only [pow_two,pow_one] using CStarAlgebra.pow_antitone hp1 hp0 (by omega : 1 ≤ 2)
  let q : M := p+(p-p*p)
  have hq0 : 0 ≤ q := add_nonneg hp0 (sub_nonneg.mpr hpsq)
  have hq1 : q ≤ 1 := by
    have hneg : 0 ≤ (1-p)*(1-p) := (IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hp1)).mul_self_nonneg
    have he : q=1-(1-p)*(1-p) := by dsimp [q]; noncomm_ring
    rw [he]
    exact sub_le_self _ hneg
  have hbq : b*q=q := by
    dsimp [q]
    rw [mul_add,mul_sub,← mul_assoc,hbp]
  have hpowq (n : ℕ) : b^n*q=q := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_assoc,ih,hbq]
  have hqle : q ≤ p := hp.2 (by
    rintro _ ⟨n,rfl⟩
    exact le_of_positive_fixed q _ hq0 hq1 (CStarAlgebra.pow_nonneg b n hb0) (hpowq n))
  have hpsq' : p ≤ p*p := sub_nonpos.mp (by
    simpa [q,add_assoc,add_comm,add_left_comm] using add_le_add_left hqle (-p))
  have hproj : IsStarProjection p := ⟨le_antisymm hpsq hpsq',(IsSelfAdjoint.of_nonneg hp0)⟩
  refine ⟨p,hproj,ht,hbp,?_⟩
  intro x hx
  let a : M := x*star x
  let r : ℝ := ‖a‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have ha0 : 0 ≤ a := mul_star_self_nonneg x
  have hca0 : 0 ≤ r⁻¹ • a := smul_nonneg (inv_nonneg.mpr hr.le) ha0
  have hcan : ‖r⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
  have hca1 : r⁻¹ • a ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hca0).mp hcan
  have hba : b*(r⁻¹ • a)=r⁻¹ • a := by dsimp [a]; rw [mul_smul_comm,← mul_assoc,hx]
  have hbna (n : ℕ) : b^n*(r⁻¹ • a)=r⁻¹ • a := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_assoc,ih,hba]
  have hcap : r⁻¹ • a ≤ p := hp.2 (by
    rintro _ ⟨n,rfl⟩
    exact le_of_positive_fixed _ _ hca0 hca1 (CStarAlgebra.pow_nonneg b n hb0) (hbna n))
  have hpa : p*a=a := by
    have hh := congrArg (fun z : M => r • z)
      (hproj.mul_right_and_mul_left_of_nonneg_of_le hca0 hcap).2
    simpa only [mul_smul_comm,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  have hzero : (1-p)*x=0 := by
    apply (CStarRing.mul_star_self_eq_zero_iff _).mp
    rw [star_mul,star_sub,star_one,hproj.isSelfAdjoint.star_eq,← mul_assoc,
      mul_assoc (1-p) x (star x)]
    change ((1-p)*a)*(1-p)=0
    rw [sub_mul,one_mul,hpa,sub_self,zero_mul]
  simpa only [sub_mul,one_mul,sub_eq_zero,eq_comm] using hzero

lemma exists_support_contraction (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ p : M, IsSupportProjection a p ∧
      PredualTendsto e (fun n : ℕ => 1-(1-a)^n) atTop p := by
  obtain ⟨q,hq,ht,hbq,hqx⟩ := exists_power_projection e (1-a)
    (sub_nonneg.mpr ha1) (sub_le_self _ ha0)
  have haq : a*q=0 := by
    have hh := hbq
    rw [sub_mul,one_mul] at hh
    exact sub_eq_self.mp hh
  have hqa : q*a=0 := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg ha0).star_eq,star_zero]
      using congrArg Star.star haq
  refine ⟨1-q,⟨hq.one_sub,?_,?_,?_⟩,?_⟩
  · simp only [sub_mul,one_mul,hqa,sub_zero]
  · simp only [mul_sub,mul_one,haq,sub_zero]
  · intro x hx
    have hbx : (1-a)*x=x := by simp only [sub_mul,one_mul,hx,sub_zero]
    simp only [sub_mul,one_mul,hqx x hbx,sub_self]
  · exact predual_tendsto_sub e (predual_tendsto_const e 1 (atTop : Filter ℕ)) ht

include e in
 

theorem exists_support_projection (a : M) (ha : 0 ≤ a) :
    ∃ p : M, IsSupportProjection a p := by
  let r : ℝ := ‖a‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hi : 0 < r⁻¹ := inv_pos.mpr hr
  have hn : ‖r⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hi]
    exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
  have hsa : 0 ≤ r⁻¹ • a := smul_nonneg hi.le ha
  obtain ⟨p,hp,_⟩ := exists_support_contraction e (r⁻¹ • a) hsa
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hsa).mp hn)
  refine ⟨p,hp.proj,?_,?_,?_⟩
  · have hh := congrArg (fun z : M => r • z) hp.left
    simpa only [mul_smul_comm,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · have hh := congrArg (fun z : M => r • z) hp.right
    simpa only [smul_mul_assoc,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · intro x hx
    apply hp.annihilate x
    simp only [smul_mul_assoc,hx,smul_zero]

include e in
 

theorem exists_dyadic_projection (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ p : M, IsStarProjection p ∧ 0 ≤ (2:ℝ) • a-p ∧ (2:ℝ) • a-p ≤ 1 := by
  let b : M := a-(1/2:ℝ) • (1:M)
  let c : M := b⁺
  let d : M := b⁻
  have hbsa : IsSelfAdjoint b := (IsSelfAdjoint.of_nonneg ha0).sub
    (IsSelfAdjoint.of_nonneg (smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) zero_le_one))
  have hb : c-d=b := CFC.posPart_sub_negPart b hbsa
  have hc0 : 0 ≤ c := CFC.posPart_nonneg b
  have hd0 : 0 ≤ d := CFC.negPart_nonneg b
  obtain ⟨p,hp⟩ := exists_support_projection e c hc0
  have hpd : p*d=0 := hp.annihilate d (CFC.posPart_mul_negPart b)
  have hdp : d*p=0 := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg hd0).star_eq,
      hp.proj.isSelfAdjoint.star_eq,star_zero] using congrArg star hpd
  have hcp : b*p=c := by rw [← hb,sub_mul,hp.right,hdp,sub_zero]
  have hpc : p*b=c := by rw [← hb,mul_sub,hp.left,hpd,sub_zero]
  have hac : Commute a p := by
    change a*p=p*a
    have hh := hcp.trans hpc.symm
    dsimp [b] at hh
    simpa only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
      sub_left_inj] using hh
  have har : 0 ≤ a*(1-p) :=
    (show Commute a (1-p) from (Commute.one_right a).sub_right hac).mul_nonneg ha0
      (sub_nonneg.mpr hp.proj.le_one)
  have hal : 0 ≤ (1-a)*p :=
    ((Commute.one_left p).sub_left hac).mul_nonneg (sub_nonneg.mpr ha1) hp.proj.nonneg
  have hpa : a*p=c+(1/2:ℝ) • p := by
    dsimp [b] at hcp
    rw [sub_mul,smul_mul_assoc,one_mul] at hcp
    exact sub_eq_iff_eq_add.mp hcp
  have hlow : 0 ≤ a-(1/2:ℝ) • p := by
    have he : a-(1/2:ℝ) • p=c+a*(1-p) := by
      rw [mul_sub,mul_one,hpa]
      module
    rw [he]
    exact add_nonneg hc0 har
  have hhigh : 0 ≤ (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p) := by
    have he : (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p)=(1-a)*p+d := by
      rw [sub_mul,one_mul,hpa]
      have haa : a=c-d+(1/2:ℝ) • (1:M) := by
        exact (sub_eq_iff_eq_add.mp hb.symm)
      conv_lhs => rw [haa]
      module
    rw [he]
    exact add_nonneg hal hd0
  refine ⟨p,hp.proj,?_,?_⟩
  · have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlow
    convert hh using 1; module
  · apply sub_nonneg.mp
    have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hhigh
    convert hh using 1; module

include e in
 

theorem dual_zero_of_projection_zero (F : StrongDual ℂ M)
    (hF : ∀ p : M, IsStarProjection p → F p=0) : F=0 := by
  have hbound : ∀ n : ℕ, ∀ a : M, 0 ≤ a → a ≤ 1 → ‖F a‖ ≤ (1/2:ℝ)^n * ‖F‖ := by
    intro n
    induction n with
    | zero =>
      intro a ha0 ha1
      simpa only [pow_zero,one_mul] using (F.le_opNorm a).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          ((CStarAlgebra.norm_le_one_iff_of_nonneg _ ha0).mpr ha1))
    | succ n ih =>
      intro a ha0 ha1
      obtain ⟨p,hp,h0,h1⟩ := exists_dyadic_projection e a ha0 ha1
      have hh := ih ((2:ℝ) • a-p) h0 h1
      have he : F ((2:ℝ) • a-p)=(2:ℝ) • F a := by
        simp only [map_sub, ← Complex.coe_smul, map_smul, hF p hp, sub_zero]
      rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      rw [pow_succ]
      nlinarith
  have hz (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : F a=0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^n * ‖F‖) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
          (by norm_num : (1/2:ℝ)<1)).mul_const ‖F‖
    exact ge_of_tendsto ht (Eventually.of_forall fun n => hbound n a ha0 ha1)
  have hpos (a : M) (ha : 0 ≤ a) : F a=0 := by
    let r : ℝ := ‖a‖+1
    have hr : 0 < r := by dsimp [r]; positivity
    have hc0 : 0 ≤ r⁻¹ • a := smul_nonneg (inv_nonneg.mpr hr.le) ha
    have hcn : ‖r⁻¹ • a‖ ≤ 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
    have hh := hz (r⁻¹ • a) hc0 ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hc0).mp hcn)
    simp only [← Complex.coe_smul, map_smul] at hh
    exact (smul_eq_zero.mp hh).resolve_left (by exact_mod_cast inv_ne_zero hr.ne')
  have hker : (⊤ : Submodule ℂ M) ≤ F.ker := by
    rw [← CStarAlgebra.span_nonneg]
    exact Submodule.span_le.mpr hpos
  ext a
  exact hker (Submodule.mem_top)

include e in
 

theorem projection_span_dense :
    (Submodule.span ℂ {p : M | IsStarProjection p}).topologicalClosure=⊤ := by
  let S := (Submodule.span ℂ {p : M | IsStarProjection p}).topologicalClosure
  let : IsClosed (S : Set M) := Submodule.isClosed_topologicalClosure _
  apply top_unique
  intro a _
  change a ∈ S
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro F
  have hzero : F.comp S.mkQL=0 := dual_zero_of_projection_zero e (F.comp S.mkQL) (by
    intro p hp
    have hm : p ∈ S := (Submodule.le_topologicalClosure _)
      (Submodule.subset_span hp)
    have hh : (Submodule.Quotient.mk (p := S) p : M ⧸ S)=0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr hm
    change F (Submodule.Quotient.mk p)=0
    rw [hh,map_zero])
  exact congrArg (fun G : StrongDual ℂ M => G a) hzero

end HochschildSakai
end

end OAI
