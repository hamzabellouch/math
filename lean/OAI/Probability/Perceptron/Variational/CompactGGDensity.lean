import Mathlib
import OAI.Probability.Perceptron.Interpolation.PerturbationContact

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

def boundedTestIntegral (μ : Measure X) [IsProbabilityMeasure μ] : (X →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (f.integrable μ) (g.integrable μ)
      map_smul' := fun c f => by simpa using integral_const_mul c (fun x => f x) }
    1 (fun f => by simpa using f.norm_integral_le_norm μ)

def compactGGTestCLM {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K)) (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) : (K →ᵇ ℝ) →L[ℝ] ℝ := by
  classical
  let I := boundedTestIntegral (μ : Measure (CompactArray K))
  let F := f.compContinuous ⟨compactBlock n,compactBlock_continuous n⟩
  let E (a b : ℕ) := BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    (⟨fun Q : CompactArray K => Q a b,by fun_prop⟩ : C(CompactArray K,K))
  let L (a b : ℕ) := I.comp ((ContinuousLinearMap.mul ℝ (CompactArray K →ᵇ ℝ) F).comp (E a b))
  exact (n:ℝ) • L i n - (I F) • (I.comp (E 0 1)) - ∑ j ∈ Finset.univ.erase i, L i j

lemma compactGGTestCLM_apply {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K)) (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ) :
    compactGGTestCLM μ n i f g = compactGGDefect μ n i f g := by
  classical
  simp [compactGGTestCLM,compactGGDefect,boundedTestIntegral]

lemma compactJoint_monomials_total (L : (CompactJointOverlap →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ p d, L (compactJointMonomial p d)=0) : L=0 := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact CompactJointOverlap ℝ ℝ
  let L' := L.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  let m (a : ℕ×ℕ) : C(CompactJointOverlap,ℝ) := (compactJointMonomial a.1 a.2).toContinuousMap
  have hm0 : m 0=1 := by ext x; simp [m]
  have hmadd (a b : ℕ×ℕ) : m (a+b)=m a*m b := by
    ext x
    exact congrArg (fun f : CompactJointOverlap →ᵇ ℝ => f x) (compactJointMonomial_add _ _ _ _)
  let M : Submonoid C(CompactJointOverlap,ℝ) :=
    { carrier := Set.range m
      one_mem' := ⟨0,hm0⟩
      mul_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,hmadd a b⟩ }
  let A := Algebra.adjoin ℝ (M : Set C(CompactJointOverlap,ℝ))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨p,d,hpd⟩ := compactJointMonomial_separates x y hxy
    have hmem : m (p,d) ∈ A :=
      Algebra.subset_adjoin (show m (p,d) ∈ M from ⟨(p,d),rfl⟩)
    exact ⟨m (p,d),⟨m (p,d),hmem,rfl⟩,hpd⟩
  have hA : (A : Set C(CompactJointOverlap,ℝ)) ⊆ (L'.ker : Set C(CompactJointOverlap,ℝ)) := by
    have hspan : Submodule.span ℝ (M : Set C(CompactJointOverlap,ℝ)) ≤ L'.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨p,d⟩,rfl⟩
      change L (e ((compactJointMonomial p d).toContinuousMap)) = 0
      have he : e ((compactJointMonomial p d).toContinuousMap) = compactJointMonomial p d := by
        ext x; rfl
      rw [he]
      exact hL p d
    intro f hf
    apply hspan
    change f ∈ A.toSubmodule at hf
    simpa only [A,Algebra.adjoin_eq_span,Submonoid.closure_eq] using hf
  have hclosed := L'.isClosed_ker
  have hc := closure_minimal hA hclosed
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hall (f : C(CompactJointOverlap,ℝ)) : L' f=0 := by
    apply hc
    change f ∈ A.topologicalClosure
    rw [htop]
    trivial
  ext g
  have h := hall (e.symm g)
  simpa [L'] using h

lemma compactGG_of_joint_monomials (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
    (h : ∀ p d, compactGGDefect μ n i f (compactJointMonomial p d)=0)
    (g : CompactJointOverlap →ᵇ ℝ) : compactGGDefect μ n i f g=0 := by
  have hz := compactJoint_monomials_total (compactGGTestCLM μ n i f)
    (fun p d => (compactGGTestCLM_apply μ n i f _).trans (h p d))
  rw [← compactGGTestCLM_apply,hz]
  rfl

end

lemma compactGGDefect_one (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
    compactGGDefect μ r i G 1=0 := by
  have hr : 1≤r := by have := i.isLt; omega
  simp only [compactGGDefect,BoundedContinuousFunction.coe_one,Pi.one_apply,mul_one,
    integral_const,probReal_univ,smul_eq_mul,Finset.sum_const,Finset.card_erase_of_mem
    (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_sub hr,Nat.cast_one]
  ring

variable (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ) (z : Fin k→ℝ)
variable (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
variable (t : ℕ→ℝ≥0) (h : ℕ→Fin (k+1)→ℝ)
variable (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
variable (u : (n : ℕ)→Fin (n+1)→ℝ) (hu : ∀ n, u n∈Icc (fun _=>1) (fun _=>2))
variable (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
  sourceExpectedPressure n k f (fun j=>p j.val) (fun j=>d j.val) (h n) z (t n) v)
  (Icc (fun _ : Fin (n+1)=>1) (fun _=>2)) (u n))
variable {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)

include hz hz0 hz1 hh0 hh hu hmin hH hhH ht in
lemma source_contact_monomial_tendsto (j r : ℕ) (i : Fin r)
    (G : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
    Tendsto (fun n => compactGGDefect (sourceGibbsArrayLaw n k f (fun a=>p a.val)
      (fun a=>d a.val) (h n) (u n) z (t n)) r i G (compactJointMonomial (p j) (d j))) atTop (𝓝 0) := by
  let c : ℝ := (2:ℝ)^(-((j+1:ℕ):ℤ))
  have hc : 0<c := by dsimp [c]; positivity
  have hN : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have he : Tendsto (fun n : ℕ => perturbationScale (n+1)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/16)).comp hN using 1
    simp only [perturbationScale,neg_div]; rfl
  have he' : Tendsto (fun n : ℕ => 8*perturbationScale (n+1)^2) atTop (𝓝 0) := by
    simpa using (he.pow 2).const_mul 8
  have hs : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)^(-(1:ℝ)/4)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp hN using 1
    simp only [neg_div,Function.comp_def]
  apply squeeze_zero_norm' (a := fun n => ‖G‖/c^2*(Real.sqrt (2*c)*((n+1:ℕ):ℝ)^(-(3:ℝ)/8)+
    (c+4*Real.sqrt (enrichedVarianceConstant k z f H T))*((n+1:ℕ):ℝ)^(-(1:ℝ)/8)))
  · filter_upwards [eventually_ge_atTop j,he'.eventually (gt_mem_nhds (by positivity : (0:ℝ)<c/16)),
      hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))] with n hn he hs
    have hj : j<n+1 := by omega
    simpa only [Real.norm_eq_abs,sourcePenaltyWeight,c] using
      source_contact_compact_gg_rate n k f (fun a=>p a.val) (fun a=>d a.val) (h n)
        (hh0 n) (hh n) z hz hz0 hz1 (t n) (hu n) (hmin n) ⟨j,hj⟩ hH (hhH n) (ht n)
        he hs.le r i G
  · exact (contact_gg_rate_tendsto c (enrichedVarianceConstant k z f H T) ‖G‖ c).comp hN

include hz hz0 hz1 hh0 hh hu hmin hH hhH ht in
lemma source_contact_limit_joint_gg
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n=>sourceGibbsArrayLaw (s n) k f (fun a=>p a.val) (fun a=>d a.val)
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν))
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (g : CompactJointOverlap →ᵇ ℝ) : compactGGDefect ν r i G g=0 := by
  apply compactGG_of_joint_monomials ν r i G
  intro a b
  by_cases hab : a+b=0
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    subst a b
    simpa only [compactJointMonomial_zero] using compactGGDefect_one ν r i G
  obtain ⟨j,hp,hd⟩ := hcover a b (by omega)
  apply compactGGDefect_limit hlim
  simpa only [hp,hd,Function.comp_def] using
    (source_contact_monomial_tendsto k f p d z hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht j r i G).comp hs.tendsto_atTop

end SphericalPerceptronFreeEnergy

end

end OAI
