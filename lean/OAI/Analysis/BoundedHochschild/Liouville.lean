import Mathlib
import OAI.Analysis.BoundedHochschild.AsymptoticRigidity
import OAI.Analysis.BoundedHochschild.WalkSelection

namespace OAI

/-! Support rigidity, constant martingale limits and harmonic multiplier identities. -/

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
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildLiouville
open HochschildRigidity HochschildWalk HochschildFirstLetter TracialUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))

 
def hilbertMap : A →L[ℂ] τ.GNS :=
  UniformSpace.Completion.toComplL.comp (TracialUltrapower.traceHilbertMap τ h1)

@[simp] lemma hilbertMap_norm (a : A) : ‖hilbertMap τ h1 a‖ = ‖τ.toPreGNS a‖ :=
  UniformSpace.Completion.norm_coe _

include htr in
lemma trace_norm_unitary_right (a : A) (u : unitary A) :
    ‖τ.toPreGNS (a*(u:A))‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_mul]
  calc
    τ ((star (u:A)*star a)*(a*(u:A))) = τ (star (u:A)*((star a*a)*(u:A))) := by
      simp only [mul_assoc]
    _ = τ (((star a*a)*(u:A))*star (u:A)) := htr _ _
    _ = τ (star a*a) := by rw [mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]

variable {G : Type*} [Group G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)

 
def algebraD (g : G) : A := R (ρ g : A) * (ρ g⁻¹ : A)
def hilbertD (g : G) : τ.GNS := hilbertMap τ h1 (algebraD ρ R g)

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraD_mul (g : G) : algebraD ρ R g * (ρ g : A) = R (ρ g : A) := by
  simp [algebraD, mul_assoc, ← Submonoid.coe_mul]

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraD_norm (g : G) : ‖algebraD ρ R g‖ ≤ ‖R‖ * ‖(1:A)‖ := by
  rw [algebraD, CStarRing.norm_mul_coe_unitary]
  have hu := CStarRing.norm_coe_unitary_mul (ρ g) (1:A)
  simp only [mul_one] at hu
  exact (R.le_opNorm _).trans_eq (by rw [hu])

lemma hilbertD_norm (g : G) : ‖hilbertD τ h1 ρ R g‖ ≤ ‖R‖ * ‖(1:A)‖ :=
  (hilbertMap_norm τ h1 _).le.trans ((preGNS_norm_le τ h1 _).trans (algebraD_norm ρ R g))

include htr in
lemma multiplied_error (g : G) (a : A) :
    ‖τ.toPreGNS (R (ρ g : A)-a*(ρ g : A))‖ =
      ‖hilbertD τ h1 ρ R g - hilbertMap τ h1 a‖ := by
  rw [hilbertD, ← map_sub, hilbertMap_norm]
  rw [← trace_norm_unitary_right τ htr (algebraD ρ R g-a) (ρ g)]
  rw [sub_mul, algebraD_mul]

 
def endpointSequence (g : ℕ → G) : ℕ →ᵇ A :=
  BoundedContinuousFunction.mkOfBound ⟨fun n => algebraD ρ R (g n), continuous_of_discreteTopology⟩
    (2*(‖R‖*‖(1:A)‖)) (fun i j => by
      rw [dist_eq_norm]
      change ‖algebraD ρ R (g i)-algebraD ρ R (g j)‖ ≤ _
      exact (norm_sub_le _ _).trans (by linarith [algebraD_norm ρ R (g i), algebraD_norm ρ R (g j)]))

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma endpointSequence_apply (g : ℕ → G) (n : ℕ) :
    endpointSequence ρ R g n = algebraD ρ R (g n) := rfl

omit [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
lemma evalList_eq_lift {I : Type*} [DecidableEq I] (u : I → G) (g : FreeGroup I) :
    evalList u g.toWord = FreeGroup.lift u g := by
  conv_rhs => rw [← FreeGroup.mk_toWord (x := g), FreeGroup.lift_mk]
  apply congrArg List.prod
  apply List.map_congr_left
  intro p _
  cases p.2 <;> rfl

omit [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
lemma lift_comp_hom {J K : Type*} [Group K] (f : G →* K) (u : J → G) (g : FreeGroup J) :
    (FreeGroup.lift (fun i => f (u i))) g = f (FreeGroup.lift u g) := by
  have he : FreeGroup.lift (fun i => f (u i)) = f.comp (FreeGroup.lift u) := by
    ext i
    simp
  exact DFunLike.congr_fun he g

variable [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]

include htr

 

theorem support_rigidity (hR : BallSequential τ.toPreGNS R)
    (hsym : μ.map (fun g => g⁻¹) = μ)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ (fun g => ‖τ (ρ g : A)‖) time)
    (z : Lp τ.GNS 2 (pathMeasure μ))
    (hz : Tendsto (fun k => ∫ ω, ‖z ω-hilbertD τ h1 ρ R (walk k ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0))
    (hc : ∀ k n, k ≤ n →
      ∫ ω, ‖hilbertD τ h1 ρ R (walk n ω)-hilbertD τ h1 ρ R (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-hilbertD τ h1 ρ R (walk k ω)‖^2 ∂pathMeasure μ)
    (a b : τ.GNS) (ha : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-a‖ < r})
    (hb : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-b‖ < r}) : a = b := by
  obtain ⟨u,hu,hfree,hblock⟩ := infinite_walk_selection μ hsym (hilbertD τ h1 ρ R)
    (‖R‖*‖(1:A)‖) (hilbertD_norm τ h1 ρ R) z hz hc a b ha hb
    (fun g => ‖τ (ρ g : A)‖) (fun _ => norm_nonneg _) time htime hmom
  let U (n : ℕ) : FreeGroup ℕ →* unitary A := FreeGroup.lift (fun i => ρ (u n i))
  let a' := endpointSequence ρ R (fun n => u n 0)
  let b' := endpointSequence ρ R (fun n => (u n 0)⁻¹)
  have ha' : Tendsto (fun n => hilbertMap τ h1 (a' n)) atTop (nhds a) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hu n 0).1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hb' : Tendsto (fun n => hilbertMap τ h1 (b' n)) atTop (nhds b) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hu n 0).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hw (g : FreeGroup ℕ) (i : ℕ) (t : Bool) (l : List (ℕ × Bool))
      (hg : g.toWord = (i,t)::l) (hn : (g.toWord.map Prod.fst).Nodup) :
      Tendsto (fun n => ‖τ.toPreGNS (R (U n g : A) - (if t then a' n else b' n)*(U n g : A))‖)
        atTop (nhds 0) := by
    have he := hblock ((i,t),l) (by simpa only [hg] using hn)
    have hnear : Tendsto (fun n =>
        ‖hilbertD τ h1 ρ R (signed t (u n i)) -
          hilbertMap τ h1 (if t then a' n else b' n)‖) atTop (nhds 0) := by
      cases t with
      | false =>
        have hi : Tendsto (fun n => hilbertD τ h1 ρ R ((u n i)⁻¹)) atTop (nhds b) := by
          rw [tendsto_iff_norm_sub_tendsto_zero]
          exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hu n i).2.le)
            tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [signed, Bool.false_eq_true, ↓reduceIte, sub_self, norm_zero] using (hi.sub hb').norm
      | true =>
        have hi : Tendsto (fun n => hilbertD τ h1 ρ R (u n i)) atTop (nhds a) := by
          rw [tendsto_iff_norm_sub_tendsto_zero]
          exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hu n i).1.le)
            tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [signed, ↓reduceIte, sub_self, norm_zero] using (hi.sub ha').norm
    have hzero := he.add hnear
    simp only [zero_add] at hzero
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hzero
    change ‖τ.toPreGNS (R (FreeGroup.lift (fun i => ρ (u n i)) g : A) - _ * _)‖ ≤ _
    rw [lift_comp_hom, multiplied_error τ h1 htr]
    have hword : evalList (u n) ((i,t)::l) = FreeGroup.lift (u n) g := by
      rw [← hg, evalList_eq_lift]
    rw [hword]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hab := asymptotic_first_letter_endpoints τ h1 htr R hR U
    (fun g hg => by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [U, lift_comp_hom] using hfree g hg) a' b' hw
  have hh : Tendsto (fun n => ‖τ.toPreGNS (a' n-b' n)‖) atTop (nhds ‖a-b‖) := by
    simpa only [← map_sub, hilbertMap_norm] using (ha'.sub hb').norm
  exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hh hab))

end HochschildLiouville

 

open MeasureTheory Filter Topology TopologicalSpace
namespace HochschildProbability

 
theorem ae_constant_of_support_unique {Ω H : Type*} [MeasurableSpace Ω] [Nonempty Ω]
    [NormedAddCommGroup H] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → H) (hf : AEStronglyMeasurable f μ)
    (huniq : ∀ a b : H,
      (∀ r > 0, 0 < μ.real {ω | ‖f ω-a‖ < r}) →
      (∀ r > 0, 0 < μ.real {ω | ‖f ω-b‖ < r}) → a = b) :
    ∃ a : H, ∀ᵐ ω ∂μ, f ω = a := by
  classical
  by_contra hn
  have hn' (b : H) : ¬ ∀ᵐ ω ∂μ, f ω = b := fun h => hn ⟨b,h⟩
  let f' := hf.mk f
  let S := Set.range f'
  have : SeparableSpace S := hf.stronglyMeasurable_mk.isSeparable_range.separableSpace
  have : Nonempty S := ⟨⟨f' (Classical.arbitrary Ω), ⟨_,rfl⟩⟩⟩
  let g : Ω → S := fun ω => ⟨f' ω, ⟨ω,rfl⟩⟩
  have hg : ∀ b : S, ∃ᵐ ω ∂μ, g ω ≠ b := by
    intro b
    apply Filter.not_eventually.mp
    intro hb
    apply hn' b.val
    filter_upwards [hf.ae_eq_mk, hb] with ω he hb
    exact he.trans (congrArg Subtype.val hb)
  obtain ⟨a,b,hab,ha,hb⟩ := exists_ne_forall_mem_nhds_pos_measure_preimage hg
  have hs (x : S) (hx : ∀ s ∈ 𝓝 x, 0 < μ (g ⁻¹' s)) :
      ∀ r > 0, 0 < μ.real {ω | ‖f ω-x.val‖ < r} := by
    intro r hr
    have hp := hx (Metric.ball x r) (Metric.ball_mem_nhds x hr)
    have he : μ {ω | ‖f ω-x.val‖ < r} = μ (g ⁻¹' Metric.ball x r) := by
      apply measure_congr
      filter_upwards [hf.ae_eq_mk] with ω hω
      change (‖f ω-x.val‖ < r) = (dist (g ω) x < r)
      rw [Subtype.dist_eq, dist_eq_norm]
      change (‖f ω-x.val‖ < r) = (‖f' ω-x.val‖ < r)
      rw [hω]
    rw [Measure.real, he]
    exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  exact hab (Subtype.ext (huniq a.val b.val (hs a ha) (hs b hb)))

end HochschildProbability

 

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma processLp_const_inner (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g) (n : ℕ) (c : H) :
    inner ℝ (processLp μ D C hD n-processLp μ D C hD 0)
      (Lp.const 2 (pathMeasure μ) c) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : inner ℝ (processLp μ D C hD (n+1)-processLp μ D C hD n)
        (Lp.const 2 (pathMeasure μ) c) = 0 := by
      rw [L2.inner_def]
      have he := increment_inner_integral μ D C hD hh n (fun _ => c) ‖c‖ (fun _ => le_rfl)
      refine Eq.trans (integral_congr_ae ?_) he
      filter_upwards [Lp.coeFn_sub (processLp μ D C hD (n+1)) (processLp μ D C hD n),
        processLp_ae μ D C hD (n+1), processLp_ae μ D C hD n,
        Lp.coeFn_const 2 (pathMeasure μ) c] with ω hs hn hn' hc
      rw [hs,Pi.sub_apply,hn,hn',hc]
      rfl
    have he : processLp μ D C hD (n+1)-processLp μ D C hD 0 =
        (processLp μ D C hD (n+1)-processLp μ D C hD n) +
          (processLp μ D C hD n-processLp μ D C hD 0) := by abel
    rw [he,inner_add_left,hstep,ih,add_zero]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma processLp_zero (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) :
    processLp μ D C hD 0 = Lp.const 2 (pathMeasure μ) (D 1) := by
  apply Lp.ext
  filter_upwards [processLp_ae μ D C hD 0, Lp.coeFn_const 2 (pathMeasure μ) (D 1)] with ω he hc
  simp only [he,hc,walk,word,List.ofFn_zero,List.prod_nil,Function.const_apply]

 

theorem atoms_eq_of_constant_limit (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g)
    (z : Lp H 2 (pathMeasure μ)) (hz : Tendsto (fun n => processLp μ D C hD n) atTop (nhds z))
    (c : H) (hc : ∀ᵐ ω ∂pathMeasure μ, z ω = c) :
    ∀ g, μ {g} ≠ 0 → D g = D 1 := by
  let Z := processLp μ D C hD
  have hzconst : z = Lp.const 2 (pathMeasure μ) c := by
    apply Lp.ext
    filter_upwards [hc, Lp.coeFn_const 2 (pathMeasure μ) c] with ω hω hconst
    exact hω.trans hconst.symm
  have hdiff : Lp.const 2 (pathMeasure μ) (c-D 1) = z-Z 0 := by
    rw [map_sub,hzconst,show Z 0 = _ from processLp_zero μ D C hD]
  have hlim := ((hz.sub_const (Z 0)).inner tendsto_const_nhds :
    Tendsto (fun n => inner ℝ (Z n-Z 0) (Lp.const 2 (pathMeasure μ) (c-D 1)))
      atTop (nhds (inner ℝ (z-Z 0) (Lp.const 2 (pathMeasure μ) (c-D 1)))))
  have hzero : inner ℝ (z-Z 0) (Lp.const 2 (pathMeasure μ) (c-D 1)) = 0 :=
    tendsto_nhds_unique hlim (by simpa only [Z,processLp_const_inner μ D C hD hh] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0)))
  rw [hdiff,real_inner_self_eq_norm_sq] at hzero
  have heq : z = Z 0 := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  obtain ⟨z',hz',_,hbound⟩ := HochschildMartingale.uniform_cauchy_error Z
    (fun _ _ h => processLp_orthogonal μ D C hD hh h) C (processLp_norm_le μ D C hD)
  have heq' : z' = Z 0 := (tendsto_nhds_unique hz' hz).trans heq
  have hZ1 : Z 1 = Z 0 := by
    have hb := hbound 0 1 (by omega)
    rw [heq',sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hb (sq_nonneg _))))
  have hpath : ∀ᵐ ω ∂pathMeasure μ, D (ω 0) = D 1 := by
    have hae := Lp.ext_iff.mp hZ1
    filter_upwards [hae,processLp_ae μ D C hD 1,processLp_ae μ D C hD 0] with ω he h1 h0
    change processLp μ D C hD 1 ω = processLp μ D C hD 0 ω at he
    rw [h1,h0] at he
    simpa [walk,word,takePath,List.ofFn_succ] using he
  have hg : ∀ᵐ g ∂μ, D g = D 1 := by
    have hm : (pathMeasure μ).map (Function.eval 0) = μ :=
      Measure.infinitePi_map_eval (fun _ : ℕ => μ) 0
    rw [← hm]
    exact (ae_map_iff (measurable_pi_apply 0).aemeasurable (Set.to_countable _).measurableSet).mpr hpath
  exact ae_iff_of_countable.mp hg

end HochschildWalk

 

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildLiouville
open HochschildRigidity HochschildWalk HochschildFirstLetter TracialUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable (hf : ∀ x : A, τ (star x * x) = 0 → x = 0)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)
variable (μ : Measure G) [IsProbabilityMeasure μ]

include htr hf

 
theorem atoms_multiplier (hR : BallSequential τ.toPreGNS R)
    (hsym : μ.map (fun g => g⁻¹) = μ)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ (fun g => ‖τ (ρ g : A)‖) time)
    (hh : ∀ g, ∫ u, hilbertD τ h1 ρ R (g*u) ∂μ = hilbertD τ h1 ρ R g) :
    ∀ g, μ {g} ≠ 0 → R (ρ g : A) = R 1 * (ρ g : A) := by
  let : InnerProductSpace ℝ τ.GNS := InnerProductSpace.rclikeToReal ℂ τ.GNS
  obtain ⟨z,hz,he,hc⟩ := harmonic_mean_square_convergence μ (hilbertD τ h1 ρ R)
    (‖R‖*‖(1:A)‖) (hilbertD_norm τ h1 ρ R) hh
  obtain ⟨a,ha⟩ := HochschildProbability.ae_constant_of_support_unique (pathMeasure μ) z
    (Lp.aestronglyMeasurable z) (support_rigidity τ h1 htr ρ R μ hR hsym time htime hmom z he hc)
  have hatom := atoms_eq_of_constant_limit μ (hilbertD τ h1 ρ R)
    (‖R‖*‖(1:A)‖) (hilbertD_norm τ h1 ρ R) hh z hz a ha
  intro g hg
  have he := hatom g hg
  have hn : ‖τ.toPreGNS (algebraD ρ R g-algebraD ρ R 1)‖ = 0 := by
    rw [← hilbertMap_norm τ h1, map_sub]
    change ‖hilbertD τ h1 ρ R g-hilbertD τ h1 ρ R 1‖ = 0
    rw [he, sub_self, norm_zero]
  have heq := sub_eq_zero.mp ((preGNS_norm_eq_zero_iff τ hf _).mp hn)
  have heq' := congrArg (fun x : A => x*(ρ g : A)) heq
  rw [algebraD_mul] at heq'
  simpa [algebraD] using heq'

 

theorem multiplier_of_walk (hR : BallSequential τ.toPreGNS R)
    (hsym : μ.map (fun g => g⁻¹) = μ)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ (fun g => ‖τ (ρ g : A)‖) time)
    (hh : ∀ g, ∫ u, hilbertD τ h1 ρ R (g*u) ∂μ = hilbertD τ h1 ρ R g)
    (hdense : ∀ u : unitary A, ∃ g : ℕ → G, (∀ n, μ {g n} ≠ 0) ∧
      Tendsto (fun n => ‖τ.toPreGNS ((ρ (g n) : A)-(u:A))‖) atTop (𝓝 0)) :
    ∀ x : A, R x = R 1*x := by
  have hatom := atoms_multiplier τ h1 htr hf ρ R μ hR hsym time htime hmom hh
  have hu (u : unitary A) : R (u:A) = R 1*(u:A) := by
    obtain ⟨g,hg,hlim⟩ := hdense u
    have hbound : ∀ n, ‖(ρ (g n) : A)-(u:A)‖ ≤ 2*‖(1:A)‖ := by
      intro n
      have ha := CStarRing.norm_coe_unitary_mul (ρ (g n)) (1:A)
      have hb := CStarRing.norm_coe_unitary_mul u (1:A)
      simp only [mul_one] at ha hb
      exact (norm_sub_le _ _).trans (by rw [ha,hb]; ring_nf; rfl)
    have hRl := hR (fun n => (ρ (g n):A)-(u:A)) ⟨_,hbound⟩ hlim
    have hmul : Tendsto (fun n => ‖τ.toPreGNS (R 1*((ρ (g n):A)-(u:A)))‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun _ => preGNS_norm_mul_le τ _ _)
        (by simpa using hlim.const_mul ‖R 1‖)
    have hzero : Tendsto (fun _ : ℕ => ‖τ.toPreGNS (R (u:A)-R 1*(u:A))‖) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hRl.add hmul)
      have he : R (u:A)-R 1*(u:A) =
          -(R ((ρ (g n):A)-(u:A))) + R 1*((ρ (g n):A)-(u:A)) := by
        rw [map_sub,mul_sub,hatom _ (hg n)]
        abel
      rw [he,map_add,map_neg]
      exact (norm_add_le _ _).trans_eq (by simp only [norm_neg, map_sub])
    have hz := tendsto_nhds_unique tendsto_const_nhds hzero
    exact sub_eq_zero.mp ((preGNS_norm_eq_zero_iff τ hf _).mp hz)
  intro x
  obtain ⟨u,c,hx,_⟩ := CStarAlgebra.exists_sum_four_unitary x
  rw [hx,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hu, mul_smul_comm]

end HochschildLiouville

 

open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace HochschildLiouville
open HochschildWalk HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)
variable (μ : Measure G) [IsProbabilityMeasure μ]

 

theorem hilbertD_harmonic
    (hh : ∀ x : A, ∫ u, R (x*(ρ u:A)) * (ρ u⁻¹:A) ∂μ = R x) :
    ∀ g, ∫ u, hilbertD τ h1 ρ R (g*u) ∂μ = hilbertD τ h1 ρ R g := by
  intro g
  let L : A →L[ℂ] τ.GNS := (hilbertMap τ h1).comp
    ((ContinuousLinearMap.mul ℂ A).flip (ρ g⁻¹:A))
  have hb (u : G) : ‖R ((ρ g:A)*(ρ u:A)) * (ρ u⁻¹:A)‖ ≤ ‖R‖*‖(1:A)‖ := by
    rw [CStarRing.norm_mul_coe_unitary]
    have he : ‖(ρ g:A)*(ρ u:A)‖ = ‖(1:A)‖ := by
      rw [CStarRing.norm_coe_unitary_mul]
      have h := CStarRing.norm_coe_unitary_mul (ρ u) (1:A)
      simpa only [mul_one] using h
    exact (R.le_opNorm _).trans_eq (by rw [he])
  have hi : Integrable (fun u => R ((ρ g:A)*(ρ u:A))*(ρ u⁻¹:A)) μ :=
    integrable_of_countable_bound μ _ (‖R‖*‖(1:A)‖) hb
  have he (u : G) : hilbertD τ h1 ρ R (g*u) = L (R ((ρ g:A)*(ρ u:A))*(ρ u⁻¹:A)) := by
    simp only [hilbertD,algebraD,map_mul,Submonoid.coe_mul,mul_inv_rev]
    simp only [mul_assoc,L,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply']
  simp_rw [he]
  rw [L.integral_comp_comm hi,hh]
  rfl

end HochschildLiouville
end

end OAI
