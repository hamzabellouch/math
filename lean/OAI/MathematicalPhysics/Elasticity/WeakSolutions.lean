import OAI.MathematicalPhysics.Elasticity.Restriction
import OAI.MathematicalPhysics.Elasticity.LocalRegularity

namespace OAI

section
noncomputable section
open MeasureTheory SchwartzMap Set TemperedDistribution
open scoped SchwartzMap LineDeriv
namespace Elasticity
variable {Ω : Set X}
abbrev realTest (g : SchwartzMap X ℝ) : SchwartzMap X ℂ := g.postcompCLM Complex.ofRealCLM
abbrev reTest (g : SchwartzMap X ℂ) : SchwartzMap X ℝ := g.postcompCLM Complex.reCLM
abbrev imTest (g : SchwartzMap X ℂ) : SchwartzMap X ℝ := g.postcompCLM Complex.imCLM
lemma realTest_d (g : SchwartzMap X ℝ) (j : Fin 3) :
    ∂_{coordVector j} (realTest g)=realTest (ElasticityKorn.d (coordVector j) g) := by
  ext x
  change fderiv ℝ ((Complex.ofRealCLM : ℝ → ℂ) ∘ (g : X → ℝ)) x (coordVector j)=
    Complex.ofRealCLM (fderiv ℝ (g : X → ℝ) x (coordVector j))
  rw [((Complex.ofRealCLM.hasFDerivAt (x := g x)).comp x
    (g.differentiableAt (x := x)).hasFDerivAt).fderiv]
  rfl
lemma test_parts (g : SchwartzMap X ℂ) : g=realTest (reTest g)+Complex.I • realTest (imTest g) := by
  ext x
  change g x=↑((g x).re)+Complex.I*↑((g x).im)
  exact (Complex.re_add_im (g x)).symm.trans (by ring)
def scalarDistribution (Ω : Set X) : ScalarL2 Ω →L[ℝ] ElasticityDistribution.Dist :=
  ((Lp.toTemperedDistributionCLM ℂ (volume.restrict Ω) 2).restrictScalars ℝ).comp
    (Complex.ofRealCLM.compLpL 2 (volume.restrict Ω))
lemma scalarDistribution_real (f : ScalarL2 Ω) (g : SchwartzMap X ℝ) :
    scalarDistribution Ω f (realTest g)=↑(inner ℝ f (schwartzR Ω g)) := by
  have hi : Integrable (fun x => g x*f x) (volume.restrict Ω) := by
    apply (L2.integrable_inner (𝕜 := ℝ) f (schwartzR Ω g)).congr
    filter_upwards [g.coeFn_toLp 2 (volume.restrict Ω)] with x hx
    change inner ℝ (f x) (g.toLp 2 (volume.restrict Ω) x)=_
    rw [hx]
    rfl
  have hpair : inner ℝ f (schwartzR Ω g)=∫ x, g x*f x ∂(volume.restrict Ω) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [g.coeFn_toLp 2 (volume.restrict Ω)] with x hx
    change inner ℝ (f x) (g.toLp 2 (volume.restrict Ω) x)=_
    rw [hx]
    rfl
  change Lp.toTemperedDistribution (Complex.ofRealCLM.compLpL 2 (volume.restrict Ω) f) (realTest g)=_
  rw [Lp.toTemperedDistribution_apply,hpair]
  calc
    _ = ∫ x, Complex.ofRealCLM (g x*f x) ∂(volume.restrict Ω) := by
      apply integral_congr_ae
      filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM f] with x hx
      rw [hx]
      change (g x : ℂ)*(f x : ℂ)=↑(g x*f x)
      exact (Complex.ofReal_mul _ _).symm
    _ = _ := Complex.ofRealCLM.integral_comp_comm hi
lemma localEq_of_realTest {U V : ElasticityDistribution.Dist}
    (h : ∀ (g : SchwartzMap X ℝ), HasCompactSupport (g : X → ℝ) → tsupport (g : X → ℝ)⊆Ω →
      U (realTest g)=V (realTest g)) : ElasticityDistribution.LocalEq Ω U V := by
  intro φ hc hs
  have hrc : HasCompactSupport (reTest φ : X → ℝ) := hc.comp_left (g := Complex.re) rfl
  have hic : HasCompactSupport (imTest φ : X → ℝ) := hc.comp_left (g := Complex.im) rfl
  have hrs : tsupport (reTest φ : X → ℝ)⊆Ω := (tsupport_comp_subset (g := Complex.re) rfl (φ : X → ℂ)).trans hs
  have his : tsupport (imTest φ : X → ℝ)⊆Ω := (tsupport_comp_subset (g := Complex.im) rfl (φ : X → ℂ)).trans hs
  conv_lhs => rw [test_parts φ]
  conv_rhs => rw [test_parts φ]
  rw [map_add,map_add,map_smul,map_smul,h (reTest φ) hrc hrs,h (imTest φ) hic his]
def h1Distribution (u : H1 Ω) (i : Fin 3) : ElasticityDistribution.Dist :=
  scalarDistribution Ω (ambientScalar Ω none i u.val)
def h1GradientDistribution (u : H1 Ω) (i j : Fin 3) : ElasticityDistribution.Dist :=
  scalarDistribution Ω (ambientScalar Ω (some j) i u.val)
/-- Actual distributional identification of every H1 gradient. -/
theorem h1_distribution_derivative (u : H1 Ω) (i j : Fin 3) :
    ElasticityDistribution.LocalEq Ω (ElasticityDistribution.dd j (h1Distribution u i))
      (h1GradientDistribution u i j) := by
  apply localEq_of_realTest
  intro g hc hs
  change (∂_{coordVector j} (h1Distribution u i)) (realTest g)=_
  rw [lineDerivOp_apply_apply,realTest_d,map_neg]
  change -scalarDistribution Ω (ambientScalar Ω none i u.val) (realTest (ElasticityKorn.d (coordVector j) g))=
    scalarDistribution Ω (ambientScalar Ω (some j) i u.val) (realTest g)
  rw [scalarDistribution_real,scalarDistribution_real,h1_weak_derivative u g hc hs i j,
    Complex.ofReal_neg,neg_neg]
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}
def stressFun (lam mu : X → ℝ) (u : Ambient Ω) (i j : Fin 3) (x : X) : ℝ :=
  (if i=j then lam x*(∑ k, u.2 k x k) else 0)+mu x*(u.2 j x i+u.2 i x j)
lemma stress_memLp (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) : MemLp (stressFun lam mu u i j) 2 (volume.restrict Ω) := by
  have hd : MemLp (fun x => ∑ k, u.2 k x k) 2 (volume.restrict Ω) :=
    memLp_finsetSum _ (fun k _ => entry_memLp u k k)
  have hs := hm.mul_memLp_fun ((entry_memLp u i j).add (entry_memLp u j i))
  change MemLp (fun x => (if i=j then lam x*(∑ k, u.2 k x k) else 0)+mu x*(u.2 j x i+u.2 i x j)) 2 (volume.restrict Ω)
  by_cases he : i=j
  · subst j
    simp only [ite_true]
    exact (hl.mul_memLp_fun hd).add hs
  · simp only [he,ite_false,zero_add]
    exact hs
 def stressL2 (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) : ScalarL2 Ω := (stress_memLp hl hm u i j).toLp _
lemma stressL2_ae (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) : stressL2 hl hm u i j =ᵐ[volume.restrict Ω] stressFun lam mu u i j :=
  (stress_memLp hl hm u i j).coeFn_toLp
lemma stress_pair (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) (g : SchwartzMap X ℝ) :
    inner ℝ (stressL2 hl hm u i j) (schwartzR Ω g)=
      ∫ x, stressFun lam mu u i j x*g x ∂(volume.restrict Ω) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [stressL2_ae hl hm u i j,g.coeFn_toLp 2 (volume.restrict Ω)] with x hx hy
  change inner ℝ (stressL2 hl hm u i j x) (g.toLp 2 (volume.restrict Ω) x)=_
  rw [hx,hy,real_inner_comm]
  rfl
lemma stress_pair_integrable (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) (g : SchwartzMap X ℝ) :
    Integrable (fun x => stressFun lam mu u i j x*g x) (volume.restrict Ω) :=
  (stress_memLp hl hm u i j).integrable_mul (g.memLp 2 (volume.restrict Ω))
lemma density_stress (a b : ℝ) (u : Fin 3 → V) (v : Fin 3 → ℝ) (i : Fin 3) :
    elasticDensity a b u (fun j => v j • coordVector i)=
      ∑ j, ((if i=j then a*(∑ k, u k k) else 0)+b*(u j i+u i j))*v j := by
  rw [density_single]
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [Finset.mul_sum,mul_add,add_mul,Finset.sum_add_distrib,mul_assoc]
lemma energy_test_stress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1 Ω) (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) :
    energy Ω lam mu u (testH1 g hc hs i)=
      ∑ j, inner ℝ (stressL2 hl hm u.val i j) (schwartzR Ω (ElasticityKorn.d (coordVector j) g)) := by
  simp only [stress_pair]
  rw [← integral_finsetSum _ (fun j _ => stress_pair_integrable hl hm u.val i j _)]
  change (∫ x, elasticDensity (lam x) (mu x) (gradient u.val x) (gradient (testH1 g hc hs i).val x) ∂(volume.restrict Ω))=_
  apply integral_congr_ae
  filter_upwards [testH1_gradient g hc hs i] with x hx
  rw [hx,density_stress]
  rfl
/-- The variational equation yields the actual scalar-test stress equation. -/
theorem weakSolution_stress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1 Ω) (hu : WeakSolution Ω lam mu u) (g : SchwartzMap X ℝ)
    (hc : HasCompactSupport (g : X → ℝ)) (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) :
    (∑ j, inner ℝ (stressL2 hl hm u.val i j) (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))=0 := by
  rw [← energy_test_stress hl hm u g hc hs i]
  exact hu _ (testH1_zeroTrace g hc hs i)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
lemma scalarDistribution_apply (f : ScalarL2 Ω) (g : SchwartzMap X ℂ) :
    scalarDistribution Ω f g=∫ x, g x*(f x : ℂ) ∂(volume.restrict Ω) := by
  change Lp.toTemperedDistribution (Complex.ofRealCLM.compLpL 2 (volume.restrict Ω) f) g=_
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM f] with x hx
  rw [hx]
  rfl
lemma scalarDistribution_mulL {a : X → ℝ} (ha : BoundedCoefficient Ω a)
    (c : Coeff) (hc : ∀ᵐ x ∂(volume.restrict Ω), eval c x=(a x : ℂ)) (f : ScalarL2 Ω) :
    scalarDistribution Ω (ha.mulL f)=c • scalarDistribution Ω f := by
  ext g
  rw [coeff_test,scalarDistribution_apply,scalarDistribution_apply]
  apply integral_congr_ae
  filter_upwards [ha.mulL_ae f,hc] with x hx hy
  rw [hx]
  rw [ElasticityNegativeOrder.mult_apply _ (growth c),hy,Complex.ofReal_mul]
  ring
lemma stressL2_eq (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) : stressL2 hl hm u i j=
      (if i=j then hl.mulL (∑ k, ambientScalar Ω (some k) k u) else 0)+
      hm.mulL (ambientScalar Ω (some j) i u+ambientScalar Ω (some i) j u) := by
  have hdiv : (∑ k, ambientScalar Ω (some k) k u : ScalarL2 Ω) =ᵐ[volume.restrict Ω]
      fun x => ∑ k, u.2 k x k := by
    have hs := lp_sum_ae Finset.univ (fun k => ambientScalar Ω (some k) k u)
    have he : ∀ᵐ x ∂(volume.restrict Ω), ∀ k, ambientScalar Ω (some k) k u x=u.2 k x k :=
      Filter.eventually_all.mpr (fun k => ambientScalar_ae u (some k) k)
    filter_upwards [hs,he] with x hx hy
    exact hx.trans (Finset.sum_congr rfl (fun k _ => hy k))
  have hs : (ambientScalar Ω (some j) i u+ambientScalar Ω (some i) j u : ScalarL2 Ω)
      =ᵐ[volume.restrict Ω] fun x => u.2 j x i+u.2 i x j := by
    filter_upwards [Lp.coeFn_add (ambientScalar Ω (some j) i u) (ambientScalar Ω (some i) j u),
      ambientScalar_ae u (some j) i,ambientScalar_ae u (some i) j] with x hx hy hz
    exact hx.trans (congrArg₂ (·+·) hy hz)
  apply Lp.ext
  by_cases he : i=j
  · simp only [he,ite_true] at *
    filter_upwards [stressL2_ae hl hm u j j, hdiv,hs,
      hl.mulL_ae (∑ k, ambientScalar Ω (some k) k u),
      hm.mulL_ae (ambientScalar Ω (some j) j u+ambientScalar Ω (some j) j u),
      Lp.coeFn_add (hl.mulL (∑ k, ambientScalar Ω (some k) k u))
        (hm.mulL (ambientScalar Ω (some j) j u+ambientScalar Ω (some j) j u))] with x hx hd hs hl hm ha
    rw [hx,ha]
    simp only [Pi.add_apply,hl,hm,hd,hs,stressFun,ite_true]
  · simp only [he,ite_false,zero_add]
    filter_upwards [stressL2_ae hl hm u i j,hs,
      hm.mulL_ae (ambientScalar Ω (some j) i u+ambientScalar Ω (some i) j u)] with x hx hs hm
    rw [hx,hm,hs]
    simp only [stressFun,he,ite_false,zero_add]
lemma stress_distribution (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ))
    (u : H1 Ω) (i j : Fin 3) : scalarDistribution Ω (stressL2 hl hm u.val i j)=
    (if i=j then L • (∑ k, h1GradientDistribution u k k) else 0)+
      M • (h1GradientDistribution u i j+h1GradientDistribution u j i) := by
  rw [stressL2_eq,map_add,scalarDistribution_mulL hm M hM,map_add]
  simp only [h1GradientDistribution]
  congr 1
  split_ifs
  · rw [scalarDistribution_mulL hl L hL,map_sum]
  · exact map_zero _
/-- The physical stress of a genuine weak solution has zero distributional divergence. -/
theorem weak_stress_divergence (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1 Ω) (hu : WeakSolution Ω lam mu u) (i : Fin 3) :
    LocalEq Ω (∑ j, dd j (scalarDistribution Ω (stressL2 hl hm u.val i j))) 0 := by
  apply localEq_of_realTest
  intro g hc hs
  simp only [sum_apply,dd_apply,lineDerivOp_apply_apply,map_neg]
  change (∑ j, -scalarDistribution Ω (stressL2 hl hm u.val i j) (∂_{coordVector j} (realTest g)))=0
  simp only [realTest_d,scalarDistribution_real,← Complex.ofReal_neg,← Complex.ofReal_sum,Finset.sum_neg_distrib]
  rw [weakSolution_stress hl hm u hu g hc hs i,neg_zero,Complex.ofReal_zero]
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
lemma dist_sd_zero (j : Fin 3) (v : Dist) : sd (0 : Fin 3 → ℂ) j v=dd j v := by
  rw [sd_apply]
  change dd j v+(0 : ℂ) • v=dd j v
  rw [zero_smul ℂ v,add_zero]
lemma physical_gradient (u : H1 Ω) (L M : Coeff) (i : Fin 3) :
    LocalEq Ω (phys 0 L M (h1Distribution u) i)
      (dd i (L • (∑ k, h1GradientDistribution u k k))+
        ∑ j, dd j (M • (h1GradientDistribution u i j+h1GradientDistribution u j i))) := by
  simp only [phys,divd,dist_sd_zero]
  have hd : LocalEq Ω (∑ k, dd k (h1Distribution u k)) (∑ k, h1GradientDistribution u k k) :=
    LocalEq.sum Finset.univ (fun k _ => h1_distribution_derivative u k k)
  have hL := (hd.coeff L).derivative i
  have hM : ∀ j : Fin 3, LocalEq Ω
      (dd j (M • (dd j (h1Distribution u i)+dd i (h1Distribution u j))))
      (dd j (M • (h1GradientDistribution u i j+h1GradientDistribution u j i))) := by
    intro j
    exact (((h1_distribution_derivative u i j).add (h1_distribution_derivative u j i)).coeff M).derivative j
  exact hL.add (LocalEq.sum Finset.univ (fun j _ => hM j))
lemma physical_stress_sum (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ))
    (u : H1 Ω) (i : Fin 3) :
    (∑ j, dd j (scalarDistribution Ω (stressL2 hl hm u.val i j)))=
      dd i (L • (∑ k, h1GradientDistribution u k k))+
        ∑ j, dd j (M • (h1GradientDistribution u i j+h1GradientDistribution u j i)) := by
  simp only [stress_distribution hl hm L M hL hM,map_add,apply_ite,map_zero,Finset.sum_add_distrib]
  simp
/-- Actual weak-to-distributional physical elasticity, for the closure-defined
H1 space and its variational equation. No PDE regularity hypothesis is introduced. -/
theorem weak_physical (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ))
    (u : H1 Ω) (hu : WeakSolution Ω lam mu u) (i : Fin 3) :
    LocalEq Ω (phys 0 L M (h1Distribution u) i) 0 := by
  have hh := physical_gradient u L M i
  rw [← physical_stress_sum hl hm L M hL hM u i] at hh
  exact hh.trans (weak_stress_divergence hl hm u hu i)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
lemma density_full_stress (a b : ℝ) (P Q : Fin 3 → V) :
    elasticDensity a b P Q=∑ i, ∑ j,
      ((if i=j then a*(∑ k, P k k) else 0)+b*(P j i+P i j))*Q j i := by
  simp [elasticDensity,Fin.sum_univ_succ]
  ring
lemma energy_testJet_stress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1 Ω) (v : Ambient Ω) (hv : v∈TestJets Ω)
    (ht : ∀ (g : SchwartzMap X ℝ), HasCompactSupport (g : X → ℝ) → tsupport (g : X → ℝ)⊆Ω →
      ∀ i, (∑ j, inner ℝ (stressL2 hl hm u.val i j)
        (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))=0) :
    ambientEnergy lam mu u.val v=0 := by
  obtain ⟨f,hf,hd,hsm,hc,hs,hv,hvd⟩ := hv
  let F (i : Fin 3) : SchwartzMap X ℝ :=
    (hc.comp_left (g := fun y : V => y i) rfl).toSchwartzMap
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hsm)
  have he (i) := ht (F i) (hc.comp_left (g := fun y : V => y i) rfl)
    ((scalar_test_support f i).trans hs) i
  have hdv : ∀ᵐ x ∂(volume.restrict Ω), ∀ j, v.2 j x=coordDeriv f j x := by
    rw [hvd]
    exact Filter.eventually_all.mpr (fun j => (hd j).coeFn_toLp)
  have heq : ambientEnergy lam mu u.val v=∑ i, ∑ j,
      inner ℝ (stressL2 hl hm u.val i j) (schwartzR Ω (ElasticityKorn.d (coordVector j) (F i))) := by
    simp only [stress_pair]
    simp_rw [← integral_finsetSum _ (fun j _ => stress_pair_integrable hl hm u.val _ j _)]
    rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => stress_pair_integrable hl hm u.val i j _))]
    apply integral_congr_ae
    filter_upwards [hdv] with x hx
    simp only [ambientDensity,density_full_stress,stressFun,gradient]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hx]
    congr 1
    exact (coordDeriv_scalar f hsm i j x).symm
  rw [heq]
  simp only [he,Finset.sum_const_zero]
/-- The scalar-test stress equation is equivalent to the physical weak
formulation; the nontrivial direction uses actual density of compact test jets. -/
theorem weakSolution_of_stress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1 Ω)
    (ht : ∀ (g : SchwartzMap X ℝ), HasCompactSupport (g : X → ℝ) → tsupport (g : X → ℝ)⊆Ω →
      ∀ i, (∑ j, inner ℝ (stressL2 hl hm u.val i j)
        (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))=0) :
    WeakSolution Ω lam mu u := by
  let E : Ambient Ω →L[ℝ] ℝ :=
    (jetEnergy hl hm ((h1Equiv Ω).symm u).val).comp (jetEquiv Ω).symm.toContinuousLinearMap
  have hE (v : H1 Ω) : E v.val=energy Ω lam mu u v := by
    have he := jetEnergy_eq_energy hl hm ((h1Equiv Ω).symm u) ((h1Equiv Ω).symm v)
    simp only [Equiv.apply_symm_apply] at he
    change jetEnergy hl hm ((jetEquiv Ω).symm u.val) ((jetEquiv Ω).symm v.val)=_
    exact he
  have htE : MapsTo E (TestJets Ω) ({0} : Set ℝ) := by
    intro v hv
    let w : H1 Ω := ⟨v,h10Submodule_le Ω (subset_closure hv)⟩
    change E w.val=0
    rw [hE]
    exact energy_testJet_stress hl hm u v hv ht
  intro v hv
  have he := htE.closure E.continuous hv
  rw [closure_singleton] at he
  exact (hE v).symm.trans he
/-- A genuine H1 field satisfying the actual distributional physical equation
is a genuine variational solution; no PDE interface is taken on faith. -/
theorem weakSolution_of_physical (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ)) (u : H1 Ω)
    (hu : ∀ i, LocalEq Ω (phys 0 L M (h1Distribution u) i) 0) : WeakSolution Ω lam mu u := by
  apply weakSolution_of_stress hl hm u
  intro g hc hs i
  have hh := physical_gradient u L M i
  rw [← physical_stress_sum hl hm L M hL hM u i] at hh
  have he := hh.symm.trans (hu i)
  have hgc : HasCompactSupport (realTest g : X → ℂ) := hc.comp_left (g := Complex.ofReal) rfl
  have hgs : tsupport (realTest g : X → ℂ)⊆Ω :=
    (tsupport_comp_subset (g := Complex.ofReal) rfl (g : X → ℝ)).trans hs
  have h := he (realTest g) hgc hgs
  simp only [sum_apply,dd_apply,lineDerivOp_apply_apply,map_neg] at h
  change (∑ j, -scalarDistribution Ω (stressL2 hl hm u.val i j)
    (∂_{coordVector j} (realTest g)))=0 at h
  simp only [realTest_d,scalarDistribution_real,← Complex.ofReal_neg,← Complex.ofReal_sum,
    Finset.sum_neg_distrib] at h
  exact neg_eq_zero.mp (Complex.ofReal_eq_zero.mp h)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X}
def schwartzJet (F : SchwartzMap X V) : Ambient Ω :=
  (F.toLp 2 (volume.restrict Ω),fun j => (∂_{coordVector j} F).toLp 2 (volume.restrict Ω))
lemma schwartzJet_mem (F : SchwartzMap X V) : schwartzJet (Ω := Ω) F∈SmoothJets Ω := by
  refine ⟨F,F.memLp 2 (volume.restrict Ω),fun j => (∂_{coordVector j} F).memLp 2 (volume.restrict Ω),F.smooth _,?_,?_⟩
  · rfl
  · rfl
def schwartzH1 (F : SchwartzMap X V) : H1 Ω := ⟨schwartzJet F,subset_closure (schwartzJet_mem F)⟩
lemma schwartzH1_value (F : SchwartzMap X V) :
    (schwartzH1 (Ω := Ω) F).val.1 =ᵐ[volume.restrict Ω] (F : X → V) :=
  F.coeFn_toLp 2 (volume.restrict Ω)
lemma schwartzH1_gradient (F : SchwartzMap X V) (i : Fin 3) :
    (schwartzH1 (Ω := Ω) F).val.2 i =ᵐ[volume.restrict Ω] ((∂_{coordVector i} F : SchwartzMap X V) : X → V) :=
  (∂_{coordVector i} F).coeFn_toLp 2 (volume.restrict Ω)
def componentTest (F : SchwartzMap X V) (i : Fin 3) : SchwartzMap X ℝ :=
  F.postcompCLM (EuclideanSpace.proj (𝕜 := ℝ) i)
lemma schwartzH1_distribution (F : SchwartzMap X V) (i : Fin 3) :
    LocalEq Ω (h1Distribution (schwartzH1 (Ω := Ω) F) i) ((realTest (componentTest F i)) : Dist) := by
  intro φ hc hs
  rw [h1Distribution,scalarDistribution_apply]
  change (∫ x, φ x * ((ambientScalar Ω none i (schwartzH1 (Ω := Ω) F).val) x : ℂ)
    ∂(volume.restrict Ω))=((realTest (componentTest F i)) : Dist) φ
  have he : ((ambientScalar Ω none i (schwartzH1 (Ω := Ω) F).val) : X → ℝ) =ᵐ[volume.restrict Ω]
      fun x => F x i := by
    filter_upwards [ambientScalar_ae (schwartzH1 (Ω := Ω) F).val none i,schwartzH1_value (Ω := Ω) F] with x hx hy
    exact hx.trans (congrArg (fun y : V => y i) hy)
  calc
    _ = ∫ x, φ x*(F x i : ℂ) ∂(volume.restrict Ω) := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    _ = ∫ x, φ x*(F x i : ℂ) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := (φ : X → ℂ)) (fun h => hx (hs h)),zero_mul]
    _ = _ := rfl
/-- A classical real displacement gives the concrete variational H1 field,
with its actual derivatives and physical equation. -/
theorem schwartzH1_weak {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ)) (F : SchwartzMap X V)
    (he : ∀ i, LocalEq Ω (phys 0 L M (fun i => ((realTest (componentTest F i)) : Dist)) i) 0) :
    WeakSolution Ω lam mu (schwartzH1 (Ω := Ω) F) := by
  apply weakSolution_of_physical hl hm L M hL hM
  intro i
  exact (LocalEq.physical (schwartzH1_distribution F) 0 L M i).trans (he i)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace ElasticityDistribution
lemma phys_add (z : Fin 3 → ℂ) (L M : Coeff) (u v : Fin 3 → Dist) (i : Fin 3) :
    phys z L M (u+v) i=phys z L M u i+phys z L M v i := by
  have ha (A : Coeff) (v w : Dist) : A • (v+w)=A • v+A • w := smul_add A v w
  simp only [phys,divd,Pi.add_apply,map_add,Finset.sum_add_distrib,ha]
  abel
lemma phys_smul (z : Fin 3 → ℂ) (L M : Coeff) (c : ℂ) (u : Fin 3 → Dist) (i : Fin 3) :
    phys z L M (c • u) i=c • phys z L M u i := by
  have hc (A : Coeff) (v : Dist) : A • (c • v)=c • (A • v) := (smul_comm c A v).symm
  have ha (v w : Dist) : c • v+c • w=c • (v+w) := (smul_add c v w).symm
  simp only [phys,divd,Pi.smul_apply,map_smul,← Finset.smul_sum,ha,hc]
end ElasticityDistribution
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
lemma physical_realTest (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ))
    (u : H1 Ω) (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) :
    phys 0 L M (h1Distribution u) i (realTest g)=
      ↑(-(∑ j, inner ℝ (stressL2 hl hm u.val i j)
        (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))) := by
  have hh := physical_gradient u L M i
  rw [← physical_stress_sum hl hm L M hL hM u i] at hh
  have hgc : HasCompactSupport (realTest g : X → ℂ) := hc.comp_left (g := Complex.ofReal) rfl
  have hgs : tsupport (realTest g : X → ℂ)⊆Ω :=
    (tsupport_comp_subset (g := Complex.ofReal) rfl (g : X → ℝ)).trans hs
  rw [hh (realTest g) hgc hgs]
  simp only [sum_apply,dd_apply,lineDerivOp_apply_apply,map_neg]
  change (∑ j, -scalarDistribution Ω (stressL2 hl hm u.val i j)
    (∂_{coordVector j} (realTest g)))=_
  simp only [realTest_d,scalarDistribution_real,← Complex.ofReal_neg,← Complex.ofReal_sum,
    Finset.sum_neg_distrib]
/-- Real and imaginary parts of a physical H1 solution solve the original real
variational problems. This is derived from the actual distribution equation. -/
theorem weakSolution_parts (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ)) (u v : H1 Ω)
    (he : ∀ i, LocalEq Ω (phys 0 L M (h1Distribution u+Complex.I • h1Distribution v) i) 0) :
    WeakSolution Ω lam mu u ∧ WeakSolution Ω lam mu v := by
  have ht (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
      (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) :
      (∑ j, inner ℝ (stressL2 hl hm u.val i j) (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))=0 ∧
      (∑ j, inner ℝ (stressL2 hl hm v.val i j) (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))=0 := by
    have hgc : HasCompactSupport (realTest g : X → ℂ) := hc.comp_left (g := Complex.ofReal) rfl
    have hgs : tsupport (realTest g : X → ℂ)⊆Ω :=
      (tsupport_comp_subset (g := Complex.ofReal) rfl (g : X → ℝ)).trans hs
    have h := he i (realTest g) hgc hgs
    rw [phys_add,phys_smul] at h
    simp only [add_apply,smul_apply,smul_eq_mul,physical_realTest hl hm L M hL hM _ g hc hs i] at h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,sub_zero,add_zero] at hr
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] at hi
    exact ⟨neg_eq_zero.mp hr,neg_eq_zero.mp hi⟩
  exact ⟨weakSolution_of_stress hl hm u (fun g hc hs i => (ht g hc hs i).1),
    weakSolution_of_stress hl hm v (fun g hc hs i => (ht g hc hs i).2)⟩
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X}
def realVectorTest (F : Fin 3 → SchwartzMap X ℝ) : SchwartzMap X V :=
  ∑ i, (F i).postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (coordVector i))
lemma realVectorTest_apply (F : Fin 3 → SchwartzMap X ℝ) (x : X) (i : Fin 3) :
    realVectorTest F x i=F i x := by
  simp [realVectorTest,coordVector,Pi.single_apply]
lemma component_realVectorTest (F : Fin 3 → SchwartzMap X ℝ) (i : Fin 3) :
    componentTest (realVectorTest F) i=F i := by
  ext x
  exact realVectorTest_apply F x i
def complexRealH1 (F : Fin 3 → SchwartzMap X ℂ) : H1 Ω :=
  schwartzH1 (realVectorTest (fun i => reTest (F i)))
def complexImagH1 (F : Fin 3 → SchwartzMap X ℂ) : H1 Ω :=
  schwartzH1 (realVectorTest (fun i => imTest (F i)))
lemma complexH1_value (F : Fin 3 → SchwartzMap X ℂ) (i : Fin 3) :
    ∀ᵐ x ∂(volume.restrict Ω),
      ((complexRealH1 (Ω := Ω) F).val.1 x i : ℂ)+Complex.I*((complexImagH1 (Ω := Ω) F).val.1 x i : ℂ)=F i x := by
  filter_upwards [schwartzH1_value (Ω := Ω) (realVectorTest (fun i => reTest (F i))),
    schwartzH1_value (Ω := Ω) (realVectorTest (fun i => imTest (F i)))] with x hr hi
  change ((schwartzH1 (Ω := Ω) _).val.1 x i : ℂ)+Complex.I*((schwartzH1 (Ω := Ω) _).val.1 x i : ℂ)=_
  rw [hr,hi,realVectorTest_apply,realVectorTest_apply]
  change ↑((F i x).re)+Complex.I*↑((F i x).im)=_
  exact (by rw [mul_comm]; exact Complex.re_add_im (F i x))
lemma complexH1_distribution (F : Fin 3 → SchwartzMap X ℂ) (i : Fin 3) :
    LocalEq Ω (h1Distribution (complexRealH1 (Ω := Ω) F) i+
      Complex.I • h1Distribution (complexImagH1 (Ω := Ω) F) i) ((F i) : Dist) := by
  have hr := schwartzH1_distribution (Ω := Ω) (realVectorTest (fun i => reTest (F i))) i
  have hi := schwartzH1_distribution (Ω := Ω) (realVectorTest (fun i => imTest (F i))) i
  rw [component_realVectorTest] at hr hi
  have he := hr.add (hi.smul Complex.I)
  rw [← coe_schwartz_smul,← coe_schwartz_add,
    ← test_parts (F i)] at he
  exact he
lemma localEq_of_schwartz_eqOn {F G : SchwartzMap X ℂ} (h : Set.EqOn (F : X → ℂ) G Ω) :
    LocalEq Ω (F : Dist) (G : Dist) := by
  intro φ _ hs
  change (∫ x, φ x*F x)=(∫ x, φ x*G x)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change φ x*F x=φ x*G x
    by_cases hx : x∈Ω
    · rw [h hx]
    · rw [image_eq_zero_of_notMem_tsupport (f := (φ : X → ℂ)) (fun hg => hx (hs hg)),zero_mul,zero_mul])
/-- A classical complex physical field embeds into the literal real DN problem
through its two actual H1 parts, rather than a presumed complex boundary map. -/
theorem complexH1_weak {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ)) (F : Fin 3 → SchwartzMap X ℂ)
    (he : ∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L) (eval M) F i : X → ℂ) 0 Ω) :
    WeakSolution Ω lam mu (complexRealH1 (Ω := Ω) F) ∧
      WeakSolution Ω lam mu (complexImagH1 (Ω := Ω) F) := by
  apply weakSolution_parts hl hm L M hL hM
  intro i
  have hp := LocalEq.physical (complexH1_distribution (Ω := Ω) F) 0 L M i
  rw [phys_schwartz] at hp
  have hh := localEq_of_schwartz_eqOn (F := ElasticityPhysicalAlgebra.physical 0 (eval L) (eval M) F i)
    (G := 0) (he i)
  simpa only [map_zero,Pi.add_def,Pi.smul_def] using hp.trans hh
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set TemperedDistribution
open scoped BigOperators SchwartzMap
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
def scalarGlobal (hs : MeasurableSet Ω) (f : ScalarL2 Ω) : Lp ℂ 2 (volume : Measure X) :=
  lpZeroExtendCLM volume Ω hs (Complex.ofRealCLM.compLpL 2 (volume.restrict Ω) f)
lemma scalarGlobal_ae (hs : MeasurableSet Ω) (f : ScalarL2 Ω) :
    (scalarGlobal hs f : X → ℂ)=ᵐ[volume] Ω.indicator (fun x => (f x : ℂ)) := by
  filter_upwards [lpZeroExtend_coe volume Ω hs (Complex.ofRealCLM.compLpL 2 (volume.restrict Ω) f),
    (ae_restrict_iff' hs).mp (ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM f)] with x hx hy
  rw [scalarGlobal,hx]
  by_cases he : x∈Ω
  · simp only [indicator_of_mem he,hy he]
    rfl
  · simp only [indicator_of_notMem he]
lemma scalarGlobal_distribution (hs : MeasurableSet Ω) (f : ScalarL2 Ω) :
    (scalarGlobal hs f : Dist)=scalarDistribution Ω f := by
  ext g
  rw [Lp.toTemperedDistribution_apply,scalarDistribution_apply]
  calc
    _ = ∫ x, Ω.indicator (fun y => g y*(f y : ℂ)) x ∂volume := by
      apply integral_congr_ae
      filter_upwards [scalarGlobal_ae hs f] with x hx
      rw [hx]
      by_cases he : x∈Ω
      · simp only [indicator_of_mem he,smul_eq_mul]
      · simp only [indicator_of_notMem he,smul_zero]
    _ = _ := integral_indicator hs
 def h1Global (hs : MeasurableSet Ω) (u : H1 Ω) : ElasticityPhysicalDual.H :=
  WithLp.toLp 2 (fun i => scalarGlobal hs (ambientScalar Ω none i u.val))
lemma h1Global_distribution (hs : MeasurableSet Ω) (u : H1 Ω) (i : Fin 3) :
    (h1Global hs u i : Dist)=h1Distribution u i := scalarGlobal_distribution hs _
lemma h1Global_ae (hs : MeasurableSet Ω) (u : H1 Ω) (i : Fin 3) :
    ∀ᵐ x ∂volume, x∈Ω → h1Global hs u i x=(u.val.1 x i : ℂ) := by
  filter_upwards [scalarGlobal_ae hs (ambientScalar Ω none i u.val),
    (ae_restrict_iff' hs).mp (ambientScalar_ae u.val none i)] with x hx hy
  intro he
  change scalarGlobal hs (ambientScalar Ω none i u.val) x=_
  rw [hx,indicator_of_mem he,hy he]
  rfl
/-- Interior regularization now applies to the genuine variational solution,
not a hypothetical distribution satisfying an assumed physical equation. -/
theorem h1_classical_representative (hΩ : IsOpen Ω) {Ω' : Set X} (hΩ' : IsOpen Ω') (hsub : Ω'⊆Ω)
    (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M N O : Coeff) (hN : N*M=1) (hO : O*(L+M+M)=1)
    (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ))
    (u : H1 Ω) (hu : WeakSolution Ω lam mu u)
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : Fin 3 → SchwartzMap X ℂ,
      (∀ i, ∀ᵐ x ∂volume, x∈Ω' → (u.val.1 x i : ℂ)=v i x) ∧
      ∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L) (eval M) v i : X → ℂ) 0 Ω' := by
  have he : ∀ i, LocalEq Ω (phys 0 L M (fun j => (h1Global hΩ.measurableSet u j : Dist)) i)
      ((0 : SchwartzMap X ℂ) : Dist) := by
    intro i
    simp only [h1Global_distribution,map_zero]
    exact weak_physical hl hm L M hL hM u hu i
  obtain ⟨v,hv,hve⟩ := classical_representative hΩ' hsub 0 L M N O hN hO
    (h1Global hΩ.measurableSet u) (fun _ => 0) he hg hc hs h1
  refine ⟨v,fun i => ?_,hve⟩
  filter_upwards [hv i,h1Global_ae hΩ.measurableSet u i] with x hx hy
  intro he
  exact (hy (hsub he)).symm.trans (hx he)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω B B' : Set X} {lam₁ mu₁ lam₂ mu₂ : X → ℝ}
/-- Actual smooth complex physical transfer on an interior ball, from the
original real variational DN equality. No augmented/artificial DN map is used. -/
theorem physical_classical_transfer
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hΩB : Ω⊆B)
    (hB : IsOpen B) (hB' : IsOpen B') (hsub : B'⊆B)
    (hl₁ : BoundedCoefficient B lam₁) (hm₁ : BoundedCoefficient B mu₁)
    (hl₂ : BoundedCoefficient B lam₂) (hm₂ : BoundedCoefficient B mu₂)
    (he : ∀ x∉Ω, lam₁ x=lam₂ x ∧ mu₁ x=mu₂ x)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂)
    (L₁ M₁ L₂ M₂ N₂ O₂ : Coeff) (hN : N₂*M₂=1) (hO : O₂*(L₂+M₂+M₂)=1)
    (hL₁ : ∀ᵐ x ∂(volume.restrict B), eval L₁ x=(lam₁ x : ℂ))
    (hM₁ : ∀ᵐ x ∂(volume.restrict B), eval M₁ x=(mu₁ x : ℂ))
    (hL₂ : ∀ᵐ x ∂(volume.restrict B), eval L₂ x=(lam₂ x : ℂ))
    (hM₂ : ∀ᵐ x ∂(volume.restrict B), eval M₂ x=(mu₂ x : ℂ))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆B) (h1 : Set.EqOn g 1 B') (F : Fin 3 → SchwartzMap X ℂ)
    (hF : ∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L₁) (eval M₁) F i : X → ℂ) 0 B) :
    ∃ G : Fin 3 → SchwartzMap X ℂ,
      (∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L₂) (eval M₂) G i : X → ℂ) 0 B') ∧
      ∀ i, Set.EqOn (G i : X → ℂ) (F i) (B'\closure Ω) := by
  obtain ⟨hr,hi⟩ := complexH1_weak hl₁ hm₁ L₁ M₁ hL₁ hM₁ F hF
  obtain ⟨wr,hwr,hre,_⟩ := physical_weak_transfer ha₁ ha₂ hΩ hOB hΩB hl₁ hm₁ hl₂ hm₂ he hDN hr
  obtain ⟨wi,hwi,hie,_⟩ := physical_weak_transfer ha₁ ha₂ hΩ hOB hΩB hl₁ hm₁ hl₂ hm₂ he hDN hi
  obtain ⟨R,hR,hRp⟩ := h1_classical_representative hB hB' hsub hl₂ hm₂ L₂ M₂ N₂ O₂ hN hO hL₂ hM₂ wr hwr hg hc hs h1
  obtain ⟨I,hI,hIp⟩ := h1_classical_representative hB hB' hsub hl₂ hm₂ L₂ M₂ N₂ O₂ hN hO hL₂ hM₂ wi hwi hg hc hs h1
  let G : Fin 3 → SchwartzMap X ℂ := R+Complex.I • I
  refine ⟨G,?_,?_⟩
  · intro i x hx
    change ElasticityPhysicalAlgebra.physical 0 (eval L₂) (eval M₂) (R+Complex.I • I) i x=0
    rw [ElasticityPhysicalDual.physical_add,ElasticityPhysicalDual.physical_smul]
    change ElasticityPhysicalAlgebra.physical 0 (eval L₂) (eval M₂) R i x+
      Complex.I*ElasticityPhysicalAlgebra.physical 0 (eval L₂) (eval M₂) I i x=0
    simp only [hRp i hx,hIp i hx,Pi.zero_apply,mul_zero,add_zero]
  · intro i
    apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure X)) _ (hB'.sdiff isClosed_closure)
      (G i).continuous.continuousOn (F i).continuous.continuousOn
    apply (ae_restrict_iff' (hB'.measurableSet.diff isClosed_closure.measurableSet)).mpr
    have hre' := (ae_restrict_iff' hB.measurableSet).mp hre
    have hie' := (ae_restrict_iff' hB.measurableSet).mp hie
    have hFv := (ae_restrict_iff' hB.measurableSet).mp (complexH1_value (Ω := B) F i)
    filter_upwards [hR i,hI i,hre',hie',hFv] with x hRx hIx hrx hix hFx hx
    have hxB := hsub hx.1
    have hxo : x∉Ω := fun hh => hx.2 (subset_closure hh)
    change R i x+Complex.I*I i x=F i x
    rw [← hRx hx.1,← hIx hx.1,hrx hxB hxo,hix hxB hxo]
    exact hFx hxB
end Elasticity

end
end

end OAI
