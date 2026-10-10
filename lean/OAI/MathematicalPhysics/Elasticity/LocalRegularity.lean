import OAI.MathematicalPhysics.Elasticity.Solvability

namespace OAI

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
namespace ElasticityRegularity


section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def LocalEqual (Ω : Set E) (u v : 𝓢'(E,ℂ)) : Prop :=
  ∀ φ : 𝓢(E,ℂ), HasCompactSupport (φ : E → ℂ) → tsupport (φ : E → ℂ) ⊆ Ω → u φ=v φ
namespace LocalEqual
variable {Ω : Set E} {u v w u' v' : 𝓢'(E,ℂ)}
lemma refl (u : 𝓢'(E,ℂ)) : LocalEqual Ω u u := fun _ _ _ => rfl
lemma symm (h : LocalEqual Ω u v) : LocalEqual Ω v u := fun φ hc hs => (h φ hc hs).symm
lemma trans (h : LocalEqual Ω u v) (h' : LocalEqual Ω v w) : LocalEqual Ω u w :=
  fun φ hc hs => (h φ hc hs).trans (h' φ hc hs)
lemma add (h : LocalEqual Ω u v) (h' : LocalEqual Ω u' v') : LocalEqual Ω (u+u') (v+v') := by
  intro φ hc hs
  simp only [add_apply,h φ hc hs,h' φ hc hs]
lemma sub (h : LocalEqual Ω u v) (h' : LocalEqual Ω u' v') : LocalEqual Ω (u-u') (v-v') := by
  intro φ hc hs
  simp only [sub_apply,h φ hc hs,h' φ hc hs]
lemma smul (h : LocalEqual Ω u v) (c : ℂ) : LocalEqual Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
lemma sum {ι : Type*} (S : Finset ι) {u v : ι → 𝓢'(E,ℂ)}
    (h : ∀ i ∈ S, LocalEqual Ω (u i) (v i)) : LocalEqual Ω (∑ i ∈ S, u i) (∑ i ∈ S, v i) := by
  intro φ hc hs
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun i hi => h i hi φ hc hs)
lemma derivative (h : LocalEqual Ω u v) (a : E) : LocalEqual Ω (∂_{a} u) (∂_{a} v) := by
  intro φ hc hs
  change u (- ∂_{a} φ) = v (- ∂_{a} φ)
  apply h
  · change HasCompactSupport (fun x => -((∂_{a} φ : 𝓢(E,ℂ)) x))
    exact (hc.fderiv_apply (𝕜 := ℝ) a).neg
  · change tsupport (-((∂_{a} φ : 𝓢(E,ℂ)) : E → ℂ)) ⊆ Ω
    rw [tsupport_neg]
    exact (derivative_support_subset (φ : E → ℂ) a).trans hs
lemma cutoff (h : LocalEqual Ω u v) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    smulLeftCLM ℂ g u = smulLeftCLM ℂ g v := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ g φ) = v (SchwartzMap.smulLeftCLM ℂ g φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_right : HasCompactSupport (g * (φ : E → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_left (f := g) (g := (φ : E → ℂ))).trans hs
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma localSobolev {s : ℝ} (h : LocalEqual Ω u v) (hv : LocalSobolev Ω s v) : LocalSobolev Ω s u := by
  intro g hg hc hs
  rw [h.cutoff hg hc hs]
  exact hv g hg hc hs
end LocalEqual
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace LocalSobolev
variable {Ω : Set E} {s : ℝ} {u v : 𝓢'(E,ℂ)}
lemma add (h : LocalSobolev Ω s u) (h' : LocalSobolev Ω s v) : LocalSobolev Ω s (u+v) := by
  intro g hg hc hs
  rw [map_add]
  exact (h g hg hc hs).add (h' g hg hc hs)
lemma sub (h : LocalSobolev Ω s u) (h' : LocalSobolev Ω s v) : LocalSobolev Ω s (u-v) := by
  intro g hg hc hs
  rw [map_sub]
  exact (h g hg hc hs).sub (h' g hg hc hs)
lemma smul (h : LocalSobolev Ω s u) (c : ℂ) : LocalSobolev Ω s (c • u) := by
  intro g hg hc hs
  rw [map_smul]
  exact (h g hg hc hs).smul c
lemma sum {ι : Type*} (S : Finset ι) {u : ι → 𝓢'(E,ℂ)}
    (h : ∀ i ∈ S, LocalSobolev Ω s (u i)) : LocalSobolev Ω s (∑ i ∈ S, u i) := by
  intro g hg hc hs
  rw [map_sum]
  exact sobolev_sum S (fun i hi => h i hi g hg hc hs)
lemma coeff (h : LocalSobolev Ω s u) {a : E → ℂ} (ha : a.HasTemperateGrowth) :
    LocalSobolev Ω s (smulLeftCLM ℂ a u) := by
  intro g hg hc hs
  rw [smulLeftCLM_smulLeftCLM_apply ha (hc.hasTemperateGrowth hg),mul_comm]
  exact h (g*a) (hg.mul ha.1) hc.mul_right (tsupport_mul_subset_left.trans hs)
lemma derivative (h : LocalSobolev Ω s u) (a : E) : LocalSobolev Ω (s-1) (∂_{a} u) := by
  intro g hg hc hs
  exact h.product_derivative hg hc hs a
end LocalSobolev

lemma local_laplacian_gain_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {Ω : Set E} {s : ℝ} {u : 𝓢'(E,ℂ)} (hu : LocalSobolev Ω s u)
    (hΔ : LocalSobolev Ω (s-1) (Δ u)) : LocalSobolev Ω (s+1) u := by
  intro g hg hgc hgs
  have hb : MemSobolev (s-1) 2 (Δ (smulLeftCLM ℂ g u)) := by
    rw [laplacian_product b hg hgc]
    apply (hΔ g hg hgc hgs).add
    apply sobolev_sum Finset.univ
    intro d _
    have hgd := smooth_derivative hg (b d)
    have hcd := compact_derivative hgc (b d)
    have hsd := (derivative_support_subset g (b d)).trans hgs
    exact ((hu _ (smooth_derivative hgd (b d)) (compact_derivative hcd (b d))
      ((derivative_support_subset _ (b d)).trans hsd)).mono (by linarith)).add
        ((hu.product_derivative hgd hcd hsd (b d)).smul 2)
  have h := laplacian_gain ((hu g hg hgc hgs).mono (by linarith : s-1 ≤ s)) hb
  convert h using 1
  ring
end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_dist_injective : Function.Injective (fun u : 𝓢(E,ℂ) => (u : 𝓢'(E,ℂ))) := by
  intro u v h
  apply SchwartzMap.injective_toLp 2 volume
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  change ((u.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ)) =
    ((v.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ))
  simpa only [Lp.toTemperedDistribution_toLp_eq] using h

lemma distribution_schwartz_product {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢(E,ℂ)) :
    smulLeftCLM ℂ g (u : 𝓢'(E,ℂ)) = (SchwartzMap.smulLeftCLM ℂ g u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply,SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma LocalEqual.cutoff_one {Ω : Set E} (u : 𝓢'(E,ℂ)) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (h1 : Set.EqOn g 1 Ω) :
    LocalEqual Ω (smulLeftCLM ℂ g u) u := by
  intro φ _ hs
  rw [smulLeftCLM_apply_apply]
  congr 1
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg,smul_eq_mul]
  by_cases hx : φ x=0
  · simp [hx]
  · rw [h1 (hs (subset_tsupport _ hx))]
    simp

lemma LocalEqual.schwartz_eqOn {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : 𝓢(E,ℂ)} (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    Set.EqOn (u : E → ℂ) (v : E → ℂ) Ω := by
  intro x hx
  obtain ⟨g,hs,hc,hg,_,h1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hΩ.mem_nhds hx)
  let f : E → ℂ := fun y => (g y : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  have hfs : tsupport f ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro y hy
    change g y ≠ 0
    intro hy0
    apply hy
    change (g y : ℂ)=0
    rw [hy0,Complex.ofReal_zero]
  have he := h.cutoff hfg hfc hfs
  rw [distribution_schwartz_product (hfc.hasTemperateGrowth hfg),
    distribution_schwartz_product (hfc.hasTemperateGrowth hfg)] at he
  have he' := congrArg (fun w : 𝓢(E,ℂ) => w x) (schwartz_dist_injective he)
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hfc.hasTemperateGrowth hfg),smul_eq_mul] at he'
  have hx1 : f x=1 := by simp only [f,h1,Complex.ofReal_one]
  simpa only [hx1,one_mul] using he'

lemma smooth_Linfty_product {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (v : BoundedContinuousFunction E ℂ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (v : E → ℂ)) :
    let f : 𝓢(E,ℂ) := (hc.mul_right : HasCompactSupport (g*(v : E → ℂ))).toSchwartzMap (hg.mul hv)
    smulLeftCLM ℂ g (((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))) : 𝓢'(E,ℂ)) = (f : 𝓢'(E,ℂ)) := by
  intro f
  ext φ
  simp only [smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply,SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [v.memLp_top.coeFn_toLp] with x hx
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hc.hasTemperateGrowth hg),hx,smul_eq_mul]
  change g x*φ x*v x = φ x*(g x*v x)
  ring

/-- Interior cutoff regularity yields an actual Schwartz representative on the
smaller open set; this is what is needed to construct physical smooth CGO
solutions on a ball from an L2 weak solution on a larger ball. -/
theorem local_schwartz_representative {Ω Ω' : Set E} (u : 𝓢'(E,ℂ))
    (hu : ∀ N : ℕ, LocalSobolev Ω N u) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : 𝓢(E,ℂ), LocalEqual Ω' u (v : 𝓢'(E,ℂ)) := by
  obtain ⟨v,hv,he⟩ := all_orders_smooth_representative (fun N => hu N g hg hc hs)
  let f : 𝓢(E,ℂ) := (hc.mul_right : HasCompactSupport (g*(v : E → ℂ))).toSchwartzMap (hg.mul hv)
  refine ⟨f,?_⟩
  have he' := smooth_Linfty_product hg hc v hv
  have hlocal := (LocalEqual.cutoff_one u (hc.hasTemperateGrowth hg) h1).symm
  have hlocal' := (LocalEqual.cutoff_one (smulLeftCLM ℂ g u) (hc.hasTemperateGrowth hg) h1).symm
  have h := hlocal.trans hlocal'
  rw [he,he'] at h
  exact h
end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma LocalEqual.lp_ae {Ω : Set E} (hΩ : IsOpen Ω)
    (u v : Lp ℂ 2 (volume : Measure E))
    (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → u x=v x := by
  have hu : LocallyIntegrable (u : E → ℂ) (volume : Measure E) := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hv : LocallyIntegrable (v : E → ℂ) (volume : Measure E) := (Lp.memLp v).locallyIntegrable (by norm_num)
  have he : ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → (u x-v x)=0 := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hu.sub hv).locallyIntegrableOn Ω) ?_
  · filter_upwards [he] with x hx
    intro hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  intro g hg hc hs
  let f : E → ℂ := fun x => (g x : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  let φ : 𝓢(E,ℂ) := hfc.toSchwartzMap hfg
  have hfs : tsupport (φ : E → ℂ) ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro x hx hzero
    apply hx
    change (g x : ℂ)=0
    rw [hzero,Complex.ofReal_zero]
  have hh := h φ hfc hfs
  simp only [Lp.toTemperedDistribution_apply] at hh
  have hiu := hu.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  have hiv := hv.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  simp only [smul_sub]
  rw [integral_sub hiu hiv,sub_eq_zero]
  simp only [show (φ : E → ℂ)=f from rfl,f,Complex.real_smul,smul_eq_mul] at hh ⊢
  convert hh using 1

/-- The smooth local representative really is the original L2 function almost
 everywhere, so the HB solution's L2 estimate is not lost in regularization. -/
theorem local_schwartz_l2_representative {Ω Ω' : Set E} (hΩ' : IsOpen Ω')
    (u : Lp ℂ 2 (volume : Measure E))
    (hu : ∀ N : ℕ, LocalSobolev Ω N (u : 𝓢'(E,ℂ))) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : 𝓢(E,ℂ), LocalEqual Ω' (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ)) ∧
      ∀ᵐ x ∂(volume : Measure E), x ∈ Ω' → u x=v x := by
  obtain ⟨v,hv⟩ := local_schwartz_representative (u : 𝓢'(E,ℂ)) hu hg hc hs h1
  refine ⟨v,hv,?_⟩
  have he : LocalEqual Ω' (u : 𝓢'(E,ℂ)) ((v.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ)) := by
    simpa only [Lp.toTemperedDistribution_toLp_eq] using hv
  filter_upwards [LocalEqual.lp_ae hΩ' u (v.toLp 2 volume) he,v.coeFn_toLp 2 volume] with x hx hxv
  intro hxΩ
  exact (hx hxΩ).trans hxv
end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal
namespace ElasticityDistribution
open ElasticityAugmented ElasticityPhysicalAlgebra ElasticityNegativeOrder

lemma coe_schwartz_add (u v : S) : ((u+v : S) : Dist)=(u : Dist)+(v : Dist) := map_add _ _ _
lemma coe_schwartz_smul (c : ℂ) (u : S) : ((c • u : S) : Dist)=c • (u : Dist) := map_smul _ _ _
lemma coe_schwartz_sum {ι : Type*} (s : Finset ι) (u : ι → S) :
    ((∑ i ∈ s, u i : S) : Dist)=∑ i ∈ s, (u i : Dist) := map_sum _ _ _
lemma sd_schwartz (z : Fin 3 → ℂ) (i : Fin 3) (u : S) :
    sd z i (u : Dist)=(shiftD z i u : Dist) := by
  rw [sd_apply,dd_apply,shiftD_apply,coe_schwartz_add,coe_schwartz_smul]
  congr 1
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq u (e i)
lemma coeff_schwartz (a : Coeff) (u : S) : a • (u : Dist)=(mult (eval a) u : Dist) :=
  ElasticityRegularity.distribution_schwartz_product (growth a) u
lemma divd_schwartz (z : Fin 3 → ℂ) (u : Fin 3 → S) :
    divd z (fun i => (u i : Dist))=(∑ i, shiftD z i (u i) : S) := by
  rw [divd,coe_schwartz_sum]
  simp only [sd_schwartz]
lemma phys_schwartz (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → S) (i : Fin 3) :
    phys z lam m (fun j => (u j : Dist)) i=(physical z (eval lam) (eval m) u i : Dist) := by
  simp only [phys,physical,divd_schwartz,sd_schwartz,← coe_schwartz_add,
    coeff_schwartz,← coe_schwartz_sum]

lemma LocalEq.physical {Ω : Set X} {u v : Fin 3 → Dist} (h : ∀ i, LocalEq Ω (u i) (v i))
    (z : Fin 3 → ℂ) (lam m : Coeff) (i : Fin 3) :
    LocalEq Ω (phys z lam m u i) (phys z lam m v i) :=
  (((LocalEq.divergence h z).coeff lam).shifted z i).add (LocalEq.sum Finset.univ
    (fun j _ => (((h i).shifted z j).add ((h j).shifted z i) |>.coeff m).shifted z j))

/-- A genuinely classical physical solution on an interior open set is obtained
from the actual weak solution, and represents that same L2 unknown there. -/
theorem classical_representative {Ω Ω' : Set X} (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (z : Fin 3 → ℂ) (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (w : ElasticityPhysicalDual.H) (F : Fin 3 → S)
    (heq : ∀ i, LocalEq Ω (phys z lam m (fun j => (w j : Dist)) i) (F i : Dist))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : Fin 3 → S, (∀ i, ∀ᵐ x ∂(volume : Measure X), x ∈ Ω' → w i x=v i x) ∧
      ∀ i, Set.EqOn (physical z (eval lam) (eval m) v i : X → ℂ) (F i : X → ℂ) Ω' := by
  have hall := physical_local_all_orders z lam m n o hn ho (fun j => (w j : Dist))
    (fun j => (F j : Dist)) heq (fun j => lp_local_zero Ω (w j)) (fun N j => schwartz_local_nat Ω (F j) N)
  have hv : ∀ i : Fin 3, ∃ v : S, ElasticityRegularity.LocalEqual Ω' (w i : Dist) (v : Dist) ∧
      ∀ᵐ x ∂(volume : Measure X), x ∈ Ω' → w i x=v x := by
    intro i
    exact ElasticityRegularity.local_schwartz_l2_representative hΩ' (w i)
      (fun N => hall N i.succ) hg hc hs h1
  choose v hv he using hv
  refine ⟨v,he,fun i => ?_⟩
  apply ElasticityRegularity.LocalEqual.schwartz_eqOn hΩ'
  have hl : ∀ j, LocalEq Ω' (w j : Dist) (v j : Dist) := hv
  have hphys := LocalEq.physical hl z lam m i
  rw [phys_schwartz] at hphys
  exact fun φ hφ hφs => (hphys φ hφ hφs).symm.trans (heq i φ hφ (hφs.trans hsub))
end ElasticityDistribution

end

end OAI
