import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.UnitNucleus

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb
lemma H1Vector.coulomb_density_prod_integrable {m : ℕ} (u : H1Vector m)
    (s : Spins m) (i : Fin m) (d : Space → ℝ) (hd : Integrable d) :
    Integrable (fun z : Configuration m × Space =>
      coulombKernel (position z.1 i-z.2)*‖u.value s z.1‖^2*d z.2)
      (volume.prod volume) := by
  let C := 4*(∑ b : Fin 3, ∫ x, ‖u.gradient s (i,b) x‖^2) +
      (1/4:ℝ)*(∫ x, ‖u.value s x‖^2)
  have hK : AEStronglyMeasurable (fun z : Configuration m × Space =>
      coulombKernel (position z.1 i-z.2)) (volume.prod volume) :=
    (((continuous_position i).measurable.comp measurable_fst).sub measurable_snd).norm.inv.aestronglyMeasurable
  have hF : AEStronglyMeasurable (fun z : Configuration m × Space =>
      coulombKernel (position z.1 i-z.2)*‖u.value s z.1‖^2*d z.2)
      (volume.prod volume) :=
    (hK.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2).comp_fst).mul hd.1.comp_snd
  have hN (y : Space) :
      (∫ x, ‖coulombKernel (position x i-y)*‖u.value s x‖^2*d y‖) =
      (∫ x, coulombKernel (position x i-y)*‖u.value s x‖^2)*‖d y‖ := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    have hk : 0 ≤ coulombKernel (position x i-y) := inv_nonneg.mpr (norm_nonneg _)
    rw [norm_mul,Real.norm_of_nonneg (mul_nonneg hk (sq_nonneg _))]
  apply (integrable_prod_iff' hF).2
  constructor
  · filter_upwards [] with y
    exact ((u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1).mul_const (d y)
  · apply (hd.norm.const_mul C).mono' hF.prod_swap.norm.integral_prod_right'
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    change (∫ x, ‖coulombKernel (position x i-y)*‖u.value s x‖^2*d y‖) ≤ C*‖d y‖
    rw [hN]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [C,mul_one,one_div] using
      (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).2

noncomputable def coreCoulombPotential {m : ℕ} (u : H1Vector m) (z : Space) : ℝ :=
  ∑ s : Spins m, ∑ i : Fin m, ∫ x, coulombKernel (position x i-z)*‖u.value s x‖^2

lemma coreCoulombPotential_nonneg {m : ℕ} (u : H1Vector m) (z : Space) :
    0 ≤ coreCoulombPotential u z := by
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg (fun x => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sq_nonneg _))

lemma coreCoulombPotential_bound {m : ℕ} (u : H1Vector m) (z : Space) :
    coreCoulombPotential u z ≤ ∑ s : Spins m, ∑ i : Fin m,
      (4*(∑ b : Fin 3, ∫ x, ‖u.gradient s (i,b) x‖^2)+(1/4:ℝ)*(∫ x, ‖u.value s x‖^2)) := by
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_one] using
    (u.nuclear_coulomb_integrable_bound s i z (by norm_num : (0:ℝ)<1)).2

lemma coreCoulombPotential_mul_integrable {m : ℕ} (u : H1Vector m)
    (d : Space → ℝ) (hd : Integrable d) :
    Integrable (fun z => coreCoulombPotential u z*d z) := by
  simp only [coreCoulombPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro s _
  apply integrable_finsetSum
  intro i _
  have H := (u.coulomb_density_prod_integrable s i d hd).integral_prod_right
  simpa only [integral_mul_const] using H

lemma coreCoulombPotential_fubini {m : ℕ} (u : H1Vector m)
    (d : Space → ℝ) (hd : Integrable d) :
    (∫ z, coreCoulombPotential u z*d z) =
      ∑ s : Spins m, ∑ i : Fin m,
        ∫ x, (∫ z, coulombKernel (position x i-z)*d z)*‖u.value s x‖^2 := by
  have hI (s : Spins m) (i : Fin m) : Integrable
      (fun z => (∫ x, coulombKernel (position x i-z)*‖u.value s x‖^2)*d z) := by
    have H := (u.coulomb_density_prod_integrable s i d hd).integral_prod_right
    simpa only [integral_mul_const] using H
  simp only [coreCoulombPotential,Finset.sum_mul]
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hI s i))]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_finsetSum _ (fun i _ => hI s i)]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← integral_mul_const]
  rw [← integral_prod_symm _ (u.coulomb_density_prod_integrable s i d hd),
    integral_prod _ (u.coulomb_density_prod_integrable s i d hd)]
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with z
  ring

variable {Y ι : Type*} [MeasurableSpace Y] [Countable ι]
lemma weighted_series_integrable_hasSum {ν : Measure Y} {F : ι → Y → ℝ}
    (hF : ∀ i, AEStronglyMeasurable (F i) ν) (hpos : ∀ i y, 0 ≤ F i y)
    (hs : ∀ᵐ y ∂ν, Summable (fun i => F i y)) {W : Y → ℝ}
    (hW : AEStronglyMeasurable W ν) (hWp : ∀ y, 0 ≤ W y)
    (hI : Integrable (fun y => W y * ∑' i, F i y) ν) :
    (∀ i, Integrable (fun y => W y * F i y) ν) ∧
      HasSum (fun i => ∫ y, W y * F i y ∂ν) (∫ y, W y * ∑' i, F i y ∂ν) := by
  have hp (i : ι) (y : Y) : 0 ≤ W y * F i y := mul_nonneg (hWp y) (hpos i y)
  have hi (i : ι) : Integrable (fun y => W y * F i y) ν := by
    apply hI.mono' (hW.mul (hF i))
    filter_upwards [hs] with y hy
    change ‖W y * F i y‖ ≤ _
    rw [Real.norm_of_nonneg (hp i y)]
    exact mul_le_mul_of_nonneg_left (hy.le_tsum i (fun j _ => hpos j y)) (hWp y)
  have hsum : Summable (fun i => ∫ y, W y * F i y ∂ν) := by
    apply summable_of_sum_le (fun i => integral_nonneg (hp i))
    intro s
    rw [← integral_finsetSum s (fun i _ => hi i)]
    apply integral_mono_ae (integrable_finsetSum s (fun i _ => hi i)) hI
    filter_upwards [hs] with y hy
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hy.sum_le_tsum s (fun i _ => hpos i y)) (hWp y)
  have hn : Summable (fun i => ∫ y, ‖W y * F i y‖ ∂ν) := by
    simpa only [Real.norm_of_nonneg (hp _ _)] using hsum
  have h := hasSum_integral_of_summable_integral_norm hi hn
  simpa only [tsum_mul_left] using And.intro hi h
end Coulomb

open scoped Classical
namespace Coulomb
lemma coreInteractionDensity_integrand_integrable {m : ℕ} (u : H1Vector m)
    (d : Space → ℝ) (hd : Integrable d) (s : Spins m) (i : Fin m) :
    Integrable (fun x => (∫ z, coulombKernel (z-position x i)*d z)*‖u.value s x‖^2) := by
  apply (u.coulomb_density_prod_integrable s i d hd).integral_prod_left.congr
  filter_upwards [] with x
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [coulombKernel_sub_comm z]
  ring

lemma coreInteractionDensity_eq {m : ℕ} (u : H1Vector m)
    (d : Space → ℝ) (hd : Integrable d) :
    coreInteractionDensity u d = ∫ z, coreCoulombPotential u z*d z := by
  rw [coreCoulombPotential_fubini u d hd]
  unfold coreInteractionDensity
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => coreInteractionDensity_integrand_integrable u d hd s i)]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [coulombKernel_sub_comm]

lemma finiteFermiDensity_integrable {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (lam : ι → ℝ) :
    Integrable (finiteFermiDensity v lam) := by
  apply integrable_finsetSum
  intro i _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro s _
  exact ((hv i s).continuous.memLp_of_hasCompactSupport (hC i s) (p := 2)).integrable_norm_pow (by norm_num)

lemma attraction_nonneg {M : ℕ} (S : Nuclei M) (x : Space) : 0 ≤ attraction S x := by
  exact Finset.sum_nonneg (fun j _ => mul_nonneg ((by norm_num : (0:ℝ)≤1).trans (S.charge_ge_one j))
    (coulombKernel_nonneg _))

lemma attraction_measurable {M : ℕ} (S : Nuclei M) : Measurable (attraction S) := by
  unfold attraction
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (coulombKernel_measurable.comp (measurable_id.sub measurable_const)))

theorem infinite_fermi_core_trial {ι : Type*} [Countable ι] {M m : ℕ}
    (S : Nuclei M) (u : H1Vector m) (hu : Antisymmetric u) (hm : mass u = 1)
    (A B : Set Space) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hsu : SpatiallySupported u A) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (hsv : ∀ a s x, x ∉ B → v a x s = 0)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∀ i, lam i ≤ 1)
    (d : Space → ℝ) (hd : Integrable d)
    (hseries : ∀ᵐ x ∂volume, Summable (fun i => lam i*∑ s, ‖v i x s‖^2))
    (hdensity : (fun x => ∑' i, lam i*∑ s, ‖v i x s‖^2) =ᵐ[volume] d)
    (hN : Integrable (fun x => attraction S x*d x))
    (hD : Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(d xy.1*d xy.2)))
    (hT : Summable (fun i => lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧
      form S ψ ≤ form S u +
      ((1/2:ℝ)*(∑' i, lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2) -
      (∫ x, attraction S x*d x) +
      (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(d xy.1*d xy.2))) +
      (∫ x, coreCoulombPotential u x*d x) + ε := by
  classical
  let f (i : ι) (x : Space) := lam i*∑ s, ‖v i x s‖^2
  have hf (i : ι) : AEStronglyMeasurable (f i) volume := by
    apply Continuous.aestronglyMeasurable
    exact continuous_const.mul (continuous_finsetSum _ (fun s _ => (hv i s).continuous.norm.pow 2))
  have hp (i : ι) (x : Space) : 0 ≤ f i x :=
    mul_nonneg (h0 i) (Finset.sum_nonneg (fun s _ => sq_nonneg _))
  have hNp : Integrable (fun x => attraction S x*∑' i, f i x) := by
    apply hN.congr
    filter_upwards [hdensity] with x hx
    rw [hx]
  have hns := (weighted_series_integrable_hasSum hf hp hseries
    (attraction_measurable S).aestronglyMeasurable (attraction_nonneg S) hNp).2
  have heN : (∫ x, attraction S x*∑' i, f i x) = ∫ x, attraction S x*d x := by
    apply integral_congr_ae
    filter_upwards [hdensity] with x hx
    rw [hx]
  rw [heN] at hns
  have hevent : ∀ᶠ F : Finset ι in atTop,
      (∫ x, attraction S x*d x)-ε < ∑ i ∈ F, ∫ x, attraction S x*f i x :=
    hns (eventually_gt_nhds (sub_lt_self _ hε))
  obtain ⟨F,hF⟩ := hevent.exists
  let vF : F → Space → Fin 2 → ℂ := fun i => v i
  let lF : F → ℝ := fun i => lam i
  let dF := finiteFermiDensity vF lF
  have hdF (x : Space) : dF x = ∑ i ∈ F, f i x := by
    exact Finset.sum_coe_sort F (fun i => f i x)
  have hpF (x : Space) : 0 ≤ dF x := by rw [hdF]; exact Finset.sum_nonneg (fun i _ => hp i x)
  have hle : ∀ᵐ x ∂volume, dF x ≤ d x := by
    filter_upwards [hseries,hdensity] with x hx hy
    rw [hdF,← hy]
    exact hx.sum_le_tsum F (fun i _ => hp i x)
  have hdi := finiteFermiDensity_integrable vF (fun a => hv a) (fun a => hC a) lF
  have hfm : AEStronglyMeasurable dF volume := hdi.1
  have hNi := finiteFermiDensity_nuclear_integrable S vF (fun a => hv a) (fun a => hC a) lF
  have hFinN : (∫ x, attraction S x*dF x) = ∑ i ∈ F, ∫ x, attraction S x*f i x := by
    simp only [hdF,Finset.mul_sum]
    exact integral_finsetSum F (fun i _ => (weighted_series_integrable_hasSum hf hp hseries
      (attraction_measurable S).aestronglyMeasurable (attraction_nonneg S) hNp).1 i)
  have hpair : ∀ᵐ xy ∂(volume : Measure Space).prod volume,
      coulombKernel (xy.1-xy.2)*(dF xy.1*dF xy.2) ≤
      coulombKernel (xy.1-xy.2)*(d xy.1*d xy.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hle, Measure.quasiMeasurePreserving_snd.ae hle] with xy hx hy
    exact mul_le_mul_of_nonneg_left (mul_le_mul hx hy (hpF _) ((hpF _).trans hx)) (coulombKernel_nonneg _)
  have hDi : Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(dF xy.1*dF xy.2)) := by
    apply hD.mono' (((coulombKernel_measurable.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).mul
      (hfm.comp_fst.mul hfm.comp_snd))
    filter_upwards [hpair] with xy hxy
    change ‖coulombKernel (xy.1-xy.2)*(dF xy.1*dF xy.2)‖ ≤ _
    rwa [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (mul_nonneg (hpF _) (hpF _)))]
  have hDbound := integral_mono_ae hDi hD hpair
  have hCoreBound := integral_mono_ae (coreCoulombPotential_mul_integrable u dF hdi)
    (coreCoulombPotential_mul_integrable u d hd) (hle.mono (fun x hx =>
      mul_le_mul_of_nonneg_left hx (coreCoulombPotential_nonneg u x)))
  have hTbound : (∑ i : F, lF i * ∑ s, ∑ b : Fin 3,
      ∫ x : Space, ‖fderiv ℝ (fun y => vF i y s) x (EuclideanSpace.single b 1)‖^2) ≤
      ∑' i, lam i * ∑ s, ∑ b : Fin 3,
      ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2 := by
    dsimp only [vF,lF]
    rw [Finset.sum_coe_sort F (fun i => lam i * ∑ s, ∑ b : Fin 3,
      ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2)]
    apply hT.sum_le_tsum
    intro i _
    exact mul_nonneg (h0 i) (Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun b _ =>
      integral_nonneg (fun x => sq_nonneg _))))
  obtain ⟨n,ψ,hψa,hψm,hψe⟩ := finite_fermi_core_trial S u hu hm A B hA hB hAB hsu vF
    (fun a => hv a) (fun a => hC a) (fun a => hsv a)
    (fun a b => by
      by_cases hab : a = b
      · subst b
        simpa [vF] using ho a a
      · have hval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
        simpa only [vF, ite_eq_right hab, ite_eq_right hval] using ho a b)
    lF (fun a => h0 a) (fun a => h1 a)
  refine ⟨n,ψ,hψa,hψm,?_⟩
  rw [coreInteractionDensity_eq u dF hdi] at hψe
  rw [← hFinN] at hF
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate

end

end OAI
