import OAI.Geometry.PinnedDistances.CutGeometry

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory Cuts
open scoped BigOperators
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma cutLength_bound (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (C : Finset P) :
    |d.cutLength f C|≤2*d.radius*|f C| := by
  rw [← Real.norm_eq_abs,cutLength]
  apply (norm_integral_le_integral_norm _).trans
  exact integral_bound_supported d.radius_nonneg (d.integrable_cutAt f hfu hfs C).norm
    (d.cutAt_bound f C) (fun r hr => by rw [d.cutAt_vanish f hfu hfs C r hr,norm_zero])

lemma sum_cutLength_univ (f : Finset P → ℝ) (g : Finset P → ℝ) :
    (∑ C ∈ d.allCuts, d.cutLength f C*g C)=∑ C, d.cutLength f C*g C := by
  exact Finset.sum_subset (Finset.subset_univ _) (fun C _ hC => by rw [d.cutLength_outside f C hC,zero_mul])

lemma cutLength_mul (f g : Finset P → ℝ) (C : Finset P) :
    d.cutLength (fun B => f B*g B) C=d.cutLength f C*g C := by
  unfold cutLength
  rw [← integral_mul_const]
  congr 1
  funext r
  simp only [cutAt,ite_mul,zero_mul]

lemma cutLength_difference_le (f g : Finset P → ℝ)
    (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0)
    (hgu : g Finset.univ=0) (hgs : ∀ x, g {x}=0) (C : Finset P) :
    |d.cutLength f C-d.cutLength g C|≤d.cutLength (fun B => |f B-g B|) C := by
  rw [cutLength,cutLength,← integral_sub (d.integrable_cutAt f hfu hfs C) (d.integrable_cutAt g hgu hgs C)]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans_eq
  congr 1
  funext r
  simp only [cutAt,Real.norm_eq_abs]
  split_ifs <;> simp

lemma distance_cut_difference (f g : Finset P → ℝ)
    (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0)
    (hgu : g Finset.univ=0) (hgs : ∀ x, g {x}=0) (x y : P) :
    |distance d.allCuts (d.cutLength f) x y-distance d.allCuts (d.cutLength g) x y|≤
      ∑ C ∈ d.allCuts, d.cutLength (fun B => |f B-g B|) C := by
  unfold distance
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro C hC
  rw [← sub_mul,abs_mul,abs_abs]
  have hi : |ind C x-ind C y|≤1 := by unfold ind; split_ifs <;> norm_num
  have h1 := mul_le_mul_of_nonneg_right (d.cutLength_difference_le f g hfu hfs hgu hgs C) (abs_nonneg (ind C x-ind C y))
  exact h1.trans (by simpa using mul_le_mul_of_nonneg_left hi (d.cutLength_nonneg _ (fun B => abs_nonneg _) C))

lemma root_cut_difference (f g : Finset P → ℝ)
    (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0)
    (hgu : g Finset.univ=0) (hgs : ∀ x, g {x}=0) (y : P) :
    |rootDistance d.allCuts (d.cutLength f) y-rootDistance d.allCuts (d.cutLength g) y|≤
      ∑ C ∈ d.allCuts, d.cutLength (fun B => |f B-g B|) C := by
  unfold rootDistance
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro C hC
  rw [← sub_mul,abs_mul]
  have hi : |ind C y|≤1 := by unfold ind; split_ifs <;> norm_num
  have h1 := mul_le_mul_of_nonneg_right (d.cutLength_difference_le f g hfu hfs hgu hgs C) (abs_nonneg (ind C y))
  exact h1.trans (by simpa using mul_le_mul_of_nonneg_left hi (d.cutLength_nonneg _ (fun B => abs_nonneg _) C))

lemma cost_cut_formula (f : Finset P → ℝ) (p a : P → ℝ) :
    cost d.allCuts (d.cutLength f) p a =
      ∑ C ∈ d.allCuts, d.cutLength (fun B => f B*|Cuts.mass p B-Cuts.mass a B|) C := by
  simp only [cost,d.cutLength_mul]

variable {Ω : Type u2} [MeasurableSpace Ω] (D : Ω → Depth P)
    (hD : ∀ x y, Measurable (fun ω => (D ω).value x y))
include hD
lemma measurable_cutLength_param (f : Finset P → ℝ) (C : Finset P) :
    Measurable (fun ω => (D ω).cutLength f C) := by
  have hm : Measurable (fun p : Ω×ℝ => (D p.1).cutAt f C p.2) :=
    (measurable_of_finite (fun s : Finset (Finset P) => if C ∈ s then f C else 0)).comp
    (measurable_cells_param (P:=P) (Ω:=Ω×ℝ) (fun p : Ω×ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma integrable_cutLength_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (f : Finset P → ℝ) (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0) (C : Finset P) :
    Integrable (fun ω => (D ω).cutLength f C) μ := by
  apply (((integrable_radius_param D hi).const_mul 2).mul_const |f C|).mono'
    (measurable_cutLength_param D hD f C).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => (D ω).cutLength_bound f hfu hfs C)

lemma integrable_cutSum_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (f g : Finset P → ℝ) (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0) :
    Integrable (fun ω => ∑ C ∈ (D ω).allCuts, (D ω).cutLength f C*g C) μ := by
  simp only [sum_cutLength_univ]
  exact integrable_finsetSum _ (fun C _ => (integrable_cutLength_param D hD hi f hfu hfs C).mul_const (g C))

lemma integrable_cutDistance_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (f : Finset P → ℝ) (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0) (x y : P) :
    Integrable (fun ω => distance (D ω).allCuts ((D ω).cutLength f) x y) μ :=
  integrable_cutSum_param D hD hi f (fun B => |ind B x-ind B y|) hfu hfs

lemma integrable_rootDistance_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (f : Finset P → ℝ) (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0) (y : P) :
    Integrable (fun ω => rootDistance (D ω).allCuts ((D ω).cutLength f) y) μ :=
  integrable_cutSum_param D hD hi f (fun B => ind B y) hfu hfs
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Cuts
lemma tent_lipschitzWith (δ : ℝ) : LipschitzWith 1 (tent δ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using tent_lipschitz δ x y
end WeakPinned.Cuts

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance Cuts
open scoped BigOperators
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable {K : Type u4} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
include h₁ h₂

lemma arch_cross_defect (v : NumberField.InfinitePlace K) (x y z : P)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (t : K)
    (hy : (Z₁ x-Z₁ y)*(Z₂ x-Z₂ y)=t) (hz : (Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t) :
    (fun ω => (arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-
      ((arch Z₂ v ω).value y z+(Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))))) =ᵐ[Grid.fullLaw]
    (fun ω => Grid.error ω (v.embedding (Z₁ y)) (v.embedding (Z₁ z))-
      Grid.error ω (v.embedding (Z₁ x)) (v.embedding (Z₁ z))-
      Grid.error ω (v.embedding (Z₂ y)) (v.embedding (Z₂ z))) := by
  have he := Arithmetic.raw_cross_fiber Z₁ Z₂ h₁ h₂ v.val x y z hxy hxz hyz t hy hz
  filter_upwards [arch_value_ae Z₁ h₁ v hyz,arch_value_ae Z₁ h₁ v hxz,arch_value_ae Z₂ h₂ v hyz] with ω ha hb hc
  rw [ha,hb,hc]
  simp only [Grid.error,← map_sub,NumberField.InfinitePlace.norm_embedding_eq]
  change -Real.log (v (Z₂ y-Z₂ z)) = -Real.log (v (Z₁ y-Z₁ z)) -
    -Real.log (v (Z₁ x-Z₁ z)) - Real.log (v t) - -Real.log (v (Z₁ x-Z₁ y)) at he
  linarith

lemma arch_cross_defect_mean (v : NumberField.InfinitePlace K) (x y z : P)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (t : K)
    (hy : (Z₁ x-Z₁ y)*(Z₂ x-Z₂ y)=t) (hz : (Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t) :
    (∫ ω, |(arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-
      ((arch Z₂ v ω).value y z+(Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))))| ∂Grid.fullLaw)≤12 := by
  have hEq := arch_cross_defect Z₁ Z₂ h₁ h₂ v x y z hxy hxz hyz t hy hz
  have heq := integral_congr_ae (hEq.fun_comp (abs : ℝ → ℝ))
  dsimp only [Function.comp_def] at heq
  rw [heq]
  have ha := Grid.error_integrable_full (embedding_ne Z₁ h₁ v hyz)
  have hb := Grid.error_integrable_full (embedding_ne Z₁ h₁ v hxz)
  have hc := Grid.error_integrable_full (embedding_ne Z₂ h₂ v hyz)
  have hh := integral_mono ((ha.sub hb).sub hc).abs ((ha.abs.add hb.abs).add hc.abs) (fun ω =>
    (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl))
  dsimp only [Pi.sub_apply,Pi.add_apply] at hh
  have hAdd := integral_add (ha.abs.add hb.abs) hc.abs
  have hAdd2 := integral_add ha.abs hb.abs
  dsimp only [Pi.add_apply] at hAdd hAdd2
  rw [hAdd,hAdd2] at hh
  have h1 := Grid.mean_abs_error_full (embedding_ne Z₁ h₁ v hyz)
  have h2 := Grid.mean_abs_error_full (embedding_ne Z₁ h₁ v hxz)
  have h3 := Grid.mean_abs_error_full (embedding_ne Z₂ h₂ v hyz)
  linarith

/-- Actual local cut projection under an arithmetic fiber probability. The
atom at y is retained and the source has zero mass. -/
lemma arch_fiber_cut (v : NumberField.InfinitePlace K) (p : P → ℝ)
    (hp0 : ∀ z, 0≤p z) (hp : ∑ z, p z=1) (x y : P) (hpx : p x=0) (hpy : p y≠0)
    (t : K) (ht : ∀ z, p z≠0 → (Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t)
    (δ : ℝ) (hδ : 0≤δ) (hps : ∀ z, p z≤δ) :
    (∫ ω, |distance (arch Z₁ v ω).allCuts ((arch Z₁ v ω).cutLength (fun C => tent δ (mass p C))) x y-
      rootDistance (arch Z₂ v ω).allCuts ((arch Z₂ v ω).cutLength (fun C => tent δ (mass p C))) y| ∂Grid.fullLaw)≤12 := by
  have hxy : x≠y := fun hh => hpy (hh ▸ hpx)
  let f : Finset P → ℝ := fun C => tent δ (mass p C)
  have hfu : f Finset.univ=0 := by simp only [f,mass,hp]; exact tent_zero_right (by linarith)
  have hfs (z) : f {z}=0 := by simp only [f,mass,Finset.sum_singleton]; exact tent_zero_left (hps z)
  have hl := Depth.integrable_cutDistance_param (arch Z₁ v) (arch_measurable Z₁ h₁ v) (arch_integrable Z₁ h₁ v) f hfu hfs x y
  have hr := Depth.integrable_rootDistance_param (arch Z₂ v) (arch_measurable Z₂ h₂ v) (arch_integrable Z₂ h₂ v) f hfu hfs y
  let c := Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))
  let E : Grid.FullSample → ℝ := fun ω => ∑ z, Tail.offTwo p x y z*
    |(arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-((arch Z₂ v ω).value y z+c)|
  have hEi (z : P) : Integrable (fun ω => Tail.offTwo p x y z*
    |(arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-((arch Z₂ v ω).value y z+c)|) Grid.fullLaw :=
    ((((arch_integrable Z₁ h₁ v y z).sub (arch_integrable Z₁ h₁ v x z)).sub
      ((arch_integrable Z₂ h₂ v y z).add (integrable_const c))).abs.const_mul _)
  have hi : Integrable E Grid.fullLaw := integrable_finsetSum _ (fun z _ => hEi z)
  have hh := integral_mono (hl.sub hr).abs hi (fun ω => by
    simpa only [f,E,Pi.sub_apply,NNReal.coe_one,one_mul] using Tail.fiber_cut_error
      (arch Z₁ v ω) (arch Z₂ v ω) p hp0 hp (tent δ) 1 (tent_lipschitzWith δ)
      (tent_zero_right (by linarith)) (fun z => tent_zero_left (hps z)) (tent_symm δ) x y hpx hxy c)
  apply hh.trans
  unfold E
  rw [integral_finsetSum Finset.univ (fun z _ => hEi z)]
  simp only [integral_const_mul]
  apply le_trans (Finset.sum_le_sum (fun z _ => show Tail.offTwo p x y z* _≤12*p z from ?_))
    (by rw [← Finset.mul_sum,hp,mul_one])
  by_cases hzx : z=x
  · subst z; simp [Tail.offTwo,hpx]
  by_cases hzy : z=y
  · subst z; simp only [Tail.offTwo,or_true,reduceIte,zero_mul]; exact mul_nonneg (by norm_num) (hp0 y)
  by_cases hpz : p z=0
  · simp [Tail.offTwo,hzx,hzy,hpz]
  · simp only [Tail.offTwo,hzx,hzy,or_self,reduceIte]
    have he := arch_cross_defect_mean Z₁ Z₂ h₁ h₂ v x y z hxy (Ne.symm hzx) (Ne.symm hzy) t (ht y hpy) (ht z hpz)
    dsimp [c]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left he (hp0 z)

end WeakPinned.Global
noncomputable section

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance Cuts
open scoped BigOperators
variable {P : Type u5} [Fintype P] [DecidableEq P]
variable {K : Type u6} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
include h₁ h₂

lemma finite_fiber_cut (v : NumberField.FinitePlace K) (p : P → ℝ)
    (hp0 : ∀ z, 0≤p z) (hp : ∑ z, p z=1) (x y : P) (hpx : p x=0) (hpy : p y≠0)
    (t : K) (ht : ∀ z, p z≠0 → (Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t)
    (δ : ℝ) (hδ : 0≤δ) (hps : ∀ z, p z≤δ) :
    |distance (finite Z₁ h₁ v).allCuts ((finite Z₁ h₁ v).cutLength (fun C => tent δ (mass p C))) x y-
      rootDistance (finite Z₂ h₂ v).allCuts ((finite Z₂ h₂ v).cutLength (fun C => tent δ (mass p C))) y|≤0 := by
  have hxy : x≠y := fun hh => hpy (hh ▸ hpx)
  let c := Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))
  have hh := Tail.fiber_cut_error (finite Z₁ h₁ v) (finite Z₂ h₂ v) p hp0 hp (tent δ) 1
    (tent_lipschitzWith δ) (tent_zero_right (by linarith)) (fun z => tent_zero_left (hps z))
    (tent_symm δ) x y hpx hxy c
  simp only [NNReal.coe_one,one_mul] at hh
  apply hh.trans
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro z _
  by_cases hxz : x=z
  · subst z; simp [Tail.offTwo]
  by_cases hyz : y=z
  · subst z; simp [Tail.offTwo]
  by_cases hpz : p z=0
  · simp [Tail.offTwo,hpz]
  · have he := Arithmetic.raw_cross_fiber Z₁ Z₂ h₁ h₂ v.val x y z hxy hxz hyz t (ht y hpy) (ht z hpz)
    change -Real.log (v (Z₂ y-Z₂ z)) = -Real.log (v (Z₁ y-Z₁ z)) -
      -Real.log (v (Z₁ x-Z₁ z)) - Real.log (v t) - -Real.log (v (Z₁ x-Z₁ y)) at he
    suffices (finite Z₁ h₁ v).value y z-(finite Z₁ h₁ v).value x z-
      ((finite Z₂ h₂ v).value y z+c)=0 by rw [this,abs_zero,mul_zero]
    simp only [finite,ite_eq_right hyz,ite_eq_right hxz,c]
    linarith

omit [NumberField K] in
lemma integrable_arch_cut_error (v : NumberField.InfinitePlace K) (p : P → ℝ)
    (δ : ℝ) (hpu : tent δ (mass p Finset.univ)=0) (hps : ∀ x, tent δ (mass p {x})=0)
    (x y : P) :
    Integrable (fun ω => |distance (arch Z₁ v ω).allCuts ((arch Z₁ v ω).cutLength (fun C => tent δ (mass p C))) x y-
      rootDistance (arch Z₂ v ω).allCuts ((arch Z₂ v ω).cutLength (fun C => tent δ (mass p C))) y|) Grid.fullLaw := by
  exact ((Depth.integrable_cutDistance_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) _ hpu hps x y).sub
    (Depth.integrable_rootDistance_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
      (arch_integrable Z₂ h₂ v) _ hpu hps y)).abs

variable {I : Type u7} [Fintype I]
omit Z₁ Z₂ h₁ h₂ in
def fiberCutDiscrepancy (w : I → ℝ) (p : I → P → ℝ) (src : I → P) (δ : ℝ) (d d' : Depth P) : ℝ :=
  ∑ i, w i*∑ y, p i y*|distance d.allCuts (d.cutLength (fun C => tent δ (mass (p i) C))) (src i) y-
    rootDistance d'.allCuts (d'.cutLength (fun C => tent δ (mass (p i) C))) y|

omit [NumberField K] in
lemma fiber_cut_discrepancy_integrable (w : I → ℝ) (p : I → P → ℝ) (src : I → P)
    (hp : ∀ i, ∑ z, p i z=1) (δ : ℝ) (hδ : 0≤δ) (hps : ∀ i z, p i z≤δ) :
    AverageIntegrable Z₁ Z₂ (fiberCutDiscrepancy w p src δ) := by
  intro v
  apply integrable_finsetSum
  intro i _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro y _
  apply Integrable.const_mul
  exact integrable_arch_cut_error Z₁ Z₂ h₁ h₂ v (p i) δ
    (by simp only [mass,hp]; exact tent_zero_right (by linarith))
    (fun z => by simp only [mass,Finset.sum_singleton]; exact tent_zero_left (hps i z)) (src i) y

/-- A bounded projection estimate with exact fiber atoms and no restriction on
    degree, finite places or variation of number fields. -/
lemma arithmetic_fiber_cut (w : I → ℝ) (p : I → P → ℝ) (src : I → P) (t : I → K)
    (hw : ∀ i, 0≤w i) (hW : ∑ i, w i=1) (hp0 : ∀ i z, 0≤p i z)
    (hp : ∀ i, ∑ z, p i z=1) (hpx : ∀ i, p i (src i)=0)
    (ht : ∀ i z, p i z≠0 → (Z₁ (src i)-Z₁ z)*(Z₂ (src i)-Z₂ z)=t i)
    (δ : ℝ) (hδ : 0≤δ) (hps : ∀ i z, p i z≤δ) :
    average Z₁ Z₂ h₁ h₂ (fiberCutDiscrepancy w p src δ)≤12 := by
  classical
  have hi (v : NumberField.InfinitePlace K) (i : I) (y : P) :=
    integrable_arch_cut_error Z₁ Z₂ h₁ h₂ v (p i) δ
      (by simp only [mass,hp]; exact tent_zero_right (by linarith))
      (fun z => by simp only [mass,Finset.sum_singleton]; exact tent_zero_left (hps i z)) (src i) y
  have ha (v : NumberField.InfinitePlace K) :
      (∫ ω, fiberCutDiscrepancy w p src δ (arch Z₁ v ω) (arch Z₂ v ω) ∂Grid.fullLaw)≤12 := by
    unfold fiberCutDiscrepancy
    rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum _ (fun y _ => (hi v i y).const_mul (p i y))).const_mul (w i))]
    simp only [integral_const_mul]
    have he (i : I) : (∫ ω, ∑ y, p i y*|distance (arch Z₁ v ω).allCuts
        ((arch Z₁ v ω).cutLength (fun C => tent δ (mass (p i) C))) (src i) y-
        rootDistance (arch Z₂ v ω).allCuts ((arch Z₂ v ω).cutLength (fun C => tent δ (mass (p i) C))) y| ∂Grid.fullLaw)≤12 := by
      rw [integral_finsetSum _ (fun y _ => (hi v i y).const_mul (p i y))]
      simp only [integral_const_mul]
      calc
        _ ≤ ∑ y, p i y*12 := Finset.sum_le_sum (fun y _ => by
          by_cases hy : p i y=0
          · simp [hy]
          · exact mul_le_mul_of_nonneg_left (arch_fiber_cut Z₁ Z₂ h₁ h₂ v (p i) (hp0 i) (hp i)
              (src i) y (hpx i) hy (t i) (ht i) δ hδ (hps i)) (hp0 i y))
        _ = 12 := by rw [← Finset.sum_mul,hp,one_mul]
    exact (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (he i) (hw i))).trans_eq
      (by rw [← Finset.sum_mul,hW,one_mul])
  have hv (v : NumberField.FinitePlace K) :
      fiberCutDiscrepancy w p src δ (finite Z₁ h₁ v) (finite Z₂ h₂ v)≤0 := by
    apply Finset.sum_nonpos
    intro i _
    apply mul_nonpos_of_nonneg_of_nonpos (hw i)
    apply Finset.sum_nonpos
    intro y _
    by_cases hy : p i y=0
    · simp [hy]
    · exact mul_nonpos_of_nonneg_of_nonpos (hp0 i y) (finite_fiber_cut Z₁ Z₂ h₁ h₂ v
        (p i) (hp0 i) (hp i) (src i) y (hpx i) hy (t i) (ht i) δ hδ (hps i))
  change placeAverage (placeUnion Z₁ Z₂ h₁ h₂) _ _≤12
  have hh := placeAverage_mono (placeUnion Z₁ Z₂ h₁ h₂) ha (fun v _ => hv v)
  rwa [placeAverage_arch_const] at hh
end WeakPinned.Global
noncomputable section
namespace WeakPinned.Cuts
open MeasureTheory Hierarchy Variance
open scoped BigOperators
variable {P : Type u8} [Fintype P] [DecidableEq P]

lemma mass_complement (p : P → ℝ) (hp : ∑ x, p x=1) (C : Finset P) : mass p Cᶜ=1-mass p C := by
  have hh := Finset.sum_compl_add_sum C p
  rw [hp] at hh
  exact eq_sub_of_add_eq hh

omit [Fintype P] [DecidableEq P] in
lemma mass_small (p : P → ℝ) (δ : ℝ) (hδ : 0≤δ) (hp : ∀ x, p x≤δ)
    (C : Finset P) (hC : C.card≤1) : mass p C≤δ := by
  have hh := Finset.sum_le_sum (s:=C) (fun x _ => hp x)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  have hc : (C.card:ℝ)≤1 := by exact_mod_cast hC
  exact hh.trans (by nlinarith)

omit [Fintype P] [DecidableEq P] in
lemma cutError_small (p a : P → ℝ) (δ : ℝ) (hδ : 0≤δ)
    (hp : ∀ x, p x≤δ) (ha : ∀ x, a x≤δ) (C : Finset P) (hC : C.card≤1) :
    cutError δ (mass p C) (mass a C)=0 := by
  simp only [cutError,tent_zero_left (mass_small p δ hδ hp C hC),
    tent_zero_left (mass_small a δ hδ ha C hC),sub_self,abs_zero,zero_mul,add_zero]

lemma cutError_complement (p a : P → ℝ) (hp : ∑ x, p x=1) (ha : ∑ x, a x=1)
    (δ : ℝ) (C : Finset P) :
    cutError δ (mass p Cᶜ) (mass a Cᶜ)=cutError δ (mass p C) (mass a C) := by
  rw [mass_complement p hp,mass_complement a ha,cutError_symm]

def charge (d : Depth P) (δ : ℝ) (p a : P → ℝ) : ℝ :=
  ∑ C ∈ d.allCuts, d.cutLength (fun B => cutError δ (mass p B) (mass a B)) C

lemma charge_nonneg (d : Depth P) (δ : ℝ) (p a : P → ℝ) : 0≤charge d δ p a :=
  Finset.sum_nonneg (fun C _ => d.cutLength_nonneg _ (fun _ => cutError_nonneg _ _ _) C)

lemma charge_occurrence (d : Depth P) (hn : 2≤Fintype.card P) (δ : ℝ) (hδ : 0≤δ)
    (p a : P → ℝ) (hp : ∑ x, p x=1) (ha : ∑ x, a x=1)
    (hps : ∀ x, p x≤δ) (has : ∀ x, a x≤δ) :
    charge d δ p a=weightedIntegral d.mass (fun C => cutError δ (mass p C) (mass a C)) := by
  symm
  exact d.symmetric_integral_cut_sum hn _ (cutError_small p a δ hδ hps has)
    (cutError_complement p a hp ha δ)

omit [DecidableEq P] in
lemma tent_mass_univ (p : P → ℝ) (hp : ∑ x, p x=1) (δ : ℝ) (hδ : 0≤δ) :
    tent δ (mass p Finset.univ)=0 := by
  simp only [mass,hp]
  exact tent_zero_right (by linarith)
omit [Fintype P] [DecidableEq P] in
lemma tent_mass_singleton (p : P → ℝ) (δ : ℝ) (hp : ∀ x, p x≤δ) (x : P) :
    tent δ (mass p {x})=0 := by
  simp only [mass,Finset.sum_singleton]
  exact tent_zero_left (hp x)

end WeakPinned.Cuts
namespace WeakPinned.Hierarchy.Depth
open Cuts MeasureTheory
variable {P : Type u9} [Fintype P] [DecidableEq P]
lemma cutLength_mono (d : Depth P) (f g : Finset P → ℝ)
    (hf : f Finset.univ=0) (hfs : ∀ x, f {x}=0) (hg : g Finset.univ=0) (hgs : ∀ x, g {x}=0)
    (hfg : ∀ C, f C≤g C) (C : Finset P) : d.cutLength f C≤d.cutLength g C := by
  apply integral_mono (d.integrable_cutAt f hf hfs C) (d.integrable_cutAt g hg hgs C)
  intro r
  simp only [cutAt]
  split_ifs
  · exact hfg C
  · rfl
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Cuts
open MeasureTheory Hierarchy Variance
variable {P : Type u10} [Fintype P] [DecidableEq P]
lemma distance_change_charge (d : Depth P) (δ : ℝ) (hδ : 0≤δ) (p a : P → ℝ)
    (hp : ∑ x, p x=1) (ha : ∑ x, a x=1) (hps : ∀ x, p x≤δ) (has : ∀ x, a x≤δ) (x y : P) :
    |distance d.allCuts (d.cutLength (fun C => tent δ (mass p C))) x y-
      distance d.allCuts (d.cutLength (fun C => tent δ (mass a C))) x y|≤charge d δ p a := by
  apply (d.distance_cut_difference _ _ (tent_mass_univ p hp δ hδ) (tent_mass_singleton p δ hps)
    (tent_mass_univ a ha δ hδ) (tent_mass_singleton a δ has) x y).trans
  apply Finset.sum_le_sum
  intro C _
  apply d.cutLength_mono
  · simp only [tent_mass_univ p hp δ hδ,tent_mass_univ a ha δ hδ,sub_self,abs_zero]
  · intro z; simp only [tent_mass_singleton p δ hps,tent_mass_singleton a δ has,sub_self,abs_zero]
  · simp only [cutError,tent_mass_univ p hp δ hδ,tent_mass_univ a ha δ hδ,sub_self,abs_zero,zero_mul,add_zero]
  · intro z; exact cutError_small p a δ hδ hps has _ (by simp)
  · intro C; exact le_add_of_nonneg_right (mul_nonneg (tent_nonneg _ _) (abs_nonneg _))

lemma root_change_charge (d : Depth P) (δ : ℝ) (hδ : 0≤δ) (p a : P → ℝ)
    (hp : ∑ x, p x=1) (ha : ∑ x, a x=1) (hps : ∀ x, p x≤δ) (has : ∀ x, a x≤δ) (y : P) :
    |rootDistance d.allCuts (d.cutLength (fun C => tent δ (mass p C))) y-
      rootDistance d.allCuts (d.cutLength (fun C => tent δ (mass a C))) y|≤charge d δ p a := by
  apply (d.root_cut_difference _ _ (tent_mass_univ p hp δ hδ) (tent_mass_singleton p δ hps)
    (tent_mass_univ a ha δ hδ) (tent_mass_singleton a δ has) y).trans
  apply Finset.sum_le_sum
  intro C _
  apply d.cutLength_mono
  · simp only [tent_mass_univ p hp δ hδ,tent_mass_univ a ha δ hδ,sub_self,abs_zero]
  · intro z; simp only [tent_mass_singleton p δ hps,tent_mass_singleton a δ has,sub_self,abs_zero]
  · simp only [cutError,tent_mass_univ p hp δ hδ,tent_mass_univ a ha δ hδ,sub_self,abs_zero,zero_mul,add_zero]
  · intro z; exact cutError_small p a δ hδ hps has _ (by simp)
  · intro C; exact le_add_of_nonneg_right (mul_nonneg (tent_nonneg _ _) (abs_nonneg _))

lemma cost_le_charge (d : Depth P) (δ : ℝ) (hδ : 0≤δ) (p a : P → ℝ)
    (hp : ∑ x, p x=1) (ha : ∑ x, a x=1) (hps : ∀ x, p x≤δ) (has : ∀ x, a x≤δ) :
    cost d.allCuts (d.cutLength (fun C => tent δ (mass a C))) p a≤charge d δ p a := by
  rw [d.cost_cut_formula]
  apply Finset.sum_le_sum
  intro C _
  apply d.cutLength_mono
  · simp only [tent_mass_univ a ha δ hδ,zero_mul]
  · intro z; simp only [tent_mass_singleton a δ has,zero_mul]
  · simp only [cutError,tent_mass_univ p hp δ hδ,tent_mass_univ a ha δ hδ,sub_self,abs_zero,zero_mul,add_zero]
  · intro z; exact cutError_small p a δ hδ hps has _ (by simp)
  · intro C; exact le_add_of_nonneg_left (abs_nonneg _)
end WeakPinned.Cuts
noncomputable section

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
