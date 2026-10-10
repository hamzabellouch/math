import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeManifoldPairingInitial

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization ManifoldKernelExtension Set MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal

lemma weight_of_dist_bound {Y : Type*} [PseudoMetricSpace Y] (n : ℕ)
    {t C r : ℝ} (ht : 0 < t) (hC : 1 ≤ C) (_hr : 0 ≤ r) (x y : Y)
    (hb : dist x y ≤ C*r) :
    VolterraBounds.weight n t x y ≤ C ^ n*(1+r/Real.sqrt t)^n := by
  unfold VolterraBounds.weight
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hh := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg t)
  rw [mul_div_assoc] at hh
  nlinarith

variable {X B : Type*} [MetricSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [NormedAddCommGroup B]

omit [IsManifold Model ∞ X] in

lemma push_weighted_gaussian (p : X) (L : Set Space)
    (C : ℝ≥0)
    (hLip : LipschitzOnWith C (extChartAt Model p).symm L)
    (K : Space × Space → B) (hsupp : Function.support K ⊆ L ×ˢ L)
    (n : ℕ) {a t M : ℝ} (ha : 0 < a) (ht : 0 < t) (hM : 0 ≤ M)
    (hK : ∀ q y, ‖K (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) (x y : X) :
    VolterraBounds.weight n t x y * ‖push p K (x,y)‖ ≤
      (max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))*
        FlatHeat.heat (2*a*t) (extChartAt Model p y-extChartAt Model p x) := by
  let e := extChartAt Model p
  have hfactor : 0 ≤ (max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ))) := by positivity
  by_cases hxy : (x,y) ∈ e.source ×ˢ e.source
  · rw [push,ite_eq_left hxy]
    by_cases hz : (e x,e y) ∈ Function.support K
    · have hs := hsupp hz
      have hd : dist x y ≤ (max (C:ℝ) 1)*‖e y-e x‖ := by
        have hb := hLip.dist_le_mul (e x) hs.1 (e y) hs.2
        rw [e.left_inv hxy.1,e.left_inv hxy.2] at hb
        exact hb.trans (by rw [dist_comm,dist_eq_norm]; gcongr; exact le_max_left _ _)
      have hw := weight_of_dist_bound n ht (le_max_right (C:ℝ) 1) (norm_nonneg (e y-e x)) x y hd
      calc
        _ ≤ ((max (C:ℝ) 1)^n*(1+‖e y-e x‖/Real.sqrt t)^n)*(M*FlatHeat.heat (a*t) (e y-e x)) :=
          mul_le_mul hw (hK (e x) (e y)) (norm_nonneg _) (by positivity)
        _ = ((max (C:ℝ) 1)^n*M)*((1+‖e y-e x‖/Real.sqrt t)^n*FlatHeat.heat (a*t) (e y-e x)) := by ring
        _ ≤ _ := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (FlatHeat.weighted_heat_bound n ha ht (e y-e x)) (show 0 ≤ (max (C:ℝ) 1)^n*M by positivity)
    · rw [Function.notMem_support.mp hz,norm_zero,mul_zero]
      exact mul_nonneg hfactor (FlatHeat.heat_nonneg _ _)
  · rw [push,ite_eq_right hxy,norm_zero,mul_zero]
    exact mul_nonneg hfactor (FlatHeat.heat_nonneg _ _)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization ManifoldKernelExtension Set MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal
variable {X B : Type*} [MetricSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [NormedAddCommGroup B]

omit [IsManifold Model ∞ X] in
lemma push_continuous (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (K : Space × Space → B)
    (hK : Continuous K) (hsupp : Function.support K ⊆ L ×ˢ L) :
    Continuous (push p K) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hh := push_joint_continuousAt p (fun _ : Unit => K) (L ×ˢ L) (hL.prod hL)
    (fun _ h => ⟨hLt h.1,hLt h.2⟩) (fun _ => hsupp) ()
    (fun w => hK.continuousAt.comp continuousAt_snd) z
  exact hh.comp (continuousAt_const.prodMk continuousAt_id)

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

include hs ht in

lemma push_gaussian_row (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (C : ℝ≥0)
    (hLip : LipschitzOnWith C (extChartAt Model p).symm L)
    (D : ℝ) (hD : 0 ≤ D) (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (K : Space × Space → B) (hKc : Continuous K) (hsupp : Function.support K ⊆ L ×ˢ L)
    (n : ℕ) {a t M : ℝ} (ha : 0 < a) (htp : 0 < t) (hM : 0 ≤ M)
    (hK : ∀ q y, ‖K (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) (x : X) :
    Integrable (fun y => VolterraBounds.weight n t x y*‖push p K (x,y)‖) (geometricVolume A J α) ∧
    (∫ y, VolterraBounds.weight n t x y*‖push p K (x,y)‖ ∂geometricVolume A J α) ≤
      D*((max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))) := by
  let c := (max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  let f := fun y => VolterraBounds.weight n t x y*‖push p K (x,y)‖
  have hf : Continuous f := (VolterraBounds.weight_continuous n t x).mul
    (((push_continuous p L hL hLt K hKc hsupp).comp (continuous_const.prodMk continuous_id)).norm)
  have hf0 (y : X) : 0 ≤ f y := mul_nonneg (VolterraBounds.weight_pos n htp x y).le (norm_nonneg _)
  let := geometricVolume_finite A J α hs ht
  refine ⟨hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
  have hfs : Function.support f ⊆ (extChartAt Model p).symm '' L := by
    intro y hy
    have hk : (x,y) ∈ Function.support (push p K) := by
      intro he
      exact hy (by dsimp [f]; rw [he,norm_zero,mul_zero])
    obtain ⟨z,hz,he⟩ := support_push p K (L ×ˢ L) hsupp hk
    exact ⟨z.2,hz.2,congrArg Prod.snd he⟩
  have hg : Integrable (fun z : Space => c*FlatHeat.heat (2*a*t) (z-extChartAt Model p x)) :=
    ((FlatHeat.heat_integrable (by positivity : 0 < 2*a*t)).comp_sub_right _).const_mul c
  have hb := integral_chart_bound J α hs ht A p L hL hLt D hD hDb f hf hf0 hfs _ hg
    (fun z => mul_nonneg hc0 (FlatHeat.heat_nonneg _ _)) (fun z hz => by
      have hp := push_weighted_gaussian p L C hLip K hsupp n ha htp hM hK x ((extChartAt Model p).symm z)
      simpa only [(extChartAt Model p).right_inv hz] using hp)
  convert hb using 1
  rw [integral_const_mul,integral_sub_right_eq_self,FlatHeat.heat_integral (by positivity),mul_one]

include hs ht in

lemma push_gaussian_col (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (C : ℝ≥0)
    (hLip : LipschitzOnWith C (extChartAt Model p).symm L)
    (D : ℝ) (hD : 0 ≤ D) (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (K : Space × Space → B) (hKc : Continuous K) (hsupp : Function.support K ⊆ L ×ˢ L)
    (n : ℕ) {a t M : ℝ} (ha : 0 < a) (htp : 0 < t) (hM : 0 ≤ M)
    (hK : ∀ q y, ‖K (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) (y : X) :
    Integrable (fun x => VolterraBounds.weight n t x y*‖push p K (x,y)‖) (geometricVolume A J α) ∧
    (∫ x, VolterraBounds.weight n t x y*‖push p K (x,y)‖ ∂geometricVolume A J α) ≤
      D*((max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))) := by
  let c := (max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  let f := fun x => VolterraBounds.weight n t x y*‖push p K (x,y)‖
  have hw : Continuous (fun x => VolterraBounds.weight n t x y) := by
    unfold VolterraBounds.weight
    fun_prop
  have hf : Continuous f := hw.mul
    (((push_continuous p L hL hLt K hKc hsupp).comp (continuous_id.prodMk continuous_const)).norm)
  have hf0 (x : X) : 0 ≤ f x := mul_nonneg (VolterraBounds.weight_pos n htp x y).le (norm_nonneg _)
  let := geometricVolume_finite A J α hs ht
  refine ⟨hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
  have hfs : Function.support f ⊆ (extChartAt Model p).symm '' L := by
    intro x hx
    have hk : (x,y) ∈ Function.support (push p K) := by
      intro he
      exact hx (by dsimp [f]; rw [he,norm_zero,mul_zero])
    obtain ⟨z,hz,he⟩ := support_push p K (L ×ˢ L) hsupp hk
    exact ⟨z.1,hz.1,congrArg Prod.fst he⟩
  have hg : Integrable (fun z : Space => c*FlatHeat.heat (2*a*t) (extChartAt Model p y-z)) :=
    ((FlatHeat.heat_integrable (by positivity : 0 < 2*a*t)).comp_sub_left _).const_mul c
  have hb := integral_chart_bound J α hs ht A p L hL hLt D hD hDb f hf hf0 hfs _ hg
    (fun z => mul_nonneg hc0 (FlatHeat.heat_nonneg _ _)) (fun z hz => by
      have hp := push_weighted_gaussian p L C hLip K hsupp n ha htp hM hK ((extChartAt Model p).symm z) y
      simpa only [(extChartAt Model p).right_inv hz] using hp)
  convert hb using 1
  rw [integral_const_mul,integral_sub_left_eq_self,FlatHeat.heat_integral (by positivity),mul_one]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
