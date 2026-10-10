import Mathlib
import OAI.Geometry.Cannon.Flows.NormalizedComparison
import OAI.Geometry.Cannon.ScalarLimits.IntervalAvoiding
import OAI.Geometry.Cannon.Flows.ContinuousDomain
import OAI.Geometry.Cannon.ScalarLimits.OrderedVariationPath

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology
open Set unitInterval

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification CannonStabilizer CannonVariation Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryPuncturedPathConnectedSetoid : Setoid (BasedRay D) := raySetoid D

omit [DiscreteTopology G] in
lemma boundary_punctured_pathConnected (φ : Boundary D ≃ₜ SphereTwo) (p : Boundary D) :
    IsPathConnected ({p}ᶜ : Set (Boundary D)) := by
  have hh := (CannonPaths.sphere_punctured_pathConnected (φ p)).image φ.symm.continuous
  convert hh using 1
  ext z
  constructor
  · intro hz
    refine ⟨φ z,?_,φ.symm_apply_apply z⟩
    exact fun h => hz (φ.injective h)
  · rintro ⟨w,hw,hwz⟩ heq
    apply hw
    apply φ.symm.injective
    change z = p at heq
    simpa only [φ.symm_apply_apply] using hwz.trans heq

theorem boundary_second_magnification_obstruction (φ : Boundary D ≃ₜ SphereTwo)
    (b : Boundary D) :
    let _ := visualMetricSpace D hδ
    ∀ (W : C(({b}ᶜ : Set (Boundary D)),ℝ)) (α : ℝ), 0 < α →
    (∀ K : Set (Boundary D), IsCompact K → K ⊆ ({b}ᶜ : Set (Boundary D)) → ∃ C ≥ 0,
      ∀ x y : ({b}ᶜ : Set (Boundary D)), x.val ∈ K → y.val ∈ K →
        |W x-W y| ≤ C*(dist x y)^α) →
    (∃ z w, W z ≠ W w) →
    (∀ s t : G, boundaryTranslate D ⟨δ,hδ⟩ s b ≠ boundaryTranslate D ⟨δ,hδ⟩ t b →
      ∀ z, z ≠ boundaryTranslate D ⟨δ,hδ⟩ s b → z ≠ boundaryTranslate D ⟨δ,hδ⟩ t b →
        NonconstantAt (fun z => onDomain W (boundaryTranslate D ⟨δ,hδ⟩ s⁻¹ z)) z →
        onDomain W (boundaryTranslate D ⟨δ,hδ⟩ t⁻¹ z) =
          onDomain W (boundaryTranslate D ⟨δ,hδ⟩ t⁻¹ (boundaryTranslate D ⟨δ,hδ⟩ s b))) → False := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro W α hα hholder hvar hcomp
  let ρ := boundaryAction D ⟨δ,hδ⟩
  let _ : MulAction G (Boundary D) := homAction ρ
  let E := MulAction.stabilizer G b
  obtain ⟨CG,hCG⟩ := boundary_stabilizer_linear D ⟨δ,hδ⟩ b
  have hlin : ∀ (F : Finset G) (t : ℕ), (∀ g ∈ F, g ∈ E) →
      (∀ g ∈ F, D.graph.dist 1 g ≤ t) → F.card ≤ CG*(t+1) := by
    intro F t hF ht
    exact hCG F t hF ht
  have hsub (g h : G) : D.graph.dist 1 (g*h) ≤ D.graph.dist 1 g + D.graph.dist 1 h := by
    calc
      _ ≤ D.graph.dist 1 g + D.graph.dist g (g*h) := D.connected.dist_triangle
      _ = _ := by rw [show D.graph.dist g (g*h) = D.graph.dist 1 h from
        by simpa only [mul_one] using D.dist_mul_left g 1 h]
  have hexcept : ∃ c : Boundary D, ∀ y, y ≠ b → ContractingDirection E b y → y = c := by
    by_cases he : ∃ c, c ≠ b ∧ ContractingDirection E b c
    · obtain ⟨c,hcb,hc⟩ := he
      refine ⟨c,fun y hy hdir => ?_⟩
      exact contracting_direction_unique E (D.graph.dist 1) (by simp) hsub CG hlin hy hcb hdir hc
    · refine ⟨b,fun y hy hdir => ?_⟩
      exact (he ⟨y,hy,hdir⟩).elim
  obtain ⟨c,hc⟩ := hexcept
  have hW : ContinuousOn (onDomain W) ({b}ᶜ : Set (Boundary D)) := continuousOn_onDomain W
  have hvar' : ∃ v ∈ ({b}ᶜ : Set (Boundary D)), ∃ w ∈ ({b}ᶜ : Set (Boundary D)),
      onDomain W v ≠ onDomain W w := by
    obtain ⟨v,w,hvw⟩ := hvar
    exact ⟨v.val,v.property,w.val,w.property,by simpa only [onDomain_eq _ _ v.property,onDomain_eq _ _ w.property] using hvw⟩
  obtain ⟨v₀,w₀,q,hq,hqw⟩ := ordered_variation_path _ (boundary_punctured_pathConnected D φ b)
    (onDomain W) hvar'
  have hbq : b ∉ range q := fun h => hq h rfl
  obtain ⟨O,P,hO,hOc,hP,hPc,hPO,hOb,hcO,hPv,d,hd,hdb⟩ :=
    variation_region_avoiding (onDomain W) b c hW q hbq hqw
  have hgood : ∀ y ∈ closure O, ¬ ContractingDirection E b y := by
    intro y hy hdir
    have hyb : y ≠ b := hOb hy
    exact hcO ((hc y hyb hdir) ▸ hy)
  obtain ⟨β,hβ,k,x,sig,p,F,hk,hx,hp,_hescape,_hdom,hFlim,_hFholder,hFvar⟩ :=
    boundary_holder_magnification D hδ φ {b}ᶜ O P isClosed_singleton.isOpen_compl hO hOc hOb
      hP hPc hPO W hPv α hα hholder b d hd hdb
  let v : ℕ → G := fun i => (boundaryBasedRay D (x i)).val (k i)
  let r : ℕ → ℝ := fun i => (Real.exp (2*visualExponent δ)^(k i))⁻¹
  let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  have ha : 1 < Real.exp (2*visualExponent δ) :=
    Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  have hr : ∀ i, 0 < r i := fun i => by dsimp [r]; positivity
  have hrlim : Tendsto r atTop (𝓝 0) := by
    simpa only [r,inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hk.tendsto_atTop
  have hfib := puncture_fibers_finite ρ b v x r CE LE (boundaryDist_le_one D hδ)
    (by dsimp [CE]; positivity) hr hrlim
    (fun i => boundaryExpansion_formula D hδ (x i) (k i)) (closure O) isClosed_closure.isCompact
    (fun i => subset_closure (hx i).1) (fun h => hOb h rfl) hgood
  obtain ⟨s,hs,hinj⟩ := injective_subsequence_of_finite_fibers (fun i => ρ ((v i)⁻¹) b) hfib
  let H : ℕ → Boundary D → ℝ := fun i =>
    normalized (onDomain W) (boundaryExpansion D hδ (x (s i)) (k (s i))) (x (s i)) (sig (s i))
  have hHcomp : ∀ i j, ρ ((v (s i))⁻¹) b ≠ ρ ((v (s j))⁻¹) b →
      ∀ z, z ≠ ρ ((v (s i))⁻¹) b → z ≠ ρ ((v (s j))⁻¹) b →
        NonconstantAt (H i) z → H j z = H j (ρ ((v (s i))⁻¹) b) := by
    intro i j hij z hzi hzj hz
    apply congrArg (fun a : ℝ => a / sig (s j))
    apply sub_left_inj.mpr
    exact hcomp ((v (s i))⁻¹) ((v (s j))⁻¹) hij z hzi hzj
      ((nonconstantAt_normalize _ _ _ (hx (s i)).2.ne' z).mp hz)
  have hHlim : ∀ K : Set (Boundary D), IsCompact K → p ∉ K →
      TendstoUniformlyOn H (onDomain F) atTop K := by
    intro K hK hpK
    have hh := uniform_onDomain
      (fun i => normalized (onDomain W) (boundaryExpansion D hδ (x i) (k i)) (x i) (sig i))
      F hFlim K hK (by intro z hz hzp; exact hpK (hzp ▸ hz))
    intro u hu
    exact hs.tendsto_atTop.eventually (hh u hu)
  have hFvar' : ∃ v ∈ ({p}ᶜ : Set (Boundary D)), ∃ w ∈ ({p}ᶜ : Set (Boundary D)),
      onDomain F v ≠ onDomain F w := by
    obtain ⟨v,w,hvw⟩ := hFvar
    exact ⟨v.val,v.property,w.val,w.property,by simpa only [onDomain_eq _ _ v.property,onDomain_eq _ _ w.property] using hvw⟩
  obtain ⟨v₁,w₁,q₁,hq₁,hq₁w⟩ := ordered_variation_path _ (boundary_punctured_pathConnected D φ p)
    (onDomain F) hFvar'
  exact CannonSecondMagnification.impossible_nonconstant_limit H
    (fun i => ρ ((v (s i))⁻¹) b) p (onDomain F) (hp.comp hs.tendsto_atTop) hinj
    (continuousOn_onDomain F) hHlim hHcomp q₁ (fun h => hq₁ h rfl) hq₁w

end CannonRelease

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
