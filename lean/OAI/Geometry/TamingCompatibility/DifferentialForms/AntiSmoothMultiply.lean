import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalPatch
import OAI.Geometry.TamingCompatibility.Functional.WeakNormalEquation
import OAI.Geometry.TamingCompatibility.Functional.CompactCutoff
import OAI.Geometry.TamingCompatibility.Charts.ChartReconstruction

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def antiMultiply (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a : antiPre A J α hs ht) : antiPre A J α hs ht :=
  ⟨⟨(fun x => ρ x • a.val.val x),a.val.property.fun_smul hρ⟩,
    antiInvariant_fun_smul J a.property ρ⟩

@[simp] lemma antiMultiply_apply (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a : antiPre A J α hs ht) (x : X) :
    (antiMultiply A J α hs ht ρ hρ a).val.val x = ρ x • a.val.val x := rfl

end TamingCompatibility.GeometricHilbert

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)
lemma rawPair_fun_smul (ρ : X → ℝ) (a : TwoForm X) (z : Space) :
    rawPair J α ht p D (fun x => ρ x • a x) z =
      ρ ((extChartAt Model p).symm z) • rawPair J α ht p D a z := by
  ext j
  fin_cases j <;> rfl
end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)

lemma supported_anti_test (p : A.centers) {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (hρU : ∀ x ∈ tsupport ρ, x ∈ (extChartAt Model p.val).source ∧ extChartAt Model p.val x ∈ U)
    (a : antiPre A J α hs ht) :
    ∃ q : 𝓢(Space,EuclideanEnergy.Pair), ∃ hc : HasCompactSupport (q : Space → EuclideanEnergy.Pair),
      ∃ hqU : tsupport q ⊆ U,
        testAnti A J α hs ht D p q hc (hqU.trans hUD) = antiMultiply A J α hs ht ρ hρ a := by
  let K := (extChartAt Model p.val) '' tsupport ρ
  have hK : IsCompact K := (isClosed_tsupport ρ).isCompact.image_of_continuousOn
    ((continuousOn_extChartAt p.val).mono (fun x hx => (hρU x hx).1))
  have hKU : K ⊆ U := by rintro _ ⟨x,hx,rfl⟩; exact (hρU x hx).2
  obtain ⟨η,hηc,hηU,hηone⟩ := SchwartzCutoff.exists_one_on_compact hK hU hKU
  let b := antiMultiply A J α hs ht ρ hρ a
  let q := SchwartzCutoff.schwartz (D p).domain_open (rawPair_smooth J α ht p.val (D p) b.val.property)
    (η.smooth ⊤) hηc (hηU.trans hUD)
  have hqc : HasCompactSupport (q : Space → EuclideanEnergy.Pair) := SchwartzCutoff.compact hηc
  have hqU : tsupport q ⊆ U := (tsupport_smul_subset_left _ _).trans hηU
  refine ⟨q,hqc,hqU,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change manifoldTest J α ht p.val (D p) q = b.val.val
  apply manifoldTest_eq J α ht p.val (D p) b.property q (hqU.trans hUD)
  · intro z hz
    change η z • rawPair J α ht p.val (D p) (fun x => ρ x • a.val.val x) z =
      rawPair J α ht p.val (D p) (fun x => ρ x • a.val.val x) z
    rw [rawPair_fun_smul]
    by_cases hr : ρ ((extChartAt Model p.val).symm z) = 0
    · change ρ ((chartAt Space p.val).symm z) = 0 at hr
      simp [hr]
    · rw [hηone z ⟨(extChartAt Model p.val).symm z,subset_closure hr,
        (extChartAt Model p.val).right_inv ((D p).domain_subset hz)⟩,one_smul]
  · intro x hx
    change ρ x • a.val.val x = 0
    have hz : ρ x = 0 := by
      by_contra hn
      have hh := hρU x (subset_closure hn)
      exact hx ⟨extChartAt Model p.val x,hUD hh.2,(extChartAt Model p.val).left_inv hh.1⟩
    rw [hz,zero_smul]

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
