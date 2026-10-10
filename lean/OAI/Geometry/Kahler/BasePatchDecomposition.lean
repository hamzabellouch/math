import OAI.Geometry.Kahler.BaseRadialModelError

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def peakPatchUnion (P : Finset Sphere) (k : ℕ) (R : ℝ) : Set Sphere := ⋃ p ∈ P, peakPatch k R p

lemma peakPatchUnion_open (P : Finset Sphere) (k : ℕ) (R : ℝ) : IsOpen (peakPatchUnion P k R) :=
  isOpen_iUnion (fun p => isOpen_iUnion (fun _ => peakPatch_open k R p))

lemma peakPatchUnion_phase (P : Finset Sphere) (k : ℕ) (R : ℝ) (z : Circle) (ξ : Sphere) :
    phaseAction z ξ ∈ peakPatchUnion P k R ↔ ξ ∈ peakPatchUnion P k R := by
  simp only [peakPatchUnion,mem_iUnion,phaseAction_patch]

lemma densityCorrection_off {k : ℕ} {R : ℝ} {f b : ℝ → ℝ} {W : Base → ℝ} {p ξ : Sphere}
    (hξ : ξ ∉ peakPatch k R p) : densityCorrection k R f b W p ξ=0 := by
  exact ite_eq_right hξ

lemma patch_decomposition {a : ℝ} (pr : RadialProfiles a) {k : ℕ} (hk : 0 < k)
    (P : Finset Sphere) (hdis : (P : Set Sphere).PairwiseDisjoint (peakPatch k pr.R))
    {V : Sphere → ℝ} (hV : Continuous V) :
    (∫ ξ : Sphere, V ξ ∂sigma)+∑ p ∈ P, ∫ ξ : Sphere,
      V ξ*densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma =
    (∫ ξ in (peakPatchUnion P k pr.R)ᶜ, V ξ ∂sigma)+
      ∑ p ∈ P, ∫ ξ in peakPatch k pr.R p,
        V ξ*(1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma := by
  have hU := (peakPatchUnion_open P k pr.R).measurableSet
  have hsplit := integral_add_compl hU (compact_continuous_integrable hV (μ := sigma))
  have hu : (∫ ξ in peakPatchUnion P k pr.R, V ξ ∂sigma)=
      ∑ p ∈ P, ∫ ξ in peakPatch k pr.R p, V ξ ∂sigma := by
    exact integral_biUnion_finset P (fun p _ => (peakPatch_open k pr.R p).measurableSet)
      hdis (fun p _ => compact_continuous_integrable hV)
  have hc : ∀ p : Sphere, Continuous (fun ξ : Sphere => V ξ*densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) := by
    intro p
    exact hV.mul ((densityCorrection_smooth hk pr.cutoff_lt pr.smooth_f pr.smooth_b
      (contDiff_const (c := (1:ℝ))) pr.tail p).continuous.comp continuous_subtype_val)
  have hp : ∀ p : Sphere, (∫ ξ : Sphere, V ξ*densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma)=
      ∫ ξ in peakPatch k pr.R p, V ξ*densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma := by
    intro p
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ξ hξ
    rw [densityCorrection_off hξ,mul_zero]
  have hsum : ∀ p : Sphere, (∫ ξ in peakPatch k pr.R p, V ξ ∂sigma)+
      (∫ ξ in peakPatch k pr.R p, V ξ*densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma)=
      ∫ ξ in peakPatch k pr.R p, V ξ*(1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma := by
    intro p
    rw [← integral_add (compact_continuous_integrable hV) (compact_continuous_integrable (hc p))]
    congr 1
    ext ξ
    ring
  rw [← hsplit,hu]
  simp_rw [hp]
  rw [add_right_comm,← Finset.sum_add_distrib]
  simp_rw [hsum]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
