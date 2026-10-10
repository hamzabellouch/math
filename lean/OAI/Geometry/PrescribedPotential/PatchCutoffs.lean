import Mathlib
import OAI.Geometry.PrescribedPotential.ChartTransport
import OAI.Geometry.PrescribedPotential.GlobalPartition

namespace OAI

/-! Patch Cutoffs. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory Manifold IsManifold
open scoped ContDiff SchwartzMap Classical

namespace GlobalElliptic
open Anticanonical EllipticKernel SobolevChart SourceSmooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 

theorem exists_chartCutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ κ : ChartCutoff U, ∀ x ∈ K, κ x = 1 := by
  obtain ⟨L, hLc, hLl, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨f, hf, hf0, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, E)) hK.isClosed hKL (n := ⊤)
  have hsm : ContDiff ℝ ∞ (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp f.contMDiff)
  have hsub : tsupport (fun x => (f x : ℂ)) ⊆ L := by
    apply closure_minimal _ hLl
    intro x hx
    by_contra hn
    exact hx (by simp [hf0 x hn])
  have hc : HasCompactSupport (fun x => (f x : ℂ)) :=
    hLc.of_isClosed_subset (isClosed_tsupport _) hsub
  refine ⟨⟨hc.toSchwartzMap hsm, hc, hsub.trans hLU⟩, ?_⟩
  intro x hx
  change (f x : ℂ) = 1
  rw [hf.self_of_nhdsSet x hx]
  rfl

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}

 

structure GluingData (g : KaehlerMetric A) (ι : Type*) [Fintype ι] where
  patch : ι → ParametrixPatch g
  localizers : Localizers A ι
  index_eq : ∀ p, localizers.index p = (patch p).index
  support_patch : ∀ p, tsupport (localizers.weight p : X → ℂ) ⊆ (patch p).source
  cutoff : ∀ p, ChartCutoff (A.euclideanChart (patch p).index).target
  cutoff_support : ∀ p, tsupport (cutoff p : EC d → ℂ) ⊆ (patch p).domain
  cutoff_one : ∀ p x, x ∈ tsupport (localizers.weight p : X → ℂ) →
    cutoff p (A.euclideanChart (patch p).index x) = 1

 

theorem exists_gluingData (g : KaehlerMetric A) :
    ∃ (S : Finset (ParametrixPatch g)), Nonempty (GluingData g S) := by
  obtain ⟨S, D, hDI, hDS⟩ := exists_patch_localizers g
  have hc (p : S) : ∃ κ : ChartCutoff p.val.domain,
      ∀ x ∈ tsupport (D.weight p : X → ℂ), κ (A.euclideanChart p.val.index x) = 1 := by
    let e := A.euclideanChart p.val.index
    have hK : IsCompact (e '' tsupport (D.weight p : X → ℂ)) :=
      (isClosed_tsupport _).isCompact.image_of_continuousOn
        (e.continuousOn.mono (fun x hx => (hDS p hx).1))
    have hKU : e '' tsupport (D.weight p : X → ℂ) ⊆ p.val.domain := by
      rintro y ⟨x, hx, rfl⟩
      exact (hDS p hx).2
    obtain ⟨κ, hκ⟩ := exists_chartCutoff hK p.val.isOpen_domain hKU
    exact ⟨κ, fun x hx => hκ _ ⟨x, hx, rfl⟩⟩
  choose κ hκ using hc
  refine ⟨S, ⟨{
    patch := Subtype.val
    localizers := D
    index_eq := hDI
    support_patch := hDS
    cutoff := fun p => ⟨(κ p).val, (κ p).compact, (κ p).support_sub.trans p.val.domain_sub⟩
    cutoff_support := fun p => (κ p).support_sub
    cutoff_one := hκ }⟩⟩

namespace GluingData
variable {ι : Type*} [Fintype ι] {g : KaehlerMetric A} (D : GluingData g ι)

omit [T2Space X] [CompactSpace X]
lemma exists_outerCutoff (p : ι) :
    ∃ η : ChartCutoff (A.euclideanChart (D.patch p).index).target,
      tsupport (η : EC d → ℂ) ⊆ (D.patch p).domain ∧
      ∀ y ∈ tsupport (D.cutoff p : EC d → ℂ), η y = 1 := by
  obtain ⟨η, hη⟩ := exists_chartCutoff (D.cutoff p).compact
    (D.patch p).isOpen_domain (D.cutoff_support p)
  exact ⟨⟨η.val, η.compact, η.support_sub.trans (D.patch p).domain_sub⟩, η.support_sub, hη⟩

 

def outerCutoff (p : ι) : ChartCutoff (A.euclideanChart (D.patch p).index).target :=
  (D.exists_outerCutoff p).choose

lemma outerCutoff_support (p : ι) :
    tsupport (D.outerCutoff p : EC d → ℂ) ⊆ (D.patch p).domain :=
  (D.exists_outerCutoff p).choose_spec.1

lemma outerCutoff_one (p : ι) (y : EC d) (hy : y ∈ tsupport (D.cutoff p : EC d → ℂ)) :
    D.outerCutoff p y = 1 := (D.exists_outerCutoff p).choose_spec.2 y hy
end GluingData

end GlobalElliptic

end
end

end OAI
