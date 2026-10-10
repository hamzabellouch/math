import Mathlib
import OAI.Geometry.Borsuk.Support.MixedHits
import OAI.Geometry.Borsuk.Projectors.CoordinateSum
import OAI.Geometry.Borsuk.MatrixGeometry.ModelRay
import OAI.Geometry.Borsuk.LocalParity.RegularModel
import OAI.Geometry.Borsuk.Projectors.RaySet
import OAI.Geometry.Borsuk.MatrixGeometry.TracePatchModels

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section MatrixParity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "T" => traceSphere (Fin (k+1))
local notation "Y" => EuclideanSpace ℝ ι
lemma Admissible.regular_facet_level_odd {f : E → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (a : Fin (k+1) ≃ ↥I)
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {z : W} (hz : z ∈ simplexInterior k)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0)
    (hfin : (orientedLevel f w (facetPoint a z)).Finite) :
    (Nat.card (orientedLevel f w (facetPoint a z)) : F₂) = 1 := by
  classical
  let L := orientedLevel f w (facetPoint a z)
  let : Fintype L := hfin.fintype
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hc (c : L) : ‖c.val‖ = 1 := c.property.1
  have hcv (c : L) : f c.val = facetPoint a z := c.property.2.1
  have hcw (c : L) : 0 < ⟪w,c.val⟫ := hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) c.property
  have hcp (c : L) : positiveSupport f c.val = I := hf.facet_support a hz (hcv c)
  have hdata (c : L) := hf.regular_model_data a hw (hc c) e he hes (hcw c) (hcv c) hr
  choose d D δ hd hds hδ hreg using hdata
  let v := uniformVector ↥(Iᶜ : Finset ι)
  have hv (i : ↥(Iᶜ : Finset ι)) : 0 < v i := by
    change 0 < (Fintype.card ↥(Iᶜ : Finset ι) : ℝ)⁻¹
    positivity
  have hvs : ∑ i, v i = 1 := coordinateSum_uniform _
  let y : Y := blockVector I (1/2:ℝ) (facetPoint a z) (1/2:ℝ) v
  have hy : y ≠ 0 := blockVector_nonzero hI (by norm_num) (facetPoint_pos a hz) _
  let F : T → Y := fun A => WithLp.toLp 2 (signedExtension f A.val)
  let G : L → T → Y := fun c A => WithLp.toLp 2 (localBlockModel f c.val (d c) a (D c) A.val)
  let K : L → Set T := fun c => matrixRayFibre F y c.val
  let S : L → Set T := fun c => regularPatch f I w c.val (d c) (δ c)
  have hF : Continuous F := (PiLp.continuous_toLp 2 _).comp
    (hf.signedExtension_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1))
  have hFz (A : T) : F A ≠ 0 := by
    intro hzA
    exact traceSphere_ne_zero A.property ((hf.signedExtension_eq_zero_iff A.property.1).mp (WithLp.toLp_injective 2 hzA))
  have hFroot (A : T) (hA : F A ∈ raySet y) :
      IsUnit A.val ∧ HasPositiveLine A.val ∧
      (Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ) A.val⁺) w ≠ 0 ∧
      0 < Matrix.trace A.val⁻ ∧ lineRepresentative w A.val ∈ L := by
    obtain ⟨t,ht,hAt⟩ := (mem_raySet_iff (hFz A) hy).mp hA
    exact hf.original_ray_level hI hmax hw hwi (facetPoint_pos a hz) (fun i hi => facetPoint_zero a z hi)
      (facetPoint_sum a z) hv hvs A.property ht hAt
  have hG (c : L) : Continuous (G c) := (PiLp.continuous_toLp 2 _).comp
    ((hf.localBlockModel_continuousOn c.val (d c) a (D c)).comp_continuous continuous_subtype_val
      (fun A => A.property.1))
  have hGz (c : L) (A : T) : G c A ≠ 0 := by
    intro hzA
    exact hf.localBlockModel_ne_zero (hc c) (d c) (hd c) (hds c) a (hcp c) (D c)
      A.property.1 (traceSphere_ne_zero A.property) (WithLp.toLp_injective 2 hzA)
  have hKS (c : L) : K c ⊆ S c := by
    intro A hA
    have hh := hFroot A hA.1
    exact hf.matrixRayFibre_subset_patch (hc c) (hcw c) (by simpa only [hcv c] using facetPoint_pos a hz)
      (d c) (hd c) (hds c) (hδ c) hA hh.1 hh.2.1 hh.2.2.1
  have hKd : Pairwise (fun c c' => Disjoint (K c) (K c')) := by
    intro c c' hcc
    apply Set.disjoint_left.mpr
    intro A hA hA'
    have hh := hFroot A hA.1
    apply hcc
    apply Subtype.ext
    exact (matrixRayFibre_representative (hc c) (hcw c) hh.2.1 hA).symm.trans
      (matrixRayFibre_representative (hc c') (hcw c') hh.2.1 hA')
  have hyi (c : L) (i : ι) (hi : i ∈ I) : y i = (1/2:ℝ)*f c.val i := by
    rw [hcv c]
    exact blockVector_in I _ _ _ _ hi
  have hyo (i : ι) (hi : i ∉ I) : y i ≤ 0 := by
    have hh := blockVector_out I (1/2:ℝ) (facetPoint a z) (1/2:ℝ) v ⟨i,Finset.mem_compl.mpr hi⟩
    change y i = _ at hh
    rw [hh]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hv _).le
  have hcover (A : T) (hA : ∃ t : ℝ, 0 < t ∧ F A = t • y) : ∃ c, A ∈ K c := by
    have hray := (mem_raySet_iff (hFz A) hy).mpr hA
    have hh := hFroot A hray
    exact ⟨⟨lineRepresentative w A.val,hh.2.2.2.2⟩,hray,positive_line_representative hh.2.1 hh.2.2.1⟩
  have hroot (c : L) (A : T) (hA : ∃ t : ℝ, 0 < t ∧ G c A = t • y) : A ∈ K c := by
    obtain ⟨t,ht,hAt⟩ := hA
    have hm : localBlockModel f c.val (d c) a (D c) A.val = t • y.ofLp := WithLp.toLp_injective 2 hAt
    obtain ⟨hb,ha,heq,hP⟩ := hf.localBlockModel_ray (hc c) (d c) (hd c) (hds c) a (hcp c) (D c)
      A.property.1 (by norm_num : (0:ℝ) < 1/2) ht (hyi c) hyo hm
    have hFt : F A = t • y := by simpa only [F,G,heq] using hAt
    refine ⟨(mem_raySet_iff (hFz A) hy).mpr ⟨t,ht,hFt⟩,?_⟩
    have htr : Matrix.trace A.val⁺ = blockScalar c.val A.val := by
      rw [hP,Matrix.trace_smul,rankOne_trace,hc c,one_pow,smul_eq_mul,mul_one]
    rwa [htr]
  have hseg (c : L) (A : T) (hA : A ∈ S c) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (1-t) • F A + t • G c A ≠ 0 := by
    have hnU := lineRepresentative_norm hA.2.2.1
    have hIU : positiveSupport f (lineRepresentative w A.val) = I := hmax _ hnU
      (fun i hi => (mem_positiveSupport f _ i).mpr (hA.2.2.2.1 i hi))
    have hh := hf.localBlockMix_ne_zero A.property.1 (hc c) hnU (d c) (hd c) a (hcp c) hIU (D c)
      (hasPositiveLine_trace_pos hA.2.1) (positive_line_representative hA.2.1 hA.2.2.1) hA.2.2.2.2.2.2.1 ht
    intro hzA
    exact hh (WithLp.toLp_injective 2 hzA)
  have hhit (c : L) (A : T) (hA : A ∈ S c) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
      (hAt : ∃ b : ℝ, 0 < b ∧ (1-t) • F A + t • G c A = b • y) : A ∈ K c := by
    obtain ⟨b,hb,heq⟩ := hAt
    have hnU := lineRepresentative_norm hA.2.2.1
    have hIU : positiveSupport f (lineRepresentative w A.val) = I := hmax _ hnU
      (fun i hi => (mem_positiveSupport f _ i).mpr (hA.2.2.2.1 i hi))
    have hmix : localBlockMix f c.val (d c) a (D c) t A.val = b • y.ofLp := WithLp.toLp_injective 2 heq
    obtain ⟨huc,hme⟩ := hf.localBlockMix_hit A.property.1 (hc c) hnU (d c) (hd c) (hds c) a (hcp c) hIU (D c)
      (hasPositiveLine_trace_pos hA.2.1) (positive_line_representative hA.2.1 hA.2.2.1)
      hA.2.2.2.2.1 hA.2.2.2.2.2.2.2
      (hreg c _ hnU hA.2.2.2.2.1 hA.2.2.2.2.2.1) (hyi c) ht hmix
    refine ⟨(mem_raySet_iff (hFz A) hy).mpr ⟨b,hb,?_⟩,?_⟩
    · exact congrArg (WithLp.toLp 2) (hme.symm.trans hmix)
    · rw [← huc]
      exact positive_line_representative hA.2.1 hA.2.2.1
  have hp := trace_patch_models hdim hn F hF hFz (by
      intro A B hB
      simp only [F,hB,signedExtension_odd,WithLp.toLp_neg])
    G hG hGz (by
      intro c A B hB
      simp only [G,hB,localBlockModel_odd,WithLp.toLp_neg])
    K S (fun c => matrixRayFibre_closed F hF y c.val) (fun c => hf.regularPatch_isOpen I w c.val (d c) (δ c))
    hKS hKd hy hcover hroot hseg hhit
  simpa only [Nat.card_eq_fintype_card] using hp
end MatrixParity
end BorsukNine

end OAI
