import Mathlib

namespace OAI

/-! Lie-group structures and surjective derivatives for quotient charts. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawQuotientLie
variable {E V G Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

 
def leftChart (q : OpenPartialHomeomorph V Q) (a : Q) : OpenPartialHomeomorph Q V :=
  (Homeomorph.mulLeft a⁻¹).toOpenPartialHomeomorph.trans q.symm

omit [NormedSpace ℝ V] in
@[simp] lemma leftChart_apply (q : OpenPartialHomeomorph V Q) (a x : Q) :
    leftChart q a x = q.symm (a⁻¹ * x) := rfl

omit [NormedSpace ℝ V] in
@[simp] lemma leftChart_symm_apply (q : OpenPartialHomeomorph V Q) (a : Q) (v : V) :
    (leftChart q a).symm v = a * q v := by
  change a⁻¹⁻¹ * q v = a * q v
  rw [inv_inv]

omit [NormedSpace ℝ V] in
@[simp] lemma leftChart_source (q : OpenPartialHomeomorph V Q) (a : Q) :
    (leftChart q a).source = (fun x => a⁻¹ * x) ⁻¹' q.target := by
  ext x
  simp [leftChart]

omit [NormedSpace ℝ V] in
@[simp] lemma leftChart_target (q : OpenPartialHomeomorph V Q) (a : Q) :
    (leftChart q a).target = q.source := by
  ext x
  simp [leftChart]

@[instance_reducible]
def quotientChartedSpace (q : OpenPartialHomeomorph V Q) (h1 : (1 : Q) ∈ q.target) :
    ChartedSpace V Q where
  atlas := range (leftChart q)
  chartAt := leftChart q
  mem_chart_source := by intro a; simpa using h1
  chart_mem_atlas := fun a => mem_range_self a

lemma quotient_isManifold (π : G →* Q) (hπ : Surjective π)
    (σ : V → G) (hσ : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ σ)
    (q : OpenPartialHomeomorph V Q) (h1 : (1 : Q) ∈ q.target)
    (hq : (q : V → Q) = π ∘ σ)
    (hcoord : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ (q.symm ∘ π) (π ⁻¹' q.target)) :
    @IsManifold ℝ _ V _ _ V _ 𝓘(ℝ,V) ∞ Q _ (quotientChartedSpace q h1) := by
  let := quotientChartedSpace q h1
  apply isManifold_of_contDiffOn 𝓘(ℝ,V) ∞ Q
  rintro e e' ⟨a,rfl⟩ ⟨b,rfl⟩
  obtain ⟨g,hg⟩ := hπ (b⁻¹ * a)
  have hf : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ (fun v => g * σ v) := contMDiff_const.mul hσ
  have hh := hcoord.comp hf.contMDiffOn (s := (leftChart q a).symm.trans (leftChart q b) |>.source) (by
    intro v hv
    change π (g * σ v) ∈ q.target
    have hv' : b⁻¹ * (a * q v) ∈ q.target := by
      have hh := hv.2
      change (leftChart q a).symm v ∈ (leftChart q b).source at hh
      simpa only [leftChart_source, Set.mem_preimage, leftChart_symm_apply] using hh
    simpa only [map_mul, hg, mul_assoc, hq, Function.comp_apply] using hv')
  have heq : ((leftChart q a).symm.trans (leftChart q b) : V → V) =
      (q.symm ∘ π) ∘ (fun v => g * σ v) := by
    funext v
    simp only [OpenPartialHomeomorph.trans_apply, leftChart_apply, leftChart_symm_apply,
      Function.comp_apply, map_mul, hg, hq, mul_assoc]
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ, heq]
    using hh.contDiffOn

end RawQuotientLie

namespace RawQuotientLie
variable {E V G Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

section
variable (q : OpenPartialHomeomorph V Q) (h1 : (1 : Q) ∈ q.target)

@[simp] lemma quotient_extChart_apply (a x : Q) :
    (letI := quotientChartedSpace q h1; extChartAt 𝓘(ℝ,V) a x) = q.symm (a⁻¹ * x) := rfl

@[simp] lemma quotient_extChart_symm_apply (a : Q) (v : V) :
    (letI := quotientChartedSpace q h1; (extChartAt 𝓘(ℝ,V) a).symm v) = a * q v := by
  change (leftChart q a).symm v = a * q v
  exact leftChart_symm_apply q a v

lemma quotient_projection_smooth (π : G →* Q) (hπc : Continuous π)
    (hcoord : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ (q.symm ∘ π) (π ⁻¹' q.target)) :
    letI := quotientChartedSpace q h1
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ π := by
  let := quotientChartedSpace q h1
  intro g
  rw [contMDiffAt_iff_target]
  refine ⟨hπc.continuousAt,?_⟩
  have h0 : (1 : G) ∈ π ⁻¹' q.target := by simpa only [mem_preimage, map_one] using h1
  have hd : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ (q.symm ∘ π) 1 :=
    hcoord.contMDiffAt ((q.open_target.preimage hπc).mem_nhds h0)
  have hL : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : G => g⁻¹ * x) :=
    contMDiff_const.mul contMDiff_id
  have hh := hd.comp_of_eq (hL g) (inv_mul_cancel g)
  convert hh using 1
  ext x
  simp only [Function.comp_apply, quotient_extChart_apply, map_mul, map_inv]

variable {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H' M]

lemma quotient_descend_smooth (π : G →* Q) (hπ : Surjective π)
    (σ : V → G) (hσ : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ σ)
    (hq : (q : V → Q) = π ∘ σ) (f : Q → M)
    (hf : ContMDiff 𝓘(ℝ,E) I' ∞ (f ∘ π)) :
    letI := quotientChartedSpace q h1
    ContMDiff 𝓘(ℝ,V) I' ∞ f := by
  let := quotientChartedSpace q h1
  intro a
  rw [contMDiffAt_iff_source]
  obtain ⟨g,hg⟩ := hπ a
  have hL : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ (fun v => g * σ v) := contMDiff_const.mul hσ
  have hh := hf.comp hL
  have heq : f ∘ (extChartAt 𝓘(ℝ,V) a).symm = (f ∘ π) ∘ (fun v => g * σ v) := by
    ext v
    simp only [Function.comp_apply, quotient_extChart_symm_apply, map_mul, hg, hq]
  rw [heq]
  exact (hh _).contMDiffWithinAt

lemma quotient_multiplication_smooth (π : G →* Q) (hπ : Surjective π)
    (hπsmooth : letI := quotientChartedSpace q h1; ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ π)
    (σ : V → G) (hσ : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ σ)
    (hq : (q : V → Q) = π ∘ σ) :
    letI := quotientChartedSpace q h1
    ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,V)) 𝓘(ℝ,V) ∞ (fun p : Q × Q => p.1 * p.2) := by
  let := quotientChartedSpace q h1
  intro p
  rw [contMDiffAt_iff_source]
  obtain ⟨g,hg⟩ := hπ p.1
  obtain ⟨g',hg'⟩ := hπ p.2
  have hF : ContMDiff 𝓘(ℝ,V × V) 𝓘(ℝ,E) ∞
      (fun v : V × V => (g * σ v.1) * (g' * σ v.2)) := by
    exact (contMDiff_const.mul (hσ.comp (ContinuousLinearMap.fst ℝ V V).contDiff.contMDiff)).mul
      (contMDiff_const.mul (hσ.comp (ContinuousLinearMap.snd ℝ V V).contDiff.contMDiff))
  have hh := hπsmooth.comp hF
  have heq : (fun p : Q × Q => p.1 * p.2) ∘ (extChartAt (𝓘(ℝ,V).prod 𝓘(ℝ,V)) p).symm =
      π ∘ (fun v : V × V => (g * σ v.1) * (g' * σ v.2)) := by
    ext v
    rw [extChartAt_prod]
    change (extChartAt 𝓘(ℝ,V) p.1).symm v.1 * (extChartAt 𝓘(ℝ,V) p.2).symm v.2 =
      π ((g * σ v.1) * (g' * σ v.2))
    simp only [quotient_extChart_symm_apply, map_mul, hg, hg', hq, Function.comp_apply]
  rw [heq]
  exact (hh _).contMDiffWithinAt

end

 

theorem quotient_lieGroup (π : G →* Q) (hπ : Surjective π) (hπc : Continuous π)
    (σ : V → G) (hσ : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ σ)
    (q : OpenPartialHomeomorph V Q) (h1 : (1 : Q) ∈ q.target)
    (hq : (q : V → Q) = π ∘ σ)
    (hcoord : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ (q.symm ∘ π) (π ⁻¹' q.target)) :
    @LieGroup ℝ _ V _ V _ _ 𝓘(ℝ,V) ∞ Q _ _ (quotientChartedSpace q h1) := by
  let := quotientChartedSpace q h1
  let := quotient_isManifold π hπ σ hσ q h1 hq hcoord
  have hπsmooth := quotient_projection_smooth q h1 π hπc hcoord
  have hmul := quotient_multiplication_smooth q h1 π hπ hπsmooth σ hσ hq
  have hinv : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ (fun a : Q => a⁻¹) := by
    apply quotient_descend_smooth q h1 π hπ σ hσ hq
    have hh := hπsmooth.comp (contMDiff_inv (I := 𝓘(ℝ,E)) (n := ∞))
    simpa only [Function.comp_def, map_inv] using hh
  exact { contMDiff_mul := hmul, contMDiff_inv := hinv }

end RawQuotientLie

namespace RawQuotientLie
variable {E V G Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

lemma quotient_derivative_surjective (π : G →* Q) (hπ : Surjective π) (hπc : Continuous π)
    (σ : V → G) (hσ : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ σ) (hσ0 : σ 0 = 1)
    (q : OpenPartialHomeomorph V Q) (hq0 : (0 : V) ∈ q.source)
    (h1 : (1 : Q) ∈ q.target) (hq : (q : V → Q) = π ∘ σ)
    (hcoord : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ (q.symm ∘ π) (π ⁻¹' q.target)) :
    letI := quotientChartedSpace q h1
    Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) π 1 : E →L[ℝ] V) := by
  let := quotientChartedSpace q h1
  let : LieGroup 𝓘(ℝ,V) ∞ Q := quotient_lieGroup π hπ hπc σ hσ q h1 hq hcoord
  have hπsmooth := quotient_projection_smooth q h1 π hπc hcoord
  have hqzero : q 0 = 1 := by simp only [hq,Function.comp_apply,hσ0,map_one]
  have hqone : q.symm 1 = 0 := by rw [← hqzero,q.left_inv hq0]
  have hc : ContMDiffAt 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ (q.symm : Q → V) 1 := by
    have he : (chartAt V (1 : Q) : Q → V) = q.symm := by
      funext a
      change q.symm ((1 : Q)⁻¹ * a) = q.symm a
      rw [inv_one,one_mul]
    rw [← he]
    exact (contMDiffOn_chart (I := 𝓘(ℝ,V)) (n := ∞)).contMDiffAt
      ((chartAt V (1 : Q)).open_source.mem_nhds (mem_chart_source _ _))
  let s : Q → G := σ ∘ q.symm
  have hs : ContMDiffAt 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ s 1 := (hσ _).comp 1 hc
  have hs1 : s 1 = 1 := by simp only [s,Function.comp_apply,hqone,hσ0]
  have heq : π ∘ s =ᶠ[𝓝 (1 : Q)] id := by
    filter_upwards [q.open_target.mem_nhds h1] with a ha
    change π (σ (q.symm a)) = a
    rw [← Function.comp_apply (f := π) (g := σ),← hq]
    exact q.right_inv ha
  have HD := mfderiv_comp_of_eq (I' := 𝓘(ℝ,E))
    (hπsmooth.mdifferentiableAt (x := (1 : G)) (by simp))
    (hs.mdifferentiableAt (by simp)) hs1
  have HE := heq.mfderiv_eq (I := 𝓘(ℝ,V)) (I' := 𝓘(ℝ,V))
  rw [mfderiv_id] at HE
  have HP := mfderiv_congr_point (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,V)) (f := π) hs1
  change (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) π (s 1) : E →L[ℝ] V) = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) π 1 at HP
  change (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (π ∘ s) 1 : V →L[ℝ] V) =
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) π (s 1)).comp (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) s 1) at HD
  rw [HP] at HD
  intro v
  refine ⟨mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) s 1 v,?_⟩
  have H := congrArg (fun A : V →L[ℝ] V => A v) (HD.symm.trans HE)
  exact H

end RawQuotientLie
end

end OAI
