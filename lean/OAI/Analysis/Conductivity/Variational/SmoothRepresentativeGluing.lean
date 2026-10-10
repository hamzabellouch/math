import Mathlib
import OAI.Analysis.Conductivity.Variational.HarmonicRankAffine
import OAI.Analysis.Conductivity.Fourier.TorusFourierAnalytic

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory MeasureTheory.Measure Filter Topology
open TopologicalSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [IsOpenPosMeasure μ]

omit [NormedSpace ℝ E] [BorelSpace E] [IsOpenPosMeasure μ] in
lemma ae_on_open_cover {ι : Type*} (O : ι → Set E) (hO : ∀ i,IsOpen (O i))
    (P : E → Prop) (hP : ∀ i,∀ᵐ x∂μ.restrict (O i),P x) :
    ∀ᵐ x∂μ.restrict (⋃ i,O i),P x := by
  obtain ⟨T,hT,he⟩ := isOpen_iUnion_countable O hO
  rw [←he]
  exact (ae_restrict_biUnion_iff O hT P).mpr (fun i _ => hP i)

theorem smooth_representatives_glue {ι : Type*} (O : ι → Set E) (hO : ∀ i,IsOpen (O i))
    (f : E → F) (g : ι → E → F) {n : WithTop ℕ∞}
    (hg : ∀ i,ContDiffOn ℝ n (g i) (O i))
    (he : ∀ i,f=ᵐ[μ.restrict (O i)] g i) :
    ∃ v : E → F,(∀ i,EqOn v (g i) (O i)) ∧
      f=ᵐ[μ.restrict (⋃ i,O i)] v ∧ ContDiffOn ℝ n v (⋃ i,O i) := by
  classical
  have hc (i j : ι) : EqOn (g i) (g j) (O i∩O j) := by
    apply eqOn_open_of_ae_eq (μ := μ) ?_ ((hO i).inter (hO j))
      ((hg i).continuousOn.mono inter_subset_left) ((hg j).continuousOn.mono inter_subset_right)
    have hi : f=ᵐ[μ.restrict (O i∩O j)] g i :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (he i)
    have hj : f=ᵐ[μ.restrict (O i∩O j)] g j :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (he j)
    exact hi.symm.trans hj
  let chooseIndex (x : E) (hx : x∈⋃ i,O i) : ι := (mem_iUnion.mp hx).choose
  have hchoose (x : E) (hx : x∈⋃ i,O i) : x∈O (chooseIndex x hx) :=
    (mem_iUnion.mp hx).choose_spec
  let v : E → F := fun x => if hx : x∈⋃ i,O i then g (chooseIndex x hx) x else f x
  have hv (i : ι) : EqOn v (g i) (O i) := by
    intro x hx
    have hxU : x∈⋃ i,O i := mem_iUnion.mpr ⟨i,hx⟩
    dsimp only [v]
    rw [dite_eq_left hxU]
    exact hc _ i ⟨hchoose x hxU,hx⟩
  refine ⟨v,hv,?_,?_⟩
  · apply ae_on_open_cover μ O hO (fun x => f x=v x)
    intro i
    filter_upwards [he i,ae_restrict_mem (hO i).measurableSet] with x hx hxi
    exact hx.trans (hv i hxi).symm
  · intro x hx
    obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
    have hi : ContDiffOn ℝ n v (O i) := (hg i).congr (hv i)
    exact (hi x hxi).contDiffAt ((hO i).mem_nhds hxi) |>.contDiffWithinAt

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma HarmonicPairRegularOn.toCartesian {g : Fin 2 → R3 → ℝ} {O : Set R3}
    (hO : IsOpen O) (hg : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (g j) O)
    (h : HarmonicPairRegularOn (g 0) (g 1) O) :
    TwoFieldRankRegular (fun y : Coord3 => fun j => g j (WithLp.toLp 2 y))
      ((WithLp.toLp 2 : Coord3 → R3) ⁻¹' O) := by
  let P : Coord3 ≃L[ℝ] R3 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let V : Set Coord3 := P ⁻¹' O
  let u : Coord3 → Fin 2 → ℝ := fun y j => g j (P y)
  have hV : IsOpen V := hO.preimage P.continuous
  have hus : ContDiffOn ℝ (↑(⊤:ℕ∞)) u V := by
    apply contDiffOn_pi.mpr
    intro j
    exact (hg j).comp P.contDiff.contDiffOn (fun _ hx => hx)
  have hud (x) (hx : x∈V) :=
    (hus.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
  have hd (j : Fin 2) (x : Coord3) (hx : x∈V) (v : R3) :
      fderiv ℝ u x (P.symm v) j=fderiv ℝ (g j) (P x) v := by
    rw [←potential_component_fderivAt (hud x hx)]
    change fderiv ℝ (g j ∘ P) x (P.symm v)=_
    rw [fderiv_comp _ ((hg j (P x) hx).contDiffAt (hO.mem_nhds hx) |>.differentiableAt (by simp))
      P.differentiableAt]
    simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
  change TwoFieldRankRegular u V
  rcases h with h|h|h|h
  · obtain ⟨p,q,hm⟩ := h
    left
    intro x hx
    apply gradientColumns_rank
    apply pairCLM_surjective_of_minor _ (P.symm p) (P.symm q)
    simp only [hd 0 x hx,hd 1 x hx]
    simpa only [mul_comm] using hm (P x) hx
  · obtain ⟨v,α,β,hm⟩ := h
    right; left
    refine ⟨fun x => u x 0,![1,α],![0,β],?_,⟨0,by simp⟩,?_,?_⟩
    · exact (hg 0).comp P.contDiff.contDiffOn (fun _ hx => hx)
    · intro x hx hz
      have he := congrArg (fun D : Coord3 →L[ℝ] ℝ => D (P.symm v)) hz
      rw [potential_component_fderivAt (hud x hx),hd 0 x hx] at he
      exact (hm (P x) hx).1 he
    · intro x hx j
      fin_cases j
      · simp [u]
      · simpa [u] using (hm (P x) hx).2
  · obtain ⟨v,α,β,hm⟩ := h
    right; left
    refine ⟨fun x => u x 1,![α,1],![β,0],?_,⟨1,by simp⟩,?_,?_⟩
    · exact (hg 1).comp P.contDiff.contDiffOn (fun _ hx => hx)
    · intro x hx hz
      have he := congrArg (fun D : Coord3 →L[ℝ] ℝ => D (P.symm v)) hz
      rw [potential_component_fderivAt (hud x hx),hd 1 x hx] at he
      exact (hm (P x) hx).1 he
    · intro x hx j
      fin_cases j
      · simpa [u] using (hm (P x) hx).2
      · simp [u]
  · obtain ⟨α,β,hm⟩ := h
    right; right
    refine ⟨![α,β],?_⟩
    intro x hx
    ext j
    fin_cases j
    · exact (hm (P x) hx).1
    · exact (hm (P x) hx).2

end ScalarConductivity

end

end OAI
