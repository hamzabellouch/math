import Mathlib
import OAI.Analysis.Commutator.BicommutantRange
import OAI.Analysis.Commutator.KaplanskyStarHomNet
import OAI.Analysis.Commutator.VonNeumannCStar
import OAI.Analysis.Commutator.WeakOperatorAlgebra
import OAI.Analysis.Commutator.WeakOperatorLimit

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalOperatorHom

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H) (φ : M →⋆ₐ[ℂ] (G →L[ℂ] G))

def BoundedNormal : Prop :=
  ∀ (C : ℝ) (x y : G), Continuous
    (fun a : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} =>
      inner ℂ x (φ ⟨a.val.toCLM,a.property.1⟩ y))

lemma sourceBall_tendsto
    {ι : Type*} {l : Filter ι} (a : ι → M) (b : M) (C : ℝ)
    (ha : ∀ i,‖a i‖≤C) (hb : ‖b‖≤C)
    (hlim : ∀ x y,Tendsto (fun i => inner ℂ ((a i:H →L[ℂ] H) x) y) l
      (𝓝 (inner ℂ ((b:H →L[ℂ] H) x) y))) :
    Tendsto (fun i => (⟨ofCLM (a i),(a i).property,ha i⟩ :
      {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C})) l
      (𝓝 ⟨ofCLM b,b.property,hb⟩) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_iff_forall_inner_apply_tendsto.mpr
  intro u v
  simpa only [RCLike.star_def,inner_conj_symm,ofCLM_apply] using (hlim u v).star

lemma tendsto (hφ : BoundedNormal M φ)
    {ι : Type*} {l : Filter ι} (a : ι → M) (b : M) (C : ℝ)
    (ha : ∀ i,‖a i‖≤C) (hb : ‖b‖≤C)
    (hlim : ∀ x y,Tendsto (fun i => inner ℂ ((a i:H →L[ℂ] H) x) y) l
      (𝓝 (inner ℂ ((b:H →L[ℂ] H) x) y))) (x y : G) :
    Tendsto (fun i => inner ℂ x (φ (a i) y)) l (𝓝 (inner ℂ x (φ b y))) := by
  let F : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} → ℂ :=
    fun z => inner ℂ x (φ ⟨z.val.toCLM,z.property.1⟩ y)
  have hF : Continuous F := hφ C x y
  have hf := sourceBall_tendsto (H:=H) M a b C ha hb hlim
  have ht := (hF.tendsto ⟨ofCLM (b:H →L[ℂ] H),b.property,hb⟩).comp hf
  exact ht

theorem range_bicommutant (hφ : BoundedNormal M φ) :
    Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ := by
  classical
  apply BicommutantRange.operatorHom_range
  intro T hT hsT hnT
  let a := Kaplansky.starHomNet φ T hT hsT hnT
  let ω : Ultrafilter (Finset G × ℕ) := Ultrafilter.of atTop
  have hω : (ω : Filter (Finset G × ℕ))≤atTop := Ultrafilter.of_le _
  have ha : ∀ i,‖a i‖≤1 := fun i => (Kaplansky.starHomNet_spec φ T hT hsT hnT i).1
  obtain ⟨W,hW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω
    (fun i => (a i:H →L[ℂ] H)) 1 (by norm_num) ha
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Eventually.of_forall fun i => (a i).property)
  let b : M := ⟨W,hWM⟩
  refine ⟨b,?_⟩
  ext y
  apply ext_inner_left ℂ
  intro x
  have hb := tendsto M φ hφ a b 1 ha hW hlim x y
  have hc : Continuous (fun z : G => inner ℂ x z) := continuous_const.inner continuous_id
  have ht := (hc.tendsto (T y)).comp
    ((Kaplansky.starHomNet_tendsto φ T hT hsT hnT y).mono_left hω)
  exact tendsto_nhds_unique hb ht

end Kadison.NormalOperatorHom

end

end OAI
