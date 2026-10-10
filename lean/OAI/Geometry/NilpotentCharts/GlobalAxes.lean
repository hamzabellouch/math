import Mathlib
import OAI.Geometry.NilpotentCharts.QuotientCharts

namespace OAI

/-! Global ordered axes from induction through central quotients. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]

def HasGlobalAxes : Prop := ∃ (n : ℕ) (v : Fin n → E₀), IsHomeomorph (orderedAxes (G := G) v)

lemma orderedAxes_append {m n : ℕ} (v : Fin m → GroupLieAlgebra 𝓘(ℝ,E₀) G) (w : Fin n → GroupLieAlgebra 𝓘(ℝ,E₀) G)
    (a : Fin m → ℝ) (b : Fin n → ℝ) :
    orderedAxes (G := G) (Fin.append v w) (Fin.append a b) = orderedAxes v a * orderedAxes w b := by
  have he : (fun i => curve (G := G) (Fin.append v w i) (Fin.append a b i)) =
      Fin.append (fun i => curve (G := G) (v i) (a i)) (fun i => curve (G := G) (w i) (b i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  simp only [orderedAxes,he,List.ofFn_fin_append,List.prod_append]

variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Group Q] [TopologicalSpace Q] [ChartedSpace F Q] [LieGroup 𝓘(ℝ,F) ∞ Q] [T2Space Q]
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

 

theorem globalAxes_of_central_quotient [SimplyConnectedSpace G]
    (π : G →* Q) (hπ : ContMDiff 𝓘(ℝ,E₀) 𝓘(ℝ,F) ∞ π)
    (hD : Surjective (mfderiv 𝓘(ℝ,E₀) 𝓘(ℝ,F) π 1 : E₀ →L[ℝ] F))
    (hker : S = π.ker) (hQ : HasGlobalAxes (G := Q) (E₀ := F)) :
    HasGlobalAxes (G := G) (E₀ := E₀) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
  let : IsTopologicalGroup Q := topologicalGroup_of_lieGroup 𝓘(ℝ,F) ∞
  obtain ⟨n,v,hv⟩ := hQ
  let qh := hv.homeomorph (orderedAxes (G := Q) v)
  choose w hw using (fun i : Fin n => hD (v i))
  have hproj : ∀ a, π (orderedAxes (G := G) w a) = orderedAxes (G := Q) v a := by
    intro a
    erw [orderedAxes_map π (hπ.mdifferentiable (by simp))]
    congr 1
    exact funext hw
  let sectionFn : Q → G := orderedAxes (G := G) w ∘ qh.symm
  have hs : Continuous sectionFn := (orderedAxes_contMDiff w).continuous.comp qh.symm.continuous
  have hsec : ∀ q, π (sectionFn q) = q := by
    intro q
    exact (hproj (qh.symm q)).trans (qh.apply_symm_apply q)
  have hq0 : qh 0 = 1 := orderedAxes_zero v
  have hs1 : sectionFn 1 = 1 := by
    change orderedAxes w (qh.symm 1) = 1
    rw [← hq0,qh.symm_apply_apply,orderedAxes_zero]
  let : SimplyConnectedSpace π.ker := RawGroupSection.fiber_simplyConnected
    π hπ.continuous sectionFn hs hsec hs1
  let : SimplyConnectedSpace S := hker ▸ inferInstance
  let b := Module.finBasis ℝ C
  let HC : (Fin (Module.finrank ℝ C) → ℝ) ≃ₜ S :=
    b.equivFun.toContinuousLinearEquiv.symm.toHomeomorph.trans (centralHomeomorph (G := G))
  have hHC : ∀ a, (HC a : G) = orderedAxes (G := G) (fun i => (show GroupLieAlgebra 𝓘(ℝ,E₀) G from (b i).val)) a := by
    intro a
    change subspaceAxes C (b.equivFun.symm a) = _
    simp only [subspaceAxes,Function.comp_apply,← show Module.finBasis ℝ C = b from rfl,
      LinearEquiv.apply_symm_apply]
  let HK : (Fin (Module.finrank ℝ C) → ℝ) ≃ₜ π.ker :=
    HC.trans (Homeomorph.setCongr (congrArg SetLike.coe hker))
  have hHK : ∀ a, (HK a : G) = orderedAxes (G := G) (fun i => (show GroupLieAlgebra 𝓘(ℝ,E₀) G from (b i).val)) a := hHC
  let T := RawGroupSection.trivialization π hπ.continuous sectionFn hs hsec
  let H := (qh.prodCongr HK).trans T
  have hH : ∀ a z, H (a,z) = orderedAxes (G := G) w a *
      orderedAxes (G := G) (fun i => (show GroupLieAlgebra 𝓘(ℝ,E₀) G from (b i).val)) z := by
    intro a z
    change sectionFn (qh a) * (HK z : G) = _
    change orderedAxes w (qh.symm (qh a)) * (HK z : G) = _
    rw [qh.symm_apply_apply,hHK]
  let P := (RawGroupSection.finAppendHomeomorph n (Module.finrank ℝ C)).symm.trans H
  refine ⟨n + Module.finrank ℝ C,Fin.append w (fun i => (show GroupLieAlgebra 𝓘(ℝ,E₀) G from (b i).val)),?_⟩
  have hP : (P : (Fin (n + Module.finrank ℝ C) → ℝ) → G) =
      orderedAxes (G := G) (Fin.append w (fun i => (show GroupLieAlgebra 𝓘(ℝ,E₀) G from (b i).val))) := by
    funext a
    change H (a ∘ Fin.castAdd _,a ∘ Fin.natAdd n) = _
    rw [hH,← orderedAxes_append]
    simp only [Function.comp_def,Fin.append_castAdd_natAdd]
  exact hP ▸ P.isHomeomorph

end RawLieIntegration

namespace RawLieIntegration

 

theorem globalAxes_dimension_induction (n : ℕ) :
    ∀ (E₀ : Type) [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
      (G : Type) [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
      [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G],
      Module.finrank ℝ E₀ = n → ∀ s : ℕ,
      (⊤ : Subgroup G).lowerCentralSeries s = ⊥ → HasGlobalAxes (G := G) (E₀ := E₀) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E₀ _ _ _ G _ _ _ _ _ _ hdim s hstop
    let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
    by_cases hz : Module.finrank ℝ E₀ = 0
    · let : Subsingleton E₀ := Module.finrank_zero_iff.mp hz
      let : DiscreteTopology G := ChartedSpace.discreteTopology E₀ G
      let : Subsingleton G := subsingleton_of_preconnected_totallyDisconnected
      refine ⟨0,Fin.elim0,?_⟩
      let : Unique G := ⟨⟨1⟩,fun _ => Subsingleton.elim _ _⟩
      convert (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) G).isHomeomorph using 1
    · obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero hz)
      let C := RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
      let S := (centralAxesHom (G := G) (E₀ := E₀)).range
      have hC : C ≠ ⊥ := RawLieAdjoint.centralTangent_ne_bot hstop v hv
      obtain ⟨W,hCW⟩ := Submodule.exists_isCompl C
      have hpos : 0 < Module.finrank ℝ C := by
        exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hC)
      have hw : Module.finrank ℝ W < n := by
        have he := Submodule.finrank_add_eq_of_isCompl hCW
        omega
      let : T2Space (G ⧸ S) := central_quotient_t2Space
      let : SimplyConnectedSpace (G ⧸ S) := central_quotient_simplyConnected
      obtain ⟨cs,hLie,hSmooth,hSurj⟩ := exists_central_quotient_submersion W hCW.symm
      let := cs
      let := hLie
      have hstopQ : (⊤ : Subgroup (G ⧸ S)).lowerCentralSeries s = ⊥ := by
        have he := congrArg (Subgroup.map (QuotientGroup.mk' S)) hstop
        rw [Subgroup.map_lowerCentralSeries,Subgroup.map_top_of_surjective _
          (QuotientGroup.mk'_surjective S),Subgroup.map_bot] at he
        exact he
      have hQ := ih (Module.finrank ℝ W) hw W (G ⧸ S) rfl s hstopQ
      exact globalAxes_of_central_quotient (QuotientGroup.mk' S) hSmooth hSurj
        (QuotientGroup.ker_mk' S).symm hQ

theorem globalAxes_of_nilpotent
    {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
    [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    HasGlobalAxes (G := G) (E₀ := E₀) :=
  globalAxes_dimension_induction (Module.finrank ℝ E₀) E₀ G rfl s hstop

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

theorem central_range_simplyConnected_of_nilpotent {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) : SimplyConnectedSpace S := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
  obtain ⟨W,hCW⟩ := Submodule.exists_isCompl C
  let : T2Space (G ⧸ S) := central_quotient_t2Space
  let : SimplyConnectedSpace (G ⧸ S) := central_quotient_simplyConnected
  obtain ⟨cs,hLie,hSmooth,hSurj⟩ := exists_central_quotient_submersion W hCW.symm
  let := cs
  let := hLie
  have hstopQ : (⊤ : Subgroup (G ⧸ S)).lowerCentralSeries s = ⊥ := by
    have he := congrArg (Subgroup.map (QuotientGroup.mk' S)) hstop
    rw [Subgroup.map_lowerCentralSeries,Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective S),Subgroup.map_bot] at he
    exact he
  obtain ⟨n,v,hv⟩ := globalAxes_of_nilpotent (E₀ := W) hstopQ
  let qh := hv.homeomorph (orderedAxes (G := G ⧸ S) v)
  choose w hw using (fun i : Fin n => hSurj (v i))
  have hproj : ∀ a, QuotientGroup.mk' S (orderedAxes (G := G) w a) =
      orderedAxes (G := G ⧸ S) v a := by
    intro a
    erw [orderedAxes_map (QuotientGroup.mk' S) (hSmooth.mdifferentiable (by simp))]
    congr 1
    exact funext hw
  let sec : G ⧸ S → G := orderedAxes (G := G) w ∘ qh.symm
  have hs : Continuous sec := (orderedAxes_contMDiff w).continuous.comp qh.symm.continuous
  have hsec : ∀ q, QuotientGroup.mk' S (sec q) = q := by
    intro q
    exact (hproj (qh.symm q)).trans (qh.apply_symm_apply q)
  have hq0 : qh 0 = 1 := orderedAxes_zero v
  have hs1 : sec 1 = 1 := by
    change orderedAxes w (qh.symm 1) = 1
    rw [← hq0,qh.symm_apply_apply,orderedAxes_zero]
  have h := RawGroupSection.fiber_simplyConnected (QuotientGroup.mk' S)
    QuotientGroup.continuous_mk sec hs hsec hs1
  rwa [QuotientGroup.ker_mk'] at h

end RawLieIntegration
end

end OAI
