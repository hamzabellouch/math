import Mathlib
import OAI.Geometry.NilpotentCharts.LatticeAxes

namespace OAI

/-! Triangular lattice bases for the nilpotent adjoint action. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))
variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Group Q] [TopologicalSpace Q] [ChartedSpace F Q] [LieGroup 𝓘(ℝ,F) ∞ Q] [T2Space Q]

lemma tangent_projection_kernel [SimplyConnectedSpace G] [SimplyConnectedSpace Q]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (hstopQ : (⊤ : Subgroup Q).lowerCentralSeries s = ⊥)
    (π : G →* Q) (hπ : ContMDiff I₀ 𝓘(ℝ,F) ∞ π) (hker : S = π.ker) :
    (mfderiv I₀ 𝓘(ℝ,F) π 1 : E₀ →L[ℝ] F).ker = C := by
  apply Submodule.ext
  intro v
  have hc : (v : E₀) ∈ C ↔ exp (G := G) v ∈ S := by
    rw [centralAxesHom_range_eq_center hstop]
    exact (exp_mem_center_iff hstop v).symm
  change mfderiv I₀ 𝓘(ℝ,F) π 1 v = 0 ↔ v ∈ C
  rw [hc,hker,MonoidHom.mem_ker]
  have he := curve_map π (hπ.mdifferentiable (by simp)) v 1
  change π (exp v) = exp (G := Q) (show GroupLieAlgebra 𝓘(ℝ,F) Q from mfderiv I₀ 𝓘(ℝ,F) π 1 v) at he
  rw [he]
  constructor
  · intro h
    rw [h]
    exact exp_zero
  · intro h
    exact exp_injective_of_nilpotent hstopQ (h.trans exp_zero.symm)

lemma adjoint_tangent_projection [SimplyConnectedSpace G] [SimplyConnectedSpace Q] {s : ℕ}
    (hstopQ : (⊤ : Subgroup Q).lowerCentralSeries s = ⊥)
    (π : G →* Q) (hπ : ContMDiff I₀ 𝓘(ℝ,F) ∞ π) (g : G) (v : E₀) :
    mfderiv I₀ 𝓘(ℝ,F) π 1 (RawLieAdjoint.adjoint (E₀ := E₀) g v) =
      RawLieAdjoint.adjoint (E₀ := F) (π g) (mfderiv I₀ 𝓘(ℝ,F) π 1 v) := by
  apply exp_injective_of_nilpotent hstopQ
  have hmap (w : E₀) := curve_map π (hπ.mdifferentiable (by simp)) w 1
  change ∀ w : E₀, π (exp w) = exp (G := Q) (show GroupLieAlgebra 𝓘(ℝ,F) Q from mfderiv I₀ 𝓘(ℝ,F) π 1 w) at hmap
  erw [← hmap,← exp_conjugate,map_mul,map_mul,map_inv,hmap,exp_conjugate]

omit [FiniteDimensional ℝ E₀] [T2Space G] in
lemma adjoint_central (g : G) (z : C) : RawLieAdjoint.adjoint (E₀ := E₀) g z.val = z.val := by
  have H := congrArg (fun A : E₀ →L[ℝ] E₀ => A z.val)
    (RawLieAdjoint.commMap_add_adjoint (E₀ := E₀) g)
  have hz := (RawLieAdjoint.mem_centralTangent z.val).mp z.property g
  simpa only [add_apply,hz,zero_add,ContinuousLinearMap.id_apply] using H

end RawLieIntegration
namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

def HasTriangularLatticeBasis (Γ : Subgroup G) : Prop :=
  ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ E₀),
    IsHomeomorph (orderedAxes (G := G) b) ∧
    (∀ a, orderedAxes (G := G) b a ∈ Γ ↔ ∀ i, ∃ z : ℤ, a i = z) ∧
    ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (E₀ := E₀) g).toLinearMap

variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Group Q] [TopologicalSpace Q] [ChartedSpace F Q] [LieGroup 𝓘(ℝ,F) ∞ Q] [T2Space Q]
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

 

theorem latticeBasis_of_central_quotient [SimplyConnectedSpace G] [SimplyConnectedSpace Q]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (hstopQ : (⊤ : Subgroup Q).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (π : G →* Q) (hπ : ContMDiff I₀ 𝓘(ℝ,F) ∞ π)
    (hker : S = π.ker)
    (hDsurj : Surjective (mfderiv I₀ 𝓘(ℝ,F) π 1 : E₀ →L[ℝ] F)) (hQ : HasTriangularLatticeBasis (G := Q) (E₀ := F) (Γ.map π)) :
    HasTriangularLatticeBasis (G := G) (E₀ := E₀) Γ := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  let : IsTopologicalGroup Q := topologicalGroup_of_lieGroup 𝓘(ℝ,F) ∞
  let : SimplyConnectedSpace S := central_range_simplyConnected_of_nilpotent hstop
  obtain ⟨n,v,hv,hvΓ,htri⟩ := hQ
  have hlog : ∀ i : Fin n, ∃ w : GroupLieAlgebra I₀ G,
      exp w ∈ Γ ∧ mfderiv I₀ 𝓘(ℝ,F) π 1 w = v i := by
    intro i
    have hei : exp (G := Q) (v i) ∈ Γ.map π := by
      erw [exp,← orderedAxes_single v i 1]
      apply (hvΓ _).mpr
      intro j
      by_cases h : j = i
      · subst j; exact ⟨1,by simp⟩
      · exact ⟨0,by simp [Pi.single_eq_of_ne h]⟩
    obtain ⟨γ,hγΓ,hγ⟩ := hei
    obtain ⟨w,hw⟩ := (exponential_of_nilpotent (E₀ := E₀) hstop).2 γ
    refine ⟨w,hw ▸ hγΓ,?_⟩
    apply exp_injective_of_nilpotent hstopQ
    exact (curve_map π (hπ.mdifferentiable (by simp)) w 1).symm.trans
      ((congrArg π hw).trans hγ)
  choose w hwΓ hw using hlog
  let qh := hv.homeomorph (orderedAxes (G := Q) v)
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
  obtain ⟨k,b,hb⟩ := exists_central_lattice_basis (E₀ := E₀) hstop Γ
  let u : Fin k → GroupLieAlgebra I₀ G := fun i => (b i).val
  let HC : (Fin k → ℝ) ≃ₜ S :=
    b.equivFun.toContinuousLinearEquiv.symm.toHomeomorph.trans (centralHomeomorph (G := G))
  have hHC : ∀ a, (HC a : G) = orderedAxes (G := G) u a := fun a => centralAxes_basis b a
  have huΓ : ∀ a, orderedAxes (G := G) u a ∈ Γ ↔ ∀ i, ∃ z : ℤ, a i = z := by
    intro a
    rw [← centralAxes_basis b a,hb]
    simp only [LinearEquiv.apply_symm_apply]
  let HK : (Fin k → ℝ) ≃ₜ π.ker := HC.trans (Homeomorph.setCongr (congrArg SetLike.coe hker))
  have hHK : ∀ a, (HK a : G) = orderedAxes (G := G) u a := hHC
  let T := RawGroupSection.trivialization π hπ.continuous sectionFn hs hsec
  let H := (qh.prodCongr HK).trans T
  have hH : ∀ a z, H (a,z) = orderedAxes (G := G) w a * orderedAxes (G := G) u z := by
    intro a z
    change sectionFn (qh a) * (HK z : G) = _
    change orderedAxes w (qh.symm (qh a)) * (HK z : G) = _
    rw [qh.symm_apply_apply,hHK]
  let P := (RawGroupSection.finAppendHomeomorph n k).symm.trans H
  have hP : (P : (Fin (n+k) → ℝ) → G) = orderedAxes (G := G) (Fin.append w u) := by
    funext a
    change H (a ∘ Fin.castAdd _,a ∘ Fin.natAdd n) = _
    rw [hH,← orderedAxes_append]
    simp only [Function.comp_def,Fin.append_castAdd_natAdd]
  have htemp : IsHomeomorph (orderedAxes (G := G) (Fin.append w u)) ∧
      ∀ a, orderedAxes (G := G) (Fin.append w u) a ∈ Γ ↔ ∀ i, ∃ z : ℤ, a i = z := by
    refine ⟨hP ▸ P.isHomeomorph,?_⟩
    intro a
    let x := a ∘ Fin.castAdd k
    let z := a ∘ Fin.natAdd n
    have ha : a = Fin.append x z := Fin.append_castAdd_natAdd.symm
    rw [ha,orderedAxes_append]
    have hm : orderedAxes w x * orderedAxes u z ∈ Γ ↔
        (∀ i, ∃ q : ℤ, x i = q) ∧ ∀ i, ∃ q : ℤ, z i = q := by
      constructor
      · intro h
        have hq : orderedAxes (G := Q) v x ∈ Γ.map π := by
          have he : π (orderedAxes (G := G) u z) = 1 := by
            rw [← hHK]; exact (HK z).property
          simpa only [map_mul,hproj,he,mul_one] using Subgroup.mem_map_of_mem π h
        have hx := (hvΓ x).mp hq
        have hz : orderedAxes (G := G) u z ∈ Γ := by
          exact (Γ.mul_mem_cancel_left (orderedAxes_int_mem Γ w hwΓ x hx)).mp h
        exact ⟨hx,(huΓ z).mp hz⟩
      · rintro ⟨hx,hz⟩
        exact Γ.mul_mem (orderedAxes_int_mem Γ w hwΓ x hx) ((huΓ z).mpr hz)
    rw [hm]
    constructor
    · rintro ⟨hx,hz⟩ i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using hx j
      · simpa only [Fin.append_right] using hz j
    · intro h
      exact ⟨fun i => by simpa only [Fin.append_left] using h (Fin.castAdd k i),
        fun i => by simpa only [Fin.append_right] using h (Fin.natAdd n i)⟩

  let D : E₀ →L[ℝ] F := mfderiv I₀ 𝓘(ℝ,F) π 1
  have hDK : D.ker = C := tangent_projection_kernel hstop hstopQ π hπ hker
  obtain ⟨bb,hbb⟩ := RawLinearBasis.basis_append_lifts C D.toLinearMap hDK hDsurj v b w hw
  refine ⟨n+k,bb,?_,?_,?_⟩
  · rw [hbb]
    exact htemp.1
  · rw [hbb]
    exact htemp.2
  · intro g
    apply RawLinearBasis.triangular_append C D.toLinearMap hDK v b w hw bb hbb
      (RawLieAdjoint.adjoint (E₀ := E₀) g).toLinearMap
      (RawLieAdjoint.adjoint (E₀ := F) (π g)).toLinearMap
    · exact adjoint_tangent_projection hstopQ π hπ g
    · exact adjoint_central g
    · exact htri (π g)

end RawLieIntegration

namespace RawLieIntegration

 

theorem latticeBasis_dimension_induction (n : ℕ) :
    ∀ (E₀ : Type) [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
      (G : Type) [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
      [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G],
      Module.finrank ℝ E₀ = n → ∀ s : ℕ,
      (⊤ : Subgroup G).lowerCentralSeries s = ⊥ →
      ∀ (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)],
      HasTriangularLatticeBasis (G := G) (E₀ := E₀) Γ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E₀ _ _ _ G _ _ _ _ _ _ hdim s hstop Γ _ _
    let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
    by_cases hz : Module.finrank ℝ E₀ = 0
    · let : Subsingleton E₀ := Module.finrank_zero_iff.mp hz
      let : DiscreteTopology G := ChartedSpace.discreteTopology E₀ G
      let : Subsingleton G := subsingleton_of_preconnected_totallyDisconnected
      refine ⟨0,Module.Basis.empty E₀,?_,?_,?_⟩
      · let : Unique G := ⟨⟨1⟩,fun _ => Subsingleton.elim _ _⟩
        convert (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) G).isHomeomorph using 1
      · intro a
        constructor
        · intro _ i; exact Fin.elim0 i
        · intro _
          convert Γ.one_mem using 1
      · intro g i; exact Fin.elim0 i
    · obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero hz)
      let C := RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
      let S := (centralAxesHom (G := G) (E₀ := E₀)).range
      have hC : C ≠ ⊥ := RawLieAdjoint.centralTangent_ne_bot hstop v hv
      obtain ⟨W,hCW⟩ := Submodule.exists_isCompl C
      have hpos : 0 < Module.finrank ℝ C :=
        Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hC)
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
      let : DiscreteTopology (Γ.map (QuotientGroup.mk' S)) :=
        central_quotient_lattice_discrete (E₀ := E₀) hstop Γ
      let : CompactSpace ((G ⧸ S) ⧸ Γ.map (QuotientGroup.mk' S)) :=
        RawLatticeFiber.compact_quotient_image Γ (QuotientGroup.mk' S)
          QuotientGroup.continuous_mk (QuotientGroup.mk'_surjective S)
      have hQ := ih (Module.finrank ℝ W) hw W (G ⧸ S) rfl s hstopQ (Γ.map (QuotientGroup.mk' S))
      exact latticeBasis_of_central_quotient hstop hstopQ Γ (QuotientGroup.mk' S) hSmooth
        (QuotientGroup.ker_mk' S).symm hSurj hQ

theorem latticeBasis_of_nilpotent
    {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
    [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    HasTriangularLatticeBasis (G := G) (E₀ := E₀) Γ :=
  latticeBasis_dimension_induction (Module.finrank ℝ E₀) E₀ G rfl s hstop Γ

end RawLieIntegration
end

end OAI
