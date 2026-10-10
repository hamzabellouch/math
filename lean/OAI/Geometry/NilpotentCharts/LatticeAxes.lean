import Mathlib
import OAI.Geometry.NilpotentCharts.Exponential
import OAI.Geometry.NilpotentCharts.LatticeQuotients
import OAI.Geometry.NilpotentCharts.LinearLattices

namespace OAI

/-! Integral axes and lattice-adapted global coordinates. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
local notation "I₀" => 𝓘(ℝ,E₀)
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

 

theorem central_quotient_lattice_discrete {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    DiscreteTopology (Γ.map (QuotientGroup.mk' S)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  obtain ⟨A,hA⟩ := finite_lattice_centralizer (E₀ := E₀) hstop Γ
  apply RawLatticeProjection.discrete_map Γ S centralAxesHom_range_le_center A
  intro g hg
  rw [centralAxesHom_range_eq_center hstop]
  exact hA g hg

 

theorem central_lattice_cocompact {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    CompactSpace (S ⧸ Γ.comap (Subgroup.subtype S)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  let : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace E₀ G
  let := central_quotient_lattice_discrete (E₀ := E₀) hstop Γ
  exact RawLatticeFiber.compact_fiber Γ S centralAxesHom_range_isClosed

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

lemma centralAxes_sum (l : List C) :
    subspaceAxes (G := G) C l.sum = (l.map (subspaceAxes (G := G) C)).prod := by
  induction l with
  | nil => simp
  | cons z l ih => simp only [List.sum_cons,subspaceAxes_central_add,ih,List.map_cons,List.prod_cons]

lemma centralAxes_smul (z : C) (t : ℝ) :
    subspaceAxes (G := G) C (t • z) = curve (G := G) z.val t := by
  rw [centralAxes_eq_exp]
  exact exp_smul (show GroupLieAlgebra I₀ G from z.val) t

lemma centralAxes_basis {n : ℕ} (b : Module.Basis (Fin n) ℝ C) (a : Fin n → ℝ) :
    subspaceAxes (G := G) C (b.equivFun.symm a) =
      orderedAxes (G := G) (fun i => (show GroupLieAlgebra I₀ G from (b i).val)) a := by
  rw [Module.Basis.equivFun_symm_apply]
  have H := centralAxes_sum (G := G) (List.ofFn (fun i => a i • b i))
  simp only [List.sum_ofFn,List.map_ofFn] at H
  rw [H]
  congr 2
  funext i
  exact centralAxes_smul (b i) (a i)

 

theorem exists_central_lattice_basis [SimplyConnectedSpace G] {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ C), ∀ z : C,
      subspaceAxes (G := G) C z ∈ Γ ↔ ∀ i, ∃ k : ℤ, b.equivFun z i = k := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  let : SimplyConnectedSpace S := central_range_simplyConnected_of_nilpotent hstop
  let : CompactSpace (S ⧸ Γ.comap (Subgroup.subtype S)) := central_lattice_cocompact hstop Γ
  let h : C ≃ₜ S := centralHomeomorph (G := G)
  let L : AddSubgroup C := ((Γ.comap (Subgroup.subtype S)).comap
    (centralAxesHom (G := G) (E₀ := E₀)).rangeRestrict).toAddSubgroup
  let : DiscreteTopology L := DiscreteTopology.preimage_of_continuous_injective
    (Γ : Set G) (continuous_subtype_val.comp h.continuous) (Subtype.val_injective.comp h.injective)
  let q : (C ⧸ L) ≃ₜ (S ⧸ Γ.comap (Subgroup.subtype S)) := Homeomorph.Quotient.congr h (by
    intro x y
    rw [QuotientAddGroup.leftRel_apply,QuotientGroup.leftRel_apply]
    change subspaceAxes C (-x+y) ∈ Γ ↔ (subspaceAxes C x)⁻¹ * subspaceAxes C y ∈ Γ
    rw [subspaceAxes_central_add]
    have hn : subspaceAxes (G := G) C (-x) = (subspaceAxes C x)⁻¹ :=
      map_inv (centralAxesHom (G := G) (E₀ := E₀)) (Multiplicative.ofAdd x)
    rw [hn])
  let : CompactSpace (C ⧸ L) := q.symm.compactSpace
  obtain ⟨n,b,hb⟩ := RawLattice.exists_vector_lattice_basis L
  exact ⟨n,b,hb⟩

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

lemma curve_int (v : GroupLieAlgebra I₀ G) (z : ℤ) : curve v (z : ℝ) = (exp v)^z := by
  have H := map_zpow (oneParameter v) (Multiplicative.ofAdd (1 : ℝ)) z
  change curve v (z • (1 : ℝ)) = (exp v)^z at H
  simpa only [zsmul_eq_mul,mul_one] using H

lemma orderedAxes_int_mem {n : ℕ} (Γ : Subgroup G) (v : Fin n → GroupLieAlgebra I₀ G)
    (hv : ∀ i, exp (v i) ∈ Γ) (a : Fin n → ℝ) (ha : ∀ i, ∃ z : ℤ, a i = z) :
    orderedAxes (G := G) v a ∈ Γ := by
  apply Γ.list_prod_mem
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  obtain ⟨z,hz⟩ := ha i
  rw [hz,curve_int]
  exact Γ.zpow_mem (hv i) z

def HasLatticeAxes (Γ : Subgroup G) : Prop := ∃ (n : ℕ) (v : Fin n → E₀),
  IsHomeomorph (orderedAxes (G := G) v) ∧
    ∀ a, orderedAxes (G := G) v a ∈ Γ ↔ ∀ i, ∃ z : ℤ, a i = z

variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Group Q] [TopologicalSpace Q] [ChartedSpace F Q] [LieGroup 𝓘(ℝ,F) ∞ Q] [T2Space Q]
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

 

theorem latticeAxes_of_central_quotient [SimplyConnectedSpace G] [SimplyConnectedSpace Q]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (hstopQ : (⊤ : Subgroup Q).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (π : G →* Q) (hπ : ContMDiff I₀ 𝓘(ℝ,F) ∞ π)
    (hker : S = π.ker) (hQ : HasLatticeAxes (G := Q) (E₀ := F) (Γ.map π)) :
    HasLatticeAxes (G := G) (E₀ := E₀) Γ := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  let : IsTopologicalGroup Q := topologicalGroup_of_lieGroup 𝓘(ℝ,F) ∞
  let : SimplyConnectedSpace S := central_range_simplyConnected_of_nilpotent hstop
  obtain ⟨n,v,hv,hvΓ⟩ := hQ
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
  refine ⟨n+k,Fin.append w u,hP ▸ P.isHomeomorph,?_⟩
  intro a
  let x := a ∘ Fin.castAdd k
  let z := a ∘ Fin.natAdd n
  have ha : a = Fin.append x z := Fin.append_castAdd_natAdd.symm
  erw [ha,orderedAxes_append]
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

end RawLieIntegration

namespace RawLieIntegration

 

theorem latticeAxes_dimension_induction (n : ℕ) :
    ∀ (E₀ : Type) [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
      (G : Type) [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
      [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G],
      Module.finrank ℝ E₀ = n → ∀ s : ℕ,
      (⊤ : Subgroup G).lowerCentralSeries s = ⊥ →
      ∀ (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)],
      HasLatticeAxes (G := G) (E₀ := E₀) Γ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E₀ _ _ _ G _ _ _ _ _ _ hdim s hstop Γ _ _
    let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
    by_cases hz : Module.finrank ℝ E₀ = 0
    · let : Subsingleton E₀ := Module.finrank_zero_iff.mp hz
      let : DiscreteTopology G := ChartedSpace.discreteTopology E₀ G
      let : Subsingleton G := subsingleton_of_preconnected_totallyDisconnected
      refine ⟨0,Fin.elim0,?_,?_⟩
      · let : Unique G := ⟨⟨1⟩,fun _ => Subsingleton.elim _ _⟩
        convert (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) G).isHomeomorph using 1
      · intro a
        constructor
        · intro _ i; exact Fin.elim0 i
        · intro _
          convert Γ.one_mem using 1
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
      exact latticeAxes_of_central_quotient hstop hstopQ Γ (QuotientGroup.mk' S) hSmooth
        (QuotientGroup.ker_mk' S).symm hQ

theorem latticeAxes_of_nilpotent
    {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
    [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    HasLatticeAxes (G := G) (E₀ := E₀) Γ :=
  latticeAxes_dimension_induction (Module.finrank ℝ E₀) E₀ G rfl s hstop Γ

end RawLieIntegration
end

end OAI
