import Mathlib
import OAI.Geometry.NilpotentCharts.AxesDerivatives
import OAI.Geometry.NilpotentCharts.Coordinates
import OAI.Geometry.NilpotentCharts.TriangularBasis

namespace OAI

/-! Rational coordinate multiplication and centric lattice bases. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]

 

theorem coordinateProduct_real_polynomial {n s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b) :
    ∀ j : Fin n, ∃ Q : MvPolynomial (Fin j.val ⊕ Fin j.val) ℝ, ∀ a c,
      coordinateProduct h a c j = a j + c j + MvPolynomial.eval
        (Sum.elim (fun k => a ⟨k.val,lt_trans k.isLt j.isLt⟩)
          (fun k => c ⟨k.val,lt_trans k.isLt j.isLt⟩)) Q := by
  obtain ⟨M,hM,hprefix⟩ := coordinateMC_polynomials hstop b hb
  have H := RawPolynomial.triangular_ode_collection M hprefix (coordinateLine h)
    (coordinateLine_zero b h hh) (coordinateLine_ode b hb h hh M hM)
  simpa only [coordinateLine,one_smul] using H
end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]

theorem coordinateProduct_rational_polynomial {n s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b)
    (hΓ : ∀ a, h a ∈ Γ ↔ ∀ i, ∃ z : ℤ, a i = z) :
    ∀ j : Fin n, ∃ Q : MvPolynomial (Fin j.val ⊕ Fin j.val) ℚ, ∀ a c,
      coordinateProduct h a c j = a j + c j + MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (fun k => a ⟨k.val,lt_trans k.isLt j.isLt⟩)
          (fun k => c ⟨k.val,lt_trans k.isLt j.isLt⟩)) Q := by
  classical
  intro j
  obtain ⟨P,hP⟩ := coordinateProduct_real_polynomial hstop b hb h hh j
  have hint : ∀ x : Fin j.val ⊕ Fin j.val → ℤ, ∃ z : ℤ,
      MvPolynomial.eval (fun i => (x i : ℝ)) P = z := by
    intro x
    let a : Fin n → ℝ := fun k => if hk : k.val < j.val then (x (Sum.inl ⟨k.val,hk⟩) : ℝ) else 0
    let c : Fin n → ℝ := fun k => if hk : k.val < j.val then (x (Sum.inr ⟨k.val,hk⟩) : ℝ) else 0
    have ha : h a ∈ Γ := (hΓ a).mpr (fun k => by
      by_cases hk : k.val < j.val
      · exact ⟨x (Sum.inl ⟨k.val,hk⟩),dite_eq_left hk⟩
      · exact ⟨0,by simp only [a,dite_eq_right hk,Int.cast_zero]⟩)
    have hc : h c ∈ Γ := (hΓ c).mpr (fun k => by
      by_cases hk : k.val < j.val
      · exact ⟨x (Sum.inr ⟨k.val,hk⟩),dite_eq_left hk⟩
      · exact ⟨0,by simp only [c,dite_eq_right hk,Int.cast_zero]⟩)
    have hprod : h (coordinateProduct h a c) ∈ Γ := by
      simpa only [coordinateProduct,h.apply_symm_apply] using Γ.mul_mem ha hc
    obtain ⟨z,hz⟩ := (hΓ _).mp hprod j
    have he := hP a c
    have hvar : Sum.elim (fun k : Fin j.val => a ⟨k.val,lt_trans k.isLt j.isLt⟩)
        (fun k : Fin j.val => c ⟨k.val,lt_trans k.isLt j.isLt⟩) = fun i => (x i : ℝ) := by
      funext i
      cases i with
      | inl k => simp only [Sum.elim_inl,a,dite_eq_left k.isLt]
      | inr k => simp only [Sum.elim_inr,c,dite_eq_left k.isLt]
    simp only [a,c,dite_eq_right (lt_irrefl j.val),zero_add,hvar] at he
    exact ⟨z,he.symm.trans hz⟩
  obtain ⟨Q,hQ⟩ := RawPolynomial.rational_of_integer_values P hint
  refine ⟨Q,?_⟩
  intro a c
  rw [hP,← hQ,MvPolynomial.eval_map]
end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]

include E₀ in
 

theorem rational_secondKind_lattice_coordinates [SimplyConnectedSpace G] {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ (n : ℕ) (c : RationalLattice.RealCoordinates G n),
      MalcevCharacters.SecondKind c ∧
      (∀ g, g ∈ Γ ↔ ∀ j, ∃ z : ℤ, c.coord g j = z) := by
  classical
  obtain ⟨n,b,hb,hΓ,htri⟩ := latticeBasis_of_nilpotent (E₀ := E₀) hstop Γ
  let h := hb.homeomorph (orderedAxes (G := G) b)
  have hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b := rfl
  have hlat : ∀ a, h a ∈ Γ ↔ ∀ j, ∃ z : ℤ, a j = z := hΓ
  choose Q hQ using coordinateProduct_rational_polynomial hstop Γ b htri h hh hlat
  let c : RationalLattice.RealCoordinates G n := {
    coord := h.symm
    one_coord := fun i => by
      have H : h.symm 1 = 0 := h.injective (by simpa only [h.apply_symm_apply,hh] using (orderedAxes_zero (G := G) b).symm)
      rw [H]; rfl
    correction := Q
    mul_coord := fun g k i => by
      have H := hQ i (h.symm g) (h.symm k)
      simpa only [coordinateProduct,h.apply_symm_apply] using H }
  have haxis : ∀ i t, MalcevCharacters.axis c i t = curve (G := G) (b i) t := by
    intro i t
    change orderedAxes (G := G) b (Pi.single i t) = _
    exact orderedAxes_single b i t
  refine ⟨n,c,⟨?_,?_⟩,?_⟩
  · intro i t u
    simp only [haxis]
    exact curve_add (G := G) (b i) t u
  · intro g
    simp only [haxis]
    change g = orderedAxes (G := G) b (h.symm g)
    exact (h.apply_symm_apply g).symm
  · intro g
    change g ∈ Γ ↔ ∀ j, ∃ z : ℤ, h.symm g j = z
    simpa only [h.apply_symm_apply] using hlat (h.symm g)
end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]

def HasCentricLatticeBasis (Γ : Subgroup G) : Prop :=
  ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ E₀),
    IsHomeomorph (orderedAxes (G := G) b) ∧
    (∀ a, orderedAxes (G := G) b a ∈ Γ ↔ ∀ i, ∃ z : ℤ, a i = z) ∧
    (∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (E₀ := E₀) g).toLinearMap) ∧
    ∃ L : (Fin n → ℝ) →ₗ[ℝ] RawLieAdjoint.centralTangent (G := G) (E₀ := E₀),
      ∀ a, orderedAxes (G := G) b a ∈ Subgroup.center G →
        subspaceAxes (G := G) _ (L a) = orderedAxes (G := G) b a
end RawLieIntegration
namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Group Q] [TopologicalSpace Q] [ChartedSpace F Q] [LieGroup 𝓘(ℝ,F) ∞ Q] [T2Space Q]
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

 

theorem centricBasis_of_central_quotient [SimplyConnectedSpace G] [SimplyConnectedSpace Q]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (hstopQ : (⊤ : Subgroup Q).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (π : G →* Q) (hπ : ContMDiff I₀ 𝓘(ℝ,F) ∞ π)
    (hker : S = π.ker)
    (hDsurj : Surjective (mfderiv I₀ 𝓘(ℝ,F) π 1 : E₀ →L[ℝ] F)) (hQ : HasTriangularLatticeBasis (G := Q) (E₀ := F) (Γ.map π)) :
    HasCentricLatticeBasis (G := G) (E₀ := E₀) Γ := by
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
  refine ⟨n+k,bb,?_,?_,?_,?_⟩
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

  · let L : (Fin (n+k) → ℝ) →ₗ[ℝ] C := b.equivFun.symm.toLinearMap.comp
        (LinearMap.pi (fun i : Fin k => LinearMap.proj (Fin.natAdd n i)))
    refine ⟨L,?_⟩
    intro a ha
    have haS : orderedAxes (G := G) bb a ∈ S := by
      rw [centralAxesHom_range_eq_center hstop]
      exact ha
    have hp1 : π (orderedAxes (G := G) bb a) = 1 := by
      rw [hker] at haS
      exact haS
    let x := a ∘ Fin.castAdd k
    let z := a ∘ Fin.natAdd n
    have hre : orderedAxes (G := G) bb a = orderedAxes w x * orderedAxes u z := by
      erw [hbb,show a = Fin.append x z from Fin.append_castAdd_natAdd.symm,orderedAxes_append]
    have hz1 : π (orderedAxes (G := G) u z) = 1 := by
      rw [← hHK]
      exact (HK z).property
    rw [hre,map_mul,hproj,hz1,mul_one] at hp1
    have hx0 : x = 0 := qh.injective (hp1.trans (orderedAxes_zero v).symm)
    have hLa : subspaceAxes (G := G) C (L a) = orderedAxes (G := G) u z := by
      change (HC z : G) = _
      exact hHC z
    rw [hLa,hre,hx0,orderedAxes_zero,one_mul]

end RawLieIntegration

namespace RawLieIntegration

theorem centricBasis_of_nilpotent
    {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
    [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    HasCentricLatticeBasis (G := G) (E₀ := E₀) Γ := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
  let C := RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
  let S := (centralAxesHom (G := G) (E₀ := E₀)).range
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
  let : DiscreteTopology (Γ.map (QuotientGroup.mk' S)) :=
    central_quotient_lattice_discrete (E₀ := E₀) hstop Γ
  let : CompactSpace ((G ⧸ S) ⧸ Γ.map (QuotientGroup.mk' S)) :=
    RawLatticeFiber.compact_quotient_image Γ (QuotientGroup.mk' S)
      QuotientGroup.continuous_mk (QuotientGroup.mk'_surjective S)
  have hQ := latticeBasis_of_nilpotent (E₀ := W) hstopQ (Γ.map (QuotientGroup.mk' S))
  exact centricBasis_of_central_quotient hstop hstopQ Γ (QuotientGroup.mk' S) hSmooth
    (QuotientGroup.ker_mk' S).symm hSurj hQ
end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]

include E₀ in
 

theorem centric_rational_coordinates [SimplyConnectedSpace G] {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ (n : ℕ) (c : RationalLattice.RealCoordinates G n),
      MalcevCharacters.SecondKind c ∧
      (∀ g, g ∈ Γ ↔ ∀ j, ∃ z : ℤ, c.coord g j = z) ∧
      ∃ L : (Fin n → ℝ) →ₗ[ℝ] RawLieAdjoint.centralTangent (G := G) (E₀ := E₀),
        ∀ g, g ∈ Subgroup.center G → subspaceAxes (G := G) _ (L (c.coord g)) = g := by
  classical
  obtain ⟨n,b,hb,hΓ,htri,L,hL⟩ := centricBasis_of_nilpotent (E₀ := E₀) hstop Γ
  let h := hb.homeomorph (orderedAxes (G := G) b)
  have hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b := rfl
  have hlat : ∀ a, h a ∈ Γ ↔ ∀ j, ∃ z : ℤ, a j = z := hΓ
  choose Q hQ using coordinateProduct_rational_polynomial hstop Γ b htri h hh hlat
  let c : RationalLattice.RealCoordinates G n := {
    coord := h.symm
    one_coord := fun i => by
      have H : h.symm 1 = 0 := h.injective (by simpa only [h.apply_symm_apply,hh] using (orderedAxes_zero (G := G) b).symm)
      rw [H]; rfl
    correction := Q
    mul_coord := fun g k i => by
      have H := hQ i (h.symm g) (h.symm k)
      simpa only [coordinateProduct,h.apply_symm_apply] using H }
  have haxis : ∀ i t, MalcevCharacters.axis c i t = curve (G := G) (b i) t := by
    intro i t
    change orderedAxes (G := G) b (Pi.single i t) = _
    exact orderedAxes_single b i t
  refine ⟨n,c,⟨?_,?_⟩,?_,L,?_⟩
  · intro i t u
    simp only [haxis]
    exact curve_add (G := G) (b i) t u
  · intro g
    simp only [haxis]
    change g = orderedAxes (G := G) b (h.symm g)
    exact (h.apply_symm_apply g).symm
  · intro g
    change g ∈ Γ ↔ ∀ j, ∃ z : ℤ, h.symm g j = z
    simpa only [h.apply_symm_apply] using hlat (h.symm g)
  · intro g hg
    have he : orderedAxes (G := G) b (h.symm g) = g := h.apply_symm_apply g
    exact (hL (h.symm g) (by rw [he]; exact hg)).trans he
end RawLieIntegration
end

end OAI
