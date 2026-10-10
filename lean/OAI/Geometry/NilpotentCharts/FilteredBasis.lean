import Mathlib
import OAI.Geometry.NilpotentCharts.CentralSubspaces
import OAI.Geometry.NilpotentCharts.Filtrations
import OAI.Geometry.NilpotentCharts.SubspaceQuotients

namespace OAI

/-! Filtered lattice bases and rational charts for simply connected nilpotent Lie groups. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)
variable (K : Submodule ℝ E₀) (hKC : K ≤ (RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)))
include hKC

lemma centralSubspace_smul (z : K) (t : ℝ) :
    subspaceAxes (G := G) K (t • z) = curve (G := G) z.val t := by
  rw [subspaceAxes_central_inclusion (G := G) K hKC,map_smul]
  exact centralAxes_smul (K.inclusion hKC z) t

lemma centralSubspace_add (z w : K) :
    subspaceAxes (G := G) K (z+w) = subspaceAxes K z * subspaceAxes K w := by
  rw [subspaceAxes_central_inclusion (G := G) K hKC,map_add,subspaceAxes_central_add,
    ← subspaceAxes_central_inclusion (G := G) K hKC,← subspaceAxes_central_inclusion (G := G) K hKC]

lemma centralSubspace_sum (l : List K) :
    subspaceAxes (G := G) K l.sum = (l.map (subspaceAxes K)).prod := by
  induction l with
  | nil => simp
  | cons z l ih => simp only [List.sum_cons,centralSubspace_add (G := G) K hKC,ih,List.map_cons,List.prod_cons]

lemma centralSubspace_basis {n : ℕ} (b : Module.Basis (Fin n) ℝ K) (a : Fin n → ℝ) :
    subspaceAxes (G := G) K (b.equivFun.symm a) =
      orderedAxes (G := G) (fun i => (show GroupLieAlgebra I₀ G from (b i).val)) a := by
  rw [Module.Basis.equivFun_symm_apply]
  have H := centralSubspace_sum (G := G) K hKC (List.ofFn (fun i => a i • b i))
  simp only [List.sum_ofFn,List.map_ofFn] at H
  rw [H]
  congr 2
  funext i
  exact centralSubspace_smul (G := G) K hKC (b i) (a i)

lemma centralSubspace_eq_exp (v : K) : subspaceAxes (G := G) K v = exp (G := G) v.val := by
  rw [subspaceAxes_central_inclusion (G := G) K hKC,centralAxes_eq_exp]
  rfl

variable [SimplyConnectedSpace G] {s : ℕ}

def centralSubspaceHomeomorph (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    K ≃ₜ (centralSubspaceHom (G := G) K hKC).range :=
  (centralSubspaceAxes_closedEmbedding (G := G) K hKC hstop).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (Set.ext (fun g => (centralSubspace_range_membership (G := G) K hKC g).symm)))

lemma centralSubspaceHomeomorph_apply (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (v : K) :
    (centralSubspaceHomeomorph (G := G) K hKC hstop v : G) = subspaceAxes K v := rfl

lemma centralSubspace_lattice_discrete (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    DiscreteTopology ((Γ.comap (centralSubspaceHom (G := G) K hKC)).toAddSubgroup) := by
  have he := centralSubspaceAxes_closedEmbedding (G := G) K hKC hstop
  apply DiscreteTopology.preimage_of_continuous_injective (Γ : Set G)
  · exact he.continuous.congr (fun v => (centralSubspaceHom_apply (G := G) K hKC v).symm)
  · intro x y hxy
    apply he.injective
    change centralSubspaceHom (G := G) K hKC (Multiplicative.ofAdd x) =
      centralSubspaceHom (G := G) K hKC (Multiplicative.ofAdd y) at hxy
    exact (centralSubspaceHom_apply (G := G) K hKC x).symm.trans
      (hxy.trans (centralSubspaceHom_apply (G := G) K hKC y))

lemma centralSubspace_lattice_cocompact (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ]
    (hspan : Submodule.span ℝ {v : K | subspaceAxes (G := G) K v ∈ Γ} = ⊤) :
    CompactSpace ((centralSubspaceHom (G := G) K hKC).range ⧸
      Γ.comap (centralSubspaceHom (G := G) K hKC).range.subtype) := by
  let S := (centralSubspaceHom (G := G) K hKC).range
  let L : AddSubgroup K := (Γ.comap (centralSubspaceHom (G := G) K hKC)).toAddSubgroup
  let : DiscreteTopology L := centralSubspace_lattice_discrete (G := G) K hKC hstop Γ
  have hL : Submodule.span ℝ (L : Set K) = ⊤ := by
    convert hspan using 2
    ext v
    change centralSubspaceHom (G := G) K hKC (Multiplicative.ofAdd v) ∈ Γ ↔ _
    rw [centralSubspaceHom_apply]
    rfl
  let : CompactSpace (K ⧸ L) := RawLattice.compact_quotient_of_span L hL
  let h := centralSubspaceHomeomorph (G := G) K hKC hstop
  let q : (K ⧸ L) ≃ₜ (S ⧸ Γ.comap S.subtype) := Homeomorph.Quotient.congr h (by
    intro x y
    rw [QuotientAddGroup.leftRel_apply,QuotientGroup.leftRel_apply]
    change centralSubspaceHom (G := G) K hKC (Multiplicative.ofAdd (-x+y)) ∈ Γ ↔
      (subspaceAxes K x)⁻¹ * subspaceAxes K y ∈ Γ
    rw [centralSubspaceHom_apply,centralSubspace_add (G := G) K hKC]
    have hn : subspaceAxes (G := G) K (-x) = (subspaceAxes K x)⁻¹ := by
      have H := map_inv (centralSubspaceHom (G := G) K hKC) (Multiplicative.ofAdd x)
      change centralSubspaceHom (G := G) K hKC (Multiplicative.ofAdd (-x)) = _ at H
      simpa only [centralSubspaceHom_apply] using H
    rw [hn])
  exact q.compactSpace

lemma exists_subspace_lattice_basis (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ]
    (hspan : Submodule.span ℝ {v : K | subspaceAxes (G := G) K v ∈ Γ} = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ K), ∀ v : K,
      subspaceAxes (G := G) K v ∈ Γ ↔ ∀ i, ∃ z : ℤ, b.equivFun v i = z := by
  let L : AddSubgroup K := (Γ.comap (centralSubspaceHom (G := G) K hKC)).toAddSubgroup
  let : DiscreteTopology L := centralSubspace_lattice_discrete (G := G) K hKC hstop Γ
  have hL : Submodule.span ℝ (L : Set K) = ⊤ := by
    convert hspan using 2
    ext v
    change centralSubspaceHom (G := G) K hKC (Multiplicative.ofAdd v) ∈ Γ ↔ _
    rw [centralSubspaceHom_apply]
    rfl
  obtain ⟨n,b,hb⟩ := RawLattice.exists_vector_lattice_basis_of_span L hL
  refine ⟨n,b,?_⟩
  intro v
  have he : v ∈ L ↔ subspaceAxes (G := G) K v ∈ Γ := by
    change centralSubspaceHom (G := G) K hKC (Multiplicative.ofAdd v) ∈ Γ ↔ _
    rw [centralSubspaceHom_apply]
  rw [← he]
  exact hb v

variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Group Q] [TopologicalSpace Q] [ChartedSpace F Q] [LieGroup 𝓘(ℝ,F) ∞ Q] [T2Space Q]

lemma subspace_tangent_projection_kernel [SimplyConnectedSpace Q]
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) {t : ℕ}
    (hstopQ : (⊤ : Subgroup Q).lowerCentralSeries t = ⊥)
    (π : G →* Q) (hπ : ContMDiff I₀ 𝓘(ℝ,F) ∞ π)
    (hker : (centralSubspaceHom (G := G) K hKC).range = π.ker) :
    (mfderiv I₀ 𝓘(ℝ,F) π 1 : E₀ →L[ℝ] F).ker = K := by
  apply Submodule.ext
  intro v
  have hc : v ∈ K ↔ exp (G := G) v ∈ (centralSubspaceHom (G := G) K hKC).range := by
    rw [centralSubspace_range_membership (G := G) K hKC]
    constructor
    · intro hv
      exact ⟨⟨v,hv⟩,centralSubspace_eq_exp (G := G) K hKC _⟩
    · rintro ⟨z,hz⟩
      rw [centralSubspace_eq_exp (G := G) K hKC] at hz
      have hv := exp_injective_of_nilpotent hstop hz
      exact hv ▸ z.property
  change mfderiv I₀ 𝓘(ℝ,F) π 1 v = 0 ↔ v ∈ K
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
end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

def HasFilteredLatticeBasis (Γ : Subgroup G) (s : ℕ) : Prop :=
  ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ E₀),
    IsHomeomorph (orderedAxes (G := G) b) ∧
    (∀ a, orderedAxes (G := G) b a ∈ Γ ↔ ∀ i, ∃ z : ℤ, a i = z) ∧
    (∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (E₀ := E₀) g).toLinearMap) ∧
    ∃ w : Fin n → ℕ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ s) ∧ Monotone w ∧
      ∀ j a, orderedAxes (G := G) b a ∈ closure ((⊤ : Subgroup G).lowerCentralSeries (j-1) : Set G) ↔
        ∀ i, w i < j → a i = 0

variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Group Q] [TopologicalSpace Q] [ChartedSpace F Q] [LieGroup 𝓘(ℝ,F) ∞ Q] [T2Space Q]
theorem filteredBasis_of_subspace_quotient [SimplyConnectedSpace G] [SimplyConnectedSpace Q]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries (s+1) = ⊥)
    (hstopQ : (⊤ : Subgroup Q).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (K : Submodule ℝ E₀) (hKC : K ≤ RawLieAdjoint.centralTangent (G := G) (E₀ := E₀))
    (hspan : Submodule.span ℝ {v : K | subspaceAxes (G := G) K v ∈ Γ} = ⊤)
    (π : G →* Q) (hπ : ContMDiff I₀ 𝓘(ℝ,F) ∞ π)
    (hker : (centralSubspaceHom (G := G) K hKC).range = π.ker)
    (hkerLevel : (π.ker : Set G) = closure ((⊤ : Subgroup G).lowerCentralSeries s : Set G))
    (hπopen : IsOpenMap π) (hπsurj : Surjective π)
    (hDsurj : Surjective (mfderiv I₀ 𝓘(ℝ,F) π 1 : E₀ →L[ℝ] F)) (hQ : HasFilteredLatticeBasis (G := Q) (E₀ := F) (Γ.map π) s) :
    HasFilteredLatticeBasis (G := G) (E₀ := E₀) Γ (s+1) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  let : IsTopologicalGroup Q := topologicalGroup_of_lieGroup 𝓘(ℝ,F) ∞
  obtain ⟨n,v,hv,hvΓ,htri,wq,hwpos,hwbound,hwmono,hwlevel⟩ := hQ
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
  obtain ⟨k,b,hb⟩ := exists_subspace_lattice_basis (G := G) K hKC hstop Γ hspan
  let u : Fin k → GroupLieAlgebra I₀ G := fun i => (b i).val
  let HC : (Fin k → ℝ) ≃ₜ (centralSubspaceHom (G := G) K hKC).range :=
    b.equivFun.toContinuousLinearEquiv.symm.toHomeomorph.trans (centralSubspaceHomeomorph (G := G) K hKC hstop)
  have hHC : ∀ a, (HC a : G) = orderedAxes (G := G) u a := fun a => centralSubspace_basis (G := G) K hKC b a
  have huΓ : ∀ a, orderedAxes (G := G) u a ∈ Γ ↔ ∀ i, ∃ z : ℤ, a i = z := by
    intro a
    rw [← centralSubspace_basis (G := G) K hKC b a,hb]
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
  have hDK : D.ker = K := subspace_tangent_projection_kernel K hKC hstop hstopQ π hπ hker
  obtain ⟨bb,hbb⟩ := RawLinearBasis.basis_append_lifts K D.toLinearMap hDK hDsurj v b w hw
  have hBB : IsHomeomorph (orderedAxes (G := G) (bb : Fin (n+k) → E₀)) := by
    rw [hbb]
    exact htemp.1
  refine ⟨n+k,bb,hBB,?_,?_,Fin.append wq (fun _ : Fin k => s+1),
    RawFilteredWeights.append_pos wq s hwpos,
    RawFilteredWeights.append_bound wq s hwbound,
    RawFilteredWeights.append_monotone wq s hwmono hwbound,?_⟩
  · rw [hbb]
    exact htemp.2
  · intro g
    apply RawLinearBasis.triangular_append K D.toLinearMap hDK v b w hw bb hbb
      (RawLieAdjoint.adjoint (E₀ := E₀) g).toLinearMap
      (RawLieAdjoint.adjoint (E₀ := F) (π g)).toLinearMap
    · exact adjoint_tangent_projection hstopQ π hπ g
    · intro z
      exact adjoint_central g (K.inclusion hKC z)
    · exact htri (π g)

  · intro l a
    let x : Fin n → ℝ := a ∘ Fin.castAdd k
    let z : Fin k → ℝ := a ∘ Fin.natAdd n
    have ha : a = Fin.append x z := Fin.append_castAdd_natAdd.symm
    have hp : π (orderedAxes (G := G) bb a) = orderedAxes (G := Q) v x := by
      erw [hbb,ha,orderedAxes_append,map_mul,hproj,← hHK]
      rw [(show π (HK z : G) = 1 from (HK z).property),mul_one]
    by_cases hl : l ≤ s+1
    · have hkl : π.ker ≤ RawClosedFiltration.level (G := G) l := by
        have he : π.ker = RawClosedFiltration.level (G := G) (s+1) := by
          apply SetLike.ext'
          simpa only [RawClosedFiltration.level,Nat.add_sub_cancel,Subgroup.topologicalClosure_coe] using hkerLevel
        rw [he]
        exact RawClosedFiltration.antitone_level hl
      have he := RawClosedFiltration.comap_level π hπ.continuous hπopen hπsurj l hkl
      change orderedAxes (G := G) bb a ∈ RawClosedFiltration.level (G := G) l ↔ _
      rw [← he]
      change π (orderedAxes (G := G) bb a) ∈ RawClosedFiltration.level (G := Q) l ↔ _
      rw [hp,RawFilteredWeights.append_zero_iff wq s hl]
      exact hwlevel l x
    · have hzero : RawClosedFiltration.level (G := G) l = ⊥ := by
        apply le_antisymm ?_ bot_le
        calc
          RawClosedFiltration.level (G := G) l ≤ RawClosedFiltration.level (G := G) (s+1+1) :=
            RawClosedFiltration.antitone_level (by omega)
          _ = ⊥ := RawClosedFiltration.level_terminal hstop
      change orderedAxes (G := G) bb a ∈ RawClosedFiltration.level (G := G) l ↔ _
      rw [hzero,Subgroup.mem_bot]
      constructor
      · intro hg i hi
        have hz : a = 0 := (hBB.homeomorph (orderedAxes (G := G) bb)).injective
          (hg.trans (orderedAxes_zero (G := G) bb).symm)
        exact congrFun hz i
      · intro hz
        have ha0 : a = 0 := by
          funext i
          exact hz i (lt_of_le_of_lt (RawFilteredWeights.append_bound wq s hwbound i) (by omega))
        rw [ha0]
        exact orderedAxes_zero (G := G) bb
end RawLieIntegration

namespace RawLieIntegration
 

theorem filteredBasis_class_induction (s : ℕ) :
    ∀ (E₀ : Type) [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
      (G : Type) [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
      [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G],
      (⊤ : Subgroup G).lowerCentralSeries s = ⊥ →
      ∀ (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)],
      HasFilteredLatticeBasis (G := G) (E₀ := E₀) Γ s := by
  induction s with
  | zero =>
    intro E₀ _ _ _ G _ _ _ _ _ _ hstop Γ _ _
    let : Subsingleton G := ⟨fun g h => by
      have hz : (⊤ : Subgroup G) = ⊥ := by simpa only [Subgroup.lowerCentralSeries_zero] using hstop
      have hg : g = 1 := Subgroup.mem_bot.mp (hz ▸ (Subgroup.mem_top g))
      have hh : h = 1 := Subgroup.mem_bot.mp (hz ▸ (Subgroup.mem_top h))
      exact hg.trans hh.symm⟩
    let : Subsingleton E₀ := ⟨fun v w => exp_injective_of_nilpotent (E₀ := E₀) hstop (Subsingleton.elim _ _)⟩
    let b : Module.Basis (Fin 0) ℝ E₀ := Module.Basis.empty E₀
    refine ⟨0,b,?_,?_,?_,(fun i => Fin.elim0 i),?_,?_,?_,?_⟩
    · let : Unique G := ⟨⟨1⟩,fun _ => Subsingleton.elim _ _⟩
      convert (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) G).isHomeomorph using 1
    · intro a
      constructor
      · intro _ i; exact Fin.elim0 i
      · intro _; convert Γ.one_mem using 1
    · intro g i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro j a
      constructor
      · intro _ i; exact Fin.elim0 i
      · intro _
        have he : orderedAxes (G := G) b a = 1 := Subsingleton.elim _ _
        rw [he]
        exact subset_closure (Subgroup.one_mem _)
  | succ s ih =>
    intro E₀ _ _ _ G _ _ _ _ _ _ hstop Γ _ _
    let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
    obtain ⟨K,hKC,hK,hspan⟩ := last_central_rational_subspace (E₀ := E₀) hstop Γ
    let S := (centralSubspaceHom (G := G) K hKC).range
    let : S.Normal := centralSubspace_range_normal (G := G) K hKC
    have hSC : IsClosed (S : Set G) := centralSubspace_range_closed (G := G) K hKC hstop
    let : IsClosed (S : Set G) := hSC
    let : T2Space (G ⧸ S) := QuotientGroup.instT2Space
    have hSmem : ∀ g, g ∈ S ↔ ∃ v : K, subspaceAxes (G := G) K v = g :=
      centralSubspace_range_membership (G := G) K hKC
    have hEmb := (centralSubspaceAxes_closedEmbedding (G := G) K hKC hstop).isEmbedding
    let : SimplyConnectedSpace (G ⧸ S) := subspace_quotient_simplyConnected K S hSmem hEmb
    obtain ⟨W,hKW⟩ := Submodule.exists_isCompl K
    obtain ⟨cs,hLie,hSmooth,hSurj⟩ := exists_subspace_quotient_submersion K S hSmem hEmb W hKW.symm
    let := cs
    let := hLie
    let π := QuotientGroup.mk' S
    have hstopQ : (⊤ : Subgroup (G ⧸ S)).lowerCentralSeries s = ⊥ := by
      have hm : ((⊤ : Subgroup G).lowerCentralSeries s).map π = ⊥ := by
        apply (Subgroup.map_eq_bot_iff _).mpr
        rw [QuotientGroup.ker_mk',show S = ((⊤ : Subgroup G).lowerCentralSeries s).topologicalClosure from hK]
        exact Subgroup.le_topologicalClosure _
      simpa only [Subgroup.map_lowerCentralSeries,Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective S)] using hm
    let : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace E₀ G
    let : LocallyCompactSpace S := hSC.locallyCompactSpace
    let : CompactSpace (S ⧸ Γ.comap S.subtype) :=
      centralSubspace_lattice_cocompact (G := G) K hKC hstop Γ hspan
    let : DiscreteTopology (Γ.map π) := RawLatticeFiber.discrete_quotient_of_compact_kernel Γ S
    let : CompactSpace ((G ⧸ S) ⧸ Γ.map π) :=
      RawLatticeFiber.compact_quotient_image Γ π QuotientGroup.continuous_mk (QuotientGroup.mk'_surjective S)
    have hQ := ih W (G ⧸ S) hstopQ (Γ.map π)
    apply filteredBasis_of_subspace_quotient hstop hstopQ Γ K hKC hspan π hSmooth
      (QuotientGroup.ker_mk' S).symm ?_ QuotientGroup.isOpenMap_coe (QuotientGroup.mk'_surjective S) hSurj hQ
    rw [QuotientGroup.ker_mk']
    exact congrArg SetLike.coe hK

variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
theorem filteredBasis_of_nilpotent {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    HasFilteredLatticeBasis (G := G) (E₀ := E₀) Γ s :=
  filteredBasis_class_induction s E₀ G hstop Γ
end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
include E₀ in
 

theorem rawChart_of_nilpotent {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Nonempty (SourceProductChart.Chart s G Γ) := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
  obtain ⟨n,b,hb,hΓ,htri,w,hwpos,_,hwmono,hwlevel⟩ := filteredBasis_of_nilpotent (E₀ := E₀) hstop Γ
  let h := hb.homeomorph (orderedAxes (G := G) b)
  have hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b := rfl
  have hlat : ∀ a, h a ∈ Γ ↔ ∀ i, ∃ z : ℤ, a i = z := hΓ
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
  have hsecond : MalcevCharacters.SecondKind c := by
    constructor
    · intro i t u
      simp only [haxis]
      exact curve_add (G := G) (b i) t u
    · intro g
      simp only [haxis]
      change g = orderedAxes (G := G) b (h.symm g)
      exact (h.apply_symm_apply g).symm
  refine ⟨{
    dim := n
    coords := c
    second := hsecond
    filtration := {
      level := RawClosedFiltration.level
      antitone := RawClosedFiltration.antitone_level
      commutator_le := RawClosedFiltration.bracket_level }
    weight := w
    level_iff := ?_
    weight_pos := hwpos
    lattice_iff := ?_
    weight_mono := hwmono
    level0 := RawClosedFiltration.level_zero
    level1 := RawClosedFiltration.level_one
    step := RawClosedFiltration.level_terminal hstop }⟩
  · intro k g
    change g ∈ closure ((⊤ : Subgroup G).lowerCentralSeries (k-1) : Set G) ↔
      ∀ i, w i < k → h.symm g i = 0
    have H := hwlevel k (h.symm g)
    rw [← hh,h.apply_symm_apply] at H
    exact H
  · intro g
    change g ∈ Γ ↔ ∀ j, ∃ z : ℤ, h.symm g j = z
    simpa only [h.apply_symm_apply] using hlat (h.symm g)
end RawLieIntegration

namespace SourceRawChartGap
 

theorem rawChartExists : RawChartExists := by
  intro s d G _ _ _ _ _ _ _ _ Γ _ _ hstop
  exact RawLieIntegration.rawChart_of_nilpotent (E₀ := EuclideanSpace ℝ (Fin d)) hstop Γ
end SourceRawChartGap

 
theorem raw_chart_reference : SourceRawChartGap.RawChartExists :=
  SourceRawChartGap.rawChartExists
end

end OAI
