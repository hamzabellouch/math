import OAI.Analysis.InterpolatedFactors.FiniteCorners

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace FreeGroupFactorMain.Amplification

section

variable {G : Type u_1} {H : Type u_2} [Group G] [Group H]

def groupPolynomial (p : G →₀ ℂ) : groupVonNeumann G :=
  p.sum (fun g z => z • groupUnitary g)

theorem groupPolynomial_dense (ξ : GroupHilbert G) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G →₀ ℂ, ‖groupL2 (groupPolynomial p)-ξ‖ < ε := by
  classical
  let K := Submodule.span ℂ (Set.range (fun g : G => groupL2 (groupUnitary g)))
  have ht : ⊤ ≤ K.topologicalClosure := by
    apply group_single_total _ (Submodule.isClosed_topologicalClosure _)
    intro g
    rw [← groupL2_groupUnitary g]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g,rfl⟩)
  have hx : ξ ∈ closure (K : Set (GroupHilbert G)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact ht trivial
  obtain ⟨x,hx,hd⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨p,hp⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨p,?_⟩
  have he : groupL2 (groupPolynomial p) = x := by
    rw [groupPolynomial,Finsupp.sum]
    simp only [map_sum,map_smul]
    exact hp
  rw [he,← dist_eq_norm,dist_comm]
  exact hd

theorem trace_iso_orbit_total (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun g : G => groupL2 (Φ (groupUnitary g))))).topologicalClosure := by
  classical
  let K := Submodule.span ℂ (Set.range (fun g : G => groupL2 (Φ (groupUnitary g))))
  apply group_single_total _ (Submodule.isClosed_topologicalClosure _)
  intro h
  change lp.single 2 h (1 : ℂ) ∈ K.topologicalClosure
  change lp.single 2 h (1 : ℂ) ∈ closure (K : Set (GroupHilbert H))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨p,hp⟩ := groupPolynomial_dense (groupL2 (Φ.symm (groupUnitary h))) hε
  refine ⟨groupL2 (Φ (groupPolynomial p)),?_,?_⟩
  · change groupL2 (Φ (groupPolynomial p)) ∈ K
    rw [groupPolynomial,Finsupp.sum]
    simp only [map_sum,map_smul]
    exact Submodule.sum_mem K (fun g _ => Submodule.smul_mem K _
      (Submodule.subset_span ⟨g,rfl⟩))
  · rw [dist_comm,dist_eq_norm,← groupL2_groupUnitary h,← map_sub]
    change twoNorm (Φ (groupPolynomial p)-groupUnitary h) < ε
    rw [← Φ.apply_symm_apply (groupUnitary h),← map_sub,twoNorm_iso Φ ht]
    change ‖groupL2 (groupPolynomial p-Φ.symm (groupUnitary h))‖ < ε
    rw [map_sub]
    exact hp

theorem spatial_of_trace_iso (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) :
    ∃ e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H,
      e deltaOne = deltaOne ∧
      ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔
        e.conjStarAlgEquiv T ∈ groupVonNeumann H := by
  classical
  let ρ : G →* groupVonNeumann H := Φ.toMonoidHom.comp
    ((unitary (groupVonNeumann G)).subtype.comp (groupUnitaryUHom G))
  have hρ (g : G) : ρ g = Φ (groupUnitary g) := rfl
  obtain ⟨e,he,_hgen,hmem⟩ := spatial_of_haar_total ρ (fun g => by
    change star (Φ (groupUnitary g)) = Φ (groupUnitary g⁻¹)
    exact (Φ.map_star' (groupUnitary g)).symm.trans
      (congrArg Φ (groupUnitary_inv g).symm)) (fun g => by
    rw [hρ,ht,canonicalTrace_groupUnitary]) (trace_iso_orbit_total Φ ht)
  exact ⟨e,he,hmem⟩

end

open scoped ENNReal
variable {I : Type u_3} {G : Type u_4} {H : Type u_5}

def nestedSpatialValue (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (ξ : NestedHilbert I G) : NestedHilbert I H :=
  ⟨fun i => e (ξ i), (lp.memℓp ξ).norm.mono (fun i => by rw [e.norm_map])⟩

@[simp] theorem nestedSpatialValue_apply (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (ξ : NestedHilbert I G) (i : I) : nestedSpatialValue e ξ i = e (ξ i) := rfl

def nestedSpatial (I : Type u_6) (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H) :
    NestedHilbert I G ≃ₗᵢ[ℂ] NestedHilbert I H where
  toFun := nestedSpatialValue e
  invFun := nestedSpatialValue e.symm
  left_inv ξ := by ext i j; change e.symm (e (ξ i)) j = ξ i j; rw [e.symm_apply_apply]
  right_inv ξ := by ext i j; change e (e.symm (ξ i)) j = ξ i j; rw [e.apply_symm_apply]
  map_add' ξ η := by ext i j; change e (ξ i+η i) j = (e (ξ i)+e (η i)) j; rw [map_add]
  map_smul' z ξ := by ext i j; change e (z • ξ i) j = (z • e (ξ i)) j; rw [map_smul]
  norm_map' ξ := by
    apply le_antisymm
    · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      exact (e.norm_map (ξ i)).le
    · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      exact (e.norm_map (ξ i)).ge

@[simp] theorem nestedSpatial_apply (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (ξ : NestedHilbert I G) (i : I) : nestedSpatial I e ξ i = e (ξ i) := rfl

def productSpatial (I : Type u_7) (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H) :
    GroupHilbert (I × G) ≃ₗᵢ[ℂ] GroupHilbert (I × H) :=
  ((hilbertFlatten I G).symm.trans (nestedSpatial I e)).trans (hilbertFlatten I H)

@[simp] theorem productSpatial_apply (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (ξ : GroupHilbert (I × G)) (i : I) (h : H) :
    productSpatial I e ξ (i,h) = e ((hilbertFlatten I G).symm ξ i) h := by
  simp only [productSpatial,LinearIsometryEquiv.trans_apply,hilbertFlatten_apply,nestedSpatial_apply]

@[simp] theorem productSpatial_symm (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H) :
    (productSpatial I e).symm = productSpatial I e.symm := by
  rfl

theorem productSpatial_productSingle (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (j : I) (ξ : GroupHilbert G) :
    productSpatial I e (productSingle I G j ξ) = productSingle I H j (e ξ) := by
  classical
  ext x
  rcases x with ⟨i,h⟩
  rw [productSpatial_apply,productSingle_apply]
  have he : (hilbertFlatten I G).symm (productSingle I G j ξ) i = if i=j then ξ else 0 := by
    ext g
    simp only [hilbertFlatten_symm_apply,productSingle_apply]
    split_ifs <;> rfl
  rw [he]
  split_ifs <;> simp

theorem matrixEntry_spatial (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (T : GroupOperator (I × G)) (i j : I) :
    matrixEntry ((productSpatial I e).conjStarAlgEquiv T) i j =
      e.conjStarAlgEquiv (matrixEntry T i j) := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext h
  rw [matrixEntry_apply]
  change (productSpatial I e) (T ((productSpatial I e).symm (productSingle I H j ξ))) (i,h) =
    e ((matrixEntry T i j) (e.symm ξ)) h
  rw [productSpatial_symm,productSpatial_productSingle,productSpatial_apply]
  rfl

variable [Group G] [Group H]

theorem productSpatial_stabilization (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (he : ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H)
    (T : GroupOperator (ℕ × G)) :
    T ∈ stabilization G ↔ (productSpatial ℕ e).conjStarAlgEquiv T ∈ stabilization H := by
  rw [mem_stabilization_iff_matrix,mem_stabilization_iff_matrix]
  simp only [matrixEntry_spatial,← he]

end FreeGroupFactorMain.Amplification

end

end OAI
