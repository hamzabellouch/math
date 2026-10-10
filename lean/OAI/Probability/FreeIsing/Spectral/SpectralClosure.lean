import OAI.Probability.FreeIsing.Spectral.SpectralTransfer

namespace OAI

noncomputable section

namespace Problem367
namespace SpectralClosure

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

lemma norm_apply_le_on_closure_range
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hT : ‖T‖ ≤ ρ)
    {y : F} (hy : y ∈ closure (Set.range D)) : ‖S y‖ ≤ ρ * ‖y‖ :=
  selfAdjoint_norm_apply_le_on_closure_range_of_intertwiner S hS T D hDS hρ hT hy

def rangeClosure (D : E →L[𝕜] F) : Submodule 𝕜 F :=
  (LinearMap.range (D : E →ₗ[𝕜] F)).topologicalClosure

instance rangeClosure_completeSpace (D : E →L[𝕜] F) : CompleteSpace (rangeClosure D) :=
  (Submodule.isClosed_topologicalClosure (LinearMap.range (D : E →ₗ[𝕜] F))).isComplete.completeSpace_coe

omit [CompleteSpace F] in
@[simp] lemma mem_rangeClosure (D : E →L[𝕜] F) (y : F) :
    y ∈ rangeClosure D ↔ y ∈ closure (Set.range D) := Iff.rfl

omit [CompleteSpace F] in

lemma mapsTo_rangeClosure (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (hDS : ∀ x, S (D x) = D (T x)) :
    ∀ y ∈ rangeClosure D, S y ∈ rangeClosure D := by
  have hmap : Set.MapsTo S (Set.range D) (Set.range D) := by
    rintro y ⟨x, rfl⟩
    exact ⟨T x, (hDS x).symm⟩
  exact hmap.closure S.continuous

def restrict (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (hDS : ∀ x, S (D x) = D (T x)) : rangeClosure D →L[𝕜] rangeClosure D :=
  S.restrict (mapsTo_rangeClosure T S D hDS)

lemma restrict_isSymmetric (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x)) :
    ((restrict T S D hDS) : rangeClosure D →ₗ[𝕜] rangeClosure D).IsSymmetric := by
  intro x y
  exact hS.isSymmetric x y

lemma restrict_isSelfAdjoint (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x)) :
    IsSelfAdjoint (restrict T S D hDS) :=
  (restrict_isSymmetric T S D hS hDS).isSelfAdjoint

lemma mapsTo_orthogonal_rangeClosure
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x)) :
    ∀ y ∈ (rangeClosure D)ᗮ, S y ∈ (rangeClosure D)ᗮ := by
  intro y hy
  rw [Submodule.mem_orthogonal]
  intro x hx
  calc
    inner 𝕜 x (S y) = inner 𝕜 (S x) y := by
      simpa only [ContinuousLinearMap.coe_coe] using (hS.isSymmetric x y).symm
    _ = 0 := Submodule.inner_right_of_mem_orthogonal (mapsTo_rangeClosure T S D hDS x hx) hy

lemma norm_restrict_le (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hT : ‖T‖ ≤ ρ) : ‖restrict T S D hDS‖ ≤ ρ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hρ
  intro y
  exact norm_apply_le_on_closure_range T S D hS hDS hρ hT y.property

omit [CompleteSpace F] in

lemma range_domRestrict_eq (D : E →L[𝕜] F) (K : Submodule 𝕜 E)
    (hcover : ∀ x : E, ∃ z ∈ K, D z = D x) :
    Set.range (D.domRestrict K) = Set.range D := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz, heq⟩ := hcover x
    exact ⟨⟨z, hz⟩, heq⟩

omit [CompleteSpace F] in

lemma rangeClosure_domRestrict_eq (D : E →L[𝕜] F) (K : Submodule 𝕜 E)
    (hcover : ∀ x : E, ∃ z ∈ K, D z = D x) :
    rangeClosure (D.domRestrict K) = rangeClosure D := by
  ext y
  simp only [mem_rangeClosure, range_domRestrict_eq D K hcover]

omit [CompleteSpace F] in

lemma source_cover_of_kills_direction (D : E →L[𝕜] F) (ℓ : E →L[𝕜] 𝕜)
    (e : E) (he : ℓ e = 1) (hDe : D e = 0) :
    ∀ x : E, ∃ z ∈ LinearMap.ker (ℓ : E →ₗ[𝕜] 𝕜), D z = D x := by
  intro x
  refine ⟨x - ℓ x • e, ?_, ?_⟩
  · change ℓ (x - ℓ x • e) = 0
    simp [he]
  · simp [hDe]

omit [CompleteSpace F] in

lemma rangeClosure_ker_eq_of_kills_direction (D : E →L[𝕜] F) (ℓ : E →L[𝕜] 𝕜)
    (e : E) (he : ℓ e = 1) (hDe : D e = 0) :
    rangeClosure (D.domRestrict (LinearMap.ker (ℓ : E →ₗ[𝕜] 𝕜))) = rangeClosure D :=
  rangeClosure_domRestrict_eq D _ (source_cover_of_kills_direction D ℓ e he hDe)

lemma norm_apply_le_of_source_subspace
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (K : Submodule 𝕜 E) (hK : ∀ x ∈ K, T x ∈ K)
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x))
    (hcover : ∀ x : E, ∃ z ∈ K, D z = D x)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hT : ‖T.restrict hK‖ ≤ ρ)
    {y : F} (hy : y ∈ closure (Set.range D)) : ‖S y‖ ≤ ρ * ‖y‖ := by
  apply norm_apply_le_on_closure_range (T.restrict hK) S (D.domRestrict K) hS
    (fun x => hDS x) hρ hT
  rwa [range_domRestrict_eq D K hcover]

lemma norm_restrict_le_of_source_subspace
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (K : Submodule 𝕜 E) (hK : ∀ x ∈ K, T x ∈ K)
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x))
    (hcover : ∀ x : E, ∃ z ∈ K, D z = D x)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hT : ‖T.restrict hK‖ ≤ ρ) :
    ‖restrict T S D hDS‖ ≤ ρ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hρ
  intro y
  exact norm_apply_le_of_source_subspace T S D K hK hS hDS hcover hρ hT y.property

lemma norm_restrict_le_of_kills_direction
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (ℓ : E →L[𝕜] 𝕜) (e : E) (he : ℓ e = 1) (hDe : D e = 0)
    (hK : ∀ x ∈ LinearMap.ker (ℓ : E →ₗ[𝕜] 𝕜),
      T x ∈ LinearMap.ker (ℓ : E →ₗ[𝕜] 𝕜))
    (hS : IsSelfAdjoint S) (hDS : ∀ x, S (D x) = D (T x))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hT : ‖T.restrict hK‖ ≤ ρ) :
    ‖restrict T S D hDS‖ ≤ ρ :=
  norm_restrict_le_of_source_subspace T S D _ hK hS hDS
    (source_cover_of_kills_direction D ℓ e he hDe) hρ hT

end SpectralClosure
end Problem367

end

end OAI
