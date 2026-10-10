import OAI.Analysis.NuclearUltrapower.TensorMatching

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v w
section ApproxInvariant
variable {ι : Type u} {Γ : Type v} [Group Γ] {E : ι → Type w}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  (l : Filter ι) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i) (x : ∀ i, E i)

/-- Pointwise approximate invariance in a varying Hilbert family. -/
def AlmostInvariant (g : Γ) : Prop :=
  Tendsto (fun i => ‖U g i (x i) - x i‖) l (𝓝 0)

theorem displacement_product_le (g h : Γ) (i : ι) :
    ‖U (g*h) i (x i)-x i‖ ≤
      ‖(U (g*h) i : E i →L[ℂ] E i) - ((U g i * U h i) : E i →L[ℂ] E i)‖ * ‖x i‖ +
      ‖U g i (x i)-x i‖ + ‖U h i (x i)-x i‖ := by
  calc
    ‖U (g*h) i (x i)-x i‖ ≤
        ‖U (g*h) i (x i) - U g i (U h i (x i))‖ +
        ‖U g i (U h i (x i)) - U g i (x i)‖ + ‖U g i (x i)-x i‖ := by
      have ht := norm_add_le (U (g*h) i (x i)-U g i (U h i (x i)))
        (U g i (U h i (x i))-U g i (x i))
      have hs := norm_add_le ((U (g*h) i (x i)-U g i (U h i (x i))) +
        (U g i (U h i (x i))-U g i (x i))) (U g i (x i)-x i)
      simp only [sub_add_sub_cancel] at ht hs
      linarith
    _ ≤ _ := by
      rw [← map_sub, (U g i).norm_map]
      have ht := ContinuousLinearMap.le_opNorm
        ((U (g*h) i : E i →L[ℂ] E i)-((U g i * U h i) : E i →L[ℂ] E i)) (x i)
      change ‖U (g*h) i (x i)-U g i (U h i (x i))‖ ≤ _ at ht
      linarith

variable {l U x}

theorem almostInvariant_mul {C : ℝ} (hx : ∀ i, ‖x i‖ ≤ C)
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g*h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) l (𝓝 0))
    {g h : Γ} (hg : AlmostInvariant l U x g) (hh : AlmostInvariant l U x h) :
    AlmostInvariant l U x (g*h) := by
  have hb (i : ι) : ‖U (g*h) i (x i)-x i‖ ≤
      ‖(U (g*h) i : E i →L[ℂ] E i)-((U g i * U h i) : E i →L[ℂ] E i)‖ * C +
      ‖U g i (x i)-x i‖ + ‖U h i (x i)-x i‖ := by
    have hle := mul_le_mul_of_nonneg_left (hx i)
      (norm_nonneg ((U (g*h) i : E i →L[ℂ] E i)-((U g i * U h i) : E i →L[ℂ] E i)))
    have hd := displacement_product_le U x g h i
    linarith
  apply squeeze_zero (fun i => norm_nonneg _) hb
  simpa using ((hmul g h).mul_const C |>.add hg |>.add hh)

theorem almostInvariant_one {C : ℝ} (hx : ∀ i, ‖x i‖ ≤ C)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) l (𝓝 0)) :
    AlmostInvariant l U x 1 := by
  apply squeeze_zero (fun i => norm_nonneg _) (fun i =>
    (ContinuousLinearMap.le_opNorm
      ((U 1 i : E i →L[ℂ] E i)-((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)) (x i)).trans
      (mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _)))
  simpa using h1.mul_const C

theorem almostInvariant_inv {C : ℝ} (hx : ∀ i, ‖x i‖ ≤ C)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) l (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g*h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) l (𝓝 0))
    {g : Γ} (hg : AlmostInvariant l U x g) : AlmostInvariant l U x g⁻¹ := by
  have he := almostInvariant_one hx h1
  have hb (i : ι) : ‖U g⁻¹ i (x i)-x i‖ ≤
      ‖(U (g*g⁻¹) i : E i →L[ℂ] E i)-((U g i * U g⁻¹ i) : E i →L[ℂ] E i)‖ * C +
        ‖U 1 i (x i)-x i‖ + ‖U g i (x i)-x i‖ := by
    rw [← (U g i).norm_map (U g⁻¹ i (x i)-x i), map_sub]
    have ht := ContinuousLinearMap.le_opNorm
      ((U (g*g⁻¹) i : E i →L[ℂ] E i)-((U g i * U g⁻¹ i) : E i →L[ℂ] E i)) (x i)
    change ‖U (g*g⁻¹) i (x i)-U g i (U g⁻¹ i (x i))‖ ≤ _ at ht
    rw [mul_inv_cancel] at ht ⊢
    have ht' := ht.trans (mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _))
    have htri := norm_sub_le_norm_sub_add_norm_sub (U g i (U g⁻¹ i (x i))) (U 1 i (x i)) (x i)
    have htri' := norm_sub_le_norm_sub_add_norm_sub (U g i (U g⁻¹ i (x i))) (x i) (U g i (x i))
    rw [norm_sub_rev (U g i (U g⁻¹ i (x i))) (U 1 i (x i))] at htri
    rw [norm_sub_rev (x i) (U g i (x i))] at htri'
    linarith
  apply squeeze_zero (fun i => norm_nonneg _) hb
  simpa using ((hmul g g⁻¹).mul_const C |>.add he |>.add hg)

/-- A fixed finite generating set controls every fixed group element. This
closure proof does not require relations at individual coordinates. -/
theorem almostInvariant_of_generators (S : Finset Γ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) {C : ℝ} (hx : ∀ i, ‖x i‖ ≤ C)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) l (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g*h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) l (𝓝 0))
    (hs : ∀ s ∈ S, AlmostInvariant l U x s) (g : Γ) : AlmostInvariant l U x g := by
  let K : Subgroup Γ := {
    carrier := {g | AlmostInvariant l U x g}
    one_mem' := almostInvariant_one hx h1
    mul_mem' := fun h k => almostInvariant_mul hx hmul h k
    inv_mem' := fun h => almostInvariant_inv hx h1 hmul h }
  have hK : Subgroup.closure (S : Set Γ) ≤ K := (Subgroup.closure_le K).mpr hs
  rw [hS] at hK
  exact hK (Subgroup.mem_top g)

end ApproxInvariant
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v w
section Energies
variable {ι : Type u} {Γ : Type v} {E : ι → Type w}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  (l : Filter ι) (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i) (x : ∀ i, E i)

theorem displacement_tendsto_of_energy
    (he : Tendsto (fun i => tupleEnergy S (fun g => U g i) (x i)) l (𝓝 0))
    (s : Γ) (hs : s ∈ S) : Tendsto (fun i => ‖U s i (x i)-x i‖) l (𝓝 0) := by
  have hb (i : ι) : ‖U s i (x i)-x i‖ ≤ Real.sqrt (tupleEnergy S (fun g => U g i) (x i)) := by
    apply (Real.le_sqrt (norm_nonneg _) (tupleEnergy_nonneg _ _ _)).mpr
    exact Finset.single_le_sum (f := fun g : Γ => ‖U g i (x i)-x i‖^2)
      (fun _ _ => sq_nonneg _) hs
  apply squeeze_zero (fun i => norm_nonneg _) hb
  simpa only [Real.sqrt_zero] using he.sqrt

theorem energy_tendsto_zero
    (hs : ∀ s ∈ S, Tendsto (fun i => ‖U s i (x i)-x i‖) l (𝓝 0)) :
    Tendsto (fun i => tupleEnergy S (fun g => U g i) (x i)) l (𝓝 0) := by
  have h := tendsto_finsetSum S (fun s h => (hs s h).pow 2)
  simpa [tupleEnergy] using h
end Energies

section Selection
variable {Γ : Type u} [Group Γ] {E : ℕ → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, Nontrivial (E i)]
  (ω : Ultrafilter ℕ) (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)

theorem free_le_atTop (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ)) :
    (ω : Filter ℕ) ≤ atTop := by
  rw [← Nat.cofinite_eq_atTop]
  exact le_cofinite_iff_compl_singleton_mem.mpr (fun i => (ω.compl_mem_iff_notMem).mpr (hω i))

omit [Group Γ] in
/-- Unit vectors with vanishing energy can be selected even while the Hilbert
spaces and their dimensions vary freely. -/
theorem exists_almost_invariant_vectors
    (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ))
    (hd : Tendsto (fun i => bottomEnergy S (fun g => U g i)) (ω : Filter ℕ) (𝓝 0)) :
    ∃ x : ∀ i, E i, (∀ i, ‖x i‖ = 1) ∧
      Tendsto (fun i => tupleEnergy S (fun g => U g i) (x i)) (ω : Filter ℕ) (𝓝 0) := by
  have hp (i : ℕ) : (0 : ℝ) < 1/((i : ℝ)+1) := by positivity
  choose x hx he using (fun i => exists_energy_lt S (fun g => U g i) (hp i))
  refine ⟨x,hx,?_⟩
  apply squeeze_zero (fun i => tupleEnergy_nonneg _ _ _) (fun i => (he i).le)
  have ht : Tendsto (fun i : ℕ => (1 : ℝ)/((i : ℝ)+1)) (ω : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (free_le_atTop ω hω)
  simpa only [add_zero] using hd.add ht

/-- Matching below the Kazhdan threshold forces the bottom energies to zero;
this uses no common bound on the dimensions. -/
theorem bottom_tendsto_zero_of_small (κ a : ℝ)
    (hgap : HasKazhdanGap.{u,v} S κ) (ha : a < κ)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) (ω : Filter ℕ) (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g*h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) (ω : Filter ℕ) (𝓝 0))
    (hm : ∀ᶠ i in (ω : Filter ℕ), bottomEnergy S (fun g => U g i) < a) :
    Tendsto (fun i => bottomEnergy S (fun g => U g i)) (ω : Filter ℕ) (𝓝 0) := by
  have ht := HilbertUltraproduct.bottomEnergy_tendsto ω S U
  rcases HilbertUltraproduct.varying_gap ω S κ hgap U h1 hmul ht with hz | hg
  · rwa [hz] at ht
  · have hr : limUnder (ω : Filter ℕ) (fun i => bottomEnergy S (fun g => U g i)) ≤ a :=
      le_of_tendsto ht (hm.mono fun _ h => h.le)
    exact False.elim (ha.not_ge (hg.1.trans hr))
end Selection
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
section TensorBounds
variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

@[simp] theorem tensorMapBetween_sub_left (U U' : E →L[ℂ] E') (V : F →L[ℂ] F') :
    tensorMapBetween (U-U') V = tensorMapBetween U V - tensorMapBetween U' V := by
  apply completion_map_ext
  intro x
  simp only [tensorMapBetween_coe, sub_apply]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      simp only [map_add, UniformSpace.Completion.coe_add, hx, hy]
      abel
  | tmul x y =>
      simp only [TensorProduct.mapL_tmul, sub_apply, TensorProduct.sub_tmul,
        UniformSpace.Completion.coe_sub]

theorem tensorMapBetween_norm_le (U : E →L[ℂ] E') (V : F →L[ℂ] F') :
    ‖tensorMapBetween U V‖ ≤ ‖U‖ * ‖V‖ := by
  rw [tensorMapBetween, completed_norm]
  exact TensorProduct.norm_mapL_le _ _

theorem tensorMapBetween_sub_norm_le (U U' : E →L[ℂ] E') (V : F →ₗᵢ[ℂ] F') :
    ‖tensorMapBetween U V.toContinuousLinearMap - tensorMapBetween U' V.toContinuousLinearMap‖
      ≤ ‖U-U'‖ := by
  rw [← tensorMapBetween_sub_left]
  exact (tensorMapBetween_norm_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left V.norm_toContinuousLinearMap_le (norm_nonneg (U-U')))

end TensorBounds
section Defects
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → unitary B)

@[simp] theorem matchingTuple_one (π : FiniteUnitaryRep.{u,v} Γ) (hu : u 1 = 1) :
    matchingTuple ρ u π 1 = 1 := by
  have hp : (π.action 1 : π →L[ℂ] π) = 1 := by
    rw [map_one]; rfl
  have hb : ρ (u 1) = 1 := by
    rw [hu, Submonoid.coe_one, map_one]
  have he : (matchingTuple ρ u π 1 : TensorHilbert E π →L[ℂ] TensorHilbert E π) = 1 := by
    rw [matchingTuple_toCLM, hb, hp, completedTensorMap_one]
  ext x
  exact congrArg (fun T : TensorHilbert E π →L[ℂ] TensorHilbert E π => T x) he

theorem matchingTuple_mul_defect (π : FiniteUnitaryRep.{u,v} Γ) (g h : Γ) :
    ‖(matchingTuple ρ u π (g*h) : TensorHilbert E π →L[ℂ] TensorHilbert E π) -
      ((matchingTuple ρ u π g * matchingTuple ρ u π h) : TensorHilbert E π →L[ℂ] TensorHilbert E π)‖
    ≤ ‖(u (g*h) : B) - (u g : B)*(u h : B)‖ := by
  have ha : (π.action (g*h) : π →L[ℂ] π) =
      (π.action g : π →L[ℂ] π)*(π.action h : π →L[ℂ] π) := by
    rw [map_mul]; rfl
  change ‖completedTensorMap (ρ (u (g*h))) (π.action (g*h) : π →L[ℂ] π) -
      completedTensorMap (ρ (u g)) (π.action g : π →L[ℂ] π) *
        completedTensorMap (ρ (u h)) (π.action h : π →L[ℂ] π)‖ ≤ _
  rw [← completedTensorMap_mul, ← ha, ← map_mul]
  have hb := tensorMapBetween_sub_norm_le (ρ (u (g*h))) (ρ ((u g : B)*(u h : B)))
    (π.action (g*h)).toLinearIsometry
  exact hb.trans (by rw [← map_sub]; exact NonUnitalStarAlgHom.norm_apply_le ρ _)

end Defects
end NuclearUltrapower
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u
section InducedVectors
variable {Γ B E : Type u} [Group Γ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (H : Subgroup Γ) [Fintype (Γ ⧸ H)] (α : FiniteUnitaryRep.{u,u} H)
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → unitary B)

def inducedCoordinate (i : Γ ⧸ H) : α →ₗᵢ[ℂ] finiteInduced H α :=
  coordinateInclusion H i

def representedUnitary (b : unitary B) : E ≃ₗᵢ[ℂ] E :=
  Unitary.linearIsometryEquiv (Unitary.map (StarMonoidHom.ofClass ρ) b)

@[simp] theorem representedUnitary_toCLM (b : unitary B) :
    (representedUnitary ρ b : E →L[ℂ] E) = ρ b := rfl

/-- The fixed finite list of induced tensor coordinates. -/
def inductionTerm (i : Γ ⧸ H) : TensorHilbert E α →L[ℂ] TensorHilbert E (finiteInduced H α) :=
  tensorMapBetween (ρ (u (cosetRep H i))) (inducedCoordinate H α i).toContinuousLinearMap

def inductionSeed (η : TensorHilbert E α) : TensorHilbert E (finiteInduced H α) :=
  ∑ i : Γ ⧸ H, inductionTerm H α ρ u i η

theorem inductionTerm_norm (i : Γ ⧸ H) (η : TensorHilbert E α) :
    ‖inductionTerm H α ρ u i η‖ = ‖η‖ := by
  change ‖tensorIsometry (representedUnitary ρ (u (cosetRep H i))).toLinearIsometry
    (inducedCoordinate H α i) η‖ = _
  exact LinearIsometry.norm_map _ _

theorem identityCoordinate_comp_inclusion (i : Γ ⧸ H) :
    (identityCoordinate H α).comp (inducedCoordinate H α i).toContinuousLinearMap =
      if i = QuotientGroup.mk 1 then 1 else 0 := by
  classical
  ext v
  change identityCoordinate H α (coordinateInclusion H i v) = (if i = QuotientGroup.mk 1 then (1 : α →L[ℂ] α) else 0) v
  rw [identityCoordinate_inclusion]
  split_ifs <;> rfl

theorem inductionSeed_identity (hu : u 1 = 1) (η : TensorHilbert E α) :
    tensorMapBetween (1 : E →L[ℂ] E) (identityCoordinate H α) (inductionSeed H α ρ u η) = η := by
  classical
  have ht (i : Γ ⧸ H) :
      tensorMapBetween (1 : E →L[ℂ] E) (identityCoordinate H α) (inductionTerm H α ρ u i η) =
        if i = QuotientGroup.mk 1 then η else 0 := by
    change ((tensorMapBetween (1 : E →L[ℂ] E) (identityCoordinate H α)).comp
      (tensorMapBetween (ρ (u (cosetRep H i))) (inducedCoordinate H α i).toContinuousLinearMap)) η = _
    rw [← tensorMapBetween_comp, identityCoordinate_comp_inclusion]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    split_ifs with hi
    · subst i
      rw [cosetRep_identity, hu, Submonoid.coe_one, map_one]
      change tensorMapBetween (1 : E →L[ℂ] E) (1 : α →L[ℂ] α) η = η
      rw [tensorMapBetween_one]
      rfl
    · rw [tensorMapBetween_zero_right]
      rfl
  simp only [inductionSeed, map_sum, ht]
  simp

theorem inductionSeed_norm_ge [Nontrivial E] (hu : u 1 = 1) (η : TensorHilbert E α) :
    ‖η‖ ≤ ‖inductionSeed H α ρ u η‖ := by
  let P := tensorMapBetween (1 : E →L[ℂ] E) (identityCoordinate H α)
  have hp : ‖P‖ ≤ 1 := by
    have h := tensorMapBetween_norm_le (1 : E →L[ℂ] E) (identityCoordinate H α)
    rw [norm_one, one_mul] at h
    exact h.trans (identityCoordinate_norm_le H α)
  have h := P.le_opNorm (inductionSeed H α ρ u η)
  change ‖tensorMapBetween (1 : E →L[ℂ] E) (identityCoordinate H α) (inductionSeed H α ρ u η)‖ ≤ _ at h
  rw [inductionSeed_identity H α ρ u hu] at h
  exact h.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg _))

theorem coordinate_action_comp (g : Γ) (i : Γ ⧸ H) :
    ((finiteInduced H α).action g : finiteInduced H α →L[ℂ] finiteInduced H α).comp
      (inducedCoordinate H α i).toContinuousLinearMap =
    (inducedCoordinate H α (g • i)).toContinuousLinearMap.comp
      (α.action (cosetCocycle H g i) : α →L[ℂ] α) := by
  ext v
  exact coordinateInclusion_action H α.action g i v

omit [CompleteSpace E] in
theorem completedTensorMap_eq_between {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    completedTensorMap U V = tensorMapBetween U V := rfl

theorem inductionTerm_action_map (g : Γ) (i : Γ ⧸ H) :
    (matchingTuple ρ u (finiteInduced H α) g :
      TensorHilbert E (finiteInduced H α) →L[ℂ] TensorHilbert E (finiteInduced H α)).comp
      (inductionTerm H α ρ u i) =
      tensorMapBetween (ρ (u g) * ρ (u (cosetRep H i)))
        ((inducedCoordinate H α (g • i)).toContinuousLinearMap.comp
          (α.action (cosetCocycle H g i) : α →L[ℂ] α)) := by
  rw [matchingTuple_toCLM, completedTensorMap_eq_between, inductionTerm,
    ← tensorMapBetween_comp, coordinate_action_comp]
  rfl

theorem inductionTerm_action (g : Γ) (i : Γ ⧸ H) (η : TensorHilbert E α) :
    matchingTuple ρ u (finiteInduced H α) g (inductionTerm H α ρ u i η) =
      tensorMapBetween (ρ (u g) * ρ (u (cosetRep H i)))
        ((inducedCoordinate H α (g • i)).toContinuousLinearMap.comp
          (α.action (cosetCocycle H g i) : α →L[ℂ] α)) η := by
  exact congrArg (fun T : TensorHilbert E α →L[ℂ] TensorHilbert E (finiteInduced H α) => T η)
    (inductionTerm_action_map H α ρ u g i)

end InducedVectors
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
universe u v
variable {Γ : Type u} [Group Γ]

section DualAction
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def dualAction (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) :
    Γ →* (StrongDual ℂ H ≃ₗᵢ[ℂ] StrongDual ℂ H) where
  toFun g := dualUnitary (ρ g)
  map_one' := by
    ext f : 1
    obtain ⟨x,rfl⟩ := (InnerProductSpace.toDual ℂ H).surjective f
    rw [dualUnitary_toDual, map_one]
    rfl
  map_mul' g h := by
    ext f : 1
    obtain ⟨x,rfl⟩ := (InnerProductSpace.toDual ℂ H).surjective f
    change dualUnitary (ρ (g*h)) (InnerProductSpace.toDual ℂ H x) =
      dualUnitary (ρ g) (dualUnitary (ρ h) (InnerProductSpace.toDual ℂ H x))
    rw [dualUnitary_toDual, dualUnitary_toDual, dualUnitary_toDual, map_mul]
    rfl

@[simp] theorem dualAction_toDual (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (g : Γ) (x : H) :
    dualAction ρ g (InnerProductSpace.toDual ℂ H x) =
      InnerProductSpace.toDual ℂ H (ρ g x) := dualUnitary_toDual _ _
end DualAction

namespace FiniteUnitaryRep

def dual (π : FiniteUnitaryRep.{u,v} Γ) : FiniteUnitaryRep.{u,v} Γ where
  carrier := StrongDual ℂ π
  action := dualAction π.action

theorem Irreducible.dual {π : FiniteUnitaryRep.{u,v} Γ} (hi : π.Irreducible) :
    π.dual.Irreducible := by
  intro W hW
  change Submodule ℂ (StrongDual ℂ π) at W
  let D := InnerProductSpace.toDual ℂ π
  let V : Submodule ℂ π := {
    carrier := {x | D x ∈ W}
    zero_mem' := by simp
    add_mem' := fun hx hy => by
      change D (_+_) ∈ W
      rw [map_add]
      exact W.add_mem hx hy
    smul_mem' := fun c x hx => by
      change D (c • x) ∈ W
      rw [map_smulₛₗ]
      exact W.smul_mem (starRingEnd ℂ c) hx }
  have hV : ∀ g x, x ∈ V → π.action g x ∈ V := by
    intro g x hx
    have h := hW g (D x) hx
    change dualAction π.action g (D x) ∈ W at h
    change D (π.action g x) ∈ W
    rwa [dualAction_toDual] at h
  rcases hi V hV with hv | hv
  · left
    apply le_antisymm ?_ bot_le
    intro f hf
    obtain ⟨x,rfl⟩ := D.surjective f
    have hx : x ∈ V := hf
    rw [hv, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  · right
    apply top_unique
    intro f _
    obtain ⟨x,rfl⟩ := D.surjective f
    have hx : x ∈ V := hv ▸ Submodule.mem_top
    exact hx

/-- Contragredience is faithful on unitary equivalence classes. -/
theorem equivalent_of_dual {π τ : FiniteUnitaryRep.{u,v} Γ}
    (he : π.dual.Equivalent τ.dual) : π.Equivalent τ := by
  obtain ⟨U,hU⟩ := he
  change StrongDual ℂ π ≃ₗᵢ[ℂ] StrongDual ℂ τ at U
  let T : π ≃ₗᵢ[ℂ] τ := ((InnerProductSpace.toDual ℂ π).trans U).trans
    (InnerProductSpace.toDual ℂ τ).symm
  refine ⟨T, fun g x => ?_⟩
  apply (InnerProductSpace.toDual ℂ τ).injective
  change InnerProductSpace.toDual ℂ τ ((InnerProductSpace.toDual ℂ τ).symm
      (U (InnerProductSpace.toDual ℂ π (π.action g x)))) =
    InnerProductSpace.toDual ℂ τ (τ.action g ((InnerProductSpace.toDual ℂ τ).symm
      (U (InnerProductSpace.toDual ℂ π x))))
  rw [LinearIsometryEquiv.apply_symm_apply]
  calc
    _ = dualAction τ.action g (U (InnerProductSpace.toDual ℂ π x)) := by
      have he := hU g (InnerProductSpace.toDual ℂ π x)
      change U (dualAction π.action g (InnerProductSpace.toDual ℂ π x)) = _ at he
      rwa [dualAction_toDual] at he
    _ = _ := by
      rw [← dualAction_toDual τ.action g, LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem dual_pull (π : FiniteUnitaryRep.{u,v} Γ) (θ : Monoid.End Γ) :
    (π.pull θ).dual = π.dual.pull θ := rfl

theorem dual_aperiodic {π : FiniteUnitaryRep.{u,v} Γ} (θ : Monoid.End Γ)
    (hπ : ∀ j : ℕ, 0 < j → ¬ π.Equivalent (π.pull (θ^j))) :
    ∀ j : ℕ, 0 < j → ¬ π.dual.Equivalent (π.dual.pull (θ^j)) := by
  intro j hj he
  rw [← dual_pull] at he
  exact hπ j hj (equivalent_of_dual he)

end FiniteUnitaryRep
end NuclearUltrapower
end
end

end OAI
