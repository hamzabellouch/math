import OAI.Analysis.NuclearUltrapower.NuclearFiniteness
import OAI.Analysis.NuclearUltrapower.FiniteInduction

namespace OAI

section

noncomputable section
universe u v
open scoped InnerProductSpace ComplexOrder TensorProduct
namespace NuclearUltrapower
section EnergyNorm
theorem complex_real_card_smul {A : Type*} [CStarAlgebra A] (n : ℕ) :
    (2 * (n : ℂ)) • (1 : A) = (2 * (n : ℝ)) • (1 : A) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp

variable {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_complement_gt_of_energy_lt (S : Finset J) (U : J → unitary (H →L[ℂ] H))
    (a : ℝ) (x : H) (hx : ‖x‖ = 1)
    (he : (∑ s ∈ S, ‖(U s : H →L[ℂ] H) x - x‖ ^ 2) < a) :
    4 * (S.card : ℝ) - a < ‖(4 * (S.card : ℝ)) • (1 : H →L[ℂ] H) -
      laplacian S (fun s => (U s : H →L[ℂ] H))‖ := by
  let C : H →L[ℂ] H := (4 * (S.card : ℝ)) • 1 - laplacian S (fun s => (U s : H →L[ℂ] H))
  have hinner : (inner ℂ x (C x)).re = 4 * (S.card : ℝ) -
      ∑ s ∈ S, ‖(U s : H →L[ℂ] H) x-x‖^2 := by
    dsimp only [C]
    rw [sub_apply, smul_apply,
      one_apply_eq_self, inner_sub_right, Complex.sub_re, inner_smul_right_eq_smul]
    rw [laplacian_inner]
    simp [inner_self_eq_norm_sq_to_K, hx]
    norm_cast
  have hle : (inner ℂ x (C x)).re ≤ ‖C‖ := by
    have hi := (Complex.re_le_norm (inner ℂ x (C x))).trans (norm_inner_le_norm x (C x))
    have ho := C.le_opNorm x
    rw [hx,one_mul] at hi
    rw [hx,mul_one] at ho
    exact hi.trans ho
  rw [hinner] at hle
  exact (sub_lt_sub_left he _).trans_le hle

end EnergyNorm
section Matching
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

def matchingUnitary (π : FiniteUnitaryRep.{u,v} Γ) (g : Γ) :
    unitary (TensorHilbert E π →L[ℂ] TensorHilbert E π) :=
  pairedTensorUnitary (Unitary.map (VariableUltra.starAlgToStarMonoid ρ) (u g))
    (Unitary.linearIsometryEquiv.symm (π.action g))

def matchingTuple (π : FiniteUnitaryRep.{u,v} Γ) (g : Γ) :
    TensorHilbert E π ≃ₗᵢ[ℂ] TensorHilbert E π :=
  Unitary.linearIsometryEquiv (matchingUnitary ρ u π g)

omit [Nontrivial E] in
@[simp] theorem matchingUnitary_val (π : FiniteUnitaryRep.{u,v} Γ) (g : Γ) :
    (matchingUnitary ρ u π g : TensorHilbert E π →L[ℂ] TensorHilbert E π) =
      completedTensorMap (ρ (u g)) (π.action g : π →L[ℂ] π) := rfl

/-- Direct second-factor convention. Conjugating all irreducibles gives an
equivalent convention with the same quantification over representation classes. -/
def Matches (a : ℝ) (π : FiniteUnitaryRep.{u,v} Γ) : Prop :=
  ∃ x : TensorHilbert E π, ‖x‖ = 1 ∧ tupleEnergy S (matchingTuple ρ u π) x < a

omit [Nontrivial E] in
theorem Matches.norm_complement {a : ℝ} {π : FiniteUnitaryRep.{u,v} Γ}
    (h : Matches ρ S u a π) :
    4 * (S.card : ℝ) - a < ‖(4 * (S.card : ℝ)) • (1 : TensorHilbert E π →L[ℂ] TensorHilbert E π) -
      laplacian S (fun s => completedTensorMap (ρ (u s)) (π.action s : π →L[ℂ] π))‖ := by
  obtain ⟨x,hx,he⟩ := h
  exact norm_complement_gt_of_energy_lt S (matchingUnitary ρ u π) a x hx he

private theorem coordinateComplement_poly (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (i : ℕ) :
    coordinateComplement ρ π S u i =
      complementPoly S (fun groupElement => tensorLeftHom (F := π i) (ρ (u groupElement)))
        (fun groupElement => tensorRightHom (E := E)
          ((π i).action groupElement : π i →L[ℂ] π i)) := by
  change (VariableUltra.eval (fun j => TensorHilbert E (π j) →L[ℂ] TensorHilbert E (π j)) i) (complementPoly S
    (fun g => tensorLeftSequence (F := fun i => π i) ρ (u g))
    (rightRepSequence (E := E) π)) = _
  rw [map_complementPoly]
  rfl

theorem coordinateComplement_apply (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (i : ℕ) :
    coordinateComplement ρ π S u i =
      (4 * (S.card : ℝ)) • (1 : TensorHilbert E (π i) →L[ℂ] TensorHilbert E (π i)) -
        laplacian S (fun s => completedTensorMap (ρ (u s)) ((π i).action s : π i →L[ℂ] π i)) := by
  have he := laplacian_complement_expand (A := TensorHilbert E (π i) →L[ℂ] TensorHilbert E (π i)) S (matchingUnitary ρ u (π i))
  simp only [matchingUnitary_val] at he
  rw [he, coordinateComplement_poly]
  simp only [complementPoly, ← map_star, tensorLeftRight_mul,
    ← completedTensorMap_star]
  congr 1
  exact complex_real_card_smul S.card

def FiniteUnitaryRep.classSetoid (Γ : Type u) [Group Γ] : Setoid (FiniteUnitaryRep.{u,v} Γ) where
  r := FiniteUnitaryRep.Equivalent
  iseqv := ⟨FiniteUnitaryRep.equivalent_refl, fun h => h.symm, fun h k => h.trans k⟩

abbrev RepClass := Quotient (FiniteUnitaryRep.classSetoid.{u,v} Γ)

def matchClasses (a : ℝ) : Set (RepClass (Γ := Γ)) :=
  {q | ∃ π : FiniteUnitaryRep.{u,v} Γ, π.Irreducible ∧ Matches ρ S u a π ∧
    Quotient.mk (FiniteUnitaryRep.classSetoid Γ) π = q}

/-- The full class-valued finiteness conclusion for an arbitrary nuclear tuple.
This does not assert any group relation for the tuple. -/
theorem matchClasses_finite (ω : Ultrafilter ℕ)
    (hB : IsNuclear.{v,v} B) (κ a : ℝ)
    (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ) (ha : a < κ ^ 2 / (4 * (S.card : ℝ)))
    (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ)) :
    (matchClasses ρ S u a).Finite := by
  classical
  by_contra hinf
  let f := Set.Infinite.natEmbedding (matchClasses ρ S u a) hinf
  have hex (i : ℕ) : ∃ π : FiniteUnitaryRep.{u,v} Γ,
      π.Irreducible ∧ Matches ρ S u a π ∧
      Quotient.mk (FiniteUnitaryRep.classSetoid Γ) π = (f i).1 := (f i).2
  choose π hirr hm he using hex
  have hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)) := by
    intro i j hij heq
    have hq := Quotient.sound (s := FiniteUnitaryRep.classSetoid Γ) heq
    rw [he i,he j] at hq
    exact hij (f.injective (Subtype.ext hq))
  apply nuclear_no_inequivalent_matches ρ π ω hB S κ a hS hκ0 hκ hgap ha hω hirr hne u
  intro i
  rw [coordinateComplement_apply]
  exact Matches.norm_complement ρ S u (hm i)

end Matching
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
theorem subspace_projection_intertwines {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (U : H ≃ₗᵢ[ℂ] H) (V : W ≃ₗᵢ[ℂ] W) (h : ∀ z : W, (V z : H) = U z) :
    W.orthogonalProjectionOnto.comp (U : H →L[ℂ] H) =
      (V : W →L[ℂ] W).comp W.orthogonalProjectionOnto := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  obtain ⟨z,rfl⟩ := V.surjective y
  change Inner.inner ℂ (V z) (W.orthogonalProjectionOnto (U x)) =
    Inner.inner ℂ (V z) (V (W.orthogonalProjectionOnto x))
  rw [W.inner_orthogonalProjectionOnto_eq_of_mem_left, h, U.inner_map_map,
    V.inner_map_map, W.inner_orthogonalProjectionOnto_eq_of_mem_left]

namespace FiniteUnitaryRep
variable {Γ : Type u} [Group Γ] (π : FiniteUnitaryRep.{u,v} Γ)
    (W : Submodule ℂ π) (hW : ∀ g x, x ∈ W → π.action g x ∈ W)

include hW

theorem orthogonal_invariant : ∀ g x, x ∈ Wᗮ → π.action g x ∈ Wᗮ := by
  intro g x hx
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  have h := hx ((π.action g⁻¹) y) (hW g⁻¹ y hy)
  have hi : Inner.inner ℂ x ((π.action g⁻¹) y) = Inner.inner ℂ ((π.action g) x) y := by
    have hy' : π.action g ((π.action g⁻¹) y) = y := by
      change (π.action g * π.action g⁻¹) y = y
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [← (π.action g).inner_map_map x ((π.action g⁻¹) y), hy']
  simpa only [hi] using h

theorem projection_action [Nontrivial W] (g : Γ) :
    W.orthogonalProjectionOnto.comp (π.action g : π →L[ℂ] π) =
      ((π.restrict W hW).action g : π.restrict W hW →L[ℂ] π.restrict W hW).comp W.orthogonalProjectionOnto := by
  exact subspace_projection_intertwines W (π.action g) ((π.restrict W hW).action g)
    (fun _ => rfl)

end FiniteUnitaryRep
section MatchSubrep
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

omit [Nontrivial E] in
/-- Normalized and homogeneous strict Rayleigh inequalities agree. -/
theorem matches_iff_homogeneous (a : ℝ) (π : FiniteUnitaryRep.{u,v} Γ) :
    Matches ρ S u a π ↔ ∃ x : TensorHilbert E π,
      tupleEnergy S (matchingTuple ρ u π) x < a * ‖x‖^2 := by
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨x, by simpa only [hx,one_pow,mul_one] using he⟩
  rintro ⟨x,hx⟩
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp [tupleEnergy] at hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  refine ⟨(‖x‖⁻¹ : ℂ) • x, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  rw [tupleEnergy_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have h := mul_lt_mul_of_pos_left hx (sq_pos_of_pos (inv_pos.mpr hn))
  calc
    _ < ‖x‖⁻¹^2 * (a * ‖x‖^2) := h
    _ = a := by field_simp

end MatchSubrep
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
section Intertwine
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

omit [Nontrivial E] in
@[simp] theorem matchingTuple_toCLM (π : FiniteUnitaryRep.{u,v} Γ) (g : Γ) :
    (matchingTuple ρ u π g : TensorHilbert E π →L[ℂ] TensorHilbert E π) =
      completedTensorMap (ρ (u g)) (π.action g : π →L[ℂ] π) := rfl

omit [Nontrivial E] in
theorem tensor_intertwining {π τ : FiniteUnitaryRep.{u,v} Γ} (T : π →L[ℂ] τ)
    (hT : ∀ g x, T (π.action g x) = τ.action g (T x)) (g : Γ)
    (x : TensorHilbert E π) :
    tensorMapBetween (1 : E →L[ℂ] E) T (matchingTuple ρ u π g x) =
      matchingTuple ρ u τ g (tensorMapBetween (1 : E →L[ℂ] E) T x) := by
  have ht : T.comp (π.action g : π →L[ℂ] π) =
      (τ.action g : τ →L[ℂ] τ).comp T := ContinuousLinearMap.ext (hT g)
  have he : (tensorMapBetween (1 : E →L[ℂ] E) T).comp
      (matchingTuple ρ u π g : TensorHilbert E π →L[ℂ] TensorHilbert E π) =
      (matchingTuple ρ u τ g : TensorHilbert E τ →L[ℂ] TensorHilbert E τ).comp
      (tensorMapBetween (1 : E →L[ℂ] E) T) := by
    rw [matchingTuple_toCLM, matchingTuple_toCLM]
    change (tensorMapBetween (1 : E →L[ℂ] E) T).comp
      (tensorMapBetween (ρ (u g)) (π.action g : π →L[ℂ] π)) =
        (tensorMapBetween (ρ (u g)) (τ.action g : τ →L[ℂ] τ)).comp
          (tensorMapBetween (1 : E →L[ℂ] E) T)
    rw [← tensorMapBetween_comp, ← tensorMapBetween_comp]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id, ht]
  exact congrArg (fun f : TensorHilbert E π →L[ℂ] TensorHilbert E τ => f x) he

omit [Nontrivial E] in
theorem Matches.embeds {a : ℝ} {π τ : FiniteUnitaryRep.{u,v} Γ}
    (hm : Matches ρ S u a π) (hπ : π.Embeds τ) : Matches ρ S u a τ := by
  obtain ⟨T,hT⟩ := hπ
  obtain ⟨x,hx,he⟩ := hm
  let U := tensorIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) T
  refine ⟨U x, by rw [U.norm_map,hx], ?_⟩
  have hi (g : Γ) : U (matchingTuple ρ u π g x) = matchingTuple ρ u τ g (U x) :=
    tensor_intertwining ρ u T.toContinuousLinearMap hT g x
  have hh : tupleEnergy S (matchingTuple ρ u τ) (U x) =
      tupleEnergy S (matchingTuple ρ u π) x := by
    apply Finset.sum_congr rfl
    intro g _
    rw [← hi, ← map_sub, U.norm_map]
  rwa [hh]

omit [Nontrivial E] in
theorem Matches.equivalent {a : ℝ} {π τ : FiniteUnitaryRep.{u,v} Γ}
    (hm : Matches ρ S u a π) (hπ : π.Equivalent τ) : Matches ρ S u a τ :=
  hm.embeds ρ S u hπ.embeds

omit [Nontrivial E] in
theorem tensor_projection_action (π : FiniteUnitaryRep.{u,v} Γ) (W : Submodule ℂ π)
    (hW : ∀ g x, x ∈ W → π.action g x ∈ W) [Nontrivial W]
    (g : Γ) (x : TensorHilbert E π) :
    tensorProjection (E := E) W (matchingTuple ρ u π g x) =
      matchingTuple ρ u (π.restrict W hW) g (tensorProjection (E := E) W x) := by
  exact tensor_intertwining (π := π) (τ := π.restrict W hW) ρ u W.orthogonalProjectionOnto
    (fun g x => congrArg (fun f : π →L[ℂ] W => f x) (π.projection_action W hW g)) g x

omit [Nontrivial E] in
theorem tensor_projection_energy (π : FiniteUnitaryRep.{u,v} Γ) (W : Submodule ℂ π)
    (hW : ∀ g x, x ∈ W → π.action g x ∈ W) [Nontrivial W] [Nontrivial Wᗮ]
    (x : TensorHilbert E π) :
    tupleEnergy S (matchingTuple ρ u π) x =
      tupleEnergy S (matchingTuple ρ u (π.restrict W hW)) (tensorProjection (E := E) W x) +
      tupleEnergy S (matchingTuple ρ u (π.restrict Wᗮ (π.orthogonal_invariant W hW)))
        (tensorProjection (E := E) Wᗮ x) := by
  simp only [tupleEnergy]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  rw [tensorProjection_norm_sq (E := E) W (matchingTuple ρ u π g x - x)]
  simp only [map_sub, tensor_projection_action ρ u π W hW,
    tensor_projection_action ρ u π Wᗮ (π.orthogonal_invariant W hW)]
  rfl

end Intertwine
end NuclearUltrapower
end
end

end OAI
