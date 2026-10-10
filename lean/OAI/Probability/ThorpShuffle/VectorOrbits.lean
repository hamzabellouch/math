import OAI.Probability.ThorpShuffle.SymmetricFamilies

namespace OAI

universe uG uE uX uH uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

variable {G : Type uG} [Group G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma cyclic_scalar_mem (ρ : Representation ℂ G E) (e : E) (χ : G → ℂ)
    (he : ∀ g, ρ g e = χ g • e) (v : E) (hv : v ∈ cyclic ρ e) :
    ∃ c : ℂ, c • e = v := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨g, rfl⟩ := hv; exact ⟨χ g, (he g).symm⟩
  | zero => exact ⟨0, zero_smul _ _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, rfl⟩ := ihx
    obtain ⟨b, rfl⟩ := ihy
    exact ⟨a+b, add_smul _ _ _⟩
  | smul a x hx ih =>
    obtain ⟨b, rfl⟩ := ih
    exact ⟨a*b, mul_smul _ _ _⟩

lemma cyclic_scalar_action (ρ : Representation ℂ G E) (e : E) (χ : G → ℂ)
    (he : ∀ g, ρ g e = χ g • e) (g : G) (v : (cyclic ρ e).toSubmodule) :
    (cyclic ρ e).toRepresentation g v = χ g • v := by
  obtain ⟨a, ha⟩ := cyclic_scalar_mem ρ e χ he v.val v.property
  apply Subtype.ext
  change ρ g v.val = χ g • v.val
  rw [← ha, map_smul, he, smul_comm]

lemma cyclic_scalar_finrank (ρ : Representation ℂ G E) (e : E) (χ : G → ℂ)
    (he : ∀ g, ρ g e = χ g • e) : Module.finrank ℂ (cyclic ρ e).toSubmodule ≤ 1 := by
  apply finrank_le_one (⟨e, self_mem_cyclic ρ e⟩ : (cyclic ρ e).toSubmodule)
  intro v
  obtain ⟨a, ha⟩ := cyclic_scalar_mem ρ e χ he v.val v.property
  exact ⟨a, Subtype.ext ha⟩

namespace PermutationSpace
variable {X : Type uX} {H : Type uH} [Fintype X] [MulAction G X] [Group H] [Fintype H]
omit [Fintype X] in
lemma translate_alternator (ι : H →* G) (χ : H →* ℂ) (a : H)
    (v : EuclideanSpace ℂ X) :
    rep (ι a) (alternator ι χ v) = χ a⁻¹ • alternator ι χ v := by
  simp only [alternator_apply, map_sum, Finset.smul_sum]
  simp only [map_smul]
  have hh := Equiv.sum_comp (Equiv.mulLeft a)
    (fun h => χ a⁻¹ • (χ h • (rep (ι h) v : EuclideanSpace ℂ X)))
  rw [← hh]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulLeft, smul_smul, map_mul]
  rw [show χ a⁻¹ * (χ a * χ h) = χ h by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]]
  rfl
end PermutationSpace

lemma row_zero_of_full (D : YoungDiagram) (h : D.rowLen 0 = Fintype.card (Cells D)) :
    ∀ x : Cells D, x.val.1 = 0 := by
  have hc : Fintype.card (Lower D) = 0 := by have hh := card_lower_add D; omega
  have he : IsEmpty (Lower D) := Fintype.card_eq_zero_iff.mp hc
  intro x
  by_contra hx
  exact he.false ⟨x, hx⟩

lemma col_zero_of_full (D : YoungDiagram) (h : D.colLen 0 = Fintype.card (Cells D)) :
    ∀ x : Cells D, x.val.2 = 0 := by
  have hc : D.transpose.rowLen 0 = Fintype.card (Cells D.transpose) := by
    rw [YoungDiagram.rowLen_transpose, ← Fintype.card_congr (transposeCells D).toEquiv, h]
  intro x
  exact row_zero_of_full D.transpose hc (transposeCells D x)

variable {α : Type uα} [Fintype α]

omit [Fintype α] in
lemma row_rep_action (D : YoungDiagram) (t : α ≃ Cells D)
    (h : ∀ x : Cells D, x.val.1 = 0) (g : Equiv.Perm α)
    (v : EuclideanSpace ℂ (Tabloid (tableauRow D t))) : tabloidRep D t g v = v := by
  ext f
  change v (g⁻¹ • f) = v f
  apply congrArg (fun a => v a)
  apply Subtype.ext
  funext x
  obtain ⟨a, ha⟩ := f.property
  simp only [tabloid_smul_apply, ha, Function.comp_apply, tableauRow, h]

lemma column_poly_action (D : YoungDiagram) (t : α ≃ Cells D)
    (h : ∀ x : Cells D, x.val.2 = 0) (g : Equiv.Perm α) :
    tabloidRep D t g (polytabloid D t) = complexSign g • polytabloid D t := by
  have hg : g ∈ fiberGroup (tableauCol D t) := by intro x; simp only [tableauCol, h]
  have hh := PermutationSpace.translate_alternator (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype) ⟨g, hg⟩
    (EuclideanSpace.single (baseTabloid (tableauRow D t)) (1 : ℂ))
  change tabloidRep D t g (polytabloid D t) = complexSign g⁻¹ • polytabloid D t at hh
  rwa [complexSign_inv] at hh

lemma exceptional_action {n : ℕ} (p : NShape n) (hp : defect p = 0) :
    degree p = 1 ∧ ((∀ g v, family p g v = v) ∨
      (∀ g v, family p g v = complexSign g • v)) := by
  let D := ofPartition p
  let t := canonicalTableau p
  have hL : longest D = Fintype.card (Cells D) := by
    have hh := defect_add_longest p
    rw [hp, zero_add] at hh
    exact hh.trans (diagram_card p).symm
  have hor : D.rowLen 0 = Fintype.card (Cells D) ∨ D.colLen 0 = Fintype.card (Cells D) := by
    unfold longest at hL
    rcases le_total (D.colLen 0) (D.rowLen 0) with h | h
    · exact Or.inl (by rwa [max_eq_left h] at hL)
    · exact Or.inr (by rwa [max_eq_right h] at hL)
  rcases hor with hr | hc
  · have he : ∀ g, tabloidRep D t g (polytabloid D t) = (1 : ℂ) • polytabloid D t := by
      intro g; rw [one_smul]; exact row_rep_action D t (row_zero_of_full D hr) g _
    have hd := cyclic_scalar_finrank (tabloidRep D t) (polytabloid D t) (fun _ => 1) he
    refine ⟨Nat.le_antisymm hd (degree_pos p), Or.inl ?_⟩
    intro g v
    apply Subtype.ext
    exact row_rep_action D t (row_zero_of_full D hr) g v.val
  · have he := column_poly_action D t (col_zero_of_full D hc)
    have hd := cyclic_scalar_finrank (tabloidRep D t) (polytabloid D t) complexSign he
    refine ⟨Nat.le_antisymm hd (degree_pos p), Or.inr ?_⟩
    exact cyclic_scalar_action (tabloidRep D t) (polytabloid D t) complexSign he

end Thorp.Specht

namespace Thorp.Fourier
open scoped Classical
variable {G : Type} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma sum_rep_invariant (ρ : Representation ℂ G E) (g : G) (v : E) :
    ρ g (∑ h, ρ h v) = ∑ h, ρ h v := by
  rw [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h => ρ h v)

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma invariant_finrank_le_one (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (v : E) (hv : v ≠ 0) (hinv : ∀ g, ρ g v = v) : Module.finrank ℂ E ≤ 1 := by
  let A : Representation.IntertwiningMap (Representation.trivial ℂ G ℂ) ρ := {
    toLinearMap := LinearMap.toSpanSingleton ℂ E v
    isIntertwining' := by intro g; ext; simp [Representation.trivial, hinv] }
  have hA : A ≠ 0 := by
    intro ha
    have hh := DFunLike.congr_fun ha 1
    exact hv (by simpa [A] using hh)
  have hs := (Representation.IsIrreducible.surjective_or_eq_zero A).resolve_right hA
  exact finrank_le_one v hs

omit [FiniteDimensional ℂ E] in
lemma integrated_uniform_zero (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hd : 1 < Module.finrank ℂ E) :
    integrated ρ (fun _ => (Fintype.card G : ℂ)⁻¹) = 0 := by
  have hz (v : E) : (∑ h, ρ h v) = 0 := by
    by_contra hn
    have hh := invariant_finrank_le_one ρ _ hn (fun g => sum_rep_invariant ρ g v)
    omega
  ext v
  simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply, ← Finset.smul_sum, hz, smul_zero,
    LinearMap.zero_apply]

omit [FiniteDimensional ℂ E] in
lemma integrated_scalar (ρ : Representation ℂ G E) (χ : G → ℂ)
    (hχ : ∀ g v, ρ g v = χ g • v) (f : G → ℂ) :
    integrated ρ f = (∑ g, f g * χ g) • LinearMap.id := by
  ext v
  simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply, hχ, smul_smul,
    Finset.sum_smul, LinearMap.id_apply]

lemma hsSq_scalar (c : ℂ) : hsSq (c • (LinearMap.id : Module.End ℂ E)) =
    (Module.finrank ℂ E : ℝ) * ‖c‖^2 := by
  simp [hsSq, norm_smul, (stdOrthonormalBasis ℂ E).norm_eq_one]

end Thorp.Fourier

end

end OAI
