import OAI.Analysis.SeparableQuotients.StrictSingularity

namespace OAI

noncomputable section

namespace SeparableQuotient.Singular
lemma top_infinite {𝕜 Y : Type*} [Field 𝕜] [AddCommGroup Y] [Module 𝕜 Y]
    (hI : ¬ FiniteDimensional 𝕜 Y) : ¬ FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 Y) := by
  intro hh
  let : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 Y) := hh
  let e : (⊤ : Submodule 𝕜 Y) ≃ₗ[𝕜] Y := Submodule.topEquiv
  exact hI (FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective)
end SeparableQuotient.Singular
namespace SeparableQuotient.ActualSpace
open Norming Singular Set
open scoped Classical Topology

abbrev Cut := WithTop Γ

def initialSet (γ : Cut) : Set Γ := {a | (a : Cut) < γ}

lemma initialSet_connected (γ : Cut) : Set.OrdConnected (initialSet γ) :=
  Set.ordConnected_Iio.preimage_mono (WithTop.coe_mono)

def initialCrop (γ : Cut) := Crop.ordinalSet (initialSet γ) (initialSet_connected γ)

def initialP (γ : Cut) : E →L[ℝ] E := projection (initialCrop γ)

def colorP (k : ℕ) : E →L[ℝ] E := projection (Crop.oneColor k)

@[simp] lemma coordinate_initialP (γ : Cut) (x : E) (a : Γ) :
    coordinate a (initialP γ x) = if (a : Cut) < γ then coordinate a x else 0 := by
  simp only [initialP,coordinate_projection,initialCrop,Crop.ordinalSet_set,initialSet,Set.mem_ofPred_eq]

@[simp] lemma coordinate_colorP (k : ℕ) (x : E) (a : Γ) :
    coordinate a (colorP k x) = if Colors.color a = k then coordinate a x else 0 := by
  simp only [colorP,coordinate_projection,Crop.oneColor_set,Norming.colorSet,Set.mem_ofPred_eq]

@[simp] lemma initialP_top (x : E) : initialP ⊤ x = x := by
  apply norming.coordinate_ext
  intro a
  simp

lemma initialP_initialP {β γ : Cut} (h : β ≤ γ) (x : E) :
    initialP β (initialP γ x) = initialP β x := by
  apply norming.coordinate_ext
  intro a
  by_cases ha : (a : Cut) < β
  · simp [ha,lt_of_lt_of_le ha h]
  · simp [ha]

lemma initialP_colorP (γ : Cut) (k : ℕ) (x : E) :
    initialP γ (colorP k x) = colorP k (initialP γ x) := by
  apply norming.coordinate_ext
  intro a
  simp only [coordinate_initialP,coordinate_colorP]
  split_ifs <;> rfl

lemma colorP_colorP (k : ℕ) (x : E) : colorP k (colorP k x) = colorP k x := by
  apply norming.coordinate_ext
  intro a
  simp only [coordinate_colorP]
  split_ifs <;> rfl

/-- The least non-strictly-singular initial projection terminates at an actual
limit cut: every coordinate below it has a strictly larger coordinate below it. -/
lemma exists_minimal_cut (F : Submodule ℝ E) (_hF : IsClosed (F : Set E))
    (hI : ¬ FiniteDimensional ℝ F) :
    ∃ γ : Cut, (¬ StrictlySingular ((initialP γ).comp F.subtypeL)) ∧
      (∀ β < γ, StrictlySingular ((initialP β).comp F.subtypeL)) ∧
      (∀ a : Γ, (a : Cut) < γ → ∃ b : Γ, a < b ∧ (b : Cut) < γ) := by
  have htop : ¬ StrictlySingular ((initialP ⊤).comp F.subtypeL) := by
    rw [not_strictlySingular_iff]
    refine ⟨⊤,isClosed_univ,?_,1,by norm_num,?_⟩
    · exact Singular.top_infinite hI
    · intro x
      simp only [ContinuousLinearMap.comp_apply,Submodule.coe_subtypeL,initialP_top,one_mul]
      exact le_rfl
  obtain ⟨γ,hγ,hmin⟩ := wellFounded_lt.has_min
    {γ : Cut | ¬ StrictlySingular ((initialP γ).comp F.subtypeL)} ⟨⊤,htop⟩
  have hsmall (β : Cut) (hβ : β < γ) : StrictlySingular ((initialP β).comp F.subtypeL) := by
    by_contra hh
    exact hmin β hh hβ
  refine ⟨γ,hγ,hsmall,?_⟩
  intro a ha
  by_contra hh
  have hup (b : Γ) (hb : (b : Cut) < γ) : b ≤ a := by
    by_contra hn
    exact hh ⟨b,lt_of_not_ge hn,hb⟩
  obtain ⟨M,hMc,hMi,c,hc,hcM⟩ := (not_strictlySingular_iff _).mp hγ
  let d : F →L[ℝ] ℝ := (coordinate a).comp F.subtypeL
  obtain ⟨N,hNM,hNc,hNi,hd⟩ := finite_annihilator M hMc hMi {d}
  obtain ⟨x,hx⟩ := hsmall (a : Cut) ha N hNc hNi c hc
  have hax : coordinate a ((x : F) : E) = 0 := hd x x.property d (Finset.mem_singleton_self _)
  have heq : initialP (a : Cut) ((x : F) : E) = initialP γ ((x : F) : E) := by
    apply norming.coordinate_ext
    intro b
    by_cases hb : (b : Cut) < γ
    · have hba := hup b hb
      rcases hba.eq_or_lt with rfl | hba
      · simp only [coordinate_initialP,lt_self_iff_false,ite_false,hax,hb,ite_true]
      · simp only [coordinate_initialP,hb,WithTop.coe_lt_coe.mpr hba,ite_true]
    · have hn : ¬ b < a := fun hba => hb (lt_trans (WithTop.coe_lt_coe.mpr hba) ha)
      simp only [coordinate_initialP,hb,WithTop.coe_lt_coe,hn,ite_false]
  have hy := hcM (⟨x,hNM x.property⟩ : M)
  change c*‖(x : F)‖ ≤ ‖initialP γ ((x : F) : E)‖ at hy
  change ‖initialP (a : Cut) ((x : F) : E)‖ < c*‖(x : F)‖ at hx
  rw [heq] at hx
  exact (not_lt_of_ge hy) hx

/-- Range reduction before the optional single-color reduction. -/
lemma exists_initial_reduction (F : Submodule ℝ E) (hF : IsClosed (F : Set E))
    (hI : ¬ FiniteDimensional ℝ F) :
    ∃ (γ : Cut) (H : Submodule ℝ E), IsClosed (H : Set E) ∧
      ¬ FiniteDimensional ℝ H ∧
      (∀ a : Γ, (a : Cut) < γ → ∃ b : Γ, a < b ∧ (b : Cut) < γ) ∧
      (∀ β < γ, StrictlySingular ((initialP β).comp H.subtypeL)) ∧
      ∃ U : H →L[ℝ] F, ∀ x : H, initialP γ (U x) = x := by
  let : CompleteSpace F := hF.completeSpace_coe
  obtain ⟨γ,hγ,hsmall,hlim⟩ := exists_minimal_cut F hF hI
  obtain ⟨H,hH,hHi,U,hU⟩ := exists_lift_of_not_strictlySingular
    ((initialP γ).comp F.subtypeL) hγ
  let : CompleteSpace H := hH.completeSpace_coe
  refine ⟨γ,H,hH,hHi,hlim,?_,U,hU⟩
  intro β hβ
  have hh := (hsmall β hβ).comp_right _ U
  have he : ((initialP β).comp F.subtypeL).comp U = (initialP β).comp H.subtypeL := by
    apply ContinuousLinearMap.ext
    intro x
    have hu : initialP γ ((U x : F) : E) = x := hU x
    change initialP β ((U x : F) : E) = initialP β (x : E)
    rw [← hu,initialP_initialP hβ.le]
  rwa [he] at hh

def familyP (γ : Cut) : Family → E →L[ℝ] E
  | .pure k => (colorP k).comp (initialP γ)
  | .mixed => initialP γ

structure BranchReduction (F : Submodule ℝ E) where
  cut : Cut
  family : Family
  H : Submodule ℝ E
  closed : IsClosed (H : Set E)
  infinite : ¬ FiniteDimensional ℝ H
  noLast : ∀ a : Γ, (a : Cut) < cut → ∃ b : Γ, a < b ∧ (b : Cut) < cut
  earlier : ∀ β < cut, StrictlySingular ((initialP β).comp H.subtypeL)
  mixed : family = .mixed → ∀ k, StrictlySingular ((colorP k).comp H.subtypeL)
  U : H →L[ℝ] F
  lift : ∀ x : H, familyP cut family (U x) = x

/-- Ordinal and color projections reduce a closed infinite-dimensional subspace to a branch subspace. -/
theorem exists_branchReduction (F : Submodule ℝ E) (hF : IsClosed (F : Set E))
    (hI : ¬ FiniteDimensional ℝ F) : Nonempty (BranchReduction F) := by
  obtain ⟨γ,H,hH,hHi,hlim,hsmall,U,hU⟩ := exists_initial_reduction F hF hI
  let : CompleteSpace H := hH.completeSpace_coe
  by_cases hm : ∀ k, StrictlySingular ((colorP k).comp H.subtypeL)
  · exact ⟨⟨γ,.mixed,H,hH,hHi,hlim,hsmall,fun _ => hm,U,hU⟩⟩
  · push Not at hm
    obtain ⟨k,hk⟩ := hm
    obtain ⟨H',hH',hH'i,V,hV⟩ := exists_lift_of_not_strictlySingular
      ((colorP k).comp H.subtypeL) hk
    let : CompleteSpace H' := hH'.completeSpace_coe
    refine ⟨⟨γ,.pure k,H',hH',hH'i,hlim,?_,by simp,U.comp V,?_⟩⟩
    · intro β hβ
      have hh := ((hsmall β hβ).comp_left _ (colorP k)).comp_right _ V
      have he : ((colorP k).comp ((initialP β).comp H.subtypeL)).comp V =
          (initialP β).comp H'.subtypeL := by
        apply ContinuousLinearMap.ext
        intro x
        change colorP k (initialP β ((V x : H) : E)) = initialP β (x : E)
        rw [← initialP_colorP,show colorP k ((V x : H) : E) = x from hV x]
      rwa [he] at hh
    · intro x
      change colorP k (initialP γ ((U (V x) : F) : E)) = x
      rw [hU]
      exact hV x

end SeparableQuotient.ActualSpace

end

end OAI
