import OAI.Combinatorics.BinaryEdit.Model
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace OAI

/-! Distortion of finite metric spaces under injective maps into real ℓ₁. -/

noncomputable section
open scoped ENNReal

namespace TreeEdit.BinaryLower

variable {X Y : Type*}

/-- The two finite sets whose maxima define distortion. -/
def expansionRatios (ρ : X → X → ℝ) (f : X → RealL1) : Set ℝ :=
  {r | ∃ x y, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y}

def contractionRatios (ρ : X → X → ℝ) (f : X → RealL1) : Set ℝ :=
  {r | ∃ x y, x ≠ y ∧ r = ρ x y / ‖f x - f y‖}

def embeddingDistortions (ρ : X → X → ℝ) : Set ℝ :=
  {D | ∃ f : X → RealL1, Function.Injective f ∧ D = distortion ρ f}

lemma expansionRatios_finite [Finite X] (ρ : X → X → ℝ) (f : X → RealL1) :
    (expansionRatios ρ f).Finite := by
  apply Set.Finite.subset (Set.finite_range (fun p : X × X => ‖f p.1 - f p.2‖ / ρ p.1 p.2))
  rintro r ⟨x, y, _, rfl⟩
  exact ⟨(x, y), rfl⟩

lemma contractionRatios_finite [Finite X] (ρ : X → X → ℝ) (f : X → RealL1) :
    (contractionRatios ρ f).Finite := by
  apply Set.Finite.subset (Set.finite_range (fun p : X × X => ρ p.1 p.2 / ‖f p.1 - f p.2‖))
  rintro r ⟨x, y, _, rfl⟩
  exact ⟨(x, y), rfl⟩

lemma expansionRatios_nonempty [Nontrivial X] (ρ : X → X → ℝ) (f : X → RealL1) :
    (expansionRatios ρ f).Nonempty := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact ⟨_, x, y, hxy, rfl⟩

lemma contractionRatios_nonempty [Nontrivial X] (ρ : X → X → ℝ) (f : X → RealL1) :
    (contractionRatios ρ f).Nonempty := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact ⟨_, x, y, hxy, rfl⟩

lemma expansion_nonneg [Finite X] [Nontrivial X] (ρ : X → X → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (f : X → RealL1) :
    0 ≤ sSup (expansionRatios ρ f) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact (div_nonneg (norm_nonneg _) (hρ x y)).trans
    (le_csSup (expansionRatios_finite ρ f).bddAbove ⟨x, y, hxy, rfl⟩)

lemma contraction_nonneg [Finite X] [Nontrivial X] (ρ : X → X → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (f : X → RealL1) :
    0 ≤ sSup (contractionRatios ρ f) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact (div_nonneg (hρ x y) (norm_nonneg _)).trans
    (le_csSup (contractionRatios_finite ρ f).bddAbove ⟨x, y, hxy, rfl⟩)

lemma distortion_nonneg [Finite X] [Nontrivial X] (ρ : X → X → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (f : X → RealL1) : 0 ≤ distortion ρ f :=
  mul_nonneg (expansion_nonneg ρ hρ f) (contraction_nonneg ρ hρ f)

/-- Every finite set admits an injection into the full sequence space. -/
lemma exists_injective_L1 (X : Type*) [Finite X] :
    ∃ f : X → RealL1, Function.Injective f := by
  classical
  let := Fintype.ofFinite X
  let f : X → RealL1 := fun x => lp.single 1 0 ((Fintype.equivFin X x).val : ℝ)
  refine ⟨f, ?_⟩
  intro x y h
  have hv := congrArg (fun z : RealL1 => z 0) h
  simp only [f, lp.single_apply_self] at hv
  apply (Fintype.equivFin X).injective
  apply Fin.ext
  exact_mod_cast hv

lemma embeddingDistortions_nonempty [Finite X] (ρ : X → X → ℝ) :
    (embeddingDistortions ρ).Nonempty := by
  obtain ⟨f, hf⟩ := exists_injective_L1 X
  exact ⟨distortion ρ f, f, hf, rfl⟩

lemma embeddingDistortions_bddBelow [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y) :
    BddBelow (embeddingDistortions ρ) := by
  refine ⟨0, ?_⟩
  rintro D ⟨f, _, rfl⟩
  exact distortion_nonneg ρ hρ f

lemma c1_nonneg [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y) : 0 ≤ c1 X ρ := by
  apply le_csInf (embeddingDistortions_nonempty ρ)
  rintro D ⟨f, _, rfl⟩
  exact distortion_nonneg ρ hρ f

lemma c1_le_distortion [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (f : X → RealL1) (hf : Function.Injective f) : c1 X ρ ≤ distortion ρ f := by
  exact csInf_le (embeddingDistortions_bddBelow ρ hρ) ⟨f, hf, rfl⟩

lemma le_c1 [Finite X] (ρ : X → X → ℝ) (D : ℝ)
    (h : ∀ f : X → RealL1, Function.Injective f → D ≤ distortion ρ f) :
    D ≤ c1 X ρ := by
  apply le_csInf (embeddingDistortions_nonempty ρ)
  rintro e ⟨f, hf, rfl⟩
  exact h f hf

lemma expansionRatios_comp_subset (ρ : X → X → ℝ) (σ : Y → Y → ℝ)
    (g : X → Y) (hg : Function.Injective g)
    (hiso : ∀ x y, σ (g x) (g y) = ρ x y) (f : Y → RealL1) :
    expansionRatios ρ (f ∘ g) ⊆ expansionRatios σ f := by
  rintro r ⟨x, y, hxy, rfl⟩
  exact ⟨g x, g y, fun h => hxy (hg h), by simp [hiso]⟩

lemma contractionRatios_comp_subset (ρ : X → X → ℝ) (σ : Y → Y → ℝ)
    (g : X → Y) (hg : Function.Injective g)
    (hiso : ∀ x y, σ (g x) (g y) = ρ x y) (f : Y → RealL1) :
    contractionRatios ρ (f ∘ g) ⊆ contractionRatios σ f := by
  rintro r ⟨x, y, hxy, rfl⟩
  exact ⟨g x, g y, fun h => hxy (hg h), by simp [hiso]⟩

/-- Restriction to an isometric subspace cannot increase distortion. -/
lemma distortion_comp_le [Finite X] [Nontrivial X] [Finite Y] [Nontrivial Y]
    (ρ : X → X → ℝ) (σ : Y → Y → ℝ) (hσ : ∀ x y, 0 ≤ σ x y)
    (g : X → Y) (hg : Function.Injective g)
    (hiso : ∀ x y, σ (g x) (g y) = ρ x y) (f : Y → RealL1) :
    distortion ρ (f ∘ g) ≤ distortion σ f := by
  have hρ : ∀ x y, 0 ≤ ρ x y := fun x y => (hiso x y) ▸ hσ (g x) (g y)
  apply mul_le_mul
  · apply csSup_le (expansionRatios_nonempty ρ (f ∘ g))
    intro r hr
    exact le_csSup (expansionRatios_finite σ f).bddAbove
      (expansionRatios_comp_subset ρ σ g hg hiso f hr)
  · apply csSup_le (contractionRatios_nonempty ρ (f ∘ g))
    intro r hr
    exact le_csSup (contractionRatios_finite σ f).bddAbove
      (contractionRatios_comp_subset ρ σ g hg hiso f hr)
  · exact contraction_nonneg ρ hρ (f ∘ g)
  · exact expansion_nonneg σ hσ f

/-- The optimal ℓ₁ distortion is monotone under injective isometries. -/
lemma c1_mono_isometry [Finite X] [Nontrivial X] [Finite Y] [Nontrivial Y]
    (ρ : X → X → ℝ) (σ : Y → Y → ℝ) (hσ : ∀ x y, 0 ≤ σ x y)
    (g : X → Y) (hg : Function.Injective g)
    (hiso : ∀ x y, σ (g x) (g y) = ρ x y) :
    c1 X ρ ≤ c1 Y σ := by
  have hρ : ∀ x y, 0 ≤ ρ x y := fun x y => (hiso x y) ▸ hσ (g x) (g y)
  apply le_c1
  intro f hf
  exact (c1_le_distortion ρ hρ (f ∘ g) (hf.comp hg)).trans
    (distortion_comp_le ρ σ hσ g hg hiso f)

lemma c1_eq_of_equiv [Finite X] [Nontrivial X] [Finite Y] [Nontrivial Y]
    (ρ : X → X → ℝ) (σ : Y → Y → ℝ) (hσ : ∀ x y, 0 ≤ σ x y)
    (e : X ≃ Y) (hiso : ∀ x y, σ (e x) (e y) = ρ x y) :
    c1 X ρ = c1 Y σ := by
  apply le_antisymm (c1_mono_isometry ρ σ hσ e e.injective hiso)
  apply c1_mono_isometry σ ρ
  · intro x y
    exact (hiso x y) ▸ hσ (e x) (e y)
  · exact e.symm.injective
  · intro x y
    simpa using (hiso (e.symm x) (e.symm y)).symm

/-- A noncontracting embedding with expansion at most `D` gives the usual
upper bound on optimal distortion. No existence theorem is assumed here. -/
lemma c1_le_of_bounds [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X → RealL1) (D : ℝ) (hD : 0 ≤ D)
    (hlower : ∀ x y, ρ x y ≤ ‖f x - f y‖)
    (hupper : ∀ x y, ‖f x - f y‖ ≤ D * ρ x y) :
    c1 X ρ ≤ D := by
  have hf : Function.Injective f := by
    intro x y h
    by_contra hxy
    have ht := hlower x y
    rw [h, sub_self, norm_zero] at ht
    exact (not_le_of_gt (hpos x y hxy)) ht
  apply (c1_le_distortion ρ hρ f hf).trans
  have he : sSup (expansionRatios ρ f) ≤ D := by
    apply csSup_le (expansionRatios_nonempty ρ f)
    rintro r ⟨x, y, hxy, rfl⟩
    exact (div_le_iff₀ (hpos x y hxy)).2 (hupper x y)
  have hc : sSup (contractionRatios ρ f) ≤ 1 := by
    apply csSup_le (contractionRatios_nonempty ρ f)
    rintro r ⟨x, y, hxy, rfl⟩
    have hn : 0 < ‖f x - f y‖ := (hpos x y hxy).trans_le (hlower x y)
    exact (div_le_iff₀ hn).2 (by simpa using hlower x y)
  calc
    distortion ρ f ≤ D * 1 :=
      mul_le_mul he hc (contraction_nonneg ρ hρ f) hD
    _ = D := mul_one D

/-- Comparing two metrics through a scaled bi-Lipschitz injection costs only
its ratio of expansion to contraction in the distortion product. -/
lemma distortion_comp_le_bilip [Finite X] [Nontrivial X] [Finite Y] [Nontrivial Y]
    (ρ : X → X → ℝ) (σ : Y → Y → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (hσ : ∀ x y, 0 ≤ σ x y)
    (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (g : X → Y) (hg : Function.Injective g)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hlower : ∀ x y, a * ρ x y ≤ σ (g x) (g y))
    (hupper : ∀ x y, σ (g x) (g y) ≤ b * ρ x y) (f : Y → RealL1) :
    distortion ρ (f ∘ g) ≤ (b / a) * distortion σ f := by
  have he : sSup (expansionRatios ρ (f ∘ g)) ≤ b * sSup (expansionRatios σ f) := by
    apply csSup_le (expansionRatios_nonempty ρ (f ∘ g))
    rintro r ⟨x, y, hxy, rfl⟩
    have ht := hpos x y hxy
    have hs : 0 < σ (g x) (g y) := (mul_pos ha ht).trans_le (hlower x y)
    have hratio : ‖f (g x) - f (g y)‖ / σ (g x) (g y) ≤
        sSup (expansionRatios σ f) :=
      le_csSup (expansionRatios_finite σ f).bddAbove
        ⟨g x, g y, fun h => hxy (hg h), rfl⟩
    calc
      ‖(f ∘ g) x - (f ∘ g) y‖ / ρ x y ≤
          (b * ‖f (g x) - f (g y)‖) / σ (g x) (g y) := by
        apply (div_le_div_iff₀ ht hs).2
        have hn := norm_nonneg (f (g x) - f (g y))
        change ‖f (g x) - f (g y)‖ * σ (g x) (g y) ≤
          b * ‖f (g x) - f (g y)‖ * ρ x y
        nlinarith [mul_le_mul_of_nonneg_left (hupper x y) hn]
      _ = b * (‖f (g x) - f (g y)‖ / σ (g x) (g y)) := by ring
      _ ≤ b * sSup (expansionRatios σ f) := mul_le_mul_of_nonneg_left hratio hb
  have hc : sSup (contractionRatios ρ (f ∘ g)) ≤
      (1 / a) * sSup (contractionRatios σ f) := by
    apply csSup_le (contractionRatios_nonempty ρ (f ∘ g))
    rintro r ⟨x, y, hxy, rfl⟩
    have hratio : σ (g x) (g y) / ‖f (g x) - f (g y)‖ ≤
        sSup (contractionRatios σ f) :=
      le_csSup (contractionRatios_finite σ f).bddAbove
        ⟨g x, g y, fun h => hxy (hg h), rfl⟩
    have hmetric : ρ x y ≤ σ (g x) (g y) / a := by
      apply (le_div_iff₀ ha).2
      simpa [mul_comm] using hlower x y
    calc
      ρ x y / ‖(f ∘ g) x - (f ∘ g) y‖ ≤
          (σ (g x) (g y) / a) / ‖f (g x) - f (g y)‖ :=
        div_le_div_of_nonneg_right hmetric (norm_nonneg _)
      _ = (1 / a) * (σ (g x) (g y) / ‖f (g x) - f (g y)‖) := by ring
      _ ≤ (1 / a) * sSup (contractionRatios σ f) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
  calc
    distortion ρ (f ∘ g) ≤
        (b * sSup (expansionRatios σ f)) *
          ((1 / a) * sSup (contractionRatios σ f)) :=
      mul_le_mul he hc (contraction_nonneg ρ hρ (f ∘ g))
        (mul_nonneg hb (expansion_nonneg σ hσ f))
    _ = (b / a) * distortion σ f := by unfold distortion; unfold expansionRatios contractionRatios; ring

/-- Optimal distortion transfer through any scaled bi-Lipschitz injection.
In particular, `a=P/804` and `b=P` give constant distortion loss. -/
lemma c1_le_bilip_mul [Finite X] [Nontrivial X] [Finite Y] [Nontrivial Y]
    (ρ : X → X → ℝ) (σ : Y → Y → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (hσ : ∀ x y, 0 ≤ σ x y)
    (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (g : X → Y) (hg : Function.Injective g)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x y, a * ρ x y ≤ σ (g x) (g y))
    (hupper : ∀ x y, σ (g x) (g y) ≤ b * ρ x y) :
    c1 X ρ ≤ (b / a) * c1 Y σ := by
  have hba : 0 < b / a := div_pos hb ha
  have h : c1 X ρ / (b / a) ≤ c1 Y σ := by
    apply le_c1
    intro f hf
    apply (div_le_iff₀ hba).2
    calc
      c1 X ρ ≤ distortion ρ (f ∘ g) := c1_le_distortion ρ hρ (f ∘ g) (hf.comp hg)
      _ ≤ (b / a) * distortion σ f :=
        distortion_comp_le_bilip ρ σ hρ hσ hpos g hg a b ha hb.le hlower hupper f
      _ = distortion σ f * (b / a) := mul_comm _ _
  simpa [mul_comm] using (div_le_iff₀ hba).1 h

/-- Rescaling by the maximal contraction ratio makes an injective embedding
noncontracting without changing the distortion bound. -/
lemma exists_normalized_embedding [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X → RealL1) (hf : Function.Injective f) :
    ∃ g : X → RealL1, Function.Injective g ∧
      ∀ x y, ρ x y ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ distortion ρ f * ρ x y := by
  let C := sSup (contractionRatios ρ f)
  let E := sSup (expansionRatios ρ f)
  have hC : 0 ≤ C := contraction_nonneg ρ hρ f
  let g : X → RealL1 := fun x => C • f x
  have hnorm (x y : X) : ‖g x - g y‖ = C * ‖f x - f y‖ := by
    dsimp [g]
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hC]
  have hbounds : ∀ x y, ρ x y ≤ ‖g x - g y‖ ∧
      ‖g x - g y‖ ≤ distortion ρ f * ρ x y := by
    intro x y
    by_cases hxy : x = y
    · subst y
      simp [hdiag]
    have hr : 0 < ρ x y := hpos x y hxy
    have hn : 0 < ‖f x - f y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxy (hf h)))
    have hc : ρ x y / ‖f x - f y‖ ≤ C :=
      le_csSup (contractionRatios_finite ρ f).bddAbove ⟨x, y, hxy, rfl⟩
    have he : ‖f x - f y‖ / ρ x y ≤ E :=
      le_csSup (expansionRatios_finite ρ f).bddAbove ⟨x, y, hxy, rfl⟩
    constructor
    · rw [hnorm]
      exact (div_le_iff₀ hn).1 hc
    · rw [hnorm]
      have ht := mul_le_mul_of_nonneg_left ((div_le_iff₀ hr).1 he) hC
      change C * ‖f x - f y‖ ≤ (E * C) * ρ x y
      nlinarith
  refine ⟨g, ?_, hbounds⟩
  intro x y h
  by_contra hxy
  have ht := (hbounds x y).1
  rw [h, sub_self, norm_zero] at ht
  exact (not_le_of_gt (hpos x y hxy)) ht

/-- An obstruction proved for all normalized embeddings gives a lower bound
on the infimum defining `c1`. This is the passage used by the two tree routes. -/
lemma le_c1_of_normalized [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (D : ℝ)
    (hobstruction : ∀ (g : X → RealL1) (A : ℝ),
      (∀ x y, ρ x y ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ A * ρ x y) → D ≤ A) :
    D ≤ c1 X ρ := by
  apply le_c1
  intro f hf
  obtain ⟨g, _, hg⟩ := exists_normalized_embedding ρ hρ hdiag hpos f hf
  exact hobstruction g (distortion ρ f) hg

/-- The dual normalization used verbatim by the finite-tree obstruction:
the image distance lies between `ρ / distortion` and `ρ`. -/
lemma exists_nonexpanding_embedding [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X → RealL1) (hf : Function.Injective f) :
    0 < distortion ρ f ∧ ∃ g : X → RealL1, Function.Injective g ∧
      ∀ x y, ρ x y / distortion ρ f ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ ρ x y := by
  obtain ⟨g, _, hg⟩ := exists_normalized_embedding ρ hρ hdiag hpos f hf
  obtain ⟨x₀, y₀, hxy⟩ := exists_pair_ne X
  have hr := hpos x₀ y₀ hxy
  have hD : 0 < distortion ρ f := by
    have ht := (hg x₀ y₀).1.trans (hg x₀ y₀).2
    nlinarith
  let g' : X → RealL1 := fun x => (1 / distortion ρ f) • g x
  have hnorm (x y : X) : ‖g' x - g' y‖ = ‖g x - g y‖ / distortion ρ f := by
    dsimp [g']
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
    ring
  have hb : ∀ x y, ρ x y / distortion ρ f ≤ ‖g' x - g' y‖ ∧
      ‖g' x - g' y‖ ≤ ρ x y := by
    intro x y
    rw [hnorm]
    constructor
    · exact div_le_div_of_nonneg_right (hg x y).1 hD.le
    · apply (div_le_iff₀ hD).2
      simpa [mul_comm] using (hg x y).2
  refine ⟨hD, g', ?_, hb⟩
  intro x y h
  by_contra hxy
  have ht := (hb x y).1
  rw [h, sub_self, norm_zero] at ht
  exact (not_le_of_gt (div_pos (hpos x y hxy) hD)) ht

lemma le_c1_of_nonexpanding [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (D : ℝ)
    (hobstruction : ∀ (g : X → RealL1) (A : ℝ), 0 < A →
      (∀ x y, ρ x y / A ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ ρ x y) → D ≤ A) :
    D ≤ c1 X ρ := by
  apply le_c1
  intro f hf
  obtain ⟨hD, g, _, hg⟩ := exists_nonexpanding_embedding ρ hρ hdiag hpos f hf
  exact hobstruction g (distortion ρ f) hD hg

end TreeEdit.BinaryLower

end

end OAI
