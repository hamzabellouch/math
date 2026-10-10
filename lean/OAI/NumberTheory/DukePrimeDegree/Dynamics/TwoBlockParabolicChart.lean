import OAI.NumberTheory.DukePrimeDegree.Dynamics.TwoBlockNeutralAction

namespace OAI

/-!
# A two-block chart with the neutral factor last

Reordering the Gauss factorization gives lower-cross × upper-cross ×
neutral coordinates. Right multiplication by a neutral element changes
only the neutral coordinate. This is the equivariance required before
applying a Haar product argument to an actual invariant measure.
-/

noncomputable section
open Matrix
open scoped Topology Classical

namespace DukePrimeDegree

abbrev TwoBlockParabolicCoordinates (a b : ℕ) :=
  Matrix (Fin b) (Fin a) ℝ × Matrix (Fin a) (Fin b) ℝ × twoBlockNeutralGroup a b

def twoBlockGaussReorderEquiv (a b : ℕ) :
    TwoBlockGaussCoordinates a b ≃ TwoBlockParabolicCoordinates a b where
  toFun p := (p.1, twoBlockUpperAction p.2.1 p.2.2, p.2.1)
  invFun p := (p.1, p.2.2, twoBlockUpperAction p.2.2⁻¹ p.2.1)
  left_inv p := by
    obtain ⟨L, C, U⟩ := p
    simp only [twoBlockUpperAction_inv_apply]
  right_inv p := by
    obtain ⟨L, U, C⟩ := p
    simp only [twoBlockUpperAction_apply_inv]

lemma continuous_twoBlockGaussReorder (a b : ℕ) :
    Continuous (twoBlockGaussReorderEquiv a b) := by
  have hL : Continuous (fun p : TwoBlockGaussCoordinates a b => p.1) := continuous_fst
  have hC : Continuous (fun p : TwoBlockGaussCoordinates a b => p.2.1) :=
    continuous_snd.fst
  have hU : Continuous (fun p : TwoBlockGaussCoordinates a b => p.2.2) :=
    continuous_snd.snd
  have hact : Continuous (fun p : TwoBlockGaussCoordinates a b =>
      twoBlockUpperAction p.2.1 p.2.2) :=
    (continuous_twoBlockUpperAction a b).comp (hC.prodMk hU)
  exact hL.prodMk (hact.prodMk hC)

lemma continuous_twoBlockGaussReorder_symm (a b : ℕ) :
    Continuous (twoBlockGaussReorderEquiv a b).symm := by
  have hL : Continuous (fun p : TwoBlockParabolicCoordinates a b => p.1) := continuous_fst
  have hC : Continuous (fun p : TwoBlockParabolicCoordinates a b => p.2.2) :=
    continuous_snd.snd
  have hU : Continuous (fun p : TwoBlockParabolicCoordinates a b => p.2.1) :=
    continuous_snd.fst
  have hact : Continuous (fun p : TwoBlockParabolicCoordinates a b =>
      twoBlockUpperAction p.2.2⁻¹ p.2.1) := by
    have h11 : Continuous (fun p : TwoBlockParabolicCoordinates a b =>
        (p.2.2⁻¹).val.val.toBlocks₁₁) := by
      change Continuous (fun p : TwoBlockParabolicCoordinates a b =>
        fun i j => (p.2.2⁻¹).val.val (Sum.inl i) (Sum.inl j))
      fun_prop
    have h22 : Continuous (fun p : TwoBlockParabolicCoordinates a b =>
        p.2.2.val.val.toBlocks₂₂) := by
      change Continuous (fun p : TwoBlockParabolicCoordinates a b =>
        fun i j => p.2.2.val.val (Sum.inr i) (Sum.inr j))
      fun_prop
    simpa only [twoBlockUpperAction, inv_inv] using (h11.matrix_mul hU).matrix_mul h22
  exact hL.prodMk (hC.prodMk hact)

def twoBlockGaussReorder (a b : ℕ) :
    TwoBlockGaussCoordinates a b ≃ₜ TwoBlockParabolicCoordinates a b where
  toEquiv := twoBlockGaussReorderEquiv a b
  continuous_toFun := continuous_twoBlockGaussReorder a b
  continuous_invFun := continuous_twoBlockGaussReorder_symm a b

def twoBlockParabolicHomeomorph (a b : ℕ) :
    twoBlockGaussCell a b ≃ₜ TwoBlockParabolicCoordinates a b :=
  (twoBlockGaussHomeomorph a b).trans (twoBlockGaussReorder a b)

def twoBlockParabolicParam {a b : ℕ} (p : TwoBlockParabolicCoordinates a b) :
    TwoBlockSL a b :=
  twoBlockLower p.1 * twoBlockUpper p.2.1 * p.2.2.val

theorem twoBlockParabolicHomeomorph_symm_val {a b : ℕ}
    (p : TwoBlockParabolicCoordinates a b) :
    ((twoBlockParabolicHomeomorph a b).symm p).val = twoBlockParabolicParam p := by
  change twoBlockLower p.1 * p.2.2.val *
      twoBlockUpper (twoBlockUpperAction p.2.2⁻¹ p.2.1) =
    twoBlockLower p.1 * twoBlockUpper p.2.1 * p.2.2.val
  rw [mul_assoc, twoBlockNeutral_upper_reorder, twoBlockUpperAction_apply_inv, ← mul_assoc]

theorem twoBlockParabolicParam_isOpenEmbedding (a b : ℕ) :
    Topology.IsOpenEmbedding
      (twoBlockParabolicParam : TwoBlockParabolicCoordinates a b → TwoBlockSL a b) := by
  have h := (isOpen_twoBlockGaussCell a b).isOpenEmbedding_subtypeVal.comp
    (twoBlockParabolicHomeomorph a b).symm.isOpenEmbedding
  have he : (Subtype.val ∘ (twoBlockParabolicHomeomorph a b).symm) =
      (twoBlockParabolicParam : TwoBlockParabolicCoordinates a b → TwoBlockSL a b) := by
    funext p
    exact twoBlockParabolicHomeomorph_symm_val p
  rw [he] at h
  exact h

theorem twoBlockParabolicParam_mem_cell {a b : ℕ}
    (p : TwoBlockParabolicCoordinates a b) :
    twoBlockParabolicParam p ∈ twoBlockGaussCell a b := by
  rw [← twoBlockParabolicHomeomorph_symm_val p]
  exact ((twoBlockParabolicHomeomorph a b).symm p).property

theorem twoBlockParabolicParam_right_neutral {a b : ℕ}
    (p : TwoBlockParabolicCoordinates a b) (C : twoBlockNeutralGroup a b) :
    twoBlockParabolicParam (p.1, p.2.1, p.2.2 * C) =
      twoBlockParabolicParam p * C.val := by
  change twoBlockLower p.1 * twoBlockUpper p.2.1 * (p.2.2.val * C.val) =
    (twoBlockLower p.1 * twoBlockUpper p.2.1 * p.2.2.val) * C.val
  exact (mul_assoc _ _ _).symm

theorem twoBlockGaussCell_right_neutral {a b : ℕ} (g : TwoBlockSL a b)
    (hg : g ∈ twoBlockGaussCell a b) (C : twoBlockNeutralGroup a b) :
    g * C.val ∈ twoBlockGaussCell a b := by
  let p := (twoBlockParabolicHomeomorph a b) ⟨g, hg⟩
  have hp : twoBlockParabolicParam p = g := by
    rw [← twoBlockParabolicHomeomorph_symm_val]
    exact congrArg Subtype.val ((twoBlockParabolicHomeomorph a b).symm_apply_apply ⟨g, hg⟩)
  rw [← hp, ← twoBlockParabolicParam_right_neutral]
  exact twoBlockParabolicParam_mem_cell _

end DukePrimeDegree

end

end OAI
