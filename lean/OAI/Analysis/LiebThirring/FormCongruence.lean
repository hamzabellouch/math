import OAI.Analysis.LiebThirring.Resolvent

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped Topology

lemma form_congr_ae {W : ℝ → ℝ} {u u' v v' : H1}
    (hu : u.val =ᵐ[volume] u'.val) (hdu : u.grad =ᵐ[volume] u'.grad)
    (hv : v.val =ᵐ[volume] v'.val) (hdv : v.grad =ᵐ[volume] v'.grad) :
    schrodingerForm W u v = schrodingerForm W u' v' := by
  unfold schrodingerForm
  congr 1
  · apply integral_congr_ae
    filter_upwards [hdu,hdv] with x hx hy
    rw [hx,hy]
  · apply integral_congr_ae
    filter_upwards [hu,hv] with x hx hy
    rw [hx,hy]

lemma toH1_ofH1_val (u : H1) : (toH1 (ofH1 u)).val =ᵐ[volume] u.val :=
  u.val_memLp.coeFn_toLp

lemma toH1_ofH1_grad (u : H1) : (toH1 (ofH1 u)).grad =ᵐ[volume] u.grad :=
  u.grad_memLp.coeFn_toLp

lemma form_ofH1 (W : ℝ → ℝ) (u v : H1) :
    schrodingerForm W (toH1 (ofH1 u)) (toH1 (ofH1 v)) = schrodingerForm W u v :=
  form_congr_ae (toH1_ofH1_val u) (toH1_ofH1_grad u)
    (toH1_ofH1_val v) (toH1_ofH1_grad v)

lemma ofH1_toH1 (u : H1C) : ofH1 (toH1 u) = u := by
  apply valL_injective
  rw [valL_ofH1,toLp_toH1]

lemma form_eq_of_valLp_eq {W : ℝ → ℝ} (v u u' : H1)
    (hu : u.val_memLp.toLp u.val = u'.val_memLp.toLp u'.val) :
    schrodingerForm W v u = schrodingerForm W v u' := by
  have he : ofH1 u = ofH1 u' := valL_injective hu
  rw [← form_ofH1 W v u,← form_ofH1 W v u',he]

/-- The usual graph characterization of the operator associated with a closed
semibounded form.  The quantifier is over the entire weak H¹ domain. -/
def IsAssociated (W : ℝ → ℝ) (A : L2C →ₗ.[ℂ] L2C) : Prop :=
  ∀ f g : L2C, (∃ hf : f ∈ A.domain, A ⟨f,hf⟩ = g) ↔
    ∃ u : H1, u.val_memLp.toLp u.val = f ∧
      ∀ v : H1, schrodingerForm W v u = inner ℂ (v.val_memLp.toLp v.val) g

lemma isAssociated_iff_graph (W : ℝ → ℝ) (A : L2C →ₗ.[ℂ] L2C) :
    IsAssociated W A ↔ ∀ f g : L2C, (∃ hf : f ∈ A.domain, A ⟨f,hf⟩ = g) ↔
      ∃ u : H1C, valL u = f ∧
        ∀ v : H1C, schrodingerForm W (toH1 v) (toH1 u) = inner ℂ (valL v) g := by
  have he (f g : L2C) :
      (∃ u : H1, u.val_memLp.toLp u.val = f ∧
        ∀ v : H1, schrodingerForm W v u = inner ℂ (v.val_memLp.toLp v.val) g) ↔
      ∃ u : H1C, valL u = f ∧
        ∀ v : H1C, schrodingerForm W (toH1 v) (toH1 u) = inner ℂ (valL v) g := by
    constructor
    · rintro ⟨u,hu,hq⟩
      refine ⟨ofH1 u,hu,fun v ↦ ?_⟩
      have h := hq (toH1 v)
      rw [toLp_toH1] at h
      rw [← form_ofH1 W (toH1 v) u,ofH1_toH1] at h
      exact h
    · rintro ⟨u,hu,hq⟩
      refine ⟨toH1 u,(toLp_toH1 u).trans hu,fun v ↦ ?_⟩
      have h := hq (ofH1 v)
      rw [← ofH1_toH1 u,form_ofH1] at h
      exact h
  unfold IsAssociated
  simp only [he]

lemma negativeEigenfunction_iff_operator {W : ℝ → ℝ} {A : L2C →ₗ.[ℂ] L2C}
    (hA : IsAssociated W A) (k : ℝ) (u : H1) :
    IsNegativeEigenfunction W k u ↔ 0 < k ∧
      ∃ hu : u.val_memLp.toLp u.val ∈ A.domain,
        A ⟨u.val_memLp.toLp u.val,hu⟩ = (-(k^2 : ℝ) : ℂ) • u.val_memLp.toLp u.val := by
  constructor
  · rintro ⟨hk,hq⟩
    refine ⟨hk,(hA _ _).mpr ⟨u,rfl,fun v ↦ ?_⟩⟩
    rw [inner_smul_right]
    simpa only [l2Pairing_eq_inner] using hq v
  · rintro ⟨hk,hu⟩
    obtain ⟨u',he,hq⟩ := (hA _ _).mp hu
    refine ⟨hk,fun v ↦ ?_⟩
    rw [form_eq_of_valLp_eq v u u' he.symm,hq,inner_smul_right,l2Pairing_eq_inner]

end SharpLiebThirring.OperatorProof

end

end OAI
