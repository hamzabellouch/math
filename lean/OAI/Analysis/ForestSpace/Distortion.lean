import OAI.Analysis.ForestSpace.Diamonds

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Diamond

noncomputable section

section Distortion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact separated approximate-midpoint estimate proved for the target space. -/
def LensProperty (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ (R ε : ℝ), 0 < R → 0 < ε → ∀ (x : E) (y : ℕ → E),
    (∀ j, ‖x+y j‖ ≤ R) → (∀ j, ‖x-y j‖ ≤ R) →
    (∀ i j, i ≠ j → ε ≤ ‖y i-y j‖) → ε^2/48 ≤ R^2-‖x‖^2

 theorem parent_step (hLens : LensProperty E) (R ℓ : ℝ) (hR : 0 < R) (hℓ : 0 < ℓ)
    (a b : E) (w : ℕ → E)
    (hp : ∀ j, ‖w j-a‖/ℓ ≤ R) (hm : ∀ j, ‖b-w j‖/ℓ ≤ R)
    (hs : ∀ i j, i ≠ j → 2*ℓ ≤ ‖w i-w j‖) :
    (‖b-a‖/(2*ℓ))^2+1/12 ≤ R^2 := by
  let x : E := (2*ℓ)⁻¹ • (b-a)
  let y : ℕ → E := fun j => ℓ⁻¹ • (w j-(1/2 : ℝ) • (a+b))
  have hc : (2*ℓ)⁻¹ = (1/2 : ℝ)*ℓ⁻¹ := by field_simp
  have hplus : ∀ j, x+y j = ℓ⁻¹ • (w j-a) := by
    intro j
    dsimp [x,y]
    rw [hc]
    module
  have hminus : ∀ j, x-y j = ℓ⁻¹ • (b-w j) := by
    intro j
    dsimp [x,y]
    rw [hc]
    module
  have hdn : ∀ i j, ‖y i-y j‖ = ‖w i-w j‖/ℓ := by
    intro i j
    have he : y i-y j = ℓ⁻¹ • (w i-w j) := by dsimp [y]; module
    rw [he,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
    ring
  have hh := hLens R 2 hR (by norm_num) x y
    (by
      intro j
      rw [hplus,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
      simpa only [div_eq_mul_inv,mul_comm] using hp j)
    (by
      intro j
      rw [hminus,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
      simpa only [div_eq_mul_inv,mul_comm] using hm j)
    (by intro i j hij; rw [hdn]; exact (le_div_iff₀ hℓ).mpr (hs i j hij))
  have hx : ‖x‖ = ‖b-a‖/(2*ℓ) := by
    dsimp [x]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hℓ.le))]
    ring
  rw [hx] at hh
  norm_num at hh
  linarith

/-- The squared loss holds on each original edge, without requiring attainment
of any supremum of edge stretches. -/
 theorem edge_sq_loss (hLens : LensProperty E) (A : Network) (hA : A.graph.Connected)
    (n : ℕ) (f : (A.iterate n).V → E) (C : ℝ) (hC : 0 ≤ C)
    (hl : ∀ u v, ((A.iterate n).graph.dist u v : ℝ) ≤ ‖f u-f v‖)
    (hu : ∀ u v, ‖f u-f v‖ ≤ C*((A.iterate n).graph.dist u v : ℝ))
    (e : A.E) :
    (‖f (A.old n (A.right e))-f (A.old n (A.left e))‖/(2:ℝ)^n)^2+(n:ℝ)/12 ≤ C^2 := by
  induction n generalizing A with
  | zero =>
    have hh := hu (A.right e) (A.left e)
    have he : A.graph.dist (A.right e) (A.left e) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (A.edge_adj e).symm
    change ‖f (A.right e)-f (A.left e)‖ ≤ C*(A.graph.dist (A.right e) (A.left e) : ℝ) at hh
    rw [he,Nat.cast_one,mul_one] at hh
    simpa using (sq_le_sq₀ (norm_nonneg _) hC).mpr hh
  | succ n ih =>
    let ℓ : ℝ := (2:ℝ)^n
    have hℓ : 0 < ℓ := pow_pos (by norm_num) _
    let a := f (A.refine.old n (Sum.inl (A.left e)))
    let b := f (A.refine.old n (Sum.inl (A.right e)))
    let w : ℕ → E := fun j => f (A.refine.old n (Sum.inr (e,j)))
    have hchild : ∀ c : A.refine.E,
        (‖f (A.refine.old n (A.refine.right c))-f (A.refine.old n (A.refine.left c))‖/ℓ)^2+
          (n:ℝ)/12 ≤ C^2 := by
      intro c
      exact ih A.refine (A.refine_connected hA) f hl hu c
    have hrad : 1 ≤ C^2-(n:ℝ)/12 := by
      have hb := hchild (e,0,false)
      have hd := A.refine.old_edge_dist (A.refine_connected hA) n (e,0,false)
      have hlo := hl (A.refine.old n (Sum.inl (A.left e))) (A.refine.old n (Sum.inr (e,0)))
      have hd' : ((A.refine.iterate n).graph.dist
          (A.refine.old n (Sum.inl (A.left e))) (A.refine.old n (Sum.inr (e,0))) : ℝ) = ℓ := by
        dsimp [ℓ]
        exact_mod_cast hd
      change ((A.refine.iterate n).graph.dist
        (A.refine.old n (Sum.inl (A.left e))) (A.refine.old n (Sum.inr (e,0))) : ℝ) ≤
          ‖a-w 0‖ at hlo
      rw [hd',norm_sub_rev] at hlo
      have hc : 1 ≤ ‖w 0-a‖/ℓ := (le_div_iff₀ hℓ).mpr (by simpa using hlo)
      change (‖w 0-a‖/ℓ)^2+(n:ℝ)/12 ≤ C^2 at hb
      nlinarith
    let R : ℝ := Real.sqrt (C^2-(n:ℝ)/12)
    have hR : 0 < R := Real.sqrt_pos.mpr (by linarith)
    have hR2 : R^2 = C^2-(n:ℝ)/12 := Real.sq_sqrt (by linarith)
    have hp : ∀ j, ‖w j-a‖/ℓ ≤ R := by
      intro j
      have hh := hchild (e,j,false)
      change (‖w j-a‖/ℓ)^2+(n:ℝ)/12 ≤ C^2 at hh
      exact Real.le_sqrt_of_sq_le (by linarith)
    have hm : ∀ j, ‖b-w j‖/ℓ ≤ R := by
      intro j
      have hh := hchild (e,j,true)
      change (‖b-w j‖/ℓ)^2+(n:ℝ)/12 ≤ C^2 at hh
      exact Real.le_sqrt_of_sq_le (by linarith)
    have hs : ∀ i j, i ≠ j → 2*ℓ ≤ ‖w i-w j‖ := by
      intro i j hij
      have hh := hl (A.refine.old n (Sum.inr (e,i))) (A.refine.old n (Sum.inr (e,j)))
      rw [A.old_middle_dist hA n e i j hij] at hh
      have he : ((2^(n+1) : ℕ) : ℝ) = 2*ℓ := by
        dsimp [ℓ]
        norm_cast
        rw [pow_succ,mul_comm]
      exact he ▸ hh
    have hh := parent_step hLens R ℓ hR hℓ a b w hp hm hs
    rw [hR2] at hh
    have he : (2:ℝ)^(n+1) = 2*ℓ := by dsimp [ℓ]; rw [pow_succ,mul_comm]
    change (‖b-a‖/(2:ℝ)^(n+1))^2+((n+1:ℕ):ℝ)/12 ≤ C^2
    rw [he,Nat.cast_add,Nat.cast_one]
    linarith

/-- The distortion convention, including its arbitrary positive scale. -/
def EmbeddingBound (k : ℕ) (f : (diamond k).V → E) (C : ℝ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ ∀ u v,
    s*distance k u v ≤ ‖f u-f v‖ ∧ ‖f u-f v‖ ≤ C*s*distance k u v

 theorem distortion_lower (hLens : LensProperty E) (k : ℕ)
    (f : (diamond k).V → E) (C : ℝ) (hf : EmbeddingBound k f C) :
    Real.sqrt (1+(k:ℝ)/12) ≤ C := by
  obtain ⟨s,hs,hf⟩ := hf
  let g : (diamond k).V → E := fun v => s⁻¹ • f v
  have hgn : ∀ u v, ‖g u-g v‖ = ‖f u-f v‖/s := by
    intro u v
    dsimp [g]
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    ring
  have hl : ∀ u v, ((base.iterate k).graph.dist u v : ℝ) ≤ ‖g u-g v‖ := by
    intro u v
    rw [hgn]
    exact (le_div_iff₀ hs).mpr (by simpa only [distance,mul_comm] using (hf u v).1)
  have hu : ∀ u v, ‖g u-g v‖ ≤ C*((base.iterate k).graph.dist u v : ℝ) := by
    intro u v
    rw [hgn]
    exact (div_le_iff₀ hs).mpr (by simpa only [distance,mul_assoc,mul_comm,mul_left_comm] using (hf u v).2)
  let a := base.old k (base.left ())
  let b := base.old k (base.right ())
  have hd : ((base.iterate k).graph.dist a b : ℝ) = (2:ℝ)^k := by
    exact_mod_cast (base.old_edge_dist base_connected k ())
  have hc : 1 ≤ C := by
    have hlo := hl a b
    have hup := hu a b
    rw [hd] at hlo hup
    have hpow : 0 < (2:ℝ)^k := pow_pos (by norm_num) _
    nlinarith
  have hbound := edge_sq_loss hLens base base_connected k g C (by linarith) hl hu ()
  have hlo : 1 ≤ ‖g b-g a‖/(2:ℝ)^k := by
    have hh := hl a b
    rw [hd,norm_sub_rev] at hh
    exact (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) k)).mpr (by simpa using hh)
  change (‖g b-g a‖/(2:ℝ)^k)^2+(k:ℝ)/12 ≤ C^2 at hbound
  apply Real.sqrt_le_iff.mpr
  exact ⟨by linarith,by nlinarith⟩

end Distortion

end
end Diamond


/-- The distortion bound, with the positive-scale
bi-Lipschitz convention and the actual shortest-path distance on D_k. -/
theorem main_diamond_distortion (k : ℕ)
    (f : (Diamond.diamond k).V → FullDual Vertex) (C : ℝ)
    (hf : Diamond.EmbeddingBound k f C) :
    Real.sqrt (1+(k:ℝ)/12) ≤ C :=
  Diamond.distortion_lower main_lens k f C hf

end

end ForestSpace

end OAI
