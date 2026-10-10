import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalTail01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped BigOperators
noncomputable section
end
end
 

 
section
noncomputable section
namespace RationalPolynomialMap
variable {σ : Type*} [Fintype σ]
lemma contDiff {f : (σ → ℝ) → ℝ} (hf : IsPolynomial f) : ContDiff ℝ (⊤ : ℕ∞) f := by
  obtain ⟨p,hp⟩ := hf
  have he : f = fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p := funext hp
  rw [he]
  clear hp he f
  induction p using MvPolynomial.induction_on with
  | C q => simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : σ → ℝ => (q:ℝ)))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (by fun_prop)

 

lemma bounded_lipschitz {f : (σ → ℝ) → ℝ} (hf : IsPolynomial f) (B : ℝ) :
    ∃ M > 0,
      (∀ x, ‖x‖ ≤ B → |f x| ≤ M) ∧
      (∀ x y, ‖x‖ ≤ B → ‖y‖ ≤ B → |f x-f y| ≤ M*‖x-y‖) := by
  have hd := contDiff hf
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : σ → ℝ) B).exists_bound_of_continuousOn hd.continuous.continuousOn
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0 : σ → ℝ) B).exists_bound_of_continuousOn
    (hd.continuous_fderiv (by simp)).continuousOn
  refine ⟨max (max M D) 0 + 1,by positivity,?_,?_⟩
  · intro x hx
    have he := hM x (by simpa using hx)
    change |f x| ≤ M at he
    exact he.trans (by grind)
  · intro x y hx hy
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x (_ : x ∈ Metric.closedBall (0 : σ → ℝ) B) => hd.differentiable (by simp) x)
      hD (convex_closedBall (0 : σ → ℝ) B) (by simpa using hy) (by simpa using hx)
    change |f x-f y| ≤ D * ‖x-y‖ at he
    exact he.trans (mul_le_mul_of_nonneg_right (by grind) (norm_nonneg _))

end RationalPolynomialMap
end
end
 

 
section
noncomputable section
namespace RationalLattice
open RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n) {σ τ : Type*}

lemma polynomialMap_comp {f : (τ → ℝ) → G} (hf : IsPolynomialMap c f)
    {g : (σ → ℝ) → (τ → ℝ)} (hg : ∀ i, IsPolynomial (fun x => g x i)) :
    IsPolynomialMap c (fun x => f (g x)) := fun i => RationalPolynomialMap.comp (hf i) hg

lemma polynomialMap_inv {f : (σ → ℝ) → G} (hf : IsPolynomialMap c f) :
    IsPolynomialMap c (fun x => (f x)⁻¹) := by
  have h : ∀ m : ℕ, ∀ hm : m < n,
      IsPolynomial (fun x => c.coord ((f x)⁻¹) ⟨m,hm⟩) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      let i : Fin n := ⟨m,hm⟩
      have he (x : σ → ℝ) : c.coord ((f x)⁻¹) i = -c.coord (f x) i -
          MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (Sum.elim (fun j : Fin i.val => c.coord (f x) ⟨j.val,lt_trans j.isLt i.isLt⟩)
              (fun j : Fin i.val => c.coord ((f x)⁻¹) ⟨j.val,lt_trans j.isLt i.isLt⟩)) (c.correction i) := by
        have he := c.mul_coord (f x) ((f x)⁻¹) i
        rw [mul_inv_cancel,c.one_coord] at he
        linarith
      simp_rw [show (⟨m,hm⟩ : Fin n)=i from rfl,he]
      apply RationalPolynomialMap.sub (RationalPolynomialMap.neg (hf i))
      apply RationalPolynomialMap.eval
      intro j
      cases j with
      | inl j => exact hf _
      | inr j => exact ih j.val j.isLt (lt_trans j.isLt hm)
  intro i
  exact h i.val i.isLt

end RationalLattice
end
end
 

 
section
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

lemma correction_eq_of_lower_eq (i : Fin n) {g g' h h' : G}
    (hg : ∀ j : Fin n, j < i → c.coord g j = c.coord g' j)
    (hh : ∀ j : Fin n, j < i → c.coord h j = c.coord h' j) :
    c.coord (g*h) i - c.coord g i - c.coord h i =
      c.coord (g'*h') i - c.coord g' i - c.coord h' i := by
  rw [c.mul_coord g h,c.mul_coord g' h']
  have he : (Sum.elim (fun j : Fin i.val => c.coord g ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j : Fin i.val => c.coord h ⟨j.val,lt_trans j.isLt i.isLt⟩)) =
    (Sum.elim (fun j : Fin i.val => c.coord g' ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j : Fin i.val => c.coord h' ⟨j.val,lt_trans j.isLt i.isLt⟩)) := by
    funext j
    cases j with
    | inl j => exact hg _ j.isLt
    | inr j => exact hh _ j.isLt
  rw [he]
  ring

lemma mul_lower_congr (i : Fin n) {g g' h h' : G}
    (hg : ∀ j : Fin n, j < i → c.coord g j = c.coord g' j)
    (hh : ∀ j : Fin n, j < i → c.coord h j = c.coord h' j) :
    ∀ j : Fin n, j < i → c.coord (g*h) j = c.coord (g'*h') j := by
  intro j hj
  have he := correction_eq_of_lower_eq c j (fun k hk => hg k (lt_trans hk hj))
    (fun k hk => hh k (lt_trans hk hj))
  rw [hg j hj,hh j hj] at he
  linarith

lemma conj_lower_congr (a : G) (i : Fin n) {u v : G}
    (huv : ∀ j : Fin n, j < i → c.coord u j = c.coord v j) :
    ∀ j : Fin n, j < i → c.coord (a⁻¹*u*a) j = c.coord (a⁻¹*v*a) j := by
  exact mul_lower_congr c i (mul_lower_congr c i (fun _ _ => rfl) huv) (fun _ _ => rfl)

lemma conj_coord_difference (a : G) (i : Fin n) {u v : G}
    (huv : ∀ j : Fin n, j < i → c.coord u j = c.coord v j) :
    c.coord (a⁻¹*u*a) i - c.coord (a⁻¹*v*a) i = c.coord u i - c.coord v i := by
  have h1 := correction_eq_of_lower_eq c i (g:=a⁻¹) (g':=a⁻¹) (fun _ _ => rfl) huv
  have h2 := correction_eq_of_lower_eq c i
    (mul_lower_congr c i (g:=a⁻¹) (g':=a⁻¹) (fun _ _ => rfl) huv) (h:=a) (h':=a) (fun _ _ => rfl)
  linarith

lemma conj_mul_coord_difference (a : G) (i : Fin n) {u u' v v' : G}
    (hu : ∀ j : Fin n, j < i → c.coord u j = c.coord u' j)
    (hv : ∀ j : Fin n, j < i → c.coord v j = c.coord v' j) :
    c.coord (a⁻¹*u*a*v) i - c.coord (a⁻¹*u'*a*v') i =
      c.coord u i - c.coord u' i + c.coord v i - c.coord v' i := by
  have h1 := conj_coord_difference c a i hu
  have h2 := correction_eq_of_lower_eq c i (conj_lower_congr c a i hu) hv
  linarith

 
def truncate (i : Fin n) (v : Fin i.val → ℝ) : G :=
  c.coord.symm (fun j => if h : j < i then v ⟨j.val,h⟩ else 0)
@[simp] lemma truncate_coord_self (i : Fin n) (v : Fin i.val → ℝ) :
    c.coord (truncate c i v) i = 0 := by simp [truncate]
lemma truncate_coord_lower (i : Fin n) (v : Fin i.val → ℝ) (j : Fin n) (hj : j < i) :
    c.coord (truncate c i v) j = v ⟨j.val,hj⟩ := by simp [truncate,hj]

lemma conj_mul_truncated (a u v : G) (i : Fin n) :
    c.coord (a⁻¹*u*a*v) i = c.coord u i + c.coord v i +
      c.coord (a⁻¹*truncate c i (fun j => c.coord u ⟨j.val,lt_trans j.isLt i.isLt⟩)*a*
        truncate c i (fun j => c.coord v ⟨j.val,lt_trans j.isLt i.isLt⟩)) i := by
  have hu : ∀ j : Fin n, j < i → c.coord u j =
      c.coord (truncate c i (fun j => c.coord u ⟨j.val,lt_trans j.isLt i.isLt⟩)) j := by
    intro j hj
    rw [truncate_coord_lower c i _ j hj]
  have hv : ∀ j : Fin n, j < i → c.coord v j =
      c.coord (truncate c i (fun j => c.coord v ⟨j.val,lt_trans j.isLt i.isLt⟩)) j := by
    intro j hj
    rw [truncate_coord_lower c i _ j hj]
  have he := conj_mul_coord_difference c a i hu hv
  rw [truncate_coord_self,truncate_coord_self] at he
  linarith

lemma polynomialMap_truncate {σ : Type*} (i : Fin n) {f : (σ → ℝ) → (Fin i.val → ℝ)}
    (hf : ∀ j, RationalPolynomialMap.IsPolynomial (fun x => f x j)) :
    IsPolynomialMap c (fun x => truncate c i (f x)) := by
  intro j
  simp only [truncate,Homeomorph.apply_symm_apply]
  split_ifs
  · exact hf _
  · exact RationalPolynomialMap.zero

end RationalLattice
end
end
 

 
section
noncomputable section
namespace PairTail
open RationalLattice

def joinHomeomorph (r d : ℕ) : ((Fin r → ℝ) × (Fin d → ℝ)) ≃ₜ (Fin (r+d) → ℝ) where
  toFun x := Fin.append x.1 x.2
  invFun x := (fun i => x (i.castAdd d),fun j => x (j.natAdd r))
  left_inv x := by simp
  right_inv x := by funext i; exact Fin.addCases (fun _ => by simp) (fun _ => by simp) i
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact (continuous_apply j).comp continuous_fst
    · simp only [Fin.append_right]
      exact (continuous_apply j).comp continuous_snd
  continuous_invFun := (continuous_pi (fun _ => continuous_apply _)).prodMk
    (continuous_pi (fun _ => continuous_apply _))

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d r : ℕ} (c : RealCoordinates G (t+d))
variable (K : Subgroup G) [K.Normal]
variable (hK : ∀ g : G, g ∈ K ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i = 0)
variable (hr : r ≤ t+d) (N : Subgroup G) [N.Normal]
variable (hN : ∀ g : G, g ∈ N ↔ ∀ i : Fin (t+d), i.val < r → c.coord g i = 0)
variable (hcent : N ≤ Subgroup.center G)

def baseSection (x : G ⧸ N) : G := MalcevPrefixQuotient.represent c
  (MalcevPrefixQuotient.coordinates c hr N hN x)
omit [IsTopologicalGroup G] [N.Normal] in
lemma section_spec (x : G ⧸ N) : (QuotientGroup.mk (baseSection c hr N hN x) : G ⧸ N) = x :=
  MalcevPrefixQuotient.rebuild_coordinates c hr N hN x
omit [IsTopologicalGroup G] [N.Normal] in
lemma section_continuous : Continuous (baseSection c hr N hN) :=
  c.coord.symm.continuous.comp (MalcevPrefixQuotient.lift_continuous.comp
    (MalcevPrefixQuotient.coordinates_continuous c hr N hN))

 

def chartHomeomorph : (square K ⧸ diagonal K N) ≃ₜ (Fin (r+d) → ℝ) :=
  (quotientHomeomorph K N hcent (baseSection c hr N hN) (section_spec c hr N hN)
    (section_continuous c hr N hN)).trans
    (((MalcevPrefixQuotient.homeomorph c hr N hN).prodCongr
      (RationalTailCoordinates.tailHomeomorph c K hK)).trans (joinHomeomorph r d))

omit [N.Normal] in
@[simp] lemma chart_base (x : square K) (i : Fin r) :
    chartHomeomorph c K hK hr N hN hcent (QuotientGroup.mk x) (i.castAdd d) =
      c.coord x.val.1 (MalcevPrefixQuotient.embed hr i) := by
  change Fin.append _ _ (i.castAdd d) = _
  rw [Fin.append_left]
  rfl
omit [N.Normal] in
@[simp] lemma chart_tail (x : square K) (j : Fin d) :
    chartHomeomorph c K hK hr N hN hcent (QuotientGroup.mk x) (j.natAdd r) =
      c.coord (x.val.1⁻¹*x.val.2) (RationalTailCoordinates.embed t j) := by
  change Fin.append _ _ (j.natAdd r) = _
  rw [Fin.append_right]
  rfl

omit [N.Normal] in
lemma chart_one : chartHomeomorph c K hK hr N hN hcent (QuotientGroup.mk (1:square K)) = 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using c.one_coord (MalcevPrefixQuotient.embed hr j)
  · simpa using c.one_coord (RationalTailCoordinates.embed t j)

omit [N.Normal] in
lemma chart_rebuild_base (x : Fin (r+d) → ℝ) :
    (chartHomeomorph c K hK hr N hN hcent).symm x =
      QuotientGroup.mk (pair K
        (MalcevPrefixQuotient.represent c (fun i : Fin r => x (i.castAdd d)))
        (RationalTailCoordinates.rebuild c K hK (fun i : Fin d => x (i.natAdd r)))) := by
  apply (chartHomeomorph c K hK hr N hN hcent).injective
  rw [Homeomorph.apply_symm_apply]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [chart_base]
    simp [pair,MalcevPrefixQuotient.represent]
  · rw [chart_tail]
    simp [pair,RationalTailCoordinates.rebuild]

end PairTail

end
end
end
end
end

end OAI
