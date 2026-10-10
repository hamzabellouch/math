import Mathlib
import OAI.Analysis.LaughlinGap.Contraction

namespace OAI

/-! Extended Pair. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators ComplexOrder

noncomputable def endCongr {n m : ℕ} (h : n=m) :
    Module.End ℂ (Hilbert n) ≃ₐ[ℂ] Module.End ℂ (Hilbert m) := h ▸ AlgEquiv.refl

lemma endCongr_transition {n m : ℕ} (h : n=m) (j : Fin n) (ε : Bool) :
    endCongr h (transition j ε) = transition (Fin.cast h j) ε := by subst m; rfl

lemma endCongr_adjoint {n m : ℕ} (h : n=m) (T : Module.End ℂ (Hilbert n)) :
    endCongr h T.adjoint = (endCongr h T).adjoint := by subst m; rfl

noncomputable def extendTo {n m : ℕ} (h : n ≤ m) :
    Module.End ℂ (Hilbert n) →ₐ[ℂ] Module.End ℂ (Hilbert m) :=
  (endCongr (Nat.add_sub_of_le h)).toAlgHom.comp (extendLocalHom n (m-n)).toAlgHom

lemma endCongr_extendLocal {n m k : ℕ} (h : m=k) (T : Module.End ℂ (Hilbert n)) :
    endCongr (congrArg (n+·) h) (extendLocal (m := m) T) = extendLocal (m := k) T := by
  subst k
  rfl

@[simp] lemma extendTo_add_dim (n m : ℕ) (T : Module.End ℂ (Hilbert n)) :
    extendTo (Nat.le_add_right n m) T = extendLocal (m := m) T := by
  exact endCongr_extendLocal (Nat.add_sub_cancel_left n m) T

@[simp] lemma extendTo_annihilation {n m : ℕ} (h : n ≤ m) (j : Fin n) :
    extendTo h (annihilation j) = annihilation (Fin.castLE h j) := by
  simp only [extendTo,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,annihilation]
  change endCongr _ (extendLocal (transition j false)) = _
  rw [extendLocal_transition,endCongr_transition]
  rfl

@[simp] lemma extendTo_adjoint {n m : ℕ} (h : n ≤ m) (T : Module.End ℂ (Hilbert n)) :
    extendTo h T.adjoint = (extendTo h T).adjoint := by
  simp only [extendTo,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom]
  change endCongr _ (extendLocal T.adjoint) = (endCongr _ (extendLocal T)).adjoint
  rw [← extendLocal_adjoint,endCongr_adjoint]

lemma extendTo_matrixLift {n m : ℕ} (h : n ≤ m) {ι : Type*} [Fintype ι]
    (B : ι → Module.End ℂ (Hilbert n)) (C : Matrix ι ι ℂ) :
    extendTo h (matrixLift B C) = matrixLift (fun r => extendTo h (B r)) C := by
  simp only [matrixLift,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,map_mul,extendTo_adjoint]

lemma localPair_support {n Q p : ℕ} (i j : Fin n) (h : i.val+j.val ≠ p+1) :
    (sphericalExteriorPairCoefficient Q p i.val j.val : ℂ) = 0 := by
  simp [sphericalExteriorPairCoefficient,h]

lemma extendTo_localPair {n m Q p : ℕ} (h : n ≤ m) (hp : p+1 < n) :
    extendTo h (localPair n Q p) = localPair m Q p := by
  classical
  simp only [localPair,pairAnnihilator,map_sum,apply_ite,map_smul,map_mul,
    extendTo_annihilation,map_zero]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  apply Finset.sum_bij_ne_zero (fun a _ _ => (Fin.castLE h a.1,Fin.castLE h a.2))
  · simp
  · intro a ha ha0 b hb hb0 he
    apply Prod.ext
    · exact Fin.ext (congrArg (fun x : Fin m × Fin m => x.1.val) he)
    · exact Fin.ext (congrArg (fun x : Fin m × Fin m => x.2.val) he)
  · intro b hb hb0
    have hw : b.1.val+b.2.val=p+1 := by
      by_contra hn
      exact hb0 (by simp [localPair_support b.1 b.2 hn])
    let a : Fin n × Fin n := (⟨b.1.val,by omega⟩,⟨b.2.val,by omega⟩)
    have he : (Fin.castLE h a.1,Fin.castLE h a.2)=b := by apply Prod.ext <;> rfl
    exact ⟨a,Finset.mem_univ _,by simpa [a] using hb0,he⟩
  · intro a ha ha0
    rfl

theorem local_four_family_transfer_to {n L : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : ι → Fin L) (j k : ι → Fin n)
    (s : ℕ → κ → ι → ℝ) (s₀ : κ → ι → ℝ)
    (C : ℕ → Matrix κ κ ℂ) (C₀ : Matrix κ κ ℂ)
    (hs : ∀ r b, Filter.Tendsto (fun Q => s Q r b) Filter.atTop (nhds (s₀ r b)))
    (hC : ∀ r t, Filter.Tendsto (fun Q => C Q r t) Filter.atTop (nhds (C₀ r t)))
    (hC₀ : C₀.IsHermitian)
    (hG : let B := fun r => ∑ b, (s₀ r b : ℂ) •
        (annihilation (k b) * annihilation (j b) * localPairStar n (p b).val)
      (createdGram B * C₀ * createdGram B).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Filter.Tendsto ρ Filter.atTop (nhds 0) ∧
      ∀ᶠ Q in Filter.atTop, ∀ m (h : n ≤ m) (x : Hilbert m),
        -(ρ Q) * (∑ a : Fin L, ‖extendTo h (localPair n Q a.val) x‖ ^ 2) ≤
          (inner ℂ x (extendTo h (matrixLift
            (fun r => ∑ b, (s Q r b : ℂ) •
              (annihilation (k b) * annihilation (j b) * localPair n Q (p b).val)) (C Q)) x)).re := by
  obtain ⟨ρ,hpos,hlim,hbound⟩ := local_four_family_transfer_of_gram p j k s s₀ C C₀ hs hC hC₀ hG
  refine ⟨ρ,hpos,hlim,?_⟩
  filter_upwards [hbound] with Q hQ
  intro m hm x
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hm
  simpa only [extendTo_add_dim] using hQ d x

end LaughlinGap.Occupation

end

end OAI
