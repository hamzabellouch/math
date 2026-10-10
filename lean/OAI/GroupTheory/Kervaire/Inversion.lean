import OAI.GroupTheory.Kervaire.Conjugation

namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A] in
lemma perm_apply_inverse (σ : Perm D) (d : D) : σ (σ⁻¹ d) = d := by
  rw [Equiv.Perm.inv_def]; exact σ.apply_symm_apply d
omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A] in
lemma perm_inverse_apply (σ : Perm D) (d : D) : σ⁻¹ (σ d) = d := by
  rw [Equiv.Perm.inv_def]; exact σ.symm_apply_apply d

omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A] in
lemma cycles_inv (σ : Perm D) : SameCycle.setoid σ⁻¹ = SameCycle.setoid σ := by
  ext x y; exact sameCycle_inv

omit [Fintype V] [Fintype I] [DecidableEq D] [Group A] in
lemma numCycles_inverse (σ : Perm D) : numCycles σ⁻¹ = numCycles σ := by
  exact Fintype.card_congr (Quotient.congrRight (fun _ _ ↦ sameCycle_inv))

omit [Fintype V] [Fintype I] [DecidableEq D] [Group A] in
lemma planar_inverse (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (hp : planar σ θ) :
    planar σ⁻¹ θ := by
  have heθ : θ⁻¹ = θ := by
    apply Equiv.ext; intro d
    apply θ.injective
    simp only [perm_apply_inverse,hθ]
  have hf : numCycles (σ⁻¹*θ) = numCycles (σ*θ) := by
    calc
      _ = numCycles (θ*σ)⁻¹ := by rw [mul_inv_rev,heθ]
      _ = numCycles (θ*σ) := numCycles_inverse _
      _ = _ := numCycles_mul_comm _ _
  unfold planar at hp ⊢
  simpa only [numCycles_inverse,hf,components,cycles_inv] using hp

omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A] in
lemma circle_inverse (σ : Perm D) (o : D) (l : List D) (h : Circle σ o l) :
    Circle σ⁻¹ o l.reverse := by
  have hh : (o::(l++[o])).IsChain (fun a b ↦ σ⁻¹ b = a) := by
    apply h.imp
    intro x y he
    apply σ.injective
    simpa only [perm_apply_inverse] using he.symm
  have hr := List.isChain_reverse.mpr hh
  simpa only [Circle,List.reverse_cons,List.reverse_append,List.reverse_singleton,List.singleton_append,
    List.append_assoc,List.cons_append,List.nil_append,List.reverse_nil] using hr

/-- Reflection reverses every vertex, negates the traversal signs, and exchanges
both sides of each band potential. -/
def OuterRibbon.inv {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) : OuterRibbon (V := V) ρ a s o l.reverse := by
  let ε : V → ℤ := fun v ↦ -r.atlas.ε v
  have hn (v : V) (i : I) : r.σ⁻¹ (r.atlas.disk (v,i)) = r.atlas.disk (vertexNext ρ ε (v,i)) := by
    apply r.σ.injective
    rw [perm_apply_inverse]
    rcases r.atlas.polarity v with hv | hv
    · simp only [vertexNext,ε,hv,show -(1:ℤ) ≠ 1 by omega,ite_false]
      rw [r.atlas.next]
      simp only [vertexNext,hv,ite_true,ρ.apply_symm_apply]
    · simp only [vertexNext,ε,hv,neg_neg,ite_true]
      rw [r.atlas.next]
      simp only [vertexNext,hv,show (-1:ℤ) ≠ 1 by omega,ite_false,ρ.symm_apply_apply]
  let b : DiskAtlas (V := V) ρ a s r.σ⁻¹ (fun d ↦ -r.t d) := {
    disk := r.atlas.disk, ε := ε
    polarity := by intro v; rcases r.atlas.polarity v with hv|hv <;> simp [ε,hv]
    next := hn
    sign := by intro v i; rw [r.atlas.sign]; exact (neg_mul _ _).symm }
  refine {
    σ := r.σ⁻¹, θ := r.θ, t := fun d ↦ -r.t d, u := r.u ∘ r.θ, atlas := b
    involutive := r.involutive, planar' := planar_inverse _ _ r.involutive r.planar'
    opposite := by intro d; rw [r.opposite]
    marker := r.marker, marker_sign := by rw [r.marker_sign,neg_zero]
    circle := circle_inverse _ _ _ r.circle
    nodup := by simpa only [List.nodup_cons,List.mem_reverse,List.nodup_reverse] using r.nodup
    unit := by intro d hd; rcases r.unit d (List.mem_reverse.mp hd) with h|h <;> simp [h]
    disjoint := by intro vi; simpa only [List.mem_cons,List.mem_reverse] using r.disjoint vi
    cover := ?_, corners := ?_ }
  · intro d
    obtain hd | hd | ⟨hs,ht⟩ := r.cover d
    · exact Or.inl hd
    · exact Or.inr (Or.inl (by simpa only [List.mem_cons,List.mem_reverse] using hd))
    · exact Or.inr (Or.inr ⟨by rw [show r.σ⁻¹ d = r.σ⁻¹ (r.σ d) from congrArg (fun x ↦ r.σ⁻¹ x) hs.symm,perm_inverse_apply],ht⟩)
  · intro v i
    have hc : corner r.σ⁻¹ r.θ (r.u ∘ r.θ) (r.atlas.disk (v,i)) =
        (corner r.σ r.θ r.u (r.σ⁻¹ (r.atlas.disk (v,i))))⁻¹ := by
      simp only [corner,Function.comp_apply,r.involutive,perm_apply_inverse,mul_inv_rev,inv_inv]
    rw [hc,hn]
    rcases r.atlas.polarity v with hv|hv
    · change vertexCorner ρ a ε (v,i) = _
      simp only [vertexNext,ε,hv,show -(1:ℤ) ≠ 1 by omega,ite_false]
      rw [← r.corners]
      simp only [vertexCorner,hv,show -(1:ℤ) ≠ 1 by omega,ite_false,ite_true]
    · change vertexCorner ρ a ε (v,i) = _
      simp only [vertexNext,ε,hv,neg_neg,ite_true]
      rw [← r.corners]
      simp only [vertexCorner,hv,neg_neg,ite_true,show (-1:ℤ) ≠ 1 by omega,ite_false,ρ.symm_apply_apply,inv_inv]

omit [Fintype V] [Fintype I] [DecidableEq D] in
lemma OuterRibbon.value_inv {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) : r.inv.value = r.value⁻¹ := by
  have he (d) : transportLetter r.θ (fun d ↦ -r.t d) (r.u ∘ r.θ) d =
      (transportLetter r.θ r.t r.u d)⁻¹ := by
    simp only [transportLetter,Function.comp_apply,r.involutive,ofAdd_neg,map_inv,mul_inv_rev,inv_inv]
    group
  have hh : transportEval r.θ (fun d ↦ -r.t d) (r.u ∘ r.θ) l.reverse =
      (transportEval r.θ r.t r.u l)⁻¹ := by
    rw [transportEval,transportEval,List.prod_inv_reverse,List.map_map,List.map_reverse]
    congr 2
    exact List.map_congr_left (fun d _ ↦ he d)
  rw [OuterRibbon.value_formula,OuterRibbon.value_formula]
  change Coprod.inl (r.u (r.θ o)) * transportEval r.θ (fun d ↦ -r.t d) (r.u ∘ r.θ) l.reverse * (Coprod.inl (r.u (r.θ o)))⁻¹ = _
  rw [r.marker,hh]
  group
end KervaireRibbon

end
end

end OAI
