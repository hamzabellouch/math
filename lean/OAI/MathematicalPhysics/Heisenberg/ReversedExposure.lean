import OAI.MathematicalPhysics.Heisenberg.ScheduledResiduals

namespace OAI

section
noncomputable section
open scoped BigOperators Classical

end

noncomputable section
open scoped BigOperators Classical
namespace Heisenberg.Exposure
open Heisenberg.Geometry Heisenberg.SpatialFrame Heisenberg.SparseWitness Heisenberg.LatticeRegular

lemma layerBlocked_frame {X B T : Type} [Fintype B] [Nonempty B] [Fintype T]
    (Λ : Finset X) (s : Equiv.Perm T) (τ : T → Equiv.Perm (Slots (B:=B) Λ))
    (P : Set (T×Slots (B:=B) Λ)) (base : T → Bool) (t : T) :
    layerBlocked (fun v : Slots (B:=B) Λ=>v.1.val) s τ P base t =
      blocked Λ (holeCut s τ base P t) := by
  ext x
  constructor
  · rintro ⟨⟨v,hv⟩,hh⟩
    have hx : x∈Λ := hv ▸ v.1.property
    refine ⟨hx,?_⟩
    intro a
    exact hh (⟨x,hx⟩,a) rfl
  · rintro ⟨hx,hh⟩
    refine ⟨⟨(⟨x,hx⟩,Classical.choice inferInstance),rfl⟩,?_⟩
    intro v hv
    obtain ⟨⟨y,hy⟩,a⟩ := v
    dsimp only at hv
    subst y
    exact hh a

theorem uniform_layer_regularity (k M b : ℕ) (hb : 100≤b)
    (α L ν a : ℝ) (hα : 0≤α) (hL : (2*(k+1):ℕ)≤L)
    (hba : 2≤(b:ℝ)^α) (hν : 0<ν) (ha : 0≤a) :
    ∃ p₀>0,∃ C≥0,∀ (T V : Type) [Fintype T] [Fintype V] (loc : V → Site (k+1)) (s : Equiv.Perm T)
      (u v : T → V) (P : Set (T×V)) (rates : T → ℝ)
      (_hrates : ∀ i,0≤rates i ∧ rates i≤1) (t : T) (p : ℝ),
      0≤p → p≤p₀ →
      (∀ U : Finset V,localGrowth loc α L U → (∀ j∈U,(t,j)∉P) →
        (∑ c,if ∀ j∈U,(t,j)∈Cycle.MissingSet
          (layerHistory s (fun i=>Equiv.swap (u i) (v i)) c) P then
          layerMass s u v P rates c else 0)≤p^U.card) →
      ∀ (x : Site (k+1)) (R : ℕ),
        (∑ c,if ¬Regular (layerBlocked loc s (fun i=>Equiv.swap (u i) (v i)) P c t)
          x R M ν then layerMass s u v P rates c else 0) ≤
          C*((1+(R:ℝ))^(k+1)*p^(2*(k+1))+(1+(R:ℝ))^(-a)) := by
  obtain ⟨p₀,hp₀,C,hC,hr⟩ := regularity_probability k M b hb α L ν a hα hL hba hν ha
  refine ⟨p₀,hp₀,C,hC,?_⟩
  intro T V _ _ loc s u v P rates hrates t p hp hpp htest x R
  apply hr (T → Bool) (layerMass s u v P rates)
    (fun c=>layerBlocked loc s (fun i=>Equiv.swap (u i) (v i)) P c t) p
    (layerMass_nonneg s u v P rates hrates) (layerMass_sum s u v P rates hrates).le hp hpp _ x R
  intro F hF
  exact layer_blocked_mass_le loc s (fun i=>Equiv.swap (u i) (v i)) P t
    (layerMass s u v P rates) (layerMass_nonneg s u v P rates hrates)
    α L p hp htest F hF

end Heisenberg.Exposure

end

noncomputable section
open scoped BigOperators Classical Fin.NatCast
namespace Heisenberg.Schedule
open Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.Serial Heisenberg.Clocks
variable {T V X : Type} [Fintype T] [Fintype V] [DecidableEq V] [PseudoMetricSpace X]

theorem indexed_cyclic_localization {m q Q : ℕ} [NeZero m] [NeZero q]
    (s : Equiv.Perm T) (e : Fin m ≃ T) (he : ∀ j,s (e j)=e (finRotate m j))
    (hQ : 0<Q) (hqQ : q≤Q) (hdiv : Q∣m)
    (loc : V → X) (choices : X → Finset (Fin q)) (next : X → Fin q → X)
    (B : ℕ) (hB : ∀ x,(choices x).card≤B)
    (a₀ b₀ : Fin q → V) (a b : T → V)
    (hab : ∀ j : Fin m,∀ hj : j.val%Q<q,a (e j)=a₀ ⟨j.val%Q,hj⟩ ∧ b (e j)=b₀ ⟨j.val%Q,hj⟩)
    (hsite : ∀ j : Fin m,q≤j.val%Q → loc (a (e j))=loc (b (e j)))
    (hstep : ∀ e v,dist (loc (Equiv.swap (a₀ e) (b₀ e) v)) (loc v)≤1)
    (hmove : ∀ e v,loc (Equiv.swap (a₀ e) (b₀ e) v)≠loc v →
      e∈choices (loc v) ∧ loc (Equiv.swap (a₀ e) (b₀ e) v)=next (loc v) e)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ)
    (hp : ∀ j,0≤p j ∧ p j≤1) (δ : ℝ) (hδ : 0≤δ)
    (hrate : ∀ j : Fin m,j.val%Q<q → 2*p (e j)≤δ)
    (t : Fin m) (n u R : ℕ) (hn : n ≤ m) (hu : n ≤ u * Q)
    (v : V) (hv : ∀ base,v∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (e t)∩I) :
    (∑ base,layerMass s a b P p base *
      (∑ j,if (R:ℝ)<dist (loc j) (loc v) then
        prefixMatrix (fun l=>exposedStep s a b base P I p (e (run t l))) n j v else 0)) ≤
      ((u+1+R).choose R:ℝ)*(2*(B:ℝ)*δ)^R := by
  let edge : ℕ → Fin q := fun j=>⟨(run t j).val%Q%q,Nat.mod_lt _ (NeZero.pos q)⟩
  let time : ℕ → Fin (u+1) := fun j=>⟨min (round t Q j) u,by omega⟩
  let index : Fin (u+1) → Fin q → Bool → T⊕T := fun g edge c=>
    if c then Sum.inl (e (clock t Q g edge)) else Sum.inr (e (clock t Q g edge))
  have htime : Monotone time := by
    intro i j hij
    exact min_le_min_right u (round_mono t hij)
  have hother (j : Fin m) (hj : q≤j.val%Q) (v : V) :
      loc (Equiv.swap (a (e j)) (b (e j)) v)=loc v := by
    by_cases ha : v=a (e j)
    · subst v; simpa using (hsite j hj).symm
    by_cases hb : v=b (e j)
    · subst v; simpa using hsite j hj
    rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  have hsp (j : ℕ) (hj : (run t j).val%Q<q) :
      a (e (run t j))=a₀ (edge j) ∧ b (e (run t j))=b₀ (edge j) := by
    simpa only [edge,Nat.mod_eq_of_lt hj] using hab (run t j) hj
  have hir : Set.InjOn (fun j=>e (run t j)) (Set.Iio n) := by
    intro i hi j hj h
    exact run_inj t hn hi hj (e.injective h)
  apply exposedPrefix_localization choices next B hB loc s a b P I p hp
    (fun j=>e (run t j)) n (u+1) R
    (fun j _=>by rw [run_succ,←he]) hir edge time index htime
  · intro j _ w
    by_cases hj : (run t j).val%Q<q
    · rw [(hsp j hj).1,(hsp j hj).2]
      exact hstep _ w
    · rw [hother _ (Nat.le_of_not_gt hj) w]
      simp
  · intro j _ w hw
    have hj : (run t j).val%Q<q := by
      by_contra h
      exact hw (hother _ (Nat.le_of_not_gt h) w)
    rw [(hsp j hj).1,(hsp j hj).2] at hw ⊢
    exact hmove _ w hw
  · intro j hj w hw c
    have hphase : (run t j).val%Q<q := by
      by_contra h
      exact hw (hother _ (Nat.le_of_not_gt h) w)
    have ht : (time j).val=round t Q j := by
      exact min_eq_left (Nat.le_of_lt_succ (round_lt t hQ (le_trans (Nat.le_of_lt hj) hu)))
    have he : (edge j).val=(run t j).val%Q := Nat.mod_eq_of_lt hphase
    simp only [index,ht,he,clock_run_phase t hdiv]
  · exact hδ
  · intro g edge c
    have hc : (clock t Q g edge).val%Q<q := by
      rw [clock_mod t hdiv,Nat.mod_eq_of_lt (lt_of_lt_of_le edge.isLt hqQ)]
      exact edge.isLt
    have hh := hrate (clock t Q g edge) hc
    cases c <;> simp only [index,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inr,Sum.elim_inl,Heisenberg.Bernoulli.doubleRates,one_mul]
    · linarith [(hp (e (clock t Q g edge))).1]
    · exact hh
  · simpa only [run_zero] using hv

end Heisenberg.Schedule

end

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Cycle
open Equiv
variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma missingSet_inv (π : Perm V) (P : Set V) : MissingSet π⁻¹ P=MissingSet π P := by
  ext i
  simp only [MissingSet,Set.mem_ofPred_eq,ne_eq,classOf_eq_iff,Perm.sameCycle_inv]

omit [Fintype V] in
lemma colorSpace_inv (π : Perm V) (P : Set V) : colorSpace π⁻¹ P=colorSpace π P := by
  ext f
  simp only [colorSpace_mem]
  constructor
  · rintro ⟨h,hP⟩
    exact ⟨fun i=>(by simpa using (h (π i)).symm),hP⟩
  · rintro ⟨h,hP⟩
    exact ⟨fun i=>(by simpa using (h (π⁻¹ i)).symm),hP⟩

lemma missingCount_inv (π : Perm V) (P : Set V) : missingCount π⁻¹ P=missingCount π P := by
  have h : 2^missingCount π⁻¹ P=2^missingCount π P := by
    rw [←card_colorSpace,←card_colorSpace,colorSpace_inv]
  exact (Nat.pow_right_injective (by decide : 1<2)) h
end Heisenberg.Cycle

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.Bernoulli Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] [Fintype V] in
lemma layerHistory_reverse (s : Equiv.Perm T) (a b : T → V) (base : T → Bool) :
    layerHistory s.symm (fun j=>Equiv.swap (a (s.symm j)) (b (s.symm j))) (base ∘ s.symm)=
      (layerHistory s (fun j=>Equiv.swap (a j) (b j)) base)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  apply Equiv.ext
  rintro ⟨t,v⟩
  simp only [Equiv.Perm.mul_apply,layerHistory,wiring_apply,Function.comp_apply,
    Equiv.symm_apply_apply,Equiv.Perm.one_apply]
  cases base t <;> simp

omit [Fintype T] [Fintype V] in
lemma holeCut_reverse (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (t : T) :
    holeCut s.symm (fun j=>Equiv.swap (a (s.symm j)) (b (s.symm j))) (base ∘ s.symm) P t=
      holeCut s (fun j=>Equiv.swap (a j) (b j)) base P t := by
  simp only [holeCut,layerHistory_reverse,missingSet_inv]

omit [DecidableEq V] in
lemma layerWeight_reverse (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) :
    layerWeight s.symm (a ∘ s.symm) (b ∘ s.symm) P (base ∘ s.symm)=layerWeight s a b P base := by
  simp only [layerWeight,Function.comp_apply,layerHistory_reverse,missingCount_inv]

omit [Fintype V] [DecidableEq V] in
lemma coin_reverse (s : Equiv.Perm T) (p : T → ℝ) (base : T → Bool) :
    weight (p ∘ s.symm) (base ∘ s.symm)=weight p base := by
  unfold weight
  exact s.symm.prod_comp (fun i=>if base i then p i else 1-p i)

omit [DecidableEq V] in
lemma layerPartition_reverse (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V)) (p : T → ℝ) :
    layerPartition s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm)=layerPartition s a b P p := by
  unfold layerPartition
  let e : (T → Bool) ≃ (T → Bool) := Equiv.arrowCongr s (Equiv.refl Bool)
  conv_lhs => rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  change weight (p ∘ s.symm) (c ∘ s.symm)*layerWeight s.symm (a ∘ s.symm) (b ∘ s.symm) P (c ∘ s.symm)=_
  rw [coin_reverse,layerWeight_reverse]

omit [DecidableEq V] in
lemma layerMass_reverse (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V)) (p : T → ℝ)
    (base : T → Bool) :
    layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm) (base ∘ s.symm)=layerMass s a b P p base := by
  rw [layerMass,layerMass,coin_reverse,layerWeight_reverse,layerPartition_reverse]

omit [Fintype T] [Fintype V] in
lemma revealed_reverse (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (t : T) :
    layerRevealed (fun j=>Equiv.swap (a (s.symm j)) (b (s.symm j)))
      (MissingSet (layerHistory s.symm (fun j=>Equiv.swap (a (s.symm j)) (b (s.symm j))) (base ∘ s.symm)) P) t ↔
    layerRevealed (fun j=>Equiv.swap (a j) (b j))
      (MissingSet (layerHistory s (fun j=>Equiv.swap (a j) (b j)) base) P) (s.symm t) := by
  rw [layerHistory_reverse,missingSet_inv]
  by_cases hab : a (s.symm t)=b (s.symm t)
  · simp [layerRevealed,hab]
  rw [layerRevealed_swap (fun j=>a (s.symm j)) (fun j=>b (s.symm j)) _ t hab,
    layerRevealed_swap a b _ (s.symm t) hab]
  have h₁ := missing_apply (layerHistory s (fun j=>Equiv.swap (a j) (b j)) base) P (s.symm t,a (s.symm t))
  have h₂ := missing_apply (layerHistory s (fun j=>Equiv.swap (a j) (b j)) base) P (s.symm t,b (s.symm t))
  simp only [layerHistory,wiring_apply,Equiv.apply_symm_apply] at h₁ h₂
  cases h : base (s.symm t) <;> simp [h] at h₁ h₂
  · exact or_congr h₁ h₂
  · exact (or_congr h₂ h₁).trans or_comm

omit [Fintype T] [Fintype V] in
lemma exposedStep_reverse (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (t : T) :
    exposedStep s.symm (a ∘ s.symm) (b ∘ s.symm) (base ∘ s.symm) P I (p ∘ s.symm) t=
      (exposedStep s a b base P I p (s.symm t)).transpose := by
  simp only [exposedStep,Function.comp_apply,holeCut_reverse]
  rw [revealed_reverse,residualBetween_transpose]
  simp

end Heisenberg.Exposure
end
end

end OAI
