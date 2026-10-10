import OAI.MathematicalPhysics.Heisenberg.ReversedExposure

namespace OAI

section
noncomputable section
open scoped Classical BigOperators

end

noncomputable section
lemma swap_classical {α : Type*} [h : DecidableEq α] (a b : α) :
    Equiv.swap a b = @Equiv.swap α (Classical.decEq α) a b := by
  have he : h=Classical.decEq α := Subsingleton.elim _ _
  cases he
  rfl
lemma exposedSweep_classical {T V : Type*} [fv : Fintype V]
    [h : DecidableEq V] :
    @Heisenberg.Exposure.exposedSweep T V fv h =
      @Heisenberg.Exposure.exposedSweep T V fv (Classical.decEq V) := by
  have he : h=Classical.decEq V := Subsingleton.elim _ _
  cases he
  rfl

end

noncomputable section
open scoped Classical BigOperators Fin.NatCast
namespace Heisenberg.SpatialFrame
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.MeshPair Heisenberg.Exposure
variable {d : ℕ} {B T : Type} [Fintype B] [Fintype T]

theorem frame_indexed_localization {m q Q : ℕ} [NeZero m] [NeZero q]
    (s : Equiv.Perm T) (ι : Fin m ≃ T) (hι : ∀ j,s (ι j)=ι (finRotate m j))
    (hQ : 0 < Q) (hqQ : q ≤ Q) (hdiv : Q∣m) (Λ : Finset (Site d))
    (e : Fin q ≃ Edges (B:=B) Step Λ) (a₀ b₀ : Fin q → Slots (B:=B) Λ)
    (ha₀ : ∀ j,a₀ j=(e j).val.1) (hb₀ : ∀ j,b₀ j=(e j).val.2)
    (a b : T → Slots (B:=B) Λ)
    (hab : ∀ j : Fin m,∀ hj : j.val%Q < q,a (ι j)=a₀ ⟨j.val%Q,hj⟩ ∧ b (ι j)=b₀ ⟨j.val%Q,hj⟩)
    (hsite : ∀ j : Fin m,q ≤ j.val%Q → (a (ι j)).1.val=(b (ι j)).1.val)
    (P : Set (T×Slots (B:=B) Λ)) (I : Set (Slots (B:=B) Λ)) (p : T → ℝ)
    (hp : ∀ j,0 ≤ p j ∧ p j ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrate : ∀ j : Fin m,j.val%Q < q → 2*p (ι j) ≤ δ)
    (t : Fin m) (n u R : ℕ) (hn : n ≤ m) (hu : n ≤ u * Q)
    (v : Slots (B:=B) Λ)
    (hv : ∀ base,v∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (ι t)∩I) :
    (∑ base,layerMass s a b P p base *
      (∑ j,if (R:ℝ) < dist j.1.val v.1.val then
        prefixMatrix (fun l=>exposedStep s a b base P I p (ι (run t l))) n j v else 0)) ≤
      ((u+1+R).choose R:ℝ)*(2*(4*d*(Fintype.card B)^2:ℕ)*δ)^R := by
  let C : Site d → Finset (Fin q) := fun x=>(choices (B:=B) Λ x).map e.symm.toEmbedding
  have hC : ∀ x,(C x).card ≤ 4*d*(Fintype.card B)^2 := by
    intro x
    simpa only [C,Finset.card_map] using choices_card (B:=B) Λ x
  apply indexed_cyclic_localization s ι hι hQ hqQ hdiv (fun v : Slots (B:=B) Λ=>v.1.val) C
    (fun x j=>next x (e j)) _ hC a₀ b₀ a b hab hsite
    (fun j v=>by rw [ha₀,hb₀]; exact swap_step _ _) ?_ P I p hp δ hδ hrate t n u R hn hu v hv
  intro j v h
  rw [ha₀,hb₀] at h ⊢
  obtain ⟨hc,he⟩:=swap_move (e j) v h
  refine ⟨?_,he⟩
  exact Finset.mem_map.mpr ⟨e j,hc,e.symm_apply_apply j⟩

end Heisenberg.SpatialFrame

noncomputable section
open scoped Classical BigOperators Fin.NatCast RealInnerProductSpace
open Filter Topology
namespace Heisenberg.Flow
@[reducible] local instance periodicDecEq (α : Type*) : DecidableEq α := Classical.decEq α
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.LatticeRegular
variable {d : ℕ}

theorem indexed_prefix_leakage (hd : 2 ≤ d) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ,∃ C ≥ 0,∀ (B : Type) [Fintype B] [Nonempty B]
      (Λ F : Finset (Site (d+1))) (q : ℕ) [NeZero q]
      (edge : Fin q ≃ Edges (B:=B) Step Λ)
      (a₀ b₀ : ℕ → Slots (B:=B) Λ)
      (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
      (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2)
      (ε : ℝ),0 < ε →
      ∀ᶠ δ in 𝓝 (0:ℝ),0 < δ → δ ≤ 2 →
      ∀ (T : Type) [Fintype T] (m Q : ℕ) [NeZero m]
        (s : Equiv.Perm T) (ι : Fin m ≃ T)
        (_hι : ∀ j,s (ι j)=ι (finRotate m j))
        (_hQ : 0 < Q) (_hqQ : q ≤ Q) (_hdiv : Q∣m)
        (a b : T → Slots (B:=B) Λ)
        (_hab : ∀ j : Fin m,∀ _hj : j.val%Q < q,
          a (ι j)=a₀ (j.val%Q) ∧ b (ι j)=b₀ (j.val%Q))
        (_hsite : ∀ j : Fin m,q ≤ j.val%Q → (a (ι j)).1.val=(b (ι j)).1.val)
        (p : T → ℝ) (_hp : ∀ i,0 ≤ p i ∧ p i ≤ 1)
        (_hrate : ∀ j : Fin m,j.val%Q < q → p (ι j)=δ/2)
        (P : Set (T×Slots (B:=B) Λ)) (t : Fin m)
        (J : Finset (Slots (B:=B) Λ))
        (f : (T → Bool) → EuclideanSpace ℝ (Slots (B:=B) Λ))
        (n R : ℕ) (ρ : ℝ),
        0 < n → Heisenberg.Schedule.cut t Q n ≤ m →
        F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
        (∀ base j,j∈J → j∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (ι t) ∧ j.1.val∈F) →
        (∀ base j,j∈J → (f base).ofLp j=1) →
        (∀ base j,0 ≤ (f base).ofLp j ∧ (f base).ofLp j ≤ 1) →
        (∀ base j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (ι t)∩{j | j.1.val∈F} → (f base).ofLp j=0) →
        (∀ z u,0 ≤ u → ((Finset.univ.filter (fun j : J=>dist j.val.1.val z ≤ u)).card:ℝ) ≤ L*(1+u)^((1:ℝ)/100)) →
        (∀ (i : Fin n) (j : J), (∑ base,Exposure.layerMass s a b P p base *
          (if ¬Regular (blocked Λ (holeCut s (fun l=>Equiv.swap (a l) (b l)) base P (ι (run t (Heisenberg.Schedule.cut t Q i)))))
            j.val.1.val R M (1/(100*(d+1:ℝ))) then (1:ℝ) else 0)) ≤ ρ) →
        (J.card:ℝ)-2*((ρ+((n+2+R).choose R:ℝ)*(2*(4*(d+1)*(Fintype.card B)^2:ℕ)*δ)^R)*J.card)-
          2*(C*(1+(R:ℝ))^((1:ℝ)/100)*J.card)/((δ/2)*(n:ℝ))-
          (n:ℝ)*(ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2) ≤
        ∑ base,Exposure.layerMass s a b P p base *
          (‖f base‖^2-‖exposedSweep s a b base P {v | v.1.val∈F} p (fun l=>ι (run t l)) (Heisenberg.Schedule.cut t Q n) (f base)‖^2) := by
  obtain ⟨M,C,hC,hflow⟩:=exposed_prefix_leakage hd L hL
  refine ⟨M,C,hC,?_⟩
  intro B _ _ Λ F q _ edge a₀ b₀ ha₀ hb₀ ε hε
  have hab₀ : ∀ j,j < q → a₀ j≠b₀ j := by
    intro j hj he
    apply edge_site_ne (edge ⟨j,hj⟩)
    have he' : (edge ⟨j,hj⟩).val.1=(edge ⟨j,hj⟩).val.2 :=
      (ha₀ ⟨j,hj⟩).symm.trans (he.trans (hb₀ ⟨j,hj⟩))
    exact congrArg (fun z : Slots (B:=B) Λ=>z.1.val) he'
  filter_upwards [round_energy a₀ b₀ q hab₀ hε] with δ hδE
  intro hδ hδ2 T _ m Q _ s ι hι hQ hqQ hdiv a b hab hsite p hp hrate P t J f n R ρ hn hhor hF hframe hJ hfJ hf hs hg hbad
  let r : ℕ → T := fun l=>ι (run t l)
  let c : ℕ → ℕ := Heisenberg.Schedule.cut t Q
  have hr : ∀ j,r (j+1)=s (r j) := by intro j; simp only [r,run_succ,←hι]
  have hc (i : ℕ) : c i+q ≤ c (i+1) := by
    dsimp only [c]
    rw [cut_step]
    omega
  have hmod (i j : ℕ) (hj : j < q) : (run t (c i+j)).val%Q=j := by
    rw [cut_mod t hQ hdiv,Nat.mod_eq_of_lt (lt_of_lt_of_le hj hqQ)]
  have ha : ∀ i j,j < q → a (r (c i+j))=a₀ j := by
    intro i j hj
    have h:= hab (run t (c i+j)) (by rw [hmod i j hj]; exact hj)
    simpa only [hmod i j hj] using h.1
  have hb : ∀ i j,j < q → b (r (c i+j))=b₀ j := by
    intro i j hj
    have h:= hab (run t (c i+j)) (by rw [hmod i j hj]; exact hj)
    simpa only [hmod i j hj] using h.2
  have hrate' : ∀ i j,j < q → p (r (c i+j))=δ/2 := by
    intro i j hj
    exact hrate _ (by rw [hmod i j hj]; exact hj)
  have hrem : 0 ≤ ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2 := by positivity
  apply hflow T B Λ F s a b p hp P r c J f a₀ b₀ q n R edge (δ/2) ρ
    (((n+2+R).choose R:ℝ)*(2*(4*(d+1)*(Fintype.card B)^2:ℕ)*δ)^R)
    (ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2) hn (by positivity) hrem hr ha₀ hb₀ hF hframe
    (by simpa only [r,run_zero] using hJ) hfJ hf (by simpa only [r,run_zero] using hs) hg hbad
  · intro i j
    have hcn : c i ≤ c n := by
      dsimp only [c,cut]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt.le) _
    have hcu : c i ≤ (n+1)*Q := by
      have hw := warm_le (Q:=Q) t
      dsimp only [c,cut]
      nlinarith [i.isLt]
    convert frame_indexed_localization s ι hι hQ hqQ hdiv Λ edge
      (fun j : Fin q=>a₀ j) (fun j : Fin q=>b₀ j) ha₀ hb₀ a b hab hsite
      P {v | v.1.val∈F} p hp δ hδ.le (fun j hj=>by rw [hrate j hj]; ring_nf; exact le_refl δ)
      t (c i) (n+1) R (hcn.trans hhor) hcu j.val (fun base=>hJ base j.val j.property) using 1
  · intro i
    have h:=hδE hδ.le hδ2 T s a b r c hr hc ha hb p hp hrate' P {v | v.1.val∈F} f hf
      (by simpa only [r,run_zero,swap_classical] using hs) i
    simpa only [swap_classical,exposedSweep_classical,show 2*(δ/2)=δ by ring,add_assoc] using h

end Heisenberg.Flow

end
end

noncomputable section
end

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Matrix
namespace Heisenberg.Schedule
variable {m : ℕ} [NeZero m]
@[simp] lemma run_period (t : Fin m) : run t m=t := by simp [run]
lemma run_ne_start (t : Fin m) {j : ℕ} (hj : 0 < j) (hjm : j < m) : run t j≠t := by
  intro h
  have hh:=run_inj t (le_refl m) hjm (NeZero.pos m) (h.trans (run_zero t).symm)
  omega
end Heisenberg.Schedule
namespace Heisenberg.Serial
open Heisenberg.Schedule Heisenberg.Hitting
variable {V : Type} [Fintype V] [DecidableEq V]

lemma cyclic_backward_return_at (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ)
    (t : Fin (n+1)) (f : Fin (n+1) → V → ℝ)
    (hf : ∀ u,u≠t → (K u).transpose*ᵥ f (finRotate (n+1) u)=f u) :
    (product (n+1) (fun i=>K (run t i))).transpose*ᵥ f t=
      (K t).transpose*ᵥ f (finRotate (n+1) t) := by
  have hh := backward_profile n (fun i=>K (run t (i.val+1)))
    (fun i=>f (run t (i.val+1))) (by
      intro i
      simpa only [Fin.val_castSucc,Fin.val_succ,run_succ] using
        hf (run t (i.val+1)) (run_ne_start t (by omega) (by omega)))
  simp only [Fin.val_last,run_period,Fin.val_zero,Nat.zero_add,run_succ,run_zero] at hh
  rw [product,Matrix.transpose_mul,←Matrix.mulVec_mulVec]
  simp only [Fin.val_zero,run_zero,Fin.val_succ]
  change (K t).transpose*ᵥ ((product n (fun i=>K (run t (i.val+1)))).transpose*ᵥ f t)=_
  simp only [run_succ]
  rw [hh]

def targetsAt (n : ℕ) (t : Fin (n+1)) (J : Finset V) : Finset (Fin (n+1)×V) :=
  J.image (fun j=>(t,j))
omit [Fintype V] in
@[simp] lemma mem_targetsAt (n : ℕ) (t u : Fin (n+1)) (J : Finset V) (j : V) :
    (u,j)∈targetsAt n t J ↔ u=t ∧ j∈J := by simp [targetsAt,and_comm,eq_comm]

theorem cyclic_hitting_energy_at (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ)
    (hK : ∀ t,DoublySubstochastic (K t)) (t : Fin (n+1)) (J : Finset V) :
    let F := hitting (cyclicKernel n K) (targetsAt n t J)
    energy (cyclicKernel n K) F =
      energy (product (n+1) (fun i=>K (run t i))) (fun v=>F (t,v)) := by
  dsimp only
  let U:=cyclicKernel n K
  let F:=hitting U (targetsAt n t J)
  have hU:=cyclicKernel_substochastic n K hK
  have hf (u : Fin (n+1)) (hu : u≠t) :
      (K u).transpose*ᵥ (fun v=>F (finRotate (n+1) u,v))=(fun v=>F (u,v)) := by
    funext v
    rw [←cyclicKernel_backward]
    exact hitting_harmonic hU _ (by simp [hu])
  have hr:=cyclic_backward_return_at n K t (fun u v=>F (u,v)) hf
  have hr' (v : V) : backward (product (n+1) (fun i=>K (run t i))) (fun v=>F (t,v)) v=
      backward U F (t,v) := by
    rw [cyclicKernel_backward]
    exact congrFun hr v
  rw [energy_transpose]
  change (∑ z,F z*(F z-backward U F z))=energy _ _
  rw [Fintype.sum_prod_type,Finset.sum_eq_single t]
  · rw [energy_transpose]
    apply Finset.sum_congr rfl
    intro v _
    rw [hr']
  · intro u _ hu
    apply Finset.sum_eq_zero
    intro v _
    have hh:=hitting_harmonic hU (targetsAt n t J) (i:=(u,v)) (by simp [hu])
    change backward U F (u,v)=F (u,v) at hh
    rw [hh,sub_self,mul_zero]
  · simp

end Heisenberg.Serial

namespace Heisenberg.Exposure
open Heisenberg.Serial Heisenberg.Schedule Heisenberg.Hitting Heisenberg.MeshPair Heisenberg.Cycle
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cut_return_energy_at (n : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) (P : Set (Fin (n+1)×V))
    (D : (Fin (n+1) → Bool) → Fin (n+1) → Set V) (t : Fin (n+1))
    (T : Finset P) (J : Finset V) (himage : T.image Subtype.val=targetsAt n t J)
    (hT : ∀ base j,j∈T → j.val.2∈D base j.val.1)
    (hQ : ∀ base,(MissingSet (layerHistory (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) base) P)ᶜ∩Pᶜ ⊆
      {z | z.2∈D base z.1}) :
    ∃ f : (Fin (n+1) → Bool) → V → ℝ,
      (∀ base j,0 ≤ f base j ∧ f base j ≤ 1) ∧
      (∀ base j,j∈J → f base j=1) ∧
      (∀ base j,j∉D base t → f base j=0) ∧
      (∑ c,layerMass (finRotate (n+1)) a b P p c *
        returnCount (layerHistory (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) c) P T) ≤ (J.card:ℝ)-
      ∑ base,layerMass (finRotate (n+1)) a b P p base *
        energy (product (n+1) (fun i=>cutFactors n a b p P D base (run t i))) (f base) := by
  let K:=cutFactors n a b p P D
  let F:=fun base=>hitting (cyclicKernel n (K base)) (targetsAt n t J)
  have hK:=cutFactors_substochastic n a b p hp P D
  have hU:=fun base=>cyclicKernel_substochastic n (K base) (hK base)
  have hTb (base : Fin (n+1) → Bool) {j : V} (hj : j∈J) : j∈D base t := by
    have ht : (t,j)∈T.image Subtype.val := by rw [himage]; simp [hj]
    obtain ⟨z,hz,he⟩:=Finset.mem_image.mp ht
    have hh:=hT base z hz
    simpa only [he] using hh
  refine ⟨fun base j=>F base (t,j),?_,?_,?_,?_⟩
  · intro base j
    exact ⟨(hitting_bounds (hU base) _).1 _,(hitting_bounds (hU base) _).2 _⟩
  · intro base j hj
    exact hitting_on (hU base) _ (by simp [hj])
  · intro base j hj
    apply hitting_zero_column (hU base) (targetsAt n t J)
    · simp only [mem_targetsAt,true_and]
      exact fun ht=>hj (hTb base ht)
    · intro z
      simp only [cyclicKernel]
      split_ifs
      · dsimp [K,cutFactors]
        simp only [residualBetween]
        split_ifs <;>  simp [killedBetween,hj,Matrix.add_apply,Matrix.smul_apply]
      · rfl
  · have hh:=averaged_layer_energy (finRotate (n+1)) a b p hp P
      (fun base=>{z | z.2∈D base z.1}) T hT hQ
    dsimp only at hh
    have hc : T.card=J.card := by
      have h:=congrArg Finset.card himage
      rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
      simpa [targetsAt,Finset.card_image_of_injective _ (fun _ _ h=>(Prod.mk.inj h).2)] using h
    rw [hc] at hh
    have hweight : ∀ base,layerMass (finRotate (n+1)) a b P p base=
        (productWeight (fun i z=>if z then p i else 1-p i) base *
          (2:ℝ)^missingCount (layerHistory (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) base) P)/
        (∑ c,productWeight (fun i z=>if z then p i else 1-p i) c *
          (2:ℝ)^missingCount (layerHistory (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) c) P) := by
      intro base
      simp only [layerMass,layerPartition,layerWeight,Heisenberg.Bernoulli.weight,productWeight,swap_classical]
      congr 1
      apply Finset.sum_congr
      · ext c; simp
      · intro c _; rfl
    simp only [hweight]
    convert hh using 2
    congr 1
    ext base
    congr 1
    rw [killed_residual_cyclic,himage]
    exact (cyclic_hitting_energy_at n (K base) (hK base) t J).symm

end Heisenberg.Exposure
end
end

end OAI
