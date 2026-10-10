import OAI.MathematicalPhysics.Heisenberg.CutContractions

namespace OAI

section
noncomputable section
open scoped Classical Fin.NatCast

noncomputable section
open scoped BigOperators Classical
namespace Heisenberg.Serial
open Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks
variable {V T X E : Type} [Fintype V] [DecidableEq V] [Fintype T]
  [PseudoMetricSpace X] [Fintype E]

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma product_snoc (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ) :
    product (n+1) K=K (Fin.last n)*product n (fun i=>K i.castSucc) := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [product,ih,product,Matrix.mul_assoc]
    rfl

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma prefix_product (K : ℕ → Matrix V V ℝ) (n : ℕ) :
    prefixMatrix K n=product n (fun i=>K i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixMatrix,product_snoc]
    simpa only [Fin.val_last,Fin.val_castSucc] using congrArg (K n * ·) ih

omit [Fintype V] [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma residualBetween_coin (D F : Set V) (M : Prop) (base : Bool) (a b : V) (p : ℝ) :
    (∑ z : Bool,(if z then p else 1-p) •
      killedBetween D F (if (if M then base else z) then Equiv.swap a b else 1))=
      residualBetween D F M base a b p := by
  by_cases hM : M
  · simp only [hM,ite_true,residualBetween]
    rw [←Finset.sum_smul]
    simp
  · simp [hM,residualBetween,add_comm]

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma mul_projection_column (A : Matrix V V ℝ) (D : Set V) {j : V} (hj : j∈D) (v : V) :
    (A*projection D) v j=A v j := by
  simp only [Matrix.mul_apply,projection,killedBetween,Equiv.Perm.one_apply]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro k _ hk
    simp [hk]
  · simp

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma sampledPrefix_exposed (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V))
    (I : Set V) (p : T → ℝ) (r : ℕ → T) (n : ℕ)
    (hr : ∀ j,j<n → r (j+1)=s (r j)) (base : T → Bool) :
    sampledPrefix (fun j=>Equiv.swap (a (r j)) (b (r j))) p r
      (fun base=>layerRevealed (fun i=>Equiv.swap (a i) (b i))
        (Heisenberg.Cycle.MissingSet (layerHistory s (fun i=>Equiv.swap (a i) (b i)) base) P)) n
      (fun base j=>holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r j)∩I) base=
    prefixMatrix (fun j=>exposedStep s a b base P I p (r j)) n *
      projection (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I) := by
  rw [sampledPrefix,prefix_product]
  congr 1
  congr 1
  funext j
  rw [residualBetween_coin]
  simp only [exposedStep,Fin.val_castSucc,Fin.val_succ,hr j j.isLt]

theorem exposedPrefix_localization
    (choices : X → Finset E) (next : X → E → X) (B : ℕ) (hB : ∀ x,(choices x).card≤B)
    (loc : V → X) (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V))
    (I : Set V) (p : T → ℝ) (hp : ∀ j,0≤p j ∧ p j≤1)
    (r : ℕ → T) (n N R : ℕ) (hr : ∀ j,j<n → r (j+1)=s (r j))
    (hir : Set.InjOn r (Set.Iio n))
    (edge : ℕ → E) (time : ℕ → Fin N) (index : Fin N → E → Bool → T⊕T)
    (htime : Monotone time)
    (hstep : ∀ j,j<n → ∀ v,dist (loc (Equiv.swap (a (r j)) (b (r j)) v)) (loc v)≤1)
    (hmove : ∀ j,j<n → ∀ v,loc (Equiv.swap (a (r j)) (b (r j)) v)≠loc v →
      edge j∈choices (loc v) ∧ loc (Equiv.swap (a (r j)) (b (r j)) v)=next (loc v) (edge j))
    (hindex : ∀ j,j<n → ∀ v,loc (Equiv.swap (a (r j)) (b (r j)) v)≠loc v → ∀ c,
      index (time j) (edge j) c=(if c then Sum.inl (r j) else Sum.inr (r j)))
    {δ : ℝ} (hδ : 0≤δ)
    (hrate : ∀ t e c,(Sum.elim (fun _=>(2:ℝ)) (fun _=>(1:ℝ)) (index t e c))*
      doubleRates p (index t e c)≤δ)
    (v : V) (hv : ∀ base,v∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I) :
    (∑ base,layerMass s a b P p base *
      (∑ j,if (R:ℝ)<dist (loc j) (loc v) then
        prefixMatrix (fun l=>exposedStep s a b base P I p (r l)) n j v else 0)) ≤
      ((N+R).choose R:ℝ)*(2*(B:ℝ)*δ)^R := by
  let τ := fun j=>Equiv.swap (a j) (b j)
  let M := fun base=>layerRevealed τ (Heisenberg.Cycle.MissingSet (layerHistory s τ base) P)
  let D := fun base (j : Fin (n+1))=>holeCut s τ base P (r j)∩I
  have h := sampledPrefix_localization choices next B hB (fun j=>τ (r j)) loc v r n N R hir
    edge time index htime hstep hmove hindex M p hp (κ:=2) (by norm_num) hδ
    (layerWeight s a b P) (layerWeight_nonneg s a b P) (layerWeight_insertion s a b P)
    D hrate
  have he (base : T → Bool) (j : V) :
      sampledPrefix (fun j=>τ (r j)) p r M n D base j v=
        prefixMatrix (fun l=>exposedStep s a b base P I p (r l)) n j v := by
    rw [sampledPrefix_exposed s a b P I p r n hr base]
    exact mul_projection_column _ _ (hv base) j
  simp only [he] at h
  have hz : 0<layerPartition s a b P p := lt_of_lt_of_le zero_lt_one (layerPartition_one_le s a b P p hp)
  simp only [layerMass,div_mul_eq_mul_div,←Finset.sum_div]
  apply (div_le_iff₀ hz).mpr
  exact h

end Heisenberg.Serial

noncomputable section
open scoped BigOperators Classical Fin.NatCast
namespace Heisenberg.Schedule
open Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.Serial Heisenberg.Clocks
variable {V X : Type} [Fintype V] [DecidableEq V] [PseudoMetricSpace X]

theorem cyclic_localization {m q Q : ℕ} [NeZero m] [NeZero q]
    (hQ : 0<Q) (hqQ : q≤Q) (hdiv : Q∣m)
    (loc : V → X) (choices : X → Finset (Fin q)) (next : X → Fin q → X)
    (B : ℕ) (hB : ∀ x,(choices x).card≤B)
    (a₀ b₀ : Fin q → V) (a b : Fin m → V)
    (hab : ∀ j : Fin m,∀ hj : j.val%Q<q,a j=a₀ ⟨j.val%Q,hj⟩ ∧ b j=b₀ ⟨j.val%Q,hj⟩)
    (hsite : ∀ j : Fin m,q≤j.val%Q → loc (a j)=loc (b j))
    (hstep : ∀ e v,dist (loc (Equiv.swap (a₀ e) (b₀ e) v)) (loc v)≤1)
    (hmove : ∀ e v,loc (Equiv.swap (a₀ e) (b₀ e) v)≠loc v →
      e∈choices (loc v) ∧ loc (Equiv.swap (a₀ e) (b₀ e) v)=next (loc v) e)
    (P : Set (Fin m×V)) (I : Set V) (p : Fin m → ℝ)
    (hp : ∀ j,0≤p j ∧ p j≤1) (δ : ℝ) (hδ : 0≤δ)
    (hrate : ∀ j : Fin m,j.val%Q<q → 2*p j≤δ)
    (t : Fin m) (n u R : ℕ) (hn : n ≤ m) (hu : n ≤ u * Q)
    (v : V) (hv : ∀ base,v∈holeCut (finRotate m) (fun i=>Equiv.swap (a i) (b i)) base P t∩I) :
    (∑ base,layerMass (finRotate m) a b P p base *
      (∑ j,if (R:ℝ)<dist (loc j) (loc v) then
        prefixMatrix (fun l=>exposedStep (finRotate m) a b base P I p (run t l)) n j v else 0)) ≤
      ((u+1+R).choose R:ℝ)*(2*(B:ℝ)*δ)^R := by
  let edge : ℕ → Fin q := fun j=>⟨(run t j).val%Q%q,Nat.mod_lt _ (NeZero.pos q)⟩
  let time : ℕ → Fin (u+1) := fun j=>⟨min (round t Q j) u,by omega⟩
  let index : Fin (u+1) → Fin q → Bool → Fin m⊕Fin m := fun g e c=>
    if c then Sum.inl (clock t Q g e) else Sum.inr (clock t Q g e)
  have htime : Monotone time := by
    intro i j hij
    exact min_le_min_right u (round_mono t hij)
  have hother (j : Fin m) (hj : q≤j.val%Q) (v : V) :
      loc (Equiv.swap (a j) (b j) v)=loc v := by
    by_cases ha : v=a j
    · subst v; simpa using (hsite j hj).symm
    by_cases hb : v=b j
    · subst v; simpa using hsite j hj
    rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  have hsp (j : ℕ) (hj : (run t j).val%Q<q) :
      a (run t j)=a₀ (edge j) ∧ b (run t j)=b₀ (edge j) := by
    simpa only [edge,Nat.mod_eq_of_lt hj] using hab (run t j) hj
  convert (exposedPrefix_localization choices next B hB loc (finRotate m) a b P I p hp
    (run t) n (u+1) R (fun j _=>run_succ t j) (run_inj t hn) edge time index htime
    ?_ ?_ ?_ hδ ?_ v ?_) using 1
  · congr 1
    ext x
    simp
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
  · intro g e c
    have hc : (clock t Q g e).val%Q<q := by
      rw [clock_mod t hdiv,Nat.mod_eq_of_lt (lt_of_lt_of_le e.isLt hqQ)]
      exact e.isLt
    have hh := hrate (clock t Q g e) hc
    cases c <;> simp only [index,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inr,Sum.elim_inl,Heisenberg.Bernoulli.doubleRates,one_mul]
    · linarith [(hp (clock t Q g e)).1]
    · exact hh
  · simpa only [run_zero] using hv

end Heisenberg.Schedule

end
end
end

noncomputable section
open scoped BigOperators Classical
namespace Heisenberg.SpatialFrame
open Heisenberg.Geometry
variable {d : ℕ} {B : Type} [Fintype B]

def neighbors (x : Site d) : Finset (Site d) :=
  Finset.univ.image fun j : Fin d × Bool=>Function.update x j.1 (x j.1+if j.2 then 1 else -1)

lemma step_mem_neighbors {x y : Site d} (h : Step x y) : y∈neighbors x := by
  obtain ⟨j,h,hj⟩:=h
  rcases h with h|h
  · refine Finset.mem_image.mpr ⟨(j,true),Finset.mem_univ _,?_⟩
    funext k
    by_cases hk : k=j
    · subst k; simp [h]
    · simp [hk,←hj k hk]
  · refine Finset.mem_image.mpr ⟨(j,false),Finset.mem_univ _,?_⟩
    funext k
    by_cases hk : k=j
    · subst k; simp; omega
    · simp [hk,←hj k hk]

lemma neighbors_card (x : Site d) : (neighbors x).card≤2*d := by
  exact (Finset.card_image_le).trans (by simp [mul_comm])

def choices (Λ : Finset (Site d)) (x : Site d) : Finset (Edges (B:=B) Step Λ) :=
  Finset.univ.filter fun e=>e.val.1.1.val=x ∨ e.val.2.1.val=x

lemma choices_card (Λ : Finset (Site d)) (x : Site d) :
    (choices (B:=B) Λ x).card≤4*d*(Fintype.card B)^2 := by
  let C := ((neighbors x).image (fun y=>(x,y)))∪((neighbors x).image (fun y=>(y,x)))
  let code : Edges (B:=B) Step Λ → (Site d × Site d) × (B×B) :=
    fun e=>((e.val.1.1.val,e.val.2.1.val),(e.val.1.2,e.val.2.2))
  have hm : Set.MapsTo code (↑(choices (B:=B) Λ x) : Set (Edges (B:=B) Step Λ)) (↑(C ×ˢ (Finset.univ : Finset (B×B))) : Set ((Site d × Site d) × (B×B))) := by
    intro e he
    apply Finset.mem_product.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    rcases (Finset.mem_filter.mp he).2 with h|h
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨e.val.2.1.val,?_,?_⟩
      · exact step_mem_neighbors (h ▸ e.property)
      · exact Prod.ext h.symm rfl
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨e.val.1.1.val,?_,?_⟩
      · exact step_mem_neighbors (h ▸ step_symm e.property)
      · exact Prod.ext rfl h.symm
  have hi : Function.Injective code := by
    intro e f h
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun z : (Site d × Site d) × (B×B)=>z.1.1) h)
      · exact congrArg (fun z : (Site d × Site d) × (B×B)=>z.2.1) h
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun z : (Site d × Site d) × (B×B)=>z.1.2) h)
      · exact congrArg (fun z : (Site d × Site d) × (B×B)=>z.2.2) h
  have hC : C.card≤4*d := by
    exact (Finset.card_union_le _ _).trans ((add_le_add
      (Finset.card_image_le.trans (neighbors_card x))
      (Finset.card_image_le.trans (neighbors_card x))).trans (by omega))
  calc
    _ ≤ (C ×ˢ (Finset.univ : Finset (B×B))).card := Finset.card_le_card_of_injOn code hm hi.injOn
    _ = C.card*(Fintype.card B)^2 := by simp [pow_two]
    _ ≤ _ := Nat.mul_le_mul_right _ hC

def next (x : Site d) {Λ : Finset (Site d)} (e : Edges (B:=B) Step Λ) : Site d :=
  if x=e.val.1.1.val then e.val.2.1.val else e.val.1.1.val

omit [Fintype B] in
lemma edge_site_ne {Λ : Finset (Site d)} (e : Edges (B:=B) Step Λ) :
    e.val.1.1.val≠e.val.2.1.val := by
  intro h
  obtain ⟨j,hj,_⟩:=e.property
  rw [h] at hj
  omega

omit [Fintype B] in
lemma swap_step {Λ : Finset (Site d)} (e : Edges (B:=B) Step Λ) (v : Slots (B:=B) Λ) :
    dist (Equiv.swap e.val.1 e.val.2 v).1.val v.1.val≤1 := by
  by_cases h₁ : v=e.val.1
  · subst v
    rw [Equiv.swap_apply_left,dist_comm]
    exact step_dist_le_one e.property
  by_cases h₂ : v=e.val.2
  · subst v
    rw [Equiv.swap_apply_right]
    exact step_dist_le_one e.property
  rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  simp

lemma swap_move {Λ : Finset (Site d)} (e : Edges (B:=B) Step Λ) (v : Slots (B:=B) Λ)
    (h : (Equiv.swap e.val.1 e.val.2 v).1.val≠v.1.val) :
    e∈choices Λ v.1.val ∧ (Equiv.swap e.val.1 e.val.2 v).1.val=next v.1.val e := by
  by_cases h₁ : v=e.val.1
  · subst v; simp [choices,next]
  by_cases h₂ : v=e.val.2
  · subst v; simp [choices,next,(edge_site_ne e).symm]
  rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂] at h
  exact False.elim (h rfl)

omit [Fintype B] in
lemma same_site_swap {Λ : Finset (Site d)} (a b v : Slots (B:=B) Λ)
    (h : a.1.val=b.1.val) : (Equiv.swap a b v).1.val=v.1.val := by
  by_cases ha : v=a
  · subst v; simpa using h.symm
  by_cases hb : v=b
  · subst v; simpa using h
  rw [Equiv.swap_apply_of_ne_of_ne ha hb]

end Heisenberg.SpatialFrame
end
end

end OAI
