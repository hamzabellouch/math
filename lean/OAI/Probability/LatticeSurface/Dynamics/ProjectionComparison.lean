import Mathlib

namespace OAI

noncomputable section

namespace ProjectionComparison

open Set

structure System (V E : Type*) where
  left : E → V
  right : E → V
  cost : E → ℝ
  pins : Set V

variable {V E : Type*}

def feasible (S : System V E) (b : V → ℝ) : Set (V → ℝ) :=
  {h | (∀ e,h (S.left e)-h (S.right e)≤S.cost e) ∧ ∀ x∈S.pins,h x=b x}

def objective [Fintype V] (v h : V → ℝ) : ℝ := ∑ x,(h x-v x)^2

def IsProjection [Fintype V] (S : System V E) (b v h : V → ℝ) : Prop :=
  h∈feasible S b ∧ ∀ k∈feasible S b,objective v h≤objective v k

end ProjectionComparison

namespace ProjectionComparison

open Set

variable {V E : Type*}

lemma min_feasible (S : System V E) (b c h k : V → ℝ) (δ : ℝ)
    (hh : h∈feasible S b) (hk : k∈feasible S c)
    (hb : ∀ x∈S.pins,b x≤c x+δ) :
    (fun x => min (h x) (k x+δ))∈feasible S b := by
  constructor
  · intro e
    apply sub_le_iff_le_add.mpr
    have h₁ : h (S.left e)≤h (S.right e)+S.cost e := by linarith [hh.1 e]
    have h₂ : k (S.left e)+δ≤(k (S.right e)+δ)+S.cost e := by linarith [hk.1 e]
    simpa only [min_add_add_right, add_comm (S.cost e)] using min_le_min h₁ h₂
  · intro x hx
    dsimp only
    rw [hh.2 x hx,hk.2 x hx,min_eq_left (hb x hx)]

lemma max_feasible (S : System V E) (b c h k : V → ℝ) (δ : ℝ)
    (hh : h∈feasible S b) (hk : k∈feasible S c)
    (hb : ∀ x∈S.pins,c x+δ≤b x) :
    (fun x => max (h x) (k x+δ))∈feasible S b := by
  constructor
  · intro e
    apply sub_le_iff_le_add.mpr
    have h₁ : h (S.left e)≤h (S.right e)+S.cost e := by linarith [hh.1 e]
    have h₂ : k (S.left e)+δ≤(k (S.right e)+δ)+S.cost e := by linarith [hk.1 e]
    simpa only [max_add_add_right, add_comm (S.cost e)] using max_le_max h₁ h₂
  · intro x hx
    dsimp only
    rw [hh.2 x hx,hk.2 x hx,max_eq_left (hb x hx)]

lemma interpolate_feasible (S : System V E) (b h k : V → ℝ)
    (hh : h∈feasible S b) (hk : k∈feasible S b) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    (fun x => (1-t)*h x+t*k x)∈feasible S b := by
  refine ⟨fun e => ?_,fun x hx => ?_⟩
  · have h₁ := mul_le_mul_of_nonneg_left (hh.1 e) (by linarith [ht.2] : 0≤1-t)
    have h₂ := mul_le_mul_of_nonneg_left (hk.1 e) ht.1
    nlinarith [h₁,h₂]
  · dsimp only;rw [hh.2 x hx,hk.2 x hx];ring

variable [Fintype V]

lemma objective_interpolate (v h k : V → ℝ) (t : ℝ) :
    objective v (fun x => (1-t)*h x+t*k x)=objective v h+
      2*t*(∑ x,(h x-v x)*(k x-h x))+t^2*(∑ x,(k x-h x)^2) := by
  unfold objective
  calc
    _ = ∑ x,((h x-v x)^2+2*t*((h x-v x)*(k x-h x))+t^2*(k x-h x)^2) := by
      apply Finset.sum_congr rfl;intro x hx;ring
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum]

lemma variational (S : System V E) (b v h : V → ℝ) (hp : IsProjection S b v h)
    (k : V → ℝ) (hk : k∈feasible S b) : 0≤∑ x,(h x-v x)*(k x-h x) := by
  let A := ∑ x,(h x-v x)*(k x-h x)
  let T := ∑ x,(k x-h x)^2
  have hT : 0≤T := Finset.sum_nonneg fun x _ => sq_nonneg _
  by_contra hA
  have hA' : A<0 := lt_of_not_ge hA
  let t := min 1 ((-A)/(T+1))
  have ht : 0<t := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
  have ht1 : t≤1 := min_le_left _ _
  have htA : t*(T+1)≤-A := (le_div_iff₀ (by linarith : 0<T+1)).mp (min_le_right _ _)
  have hineq := hp.2 _ (interpolate_feasible S b h k hp.1 hk t ⟨ht.le,ht1⟩)
  rw [objective_interpolate] at hineq
  change objective v h≤objective v h+2*t*A+t^2*T at hineq
  have hn : 2*A+t*T<0 := by linarith
  have hneg := mul_neg_of_pos_of_neg ht hn
  nlinarith [hneg]

lemma projection_order (S : System V E) (b₁ b₂ v₁ v₂ h₁ h₂ : V → ℝ) (δ : ℝ)
    (hp₁ : IsProjection S b₁ v₁ h₁) (hp₂ : IsProjection S b₂ v₂ h₂)
    (hb : ∀ x∈S.pins,b₁ x≤b₂ x+δ) (hv : ∀ x∉S.pins,v₁ x≤v₂ x+δ) :
    ∀ x,h₁ x≤h₂ x+δ := by
  let H : V → ℝ := fun x => max (h₁ x-h₂ x-δ) 0
  have hH (x) : 0≤H x := le_max_right _ _
  let k₁ : V → ℝ := fun x => min (h₁ x) (h₂ x+δ)
  let k₂ : V → ℝ := fun x => max (h₂ x) (h₁ x+(-δ))
  have hk₁ := min_feasible S b₁ b₂ h₁ h₂ δ hp₁.1 hp₂.1 hb
  have hk₂ := max_feasible S b₂ b₁ h₂ h₁ (-δ) hp₂.1 hp₁.1 (fun x hx => by linarith [hb x hx])
  have ht₁ := variational S b₁ v₁ h₁ hp₁ k₁ hk₁
  have ht₂ := variational S b₂ v₂ h₂ hp₂ k₂ hk₂
  have hd₁ (x) : k₁ x-h₁ x=-(H x) := by
    dsimp [k₁,H];by_cases hx : h₁ x≤h₂ x+δ
    · rw [min_eq_left hx,max_eq_right (by linarith)];ring
    · rw [min_eq_right (by linarith),max_eq_left (by linarith)];ring
  have hd₂ (x) : k₂ x-h₂ x=H x := by
    dsimp [k₂,H];by_cases hx : h₁ x≤h₂ x+δ
    · rw [max_eq_left (by linarith),max_eq_right (by linarith)];ring
    · rw [max_eq_right (by linarith),max_eq_left (by linarith)];ring
  simp only [hd₁,mul_neg,Finset.sum_neg_distrib,neg_nonneg] at ht₁
  simp only [hd₂] at ht₂
  have hpoint (x : V) : (H x)^2≤(h₁ x-v₁ x)*H x-(h₂ x-v₂ x)*H x := by
    by_cases hx : x∈S.pins
    · have hz : H x=0 := by dsimp [H];rw [hp₁.1.2 x hx,hp₂.1.2 x hx,max_eq_right (by linarith [hb x hx])]
      rw [hz];ring_nf;exact le_rfl
    · have hvx := hv x hx
      dsimp [H]
      by_cases hm : h₁ x-h₂ x-δ≤0
      · rw [max_eq_right hm];simp
      · rw [max_eq_left (by linarith)]
        nlinarith [mul_nonneg (by linarith : 0≤h₁ x-h₂ x-δ) (by linarith : 0≤v₂ x+δ-v₁ x)]
  have hsum : (∑ x,(H x)^2)≤0 := by
    have h := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => hpoint x)
    rw [Finset.sum_sub_distrib] at h
    linarith
  intro x
  have hx := Finset.single_le_sum (fun y (_ : y∈Finset.univ) => sq_nonneg (H y)) (Finset.mem_univ x)
  have hz : H x=0 := by nlinarith [hx,hsum]
  have hm := le_max_left (h₁ x-h₂ x-δ) 0
  change h₁ x-h₂ x-δ≤H x at hm
  linarith

theorem projection_parameter_stability (S : System V E) (b₁ b₂ v₁ v₂ h₁ h₂ : V → ℝ) (δ : ℝ) (_hδ : 0≤δ)
    (hp₁ : IsProjection S b₁ v₁ h₁) (hp₂ : IsProjection S b₂ v₂ h₂)
    (hb : ∀ x∈S.pins,|b₁ x-b₂ x|≤δ) (hv : ∀ x∉S.pins,|v₁ x-v₂ x|≤δ) :
    ∀ x,|h₁ x-h₂ x|≤δ := by
  have hup := projection_order S b₁ b₂ v₁ v₂ h₁ h₂ δ hp₁ hp₂
    (fun x hx => by have := (abs_le.mp (hb x hx)).2;linarith)
    (fun x hx => by have := (abs_le.mp (hv x hx)).2;linarith)
  have hlo := projection_order S b₂ b₁ v₂ v₁ h₂ h₁ δ hp₂ hp₁
    (fun x hx => by have := (abs_le.mp (hb x hx)).1;linarith)
    (fun x hx => by have := (abs_le.mp (hv x hx)).1;linarith)
  intro x
  exact abs_le.mpr ⟨by linarith [hlo x],by linarith [hup x]⟩

end ProjectionComparison

end

end OAI
