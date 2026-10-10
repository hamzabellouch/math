import Mathlib
import OAI.Probability.SKBarriers.Dynamics.HeatBathStationary

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic
namespace FiniteMarkov
variable {X : Type*}

theorem sum_cons [Fintype X] (m : ℕ) (f : (Fin (m+1) → X) → ℝ) :
    (∑ s,f s)=∑ x : X,∑ t : Fin m → X,f (Fin.cons x t) := by
  classical
  calc
    _ = ∑ z : X × (Fin m → X),f (Fin.cons z.1 z.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => X)).symm
      intro s
      simp only [Fin.consEquiv_symm_apply,Fin.cons_self_tail]
    _ = _ := Fintype.sum_prod_type _

def walkWeight (K : X → X → ℝ) : (m : ℕ) → X → (Fin m → X) → ℝ
  | 0,_,_ => 1
  | m+1,x,s => K x (s 0)*walkWeight K m (s 0) (Fin.tail s)

@[simp] theorem walkWeight_zero (K : X → X → ℝ) (x : X) (s : Fin 0 → X) :
    walkWeight K 0 x s=1 := rfl

@[simp] theorem walkWeight_cons (K : X → X → ℝ) (m : ℕ) (x y : X) (s : Fin m → X) :
    walkWeight K (m+1) x (Fin.cons y s)=K x y*walkWeight K m y s := rfl

theorem walkWeight_nonneg (K : X → X → ℝ) (hK : ∀ x y,0≤K x y) (m : ℕ) (x : X) (s : Fin m → X) :
    0≤walkWeight K m x s := by
  induction m generalizing x with
  | zero => exact zero_le_one
  | succ m ih => exact mul_nonneg (hK _ _) (ih _ _)

theorem walkWeight_sum [Fintype X] (K : X → X → ℝ) (hK : ∀ x,∑ y,K x y=1) (m : ℕ) (x : X) :
    ∑ s : Fin m → X,walkWeight K m x s=1 := by
  classical
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [sum_cons]
    simp only [walkWeight_cons,← Finset.mul_sum,ih,mul_one,hK]

def pathWeight (p : X → ℝ) (K : X → X → ℝ) (m : ℕ) (s : Fin (m+1) → X) : ℝ :=
  p (s 0)*walkWeight K m (s 0) (Fin.tail s)

theorem pathWeight_nonneg (p : X → ℝ) (K : X → X → ℝ)
    (hp : ∀ x,0≤p x) (hK : ∀ x y,0≤K x y) (m : ℕ) (s : Fin (m+1) → X) :
    0≤pathWeight p K m s := mul_nonneg (hp _) (walkWeight_nonneg K hK _ _ _)

theorem pathWeight_sum [Fintype X] (p : X → ℝ) (K : X → X → ℝ)
    (hp : ∑ x,p x=1) (hK : ∀ x,∑ y,K x y=1) (m : ℕ) :
    ∑ s : Fin (m+1) → X,pathWeight p K m s=1 := by
  rw [sum_cons]
  simp only [pathWeight,Fin.cons_zero,Fin.tail_cons,← Finset.mul_sum,walkWeight_sum K hK,mul_one,hp]

theorem pathWeight_first [Fintype X] (p : X → ℝ) (K : X → X → ℝ)
    (hK : ∀ x,∑ y,K x y=1) (m : ℕ) (f : X → ℝ) :
    (∑ s : Fin (m+1) → X,pathWeight p K m s*f (s 0))=∑ x,p x*f x := by
  rw [sum_cons]
  simp only [pathWeight,Fin.cons_zero,Fin.tail_cons,mul_right_comm (p _) _ (f _),← Finset.mul_sum,
    walkWeight_sum K hK,mul_one]

theorem pathWeight_marginal [Fintype X] (p : X → ℝ) (K : X → X → ℝ)
    (hK : ∀ x,∑ y,K x y=1) (hstat : ∀ y,∑ x,p x*K x y=p y)
    (m : ℕ) (k : Fin (m+1)) (f : X → ℝ) :
    (∑ s : Fin (m+1) → X,pathWeight p K m s*f (s k))=∑ y,p y*f y := by
  classical
  induction m with
  | zero =>
    have hk : k=0 := by exact Fin.ext (by omega)
    subst k
    exact pathWeight_first p K hK 0 f
  | succ m ih =>
    refine Fin.cases (pathWeight_first p K hK (m+1) f) (fun k => ?_) k
    rw [sum_cons]
    simp only [pathWeight,Fin.cons_zero,Fin.tail_cons,Fin.cons_succ,walkWeight]
    simp_rw [sum_cons m]
    simp only [Fin.cons_zero,Fin.tail_cons]
    have he (x y : X) (s : Fin m → X) :
        p x*(K x y*walkWeight K m y s)*f ((Fin.cons y s : Fin (m+1) → X) k)=
        (p x*K x y)*(walkWeight K m y s*f ((Fin.cons y s : Fin (m+1) → X) k)) := by ring
    simp_rw [he,← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hstat]
    have HH := ih k
    rw [sum_cons] at HH
    simpa only [pathWeight,Fin.cons_zero,Fin.tail_cons,mul_assoc,← Finset.mul_sum] using HH

theorem walkWeight_pos_step (K : X → X → ℝ) (hK : ∀ x y,0≤K x y)
    (m : ℕ) (x : X) (s : Fin m → X) (h : 0<walkWeight K m x s) :
    ∀ i : Fin m,0<K ((Fin.cons x s : Fin (m+1) → X) i.castSucc) (s i) := by
  induction m generalizing x with
  | zero => intro i; exact Fin.elim0 i
  | succ m ih =>
    have hfirst : 0<K x (s 0) := lt_of_le_of_ne (hK _ _) (by intro he; simp [walkWeight,← he] at h)
    have htail : 0<walkWeight K m (s 0) (Fin.tail s) := (mul_pos_iff_of_pos_left hfirst).mp h
    intro i
    refine Fin.cases (by simpa using hfirst) (fun i => ?_) i
    simpa only [Fin.castSucc_succ,Fin.cons_succ,Fin.cons_self_tail,Fin.tail] using ih (s 0) (Fin.tail s) htail i

theorem pathWeight_pos_step (p : X → ℝ) (K : X → X → ℝ)
    (hp : ∀ x,0≤p x) (hK : ∀ x y,0≤K x y)
    (m : ℕ) (s : Fin (m+1) → X) (h : 0<pathWeight p K m s) :
    ∀ i : Fin m,0<K (s i.castSucc) (s i.succ) := by
  have hh : 0<walkWeight K m (s 0) (Fin.tail s) :=
    pos_of_mul_pos_right h (hp (s 0))
  intro i
  simpa only [Fin.cons_self_tail,Fin.tail] using walkWeight_pos_step K hK m (s 0) (Fin.tail s) hh i

end FiniteMarkov

def stationaryPathWeight {n : ℕ} (β : ℝ) (J : Disorder n) (m : ℕ) : (Fin (m+1) → Config n) → ℝ :=
  FiniteMarkov.pathWeight (gibbs β J) (heatBath β J) m

theorem stationaryPathWeight_sum {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (m : ℕ) :
    ∑ s,stationaryPathWeight β J m s=1 :=
  FiniteMarkov.pathWeight_sum _ _ (gibbs_sum β J) (heatBath_sum hn β J) m

theorem stationaryPathWeight_marginal {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n)
    (m : ℕ) (k : Fin (m+1)) (f : Config n → ℝ) :
    (∑ s,stationaryPathWeight β J m s*f (s k))=∑ y,gibbs β J y*f y :=
  FiniteMarkov.pathWeight_marginal _ _ (heatBath_sum hn β J) (heatBath_stationary hn β J) m k f

theorem stationaryPathWeight_pos_jump {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n)
    (m : ℕ) (s : Fin (m+1) → Config n) (hs : 0<stationaryPathWeight β J m s)
    (v : Config n) (i : Fin m) : |overlap v (s i.succ)-overlap v (s i.castSucc)|≤2/(n:ℝ) :=
  heatBath_overlap_step hn β J v _ _
    (FiniteMarkov.pathWeight_pos_step _ _ (fun x => (gibbs_pos β J x).le) (heatBath_nonneg β J) m s hs i)

end SK.Analytic

end
end

end OAI
