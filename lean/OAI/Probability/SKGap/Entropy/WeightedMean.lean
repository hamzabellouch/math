import Mathlib
import OAI.Probability.SKGap.Stability.ResidualRoot
import OAI.Probability.SKGap.Localization.ConstantRecipe

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static

lemma cutoff_scalar_mean_bound {X : Type*} [Fintype X] (μ v : X→ℝ) (t : ℝ)
    (m C : ℕ→X→ℝ) (d : ℕ) (hμ : ∀x,0≤μ x) (hC : ∀k x,0≤C k x ∧ C k x≤1)
    {A L D : ℝ} (hL : 0≤L) (hD : 0≤D)
    (hres : |∑x,μ x*(∑k∈Finset.range d,cutoffWeight (fun l=>C l x) k*(v x-m k x))|≤A)
    (hroot : ∀k x,C k x≠0→|m k x-t|≤L) (hdiam : ∀x,|v x-t|≤D) :
    |∑x,μ x*(v x-t)|≤ A+L*(∑x,μ x)+D*(∑x,if 0<cutoffDeficit (fun l=>C l x) d then μ x else 0) := by
  classical
  let w:=fun k x=>cutoffWeight (fun l=>C l x) k
  let Q:=fun x=>cutoffDeficit (fun l=>C l x) d
  have hw (k : ℕ) (x : X) : 0≤w k x ∧ w k x≤C k x:=cutoffWeight_bounds _ _ (fun k=>hC k x)
  have hQ (x : X) : 0≤Q x ∧ Q x≤1:=cutoffDeficit_bounds _ d (fun k=>hC k x)
  have hsum (x : X) : ∑k∈Finset.range d,w k x≤1 := by
    have hh:0≤1-∑k∈Finset.range d,w k x:= (hQ x).1
    linarith
  have hr (x : X) : |∑k∈Finset.range d,w k x*(m k x-t)|≤L := by
    calc
      _ ≤ ∑k∈Finset.range d,|w k x*(m k x-t)|:=Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑k∈Finset.range d,w k x*L := by
        apply Finset.sum_le_sum; intro k hk
        rw [abs_mul,abs_of_nonneg (hw k x).1]
        by_cases hc : C k x=0
        · have hz:w k x=0:=le_antisymm (by simpa [hc] using (hw k x).2) (hw k x).1
          simp [hz]
        · exact mul_le_mul_of_nonneg_left (hroot k x hc) (hw k x).1
      _ = (∑k∈Finset.range d,w k x)*L:= (Finset.sum_mul ..).symm
      _ ≤ L := mul_le_of_le_one_left hL (hsum x)
  have hrs : |∑x,μ x*(∑k∈Finset.range d,w k x*(m k x-t))|≤L*(∑x,μ x) := by
    calc
      _ ≤ ∑x,|μ x*(∑k∈Finset.range d,w k x*(m k x-t))|:=Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑x,μ x*L := by
        apply Finset.sum_le_sum;intro x _
        rw [abs_mul,abs_of_nonneg (hμ x)]
        exact mul_le_mul_of_nonneg_left (hr x) (hμ x)
      _ = _ := by rw [←Finset.sum_mul];ring
  have hqs : |∑x,μ x*Q x*(v x-t)|≤D*(∑x,if 0<Q x then μ x else 0) := by
    calc
      _ ≤ ∑x,|μ x*Q x*(v x-t)|:=Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑x,D*(if 0<Q x then μ x else 0) := by
        apply Finset.sum_le_sum;intro x _
        rw [abs_mul,abs_of_nonneg (mul_nonneg (hμ x) (hQ x).1)]
        by_cases hq:0<Q x
        · simp only [ite_eq_left hq]
          exact (mul_le_mul_of_nonneg_left (hdiam x) (mul_nonneg (hμ x) (hQ x).1)).trans
            (by nlinarith [mul_le_of_le_one_right (hμ x) (hQ x).2])
        · have hz:Q x=0:=le_antisymm (le_of_not_gt hq) (hQ x).1
          simp [hz]
      _ = _ := (Finset.mul_sum ..).symm
  have he : (∑x,μ x*(v x-t))=
      (∑x,μ x*(∑k∈Finset.range d,w k x*(v x-m k x)))+
      (∑x,μ x*(∑k∈Finset.range d,w k x*(m k x-t)))+
      (∑x,μ x*Q x*(v x-t)) := by
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro x _
    have hh:(∑k∈Finset.range d,w k x*(v x-m k x))+
      (∑k∈Finset.range d,w k x*(m k x-t))=(∑k∈Finset.range d,w k x)*(v x-t) := by
      rw [←Finset.sum_add_distrib,Finset.sum_mul]
      apply Finset.sum_congr rfl;intros;ring
    change μ x*(v x-t)=μ x*(∑k∈Finset.range d,w k x*(v x-m k x))+
      μ x*(∑k∈Finset.range d,w k x*(m k x-t))+
      μ x*(1-∑k∈Finset.range d,w k x)*(v x-t)
    rw [←mul_add,hh]
    ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hres hrs)) hqs))

lemma vectorNorm_le_of_unit_dot {n : ℕ} (v : Fin n→ℝ) {B : ℝ} (hB : 0≤B)
    (h : ∀e : Fin n→ℝ,vectorNorm e≤1→|∑i,v i*e i|≤B) : vectorNorm v≤B := by
  by_cases hv:vectorNorm v=0
  · simpa [hv] using hB
  have hp:0<vectorNorm v:=lt_of_le_of_ne (vectorNorm_nonneg _) (Ne.symm hv)
  let e:=fun i=>(vectorNorm v)⁻¹*v i
  have he:vectorNorm e=1 := by
    change SKGap.vectorNorm (fun i=>(vectorNorm v)⁻¹*v i)=1
    rw [SKGap.vectorNorm_smul,abs_of_pos (inv_pos.mpr hp)]
    exact inv_mul_cancel₀ hv
  have hh:=h e he.le
  have hd:(∑i,v i*e i)=vectorNorm v := by
    calc
      _ = (vectorNorm v)⁻¹*(∑i,(v i)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl;intro i _;dsimp [e];ring
      _ = (vectorNorm v)⁻¹*(vectorNorm v)^2 := by rw [vectorNorm_sq]
      _ = _ := by field_simp
  simpa only [hd,abs_of_nonneg (vectorNorm_nonneg _)] using hh

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C ρ : ℝ}
variable {J : ∀a,Interaction (N a)} {h e : ∀a,Fin (N a)→ℝ}

lemma gibbs_selected_direction_control (d : ℕ) (hρ : 0<ρ)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 d 0) B W C (d+1) (2*d) (J a))
    (he : ∀a,vectorNorm (e a)≤1) :
    ∃A:ℝ,0≤A ∧ ∀a (f:Observables (N a)),
      |∑x,fieldGibbs (J a) (h a) x*(f x)^2*
        (∑k∈Finset.range (d-1),cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k*
          (∑i,(spin x i-mag j (J a) (h a) (k+2) x i)*e a i))|≤
      A*starSquared (fieldGibbs (J a) (h a)) f := by
  have hh : UniformSquare (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑k∈Finset.range (d-1),cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k*
          (∑i,(spin x i-mag j (J a) (h a) (k+2) x i)*e a i)) := by
    apply UniformSquare.finset_sum
    intro k hk
    have hk':k<d-1:=Finset.mem_range.mp hk
    exact (gibbs_constant_residuals d hR hB hW hC hn hJ hdiag hevent he (k+2) (by omega)).2.mul
      (fun a x=>(fieldGibbs_pos _ _ _).le)
      (residualWeight_uniform hρ hR hB hn (fun a=>(hevent a).1)
        (fun a x l hl=>(hevent a).2.1 (h a) x l hl) k (by omega))
  obtain ⟨A,hA,hh⟩:=hh 1 0 zero_le_one le_rfl
  refine ⟨A,hA,fun a f=>?_⟩
  simpa only [mul_one] using hh a f (fun _=>1) (by simp)
    (by intro x;simp [halfDiff])

lemma gibbs_selected_all_directions (d : ℕ) (hρ : 0<ρ)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 d 0) B W C (d+1) (2*d) (J a)) :
    ∃A:ℝ,0≤A ∧ ∀a (e:Fin (N a)→ℝ),vectorNorm e≤1→∀f:Observables (N a),
      |∑x,fieldGibbs (J a) (h a) x*(f x)^2*
        (∑k∈Finset.range (d-1),cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k*
          (∑i,(spin x i-mag j (J a) (h a) (k+2) x i)*e i))|≤
      A*starSquared (fieldGibbs (J a) (h a)) f := by
  let Ω' := (a : Ω) × {e : Fin (N a)→ℝ // vectorNorm e≤1}
  obtain ⟨A,hA,hh⟩:=gibbs_selected_direction_control (Ω:=Ω') (N:=fun a=>N a.1)
    (J:=fun a=>J a.1) (h:=fun a=>h a.1) (e:=fun a=>a.2.val) d hρ hR hB hW hC
    (fun a=>hn a.1) (fun a=>hJ a.1) (fun a=>hdiag a.1) (fun a=>hevent a.1) (fun a=>a.2.property)
  exact ⟨A,hA,fun a e he f=>hh ⟨a,⟨e,he⟩⟩ f⟩

lemma magnetization_norm {n : ℕ} (r : Fin n→ℝ) :
    vectorNorm (SKGap.magnetization r)≤Real.sqrt (n:ℝ) := by
  apply nonneg_le_nonneg_of_sq_le_sq (Real.sqrt_nonneg _)
  simp only [←sq,vectorNorm_sq,Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑_i:Fin n,(1:ℝ) := Finset.sum_le_sum (fun i _=>(Real.tanh_sq_lt_one (r i)).le)
    _ = _ := by simp

theorem gibbs_square_mean (m : ℕ) {c r₀ ε : ℝ}
    (hj : 0≤j) (hR : 0≤R) (hc : 0<c) (hr₀ : 0<r₀) (hρ : 0<ρ) (hε : 0<ε)
    (hbuffer : (R+4*j)*ρ<r₀) (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
    (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J a))
    (hH : ∀a y,vectorNorm (SKGap.tapField j (J a) (h a) y)≤r₀*Real.sqrt (N a:ℝ)→∀v,
      c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j (J a) y (SKGap.spinVariance y)) v) :
    ∃r : ∀a,Fin (N a)→ℝ,
      (∀a,SKGap.tapField j (J a) (h a) (r a)=0 ∧
        ∀y,SKGap.tapField j (J a) (h a) y=0→y=r a) ∧
      ∃A:ℝ,0≤A ∧ ∀a (f:Observables (N a)),
      vectorNorm (fun i=>∑x,fieldGibbs (J a) (h a) x*(f x)^2*(spin x i-SKGap.magnetization (r a) i))≤
        ((1+(R+3*j)/c)*(R+4*j))*ρ*Real.sqrt (N a:ℝ)*(∑x,fieldGibbs (J a) (h a) x*(f x)^2)+
        A*starSquared (fieldGibbs (J a) (h a)) f := by
  classical
  have hs (a : Ω) : 0<Real.sqrt (N a:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hn a))
  have hroots (a : Ω) := selected_tap_root (hn a) hj hR hc hr₀ hρ hbuffer
    (J a) (hJ a) (h a) (fun v=>(vectorNorm_matrix_mul (J a) v).trans
      (mul_le_mul_of_nonneg_right (hevent a).1 (vectorNorm_nonneg _))) (hH a)
  choose r hr hu hd using hroots
  obtain ⟨A,hA,ha⟩:=gibbs_selected_all_directions (h:=h) (2*m) hρ hR hB hW hC hn hJ hdiag hevent
  obtain ⟨C₁,C₂,hC₁,hC₂,ht⟩:=gibbs_residual_selection_tail (h:=h) m hρ hε hm he hR hB hW hC hn hJ hdiag hevent
  refine ⟨r,fun a=>⟨hr a,hu a⟩,A+2*C₂,by positivity,fun a f=>?_⟩
  let μ:=fun x=>fieldGibbs (J a) (h a) x*(f x)^2
  let L:=((1+(R+3*j)/c)*(R+4*j))*ρ*Real.sqrt (N a:ℝ)
  have hL:0≤L:=by dsimp [L];positivity
  have hμ (x : Spin (N a)) : 0≤μ x:=mul_nonneg (fieldGibbs_pos _ _ _).le (sq_nonneg _)
  apply vectorNorm_le_of_unit_dot
  · exact add_nonneg (mul_nonneg hL (Finset.sum_nonneg (fun x _=>hμ x)))
      (mul_nonneg (by positivity) (starSquared_nonneg _ (fun x=>(fieldGibbs_pos _ _ x).le) f))
  intro e he
  have hpair (x : Spin (N a)) (z : Fin (N a)→ℝ) :
      (∑i,spin x i*e i)-(∑i,z i*e i)=∑i,(spin x i-z i)*e i := by
    rw [←Finset.sum_sub_distrib];apply Finset.sum_congr rfl;intros;ring
  have hrootpair (k : ℕ) (x : Spin (N a))
      (hh:residualCutoff ρ j (J a) (h a) k x≠0) :
      |(∑i,mag j (J a) (h a) (k+2) x i*e i)-(∑i,SKGap.magnetization (r a) i*e i)|≤L := by
    rw [←Finset.sum_sub_distrib]
    have hdot:|∑i,(mag j (J a) (h a) (k+2) x i-SKGap.magnetization (r a) i)*e i|≤L :=
      (SKGap.vector_dot_abs_le _ e).trans
        ((mul_le_mul_of_nonneg_left he (vectorNorm_nonneg _)).trans
          (by convert! hd a k x hh using 1; simp only [mul_one]; rfl))
    convert hdot using 2
    apply Finset.sum_congr rfl;intro i _;ring
  have hdiam (x : Spin (N a)) :
      |(∑i,spin x i*e i)-(∑i,SKGap.magnetization (r a) i*e i)|≤2*Real.sqrt (N a:ℝ) := by
    rw [hpair]
    have hv : vectorNorm (spin x-SKGap.magnetization (r a))≤2*Real.sqrt (N a:ℝ) := by
      exact (SKGap.vectorNorm_sub_le _ _).trans
        ((add_le_add (by convert! mag_vectorNorm j (J a) (h a) 0 x using 1)
          (magnetization_norm (r a))).trans_eq (by ring))
    exact (SKGap.vector_dot_abs_le _ e).trans
      ((mul_le_mul_of_nonneg_left he (vectorNorm_nonneg _)).trans (by convert! hv using 1; simp only [mul_one]; rfl))
  have hres : |∑x,μ x*(∑k∈Finset.range (2*m-1),
      cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k*
      ((∑i,spin x i*e i)-(∑i,mag j (J a) (h a) (k+2) x i*e i)))|≤
      A*starSquared (fieldGibbs (J a) (h a)) f := by
    simpa only [hpair] using ha a e he f
  have hb:=cutoff_scalar_mean_bound μ (fun x=>∑i,spin x i*e i) (∑i,SKGap.magnetization (r a) i*e i)
    (fun k x=>∑i,mag j (J a) (h a) (k+2) x i*e i)
    (fun k x=>residualCutoff ρ j (J a) (h a) k x) (2*m-1) hμ
    (fun k x=>residualCutoff_bounds ρ j (J a) (h a) k x) hL (by positivity) hres hrootpair hdiam
  have htail:=mul_le_mul_of_nonneg_left ((ht a).2 f) (show 0≤2*Real.sqrt (N a:ℝ) by positivity)
  have hcancel : 2*Real.sqrt (N a:ℝ)*(C₂/Real.sqrt (N a:ℝ)*starSquared (fieldGibbs (J a) (h a)) f)=
      2*C₂*starSquared (fieldGibbs (J a) (h a)) f := by field_simp [ne_of_gt (hs a)]
  rw [hcancel] at htail
  have heq : (∑i,(∑x,μ x*(spin x i-SKGap.magnetization (r a) i))*e i)=
      ∑x,μ x*((∑i,spin x i*e i)-(∑i,SKGap.magnetization (r a) i*e i)) := by
    simp only [Finset.sum_mul,Finset.mul_sum,hpair]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro x _
    apply Finset.sum_congr rfl;intros;ring
  change |∑i,(∑x,μ x*(spin x i-SKGap.magnetization (r a) i))*e i|≤_
  rw [heq]
  calc
    _ ≤ A*starSquared (fieldGibbs (J a) (h a)) f+L*(∑x,μ x)+
        2*Real.sqrt (N a:ℝ)*(∑x,if 0<cutoffDeficit (fun l=>residualCutoff ρ j (J a) (h a) l x) (2*m-1) then μ x else 0) := hb
    _ ≤ A*starSquared (fieldGibbs (J a) (h a)) f+L*(∑x,μ x)+
        2*C₂*starSquared (fieldGibbs (J a) (h a)) f := add_le_add_right htail _
    _ = _ := by dsimp only [L,μ]; ring

end SKGapCutoff.Recipe

end
end

end OAI
