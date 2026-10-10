import Mathlib
import OAI.Probability.SKGap.Localization.LocalWeakBase
import OAI.Probability.SKGap.Localization.StartedPrefix

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open SKGap.Stein Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma appendProduct_started_new_partial (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (N : ℕ) (hN : 0<N) (F F') (l : ι) (hzero : D.startedPartial w y N l=0) :
    (D.appendProduct N F F').startedPartial w y (N+1) l=
      fun x i=>localPartial D.H D.θ F' (.inl l) x i*D.startedSource w y N x i := by
  rw [appendProduct_started_partial _ _ _ _ hN,hzero]
  ext x i; simp

lemma appendStein_started_source (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (N : ℕ) (hN : 0<N) (l m : ι) (α : κ)
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x)) :
    (D.appendStein N l m α).startedSource w y (N+1)=steinSource j J h k (D.startedSource w y N) := by
  rw [appendStein,appendProduct_started_source _ w y N hN]
  ext x i
  simp [coefficient,phiCoefficient_eq,localArgs,hl,hm,ha,steinSource]

lemma appendStein_started_partial (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (N : ℕ) (hN : 0<N) (l m : ι) (α : κ)
    (hlm : l≠m) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x))
    (hzero : D.startedPartial w y N l=0) :
    (D.appendStein N l m α).startedPartial w y (N+1) l=steinPartial j J h k (D.startedSource w y N) := by
  rw [appendStein,appendProduct_started_new_partial _ w y N hN _ _ _ hzero]
  ext x i
  simp [localPartial,phiDerivative_first l m α hlm,localArgs,hl,hm,ha,steinPartial]

lemma appendStein_started_preserves_vanishing (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (N : ℕ) (hN : 0<N) (l m q : ι) (α : κ)
    (hql : q≠l) (hqm : q≠m) (hzero : D.startedPartial w y N q=0) :
    (D.appendStein N l m α).startedPartial w y (N+1) q=0 := by
  rw [appendStein,appendProduct_started_new_partial _ w y N hN _ _ _ hzero]
  ext x i
  simp only [localPartial,phiDerivative_other l m q α hql hqm,zero_mul,Pi.zero_apply]

lemma started_auxiliary_split (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (a : ℕ) (ha : 0<a) (l : ι) (x : Spin n) (i : Fin n) :
    D.startedAuxiliary w y a x i=(∑b,D.J i b*D.startedSource w y a x b)-
      D.j*siteMean (D.startedPartial w y a l) x*D.predecessor l x i-
      D.j*(∑q:{q:ι//q≠l},siteMean (D.startedPartial w y a q) x*D.predecessor q x i)-
      D.j*∑b:Fin a,siteMean (D.auxCoefficient a b) x*D.startedSource w y b x i := by
  rw [D.startedAuxiliary_eq w y ha]
  simp only [fieldOf,←D.startedSource_eq w y ha,startedPartial,Matrix.mulVec,dotProduct]
  rw [sum_split _ l]
  ring

lemma appendStein_started_auxiliary (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (N : ℕ) (hN : 0<N) (l m : ι) (α : κ)
    (hlm : l≠m) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (L : ι→ℕ) (hj : D.j=j) (hJ : D.J=J)
    (hp : ∀q,D.predecessor q=mag j J h (L q)) (hL : L l=k)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x))
    (hzero : D.startedPartial w y N l=0) :
    let E:=D.appendStein N l m α
    E.startedAuxiliary w y (N+1)=nextField j J h k (D.startedSource w y N)
      (fun q:{q:ι//q≠l}=>L q) (fun q=>siteMean (E.startedPartial w y (N+1) q))
      (fun b:Fin (N+1)=>E.startedSource w y b) (fun b=>siteMean (E.auxCoefficient (N+1) b)) := by
  dsimp only
  funext x i
  rw [started_auxiliary_split _ w y _ (by omega) l,appendStein_started_source D w y N hN l m α j J h k hl hm ha,
    appendStein_started_partial D w y N hN l m α hlm j J h k hl hm ha hzero]
  simp only [appendStein,appendProduct,hJ,hj,hp,hL,nextField]

theorem started_residual_step (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (N : ℕ) (hN : 0<N) (l m : ι) (α : κ)
    (hlm : l≠m) (hn : 0<n) (j : ℝ) (J : Interaction n) (hJs : J.IsSymm)
    (h : Fin n→ℝ) (k : ℕ) (L : ι→ℕ) (hj : D.j=j) (hJ : D.J=J)
    (hp : ∀q,D.predecessor q=mag j J h (L q)) (hL : L l=k)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x))
    (hzero : D.startedPartial w y N l=0) (x : Spin n) :
    let E:=D.appendStein N l m α
    (∑i,residual j J h (k+1) x i*D.startedSource w y N x i)=
      (∑i,residual j J h k x i*E.startedAuxiliary w y (N+1) x i)+
      j*(onsager j J h (k+1) x-onsager j J h k x)*(∑i,residual j J h k x i*E.startedSource w y (N+1) x i)-
      j*onsager j J h k x*(∑i,previousResidual j J h k x i*E.startedSource w y (N+1) x i)+
      j*(∑b:Fin (N+1),siteMean (E.auxCoefficient (N+1) b) x*∑i,residual j J h k x i*E.startedSource w y b x i)+
      j*(∑q:{q:ι//q≠l},siteMean (E.startedPartial w y (N+1) q) x*∑i,residual j J h k x i*mag j J h (L q) x i)-
      j*siteMean (E.startedPartial w y (N+1) l) x*(∑i,residual j J h k x i*mag j J h (k+1) x i) := by
  dsimp only
  rw [appendStein_started_auxiliary D w y N hN l m α hlm j J h k L hj hJ hp hL hl hm ha hzero,
    appendStein_started_source D w y N hN l m α j J h k hl hm ha,
    appendStein_started_partial D w y N hN l m α hlm j J h k hl hm ha hzero]
  exact residual_induction_identity hn j J hJs h k (D.startedSource w y N)
    (fun q:{q:ι//q≠l}=>L q)
    (fun q=>siteMean ((D.appendStein N l m α).startedPartial w y (N+1) q))
    (fun b:Fin (N+1)=>(D.appendStein N l m α).startedSource w y b)
    (fun b=>siteMean ((D.appendStein N l m α).auxCoefficient (N+1) b)) x

end SKGapCutoff.Recipe.OrdinaryData

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma halfDiff_zero_off_neighborhood (E : Set (Spin n)) (G : Observables n)
    (hG : ∀x,x∉E→G x=0) (x : Spin n) (i : Fin n) (hx : x∉E) (hi : flip x i∉E) :
    halfDiff i G x=0 := by
  simp [halfDiff_as_flip,hG x hx,hG (flip x i) hi]

lemma local_multiplier_energy (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (E : Set (Spin n)) (θ G : Observables n) {B L : ℝ}
    (hG : ∀x,x∉E→G x=0) (hθ : ∀x∈flipNeighborhood E,|θ x|≤B)
    (hd : ∀x∈E,∑i,(halfDiff i θ x)^2≤L^2) :
    varianceEnergy P (fun x=>θ x*G x)≤
      2*B^2*varianceEnergy P G+2*L^2*(∑x,P x*(G x)^2) := by
  have ht (x : Spin n) (i : Fin n) :
      (θ (flip x i))^2*(halfDiff i G x)^2≤B^2*(halfDiff i G x)^2 := by
    by_cases hx:x∈E
    · have hf : flip x i∈flipNeighborhood E:=Or.inr ⟨i,by simpa⟩
      exact mul_le_mul_of_nonneg_right (by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hθ _ hf) 2) (sq_nonneg _)
    · by_cases hi:flip x i∈E
      · exact mul_le_mul_of_nonneg_right (by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hθ _ (Or.inl hi)) 2) (sq_nonneg _)
      · simp [halfDiff_zero_off_neighborhood E G hG x i hx hi]
  calc
    _ ≤ ∑x,P x*∑i,conditionalVariance P x i*
        (2*B^2*(halfDiff i G x)^2+2*(G x)^2*(halfDiff i θ x)^2) := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hP x)
      apply Finset.sum_le_sum; intro i _
      apply mul_le_mul_of_nonneg_left _ (conditionalVariance_nonneg P hP x i)
      rw [halfDiff_mul_flipped]
      nlinarith only [ht x i,sq_nonneg (θ (flip x i)*halfDiff i G x-G x*halfDiff i θ x)]
    _ ≤ ∑x,P x*(2*B^2*(∑i,conditionalVariance P x i*(halfDiff i G x)^2)+2*(G x)^2*L^2) := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hP x)
      simp only [mul_add,Finset.sum_add_distrib]
      have h1 : (∑i,conditionalVariance P x i*(2*B^2*(halfDiff i G x)^2))=
          2*B^2*(∑i,conditionalVariance P x i*(halfDiff i G x)^2) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [h1]
      apply add_le_add_right
      calc
        _ ≤ ∑i,2*(G x)^2*(halfDiff i θ x)^2 := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_of_le_one_left (by positivity) (conditionalVariance_le_one P x i)
        _ = 2*(G x)^2*(∑i,(halfDiff i θ x)^2) := by rw [Finset.mul_sum]
        _ ≤ _ := by
          by_cases hx:x∈E
          · exact mul_le_mul_of_nonneg_left (hd x hx) (by positivity)
          · simp [hG x hx]
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,varianceEnergy,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring_nf

lemma local_multiplier_starSquared (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (E : Set (Spin n)) (θ G : Observables n) {B L : ℝ}
    (hG : ∀x,x∉E→G x=0) (hθ : ∀x∈flipNeighborhood E,|θ x|≤B)
    (hd : ∀x∈E,∑i,(halfDiff i θ x)^2≤L^2) :
    starSquared P (fun x=>θ x*G x)≤(3*B^2+2*L^2)*starSquared P G := by
  have hs : (∑x,P x*(θ x*G x)^2)≤B^2*(∑x,P x*(G x)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    by_cases hx:x∈E
    · have ht : (θ x)^2≤B^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hθ x (Or.inl hx)) 2
      have hm := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ht (sq_nonneg (G x))) (hP x)
      nlinarith only [hm]
    · simp [hG x hx]
  have he:=local_multiplier_energy P hP E θ G hG hθ hd
  have hn:=varianceEnergy_nonneg P hP G
  have hn' : 0≤∑x,P x*(G x)^2 := Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _)
  dsimp only [starSquared]
  nlinarith [mul_nonneg (sq_nonneg B) hn,mul_nonneg (sq_nonneg L) hn,
    mul_nonneg (sq_nonneg B) hn']

lemma local_star_multiplier (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (E : Set (Spin n)) (θ G : Observables n) {B L : ℝ}
    (hG : ∀x,x∉E→G x=0) (hθ : ∀x∈flipNeighborhood E,|θ x|≤B)
    (hd : ∀x∈E,∑i,(halfDiff i θ x)^2≤L^2) :
    starNorm P (fun x=>θ x*G x)≤Real.sqrt (3*B^2+2*L^2)*starNorm P G := by
  exact (Real.sqrt_le_sqrt (local_multiplier_starSquared P hP E θ G hG hθ hd)).trans_eq
    (Real.sqrt_mul (by positivity) _)

end SKGapCutoff.Static

end
end

end OAI
