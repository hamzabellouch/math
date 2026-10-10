import OAI.Probability.DilutedSpin.RegularizedNormalization
import OAI.Probability.DilutedSpin.UpperRegularized

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped BigOperators Topology

namespace FiniteLaw
variable {A : Type} [Fintype A]

lemma tendsto_expect {X : Type} {l : Filter X} (P : FiniteLaw A)
    (f : X → A → ℝ) (g : A → ℝ) (hf : ∀ a,Tendsto (fun x => f x a) l (𝓝 (g a))) :
    Tendsto (fun x => P.expect (f x)) l (𝓝 (P.expect g)) := by
  unfold expect
  exact tendsto_finsetSum _ (fun a _ => (hf a).const_mul _)

lemma tendsto_logMean {X : Type} {l : Filter X} (P : FiniteLaw A) (m : ℝ)
    (f : X → A → ℝ) (g : A → ℝ) (hf : ∀ a,Tendsto (fun x => f x a) l (𝓝 (g a))) :
    Tendsto (fun x => P.logMean m (f x)) l (𝓝 (P.logMean m g)) := by
  have he := P.tendsto_expect (fun x a => Real.exp (m*f x a)) (fun a => Real.exp (m*g a))
    (fun a => ((hf a).const_mul m).rexp)
  exact (he.log (ne_of_gt (P.expMoment_pos m g))).div_const m

end FiniteLaw
namespace KernelTower
variable {Ω : Type} [Fintype Ω]

lemma tendsto_backwardLog {X : Type} {l : Filter X} (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f : X → FinitePath Ω n → ℝ) (g : FinitePath Ω n → ℝ)
    (hf : ∀ a,Tendsto (fun x => f x a) l (𝓝 (g a))) :
    Tendsto (fun x => backwardLog n T m (f x)) l (𝓝 (backwardLog n T m g)) := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
      exact T.1.tendsto_logMean (m 0) _ _ (fun a => ih (T.2 a) (fun j => m j.succ)
        (fun x y => f x (a,y)) (fun y => g (a,y)) (fun y => hf (a,y)))

end KernelTower
namespace PrescribedTree
variable {Ω A : Type} [Fintype Ω] [Fintype A] {n : ℕ}

lemma normalized_logInsertion_eq (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n,m j.succ≠0) (D : FinitePath Ω n → ℝ) (d t : ℝ)
    (hd : 0<1+t*d) (hD : ∀ y,0<1+t*D y) :
    logInsertion T m D t-Real.log (1+t*d)=
      KernelTower.backwardLog n T (fun j => m j.succ)
        (fun y => Real.log ((1+t*D y)/(1+t*d))) := by
  simp_rw [Real.log_div (ne_of_gt (hD _)) (ne_of_gt hd),sub_eq_add_neg]
  exact (KernelTower.backwardLog_add n T _ hnz _ _).symm

lemma normalized_logInsertion_bound (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n,0 < m j.succ) (P : FinitePath Ω n → FiniteLaw A)
    (θ D : A → ℝ) (a : ℝ) (ha : 0<a) (hfac : ∀ s,Real.exp (θ s)=a*(1+D s))
    (s₀ : A) (hD : ∀ s,|D s|<1) {B t : ℝ} (hB : 0≤B) (hθ : ∀ s,|θ s|≤B)
    (ht0 : 0≤t) (ht : t<1) :
    |logInsertion T m (fun y => (P y).expect D) t-Real.log (1+t*D s₀)|≤2*B := by
  have ht' : |t|<1 := by rwa [abs_of_nonneg ht0]
  have hDP (y : FinitePath Ω n) : |(P y).expect D|≤1 :=
    (P y).abs_expect_le (fun a => (hD a).le)
  rw [normalized_logInsertion_eq T m (fun j => ne_of_gt (hm j)) _ _ _
    (insertion_pos (n := 0) (Ω := Unit) (fun _ => D s₀) (fun _ => (hD s₀).le) ht' ())
    (fun y => insertion_pos _ hDP ht' y)]
  exact KernelTower.backwardLog_bound n T _ hm (fun y =>
    (P y).normalized_factor_log_bound θ D a ha hfac s₀ (hD s₀) hB hθ ht0 ht)

lemma normalized_logInsertion_limit (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n,m j.succ≠0) (P : FinitePath Ω n → FiniteLaw A)
    (θ D : A → ℝ) (a : ℝ) (ha : 0<a) (hfac : ∀ s,Real.exp (θ s)=a*(1+D s))
    (s₀ : A) (hD : ∀ s,|D s|<1) :
    Tendsto (fun t : ℝ => logInsertion T m (fun y => (P y).expect D) t-Real.log (1+t*D s₀))
      (𝓝 1) (𝓝 (KernelTower.backwardLog n T (fun j => m j.succ)
        (fun y => (P y).logMean 1 θ)-θ s₀)) := by
  have hDP (y : FinitePath Ω n) : 0<1+(P y).expect D := by
    have hh := (P y).factor_expect θ D a hfac
    have hp := (P y).expMoment_pos 1 θ
    simp only [FiniteLaw.expMoment,one_mul] at hp
    nlinarith
  have hd : 0<1+D s₀ := by have := (abs_lt.mp (hD s₀)).1; linarith
  have hlog (y : FinitePath Ω n) :
      (P y).logMean 1 θ=Real.log (1+(P y).expect D)+Real.log a := by
    simp only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one]
    rw [(P y).factor_expect θ D a hfac,Real.log_mul (ne_of_gt ha) (ne_of_gt (hDP y)),add_comm]
  have hθ₀ : θ s₀=Real.log (1+D s₀)+Real.log a := by
    rw [← Real.log_exp (θ s₀),hfac s₀,Real.log_mul (ne_of_gt ha) (ne_of_gt hd),add_comm]
  have he : KernelTower.backwardLog n T (fun j => m j.succ)
      (fun y => (P y).logMean 1 θ)-θ s₀=
      KernelTower.backwardLog n T (fun j => m j.succ)
        (fun y => Real.log (1+(P y).expect D))-Real.log (1+D s₀) := by
    simp_rw [hlog]
    rw [KernelTower.backwardLog_add n T _ hnz,hθ₀]
    ring
  rw [he]
  apply Tendsto.sub
  · apply KernelTower.tendsto_backwardLog
    intro y
    simpa only [one_mul,id_eq] using
      (((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 (1:ℝ)) (𝓝 1)).mul_const ((P y).expect D)).const_add 1).log (by simpa only [one_mul] using ne_of_gt (hDP y))
  · simpa only [one_mul,id_eq] using
      (((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 (1:ℝ)) (𝓝 1)).mul_const (D s₀)).const_add 1).log (by simpa only [one_mul] using ne_of_gt hd)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
