import OAI.Probability.DilutedSpin.ReservoirShapeLimit

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

lemma logMean_bind_add (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ)
    (f : Ω → ℝ) (g : Λ → ℝ) :
    (P.bind (fun _ => Q)).logMean m (fun z => f z.1+g z.2)=P.logMean m f+Q.logMean m g := by
  unfold logMean expMoment
  simp only [mul_add,Real.exp_add,expect_bind,expect_mul_left,expect_mul_right]
  change Real.log (P.expMoment m f*Q.expMoment m g)/m=Real.log (P.expMoment m f)/m+Real.log (Q.expMoment m g)/m
  rw [Real.log_mul (P.expMoment_pos m f).ne' (Q.expMoment_pos m g).ne',add_div]

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

lemma backwardLog_prod_add (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) (g : FinitePath Λ n → ℝ) :
    backwardLog n (prod n T U) m (fun y => f (pathFst n y)+g (pathSnd n y))=
      backwardLog n T m f+backwardLog n U m g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change FiniteLaw Ω×(Ω → KernelTower Ω n) at T
      change FiniteLaw Λ×(Λ → KernelTower Λ n) at U
      change Ω×FinitePath Ω n → ℝ at f
      change Λ×FinitePath Λ n → ℝ at g
      simp only [backwardLog,prod,pathFst,pathSnd]
      have hh (x : Ω×Λ) := ih (T.2 x.1) (U.2 x.2) (fun j => m j.succ)
        (fun y => f (x.1,y)) (fun y => g (x.2,y))
      simp only [hh]
      exact FiniteLaw.logMean_bind_add T.1 U.1 (m 0)
        (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
        (fun x => backwardLog n (U.2 x) (fun j => m j.succ) (fun y => g (x,y)))

noncomputable def pad (a : Ω) : (n : ℕ) → KernelTower Ω n → KernelTower Ω (n+1)
  | 0,_ => (FiniteLaw.point a,fun _ => ())
  | n+1,T => (T.1,fun x => pad a n (T.2 x))

def pathPrefix : (n : ℕ) → FinitePath Ω (n+1) → FinitePath Ω n
  | 0,_ => ()
  | n+1,x => (x.1,pathPrefix n x.2)

lemma backwardLog_pad (a : Ω) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : m (Fin.last n)≠0) (f : FinitePath Ω n → ℝ) :
    backwardLog (n+1) (pad a n T) m (fun y => f (pathPrefix n y))=
      backwardLog n T (fun j => m j.castSucc) f := by
  induction n with
  | zero =>
      change (FiniteLaw.point a).logMean (m 0) (fun _ => f ())=f ()
      exact FiniteLaw.logMean_const _ hm _
  | succ n ih =>
      simp only [pad,backwardLog,pathPrefix]
      congr 1
      funext x
      exact ih (T.2 x) (fun j => m j.succ) hm (fun y => f (x,y))

omit [Fintype Ω] [Fintype Λ] in
lemma pathPrefix_pathFst (n : ℕ) (y : FinitePath (Ω×Λ) (n+1)) :
    pathPrefix n (pathFst (n+1) y)=pathFst n (pathPrefix n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (y.1.1,pathPrefix n (pathFst (n+1) y.2))=(y.1.1,pathFst n (pathPrefix n y.2))
      rw [ih]

omit [Fintype Ω] [Fintype Λ] in
lemma pathPrefix_pathSnd (n : ℕ) (y : FinitePath (Ω×Λ) (n+1)) :
    pathPrefix n (pathSnd (n+1) y)=pathSnd n (pathPrefix n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (y.1.2,pathPrefix n (pathSnd (n+1) y.2))=(y.1.2,pathSnd n (pathPrefix n y.2))
      rw [ih]

end DilutedSpinGlass.KernelTower

end

end OAI
