import OAI.Combinatorics.MatroidCounting.CommonBases

namespace OAI

/-! # Exact transport of finite experiments with rational outputs

Output values need not form a finite type. Equality against every real
observable is preserved by deterministic postprocessing and by the
independent arrays used in the counting estimator.
-/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical

noncomputable section
variable {X Y U V Z W : Type*}
variable [Fintype X] [Fintype Y] [Fintype U] [Fintype V]

def SameLaw (f : X → Z) (g : Y → Z) : Prop :=
  ∀ phi : Z → ℝ,uniformAverage (fun x => phi (f x))=uniformAverage (fun y => phi (g y))

lemma SameLaw.map {f : X → Z} {g : Y → Z} (h : SameLaw f g) (F : Z → W) :
    SameLaw (fun x => F (f x)) (fun y => F (g y)) := by
  intro phi
  exact h (fun z => phi (F z))

lemma SameLaw.prod {f : X → Z} {g : Y → Z} {a : U → W} {b : V → W}
    (hfg : SameLaw f g) (hab : SameLaw a b) :
    SameLaw (fun x : X×U => (f x.1,a x.2)) (fun y : Y×V => (g y.1,b y.2)) := by
  intro phi
  rw [uniformAverage_prod,uniformAverage_prod]
  have hinner (x : X) :
      uniformAverage (fun u : U => phi (f x,a u))=
        uniformAverage (fun v : V => phi (f x,b v)) :=
    hab (fun w => phi (f x,w))
  simp_rw [hinner]
  exact hfg (fun z => uniformAverage (fun v : V => phi (z,b v)))

lemma SameLaw.independent {f : X → Z} {g : Y → Z} (h : SameLaw f g) (N : ℕ) :
    SameLaw (fun xs : Fin N → X => fun i => f (xs i))
      (fun ys : Fin N → Y => fun i => g (ys i)) := by
  intro phi
  exact uniformAverage_independent_eq f g h N phi

lemma indexed (N : ℕ) (f : Fin N → X → Z) (g : Fin N → Y → Z)
    (h : ∀ i,SameLaw (f i) (g i)) :
    SameLaw (fun xs : Fin N → X => fun i => f i (xs i))
      (fun ys : Fin N → Y => fun i => g i (ys i)) := by
  intro phi
  induction N with
  | zero =>
    have hf (xs : Fin 0 → X) : (fun i => f i (xs i))=(fun i : Fin 0 => Fin.elim0 i) := by
      funext i
      exact Fin.elim0 i
    have hg (ys : Fin 0 → Y) : (fun i => g i (ys i))=(fun i : Fin 0 => Fin.elim0 i) := by
      funext i
      exact Fin.elim0 i
    simp_rw [hf,hg,uniformAverage_const]
  | succ N ih =>
    have hf (x : X) (xs : Fin N → X) :
        (fun i => f i ((Fin.cons x xs : Fin (N+1) → X) i))=Fin.cons (f 0 x) (fun i => f i.succ (xs i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hg (y : Y) (ys : Fin N → Y) :
        (fun i => g i ((Fin.cons y ys : Fin (N+1) → Y) i))=Fin.cons (g 0 y) (fun i => g i.succ (ys i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp_rw [hf,hg]
    have htail (x : X) := ih (fun i => f i.succ) (fun i => g i.succ)
      (fun i => h i.succ) (fun zs => phi (Fin.cons (f 0 x) zs))
    simp_rw [htail]
    exact h 0 (fun z => uniformAverage (fun ys : Fin N → Y =>
      phi (Fin.cons z (fun i => g i.succ (ys i)))))

end
end ContingencyTables.FiniteObservableTransport

end OAI
