import OAI.Computability.SpaceSimulation.OneTape.Supply

namespace OAI

namespace Fifths
namespace Cost
def lg (T : ℕ) := T.size + 1
theorem lg_pos (T : ℕ) : 0 < lg T := Nat.zero_lt_succ _
theorem lg_mono : Monotone lg := fun _ _ h => Nat.add_le_add_right (Nat.size_le_size h) _
def power (T : ℕ) := (T.size+4)/5
def K (T : ℕ) := 2^power T
theorem K_pos (T : ℕ) : 0 < K T := by unfold K; positivity
theorem bigK (T : ℕ) : T ≤ K T ^ 5 := by
  unfold K; rw [← pow_mul]
  exact le_trans (Nat.lt_size_self T).le (Nat.pow_le_pow_right (by omega)
    (by unfold power; omega))
theorem K_mono : Monotone K :=
  fun _ _ h => Nat.pow_le_pow_right (by omega)
    (Nat.div_le_div_right (Nat.add_le_add_right (Nat.size_le_size h) _))

/-- room for any fixed power of the allowed accessor logarithm
and for start-up costs. -/
def bound (d T : ℕ) := K T*K T*lg T^(d+2)
theorem lg_pow_le (d T : ℕ) : lg T^d ≤ bound d T := by
  calc
    _ ≤ lg T^(d+2) := Nat.pow_le_pow_right (lg_pos _) (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.mul_pos (K_pos _) (K_pos _))
theorem lg_le (d T : ℕ) : lg T ≤ bound d T := by
  calc
    _ = lg T ^ 1 := by simp
    _ ≤ lg T^(d+2) := Nat.pow_le_pow_right (lg_pos _) (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.mul_pos (K_pos _) (K_pos _))
theorem bound_pos (d T : ℕ) : 0 < bound d T := lt_of_lt_of_le (lg_pos _) (lg_le ..)
theorem bound_mono (d : ℕ) : Monotone (bound d) := by
  intro i j r
  exact Nat.mul_le_mul (Nat.mul_le_mul (K_mono r) (K_mono r))
    (Nat.pow_le_pow_left (lg_mono r) _)

variable {I X : Type}

theorem ofT {S a T : I → ℕ} {x : I → List X} (p : Comp x S a T) :
    Comp x S a (fun i => K (T i)) := by
  have v := p.size
  have s := p.source
  have q : Comp x S a (fun i => power (T i)) :=
    (v.add (Comp.constant s 4)).div (Comp.constant s 5)
  refine (Comp.constant s 2).pow q ?_
  refine Scaled.of_le ((Scaled.add p.target (Scaled.const _ 2))) (fun i => ?_)
  change (2^power (T i)).size ≤ (T i).size+2
  rw [Nat.size_pow]; unfold power; omega
end Cost

namespace Scaled
variable {I : Type} {S T a b : I → ℕ}

theorem looser (h : Scaled S a) (g : ∀ i, S i ≤ T i) : Scaled T a :=
  h.trans ((Scaled.refl T).of_le g)

theorem prodPos (h : Scaled S a) (g : Scaled T b)
    (l : ∀ i, 0 < S i) (p : ∀ i, 0<T i) :
    Scaled (fun i => S i*T i) (fun i => a i*b i) := by
  refine (h.mulFamily g).trans ⟨4,fun i => ?_⟩
  change (S i+1)*(T i+1) ≤ 4*(S i*T i+1)
  calc
    _ ≤ (S i+S i)*(T i+T i) :=
      Nat.mul_le_mul (Nat.add_le_add_left (l i) _) (Nat.add_le_add_left (p i) _)
    _ ≤ _ := by nlinarith
end Scaled

namespace Single
open Cost Tour
variable {X I : Type} (M : Single X) (W : I → Site) (x : I → List X)

/-- Simultaneous verification of register and stack bounds after
balancing. Uses arbitrary indices to avoid unnecessary restrictions
on profiles of inputs that can be rescanned. -/
theorem estimate (d : ℕ) (p : ∀ i, (W i).k = K (W i).T) :
    (Fits (fun i => bound d (W i).T) fun i =>
       let C := (M.tour (x i) (W i)).circuit; C.P.n ^ (C.width+1)) ∧
    Scaled (fun i => bound d (W i).T) (fun i =>
       let D := M.tour (x i) (W i); D.E * D.per) := by
  let T := fun i => (W i).T
  let k := fun i => (W i).k
  let b := fun i => (W i).b
  let J := fun i => lg (T i)
  let N := fun i => bound d (T i)
  let c := fun i => M.c (T i)
  let D := fun i => M.tour (x i) (W i)
  let C := fun i => (D i).circuit
  let width := fun i => (C i).width
  let kl := fun i => k i * J i
  let bl := fun i => b i * J i
  have kpos (i) : 0 < k i := (W i).positive
  have bpos (i) : 0 < b i := (W i).b_pos
  have jpos (i) : 0 < J i := lg_pos _
  have blpos (i) : 0 < bl i := Nat.mul_pos (bpos _) (jpos _)
  have klpos (i) : 0 < kl i := Nat.mul_pos (kpos _) (jpos _)
  have env (i) : bl i * J i ≤ N i := by
    change (k i * k i * J i) * J i ≤ K _ * K _ * J i^(d+2)
    rw [show k i = K (T i) from p i, mul_assoc,← pow_two (J i)]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (jpos _) (show 2 ≤ d+2 by omega))
  have ft : Fits J T :=
    (Scaled.refl J).of_le (fun i => show (T i).size ≤ J i from Nat.le_succ _)
  have fc : Scaled J c := by
    have h : Scaled J (fun i => M.w (T i)) :=
      (((((Fits.const J 2).mul ft).add (Fits.const J (Fintype.card M.Q))).add
        (Fits.const J (Fintype.card M.A))).add (Fits.const J 1))
    exact h.mulConst M.fields
  have fk : Fits J k := by
    apply Scaled.of_le ((Scaled.refl J).add (Scaled.const _ 2))
    intro i
    rw [show k i=K (T i) from p i,Cost.K,Nat.size_pow]; unfold power
    change _ ≤ (T i).size + 1 + 2
    omega
  have fb : Fits J b := fk.mul fk
  have fw : Fits J width :=
    (Fits.of_scaled fc).mul (fb.add (Fits.const _ 1))
  have fn : Fits J (fun i => (D i).N) :=
    ((((Fits.const _ 2).mul ft).add fb).add (Fits.const _ 2))
  have fNodes : Fits J (fun i => (D i).total) :=
    (fk.add (Fits.const _ 1)).mul ((fn.add fk).add (Fits.const _ 1))
  have fP : Fits J (fun i => (C i).P.n) := by
    have h : Fits J (fun i => (C i).outerDegree) :=
      (fn.add (Fits.const _ 1)).mul fw
    exact ((((Fits.const _ 2).mul (h.add (Fits.const _ 1))).add (Fits.const _ 1))).mono
      (fun _ => (Modulus.chosen_small _).le)
  have wt : Scaled bl width := by
    have h := ((Scaled.refl b).add (Scaled.const _ 1)).prodPos fc bpos jpos
    exact h.congr fun i => show (b i+1)*c i = c i*(b i+1) from mul_comm _ _

  constructor
  · change Fits N (fun i => (C i).P.n ^ (width i+1))
    exact Fits.pow _ _ (((wt.add (Scaled.const _ 1)).prodPos fP blpos jpos).looser env)
  have l (f : I → ℕ) (h : Scaled J f) : Scaled kl f :=
    h.looser (fun i => Nat.le_mul_of_pos_left (J i) (kpos _))
  have g : Scaled kl (fun i => (D i).guessLength) := by
    refine ((Scaled.refl k).prodPos fc kpos jpos).congr (fun i => ?_)
    show k i*c i = c i*k i; ac_rfl
  let p1 := fun i =>
    1 + (C i).nodes.size + (C i).width.size + (C i).count.size + (C i).P.n.size
  have r : Scaled J p1 := ((((Scaled.const J 1).add fNodes).add fw).add fn).add fP
  have e : Scaled J (fun i => (D i).coinsEasy) := by
    refine (((r.add (Scaled.const J 0)).add (Scaled.const J 1)).mulConst 100).congr (fun i => ?_)
    show (p1 i+0+1)*100 = 100*(p1 i+0+1)
    ac_rfl
  have u : Scaled kl (fun i => (D i).coinsHard) := by
    refine (((((l p1 r).add g).add (Scaled.const kl 1))).mulConst 100).congr (fun i => ?_)
    show (p1 i+(D i).guessLength+1)*100 = 100*(p1 i+(D i).guessLength+1)
    ac_rfl
  have s : Scaled kl (fun i => (D i).per) :=
    u.add (((Scaled.refl k).add (Scaled.const _ 2)).prodPos e kpos jpos)
  refine (((Scaled.refl k).add (Scaled.const _ 1)).prodPos s kpos klpos).looser
    (fun i => ?_)
  have g (i : I) : k i * kl i = bl i := by change k i*(k i*J i)=k i*k i*J i; ring
  exact le_trans (g i).le (le_trans (Nat.le_mul_of_pos_right (bl i) (jpos _)) (env i))
end Single
end Fifths

end OAI
