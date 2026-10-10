import OAI.MathematicalPhysics.Heisenberg.GibbsLimits

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.TensorUnits

lemma prod_interleave {X E : Type*} [Monoid E] (L : List X) (hL : L.Nodup)
    (f g : X → E) (hfg : ∀ x∈L,∀ y∈L,x≠y → Commute (f x) (g y)) :
    (L.map f).prod*(L.map g).prod=(L.map (fun x=>f x*g x)).prod := by
  induction L with
  | nil=>simp
  | cons a L ih=>
    obtain ⟨ha,hL⟩:=List.nodup_cons.mp hL
    have hc : Commute (L.map f).prod (g a) := by
      apply Commute.list_prod_left
      intro z hz
      obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hz
      exact hfg x (List.mem_cons_of_mem a hx) a (List.mem_cons_self ..)
        (fun he=>ha (he ▸ hx))
    simp only [List.map_cons,List.prod_cons]
    calc
      _=f a*((L.map f).prod*g a)*(L.map g).prod := by simp only [mul_assoc]
      _=(f a*g a)*((L.map f).prod*(L.map g).prod) := by rw [hc.eq]; simp only [mul_assoc]
      _=_ := by rw [ih hL (fun x hx y hy hxy=>hfg x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)]

variable {R E : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
variable {n : ℕ} {K : Type*} [Fintype K] [DecidableEq K]

def system (u : Fin n → K → K → E) (a b : Fin n → K) : E :=
  (List.ofFn (fun i=>u i (a i) (b i))).prod

omit [Fintype K] in
lemma system_mul (u : Fin n → K → K → E)
    (hu : ∀ i a b c d,u i a b*u i c d=if b=c then u i a d else 0)
    (hc : ∀ i j,i≠j → ∀ a b c d,Commute (u i a b) (u j c d))
    (a b c d : Fin n → K) :
    system u a b*system u c d=if b=c then system u a d else 0 := by
  have he := prod_interleave (List.ofFn (id : Fin n → Fin n))
    (List.nodup_ofFn.mpr Function.injective_id) (fun i=>u i (a i) (b i))
    (fun i=>u i (c i) (d i)) (fun i _ j _ hij=>hc i j hij ..)
  simp only [List.map_ofFn,Function.comp_def,id_eq] at he
  unfold system
  rw [he]
  by_cases hbc : b=c
  · subst c
    simp only [hu,ite_true]
  · rw [ite_eq_right hbc]
    obtain ⟨i,hi⟩:=Function.ne_iff.mp hbc
    apply List.prod_eq_zero
    apply List.mem_ofFn.mpr
    exact ⟨i,by rw [hu,ite_eq_right hi]⟩

omit [DecidableEq K] in
lemma system_diagonal_sum (R : Type*) [CommSemiring R] [Algebra R E] (u : Fin n → K → K → E) (hu : ∀ i,∑ a,u i a a=1) :
    ∑ a : Fin n → K,system u a a=1 := by
  have hh:=(MultilinearMap.mkPiAlgebraFin R n E).map_sum (fun i a=>u i a a)
  simp only [hu,MultilinearMap.mkPiAlgebraFin_apply] at hh
  simpa only [system,List.ofFn_const,List.prod_replicate,one_pow] using hh.symm

end Heisenberg.TensorUnits
end

end OAI
