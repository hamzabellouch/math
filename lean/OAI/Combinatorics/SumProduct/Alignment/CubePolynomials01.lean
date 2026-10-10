import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeFaces01
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped commutatorElement Pointwise
namespace CubePolynomials

variable {A : Type*} [AddCommGroup A]
open CubeFaces
noncomputable section
variable {G : Type*} [Group G]

def pattern (I : Finset ℕ) (h : ℕ → A) (n : A) : (A → G) →* (Finset ℕ → G) where
  toFun f v := f (n + ∑ i ∈ v ∩ I, h i)
  map_one' := rfl
  map_mul' _ _ := rfl

def polynomials (H : Filtration G) (k : ℕ) : Subgroup (A → G) :=
  ⨅ (I : Finset ℕ) (h : ℕ → A) (n : A), (cube H I k).comap (pattern I h n)

lemma mem_polynomials (H : Filtration G) (k : ℕ) (f : A → G) :
    f ∈ polynomials H k ↔ ∀ I h n, pattern I h n f ∈ cube H I k := by
  simp [polynomials]

lemma polynomials_antitone (H : Filtration G) : Antitone (polynomials (A := A) H) := by
  intro i j hij f hf
  rw [mem_polynomials] at hf ⊢
  intro I h n
  exact cube_shift_le H I hij (hf I h n)

lemma eval_mem {H : Filtration G} {k : ℕ} {f : A → G}
    (hf : f ∈ polynomials H k) (n : A) : f n ∈ H.level k := by
  have h := (mem_polynomials H k f).mp hf ∅ (fun _ => 0) n
  simpa [pattern] using cube_eval_mem H h ∅

lemma const_mem {H : Filtration G} {k : ℕ} {g : G} (hg : g ∈ H.level k) :
    (fun _ : A => g) ∈ polynomials H k := by
  rw [mem_polynomials]
  intro I h n
  have he : pattern I h n (fun _ : A => g) = face ∅ g := by ext v; simp [pattern, face]
  rw [he]
  exact face_mem_cube H (Finset.empty_subset I) (by simpa using hg)

lemma polynomials_eq_bot {H : Filtration G} {k : ℕ} (hk : H.level k = ⊥) :
    polynomials (A := A) H k = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  apply Subgroup.mem_bot.mpr
  funext n
  have h := eval_mem hf n
  simpa [hk] using h

def shift (t : A) : (A → G) ≃* (A → G) where
  toFun f n := f (n+t)
  invFun f n := f (n-t)
  left_inv f := by ext n; simp
  right_inv f := by ext n; simp
  map_mul' _ _ := rfl

lemma shift_mem {H : Filtration G} {k : ℕ} {f : A → G}
    (hf : f ∈ polynomials H k) (t : A) : shift t f ∈ polynomials H k := by
  rw [mem_polynomials] at hf ⊢
  intro I h n
  convert hf I h (n+t) using 1
  ext v
  change f ((n + ∑ i ∈ v ∩ I, h i) + t) = f ((n+t) + ∑ i ∈ v ∩ I, h i)
  congr 1
  abel

lemma derivative_mem {H : Filtration G} {k : ℕ} {f : A → G}
    (hf : f ∈ polynomials H k) (t : A) : f⁻¹ * shift t f ∈ polynomials H (k+1) := by
  rw [mem_polynomials] at hf ⊢
  intro I h n
  let a := I.sup id + 1
  have ha : a ∉ I := by
    intro ha
    have hle : a ≤ I.sup id := Finset.le_sup (f := id) ha
    dsimp [a] at hle
    omega
  let h' := Function.update h a t
  have hcube := hf (insert a I) h' n
  obtain ⟨l,hl,u,hu,he⟩ := cube_decompose H a I k hcube
  have heq : pattern I h n (f⁻¹ * shift t f) = u := by
    funext v
    let V := v ∩ I
    have hVI : V ⊆ I := Finset.inter_subset_right
    have haV : a ∉ V := fun h => ha (hVI h)
    have hs : ∑ j ∈ V, h' j = ∑ j ∈ V, h j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjne : j ≠ a := by rintro rfl; exact haV hj
      exact Function.update_of_ne hjne t h
    have hVa : V ∩ insert a I = V := Finset.inter_eq_left.mpr (hVI.trans (Finset.subset_insert a I))
    have hVai : insert a V ∩ insert a I = insert a V :=
      Finset.inter_eq_left.mpr (Finset.insert_subset_insert a hVI)
    have hlo := congrFun he V
    have hhi := congrFun he (insert a V)
    change f (n + ∑ j ∈ V ∩ insert a I, h' j) = l V * (if a ∈ V then u V else 1) at hlo
    change f (n + ∑ j ∈ insert a V ∩ insert a I, h' j) =
      l (insert a V) * (if a ∈ insert a V then u (insert a V) else 1) at hhi
    simp only [hVa, haV, ite_false, mul_one, hs] at hlo
    simp only [hVai, Finset.mem_insert_self, ite_true,
      cube_insert_irrelevant H ha hl, cube_insert_irrelevant H ha hu,
      Finset.sum_insert haV, show h' a = t from Function.update_self a t h, hs] at hhi
    change (f (n + ∑ j ∈ V, h j))⁻¹ * f ((n + ∑ j ∈ V, h j) + t) = u v
    rw [show (n + ∑ j ∈ V, h j) + t = n + (t + ∑ j ∈ V, h j) by abel,
      hlo, hhi, inv_mul_cancel_left]
    exact cube_restrict H hu v
  rw [heq]
  exact hu

 

lemma mem_of_derivatives {H : Filtration G} {k : ℕ} {f : A → G}
    (hvalue : ∀ n, f n ∈ H.level k)
    (hd : ∀ t, f⁻¹ * shift t f ∈ polynomials H (k+1)) : f ∈ polynomials H k := by
  rw [mem_polynomials]
  intro I
  induction I using Finset.induction_on with
  | empty =>
      intro h n
      have he : pattern ∅ h n f = face ∅ (f n) := by ext v; simp [pattern, face]
      rw [he]
      exact face_mem_cube H (Finset.empty_subset ∅) (by simpa using hvalue n)
  | @insert a I ha ih =>
      intro h n
      let l := pattern I h n f
      let u := pattern I h n (f⁻¹ * shift (h a) f)
      have hl : l ∈ cube H I k := ih h n
      have hu : u ∈ cube H I (k+1) := (mem_polynomials H (k+1) _).mp (hd (h a)) I h n
      have he : pattern (insert a I) h n f = l * upper a u := by
        funext v
        have haV : a ∉ v ∩ I := fun hh => ha (Finset.mem_inter.mp hh).2
        by_cases hav : a ∈ v
        · have hv : v ∩ insert a I = insert a (v ∩ I) := by
            ext b
            simp only [Finset.mem_inter, Finset.mem_insert]
            aesop
          change f (n + ∑ i ∈ v ∩ insert a I, h i) =
            f (n + ∑ i ∈ v ∩ I, h i) * (if a ∈ v then
              (f (n + ∑ i ∈ v ∩ I, h i))⁻¹ * f ((n + ∑ i ∈ v ∩ I, h i) + h a) else 1)
          rw [hv, Finset.sum_insert haV, ite_eq_left hav, mul_inv_cancel_left]
          congr 1
          abel
        · have hv : v ∩ insert a I = v ∩ I := by
            ext b
            simp only [Finset.mem_inter, Finset.mem_insert]
            aesop
          change f (n + ∑ i ∈ v ∩ insert a I, h i) =
            f (n + ∑ i ∈ v ∩ I, h i) * (if a ∈ v then u v else 1)
          rw [hv, ite_eq_right hav, mul_one]
      rw [he]
      exact (cube H (insert a I) k).mul_mem
        (cube_mono H (Finset.subset_insert a I) k hl) (upper_cube_mem H ha k hu)

end
end CubePolynomials

end
 

 
section
open scoped commutatorElement
namespace CubePolynomials
open CubeFaces
noncomputable section
variable {G : Type*} [Group G]
lemma commutator_mem {H : Filtration G} {i j : ℕ} {f g : ℤ → G}
    (hf : f ∈ polynomials H i) (hg : g ∈ polynomials H j) :
    ⁅f,g⁆ ∈ polynomials H (i+j) := by
  rw [mem_polynomials] at hf hg ⊢
  intro I h n
  rw [map_commutatorElement]
  exact cube_commutator_mem H I (hf I h n) (hg I h n)

lemma normalizes (H : Filtration G) (k : ℕ) :
    polynomials (A := ℤ) H 0 ≤ (Subgroup.normalizer (polynomials (A := ℤ) H k)) := by
  intro f hf
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  have hconj {f : ℤ → G} (hf : f ∈ polynomials H 0) {g : ℤ → G}
      (hg : g ∈ polynomials H k) : f*g*f⁻¹ ∈ polynomials H k := by
    have hc : ⁅f,g⁆ ∈ polynomials H k := by simpa using commutator_mem hf hg
    have he : f*g*f⁻¹ = ⁅f,g⁆ * g := by simp [commutatorElement_def, mul_assoc]
    rw [he]
    exact (polynomials H k).mul_mem hc hg
  constructor
  · exact hconj hf
  · intro hg
    have hh := hconj ((polynomials H 0).inv_mem hf) hg
    simpa [mul_assoc] using hh

open Polynomial in
lemma power_polynomial_mem {H : Filtration G} (e k : ℕ) (a : G)
    (ha : a ∈ H.level (e+k)) (p : ℤ[X]) (hp : p.natDegree ≤ e) :
    (fun n : ℤ => a ^ p.eval n) ∈ polynomials H k := by
  induction e generalizing k p with
  | zero =>
    have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hp)
    rw [he]
    simp only [eval_C]
    apply const_mem
    simpa only [Nat.zero_add] using (H.level (0+k)).zpow_mem ha (p.coeff 0)
  | succ e ih =>
    apply mem_of_derivatives
    · intro n
      exact (H.level k).zpow_mem (H.antitone (Nat.le_add_left k (e+1)) ha) _
    · intro t
      let q := taylor t p - p
      have hq : q.natDegree ≤ e := by
        by_cases hp0 : p = 0
        · simp [q,hp0]
        by_cases hq0 : q = 0
        · simp [hq0]
        have hd : q.degree < p.degree :=
          degree_sub_lt_right (degree_taylor p t) hp0 (leadingCoeff_taylor t p)
        have hd' : q.natDegree < p.natDegree := (natDegree_lt_natDegree_iff hq0).mpr hd
        omega
      have ha' : a ∈ H.level (e+(k+1)) := by simpa only [Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ha
      have h := ih (k+1) ha' q hq
      convert h using 1
      funext n
      change (a ^ p.eval n)⁻¹ * a ^ p.eval (n+t) = a ^ q.eval n
      rw [← zpow_neg, ← zpow_add]
      congr 1
      simp [q, taylor_apply, eval_comp]
      ring

end

end CubePolynomials
namespace NilpotentTaylor
open CubeFaces CubePolynomials
open scoped BigOperators
noncomputable section
variable {G : Type*} [Group G]

 
lemma all_derivatives_of_unit {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hf : f⁻¹ * shift 1 f ∈ polynomials H k) :
    ∀ t : ℤ, f⁻¹ * shift t f ∈ polynomials H k := by
  let S : AddSubgroup ℤ :=
    { carrier := {t | f⁻¹ * shift t f ∈ polynomials H k}
      zero_mem' := by
        change f⁻¹ * shift 0 f ∈ polynomials H k
        have he : f⁻¹ * shift 0 f = 1 := by ext n; simp [shift]
        rw [he]
        exact (polynomials H k).one_mem
      add_mem' := by
        intro u v hu hv
        change f⁻¹ * shift (u+v) f ∈ polynomials H k
        have he : f⁻¹ * shift (u+v) f = (f⁻¹ * shift u f) *
            shift u (f⁻¹ * shift v f) := by
          ext n
          change (f n)⁻¹ * f (n+(u+v)) =
            ((f n)⁻¹ * f (n+u)) * ((f (n+u))⁻¹ * f ((n+u)+v))
          rw [add_assoc]
          group
        rw [he]
        exact (polynomials H k).mul_mem hu (shift_mem hv u)
      neg_mem' := by
        intro u hu
        change f⁻¹ * shift (-u) f ∈ polynomials H k
        have he : f⁻¹ * shift (-u) f = (shift (-u) (f⁻¹ * shift u f))⁻¹ := by
          ext n
          simp [shift]
        rw [he]
        exact (polynomials H k).inv_mem (shift_mem hu (-u)) }
  intro t
  have h1 : (1 : ℤ) ∈ S := hf
  change t ∈ S
  simpa using S.zsmul_mem h1 t

lemma mem_of_unit_derivative {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hvalue : ∀ n, f n ∈ H.level k)
    (hd : f⁻¹ * shift 1 f ∈ polynomials H (k+1)) : f ∈ polynomials H k :=
  mem_of_derivatives hvalue (all_derivatives_of_unit hd)

 
lemma binomial_mem {H : Filtration G} (d k : ℕ) (a : G)
    (ha : a ∈ H.level (d+k)) :
    (fun n : ℤ => a ^ Ring.choose n d) ∈ polynomials H k := by
  induction d generalizing k with
  | zero =>
    simpa only [Ring.choose_zero_right, zpow_one, Nat.zero_add] using
      (const_mem (k := k) (by simpa using ha))
  | succ d ih =>
    apply mem_of_unit_derivative
    · intro n
      exact (H.level k).zpow_mem (H.antitone (by omega) ha) _
    · have ha' : a ∈ H.level (d+(k+1)) := by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha
      have h := ih (k+1) ha'
      convert h using 1
      ext n
      change (a ^ Ring.choose n (d+1))⁻¹ * a ^ Ring.choose (n+1) (d+1) =
        a ^ Ring.choose n d
      rw [Ring.choose_succ_succ, ← zpow_neg, ← zpow_add]
      congr 1
      omega

 

lemma initial_value_mem {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hf : f ∈ polynomials H k) (d : ℕ)
    (hz : ∀ n < d, f (n : ℤ) = 1) : f (d : ℤ) ∈ H.level (d+k) := by
  induction d generalizing k f with
  | zero => simpa using eval_mem hf 0
  | succ d ih =>
    have hd := derivative_mem hf 1
    have hz' : ∀ n < d, (f⁻¹ * shift 1 f) (n : ℤ) = 1 := by
      intro n hn
      change (f (n : ℤ))⁻¹ * f ((n : ℤ)+1) = 1
      rw [hz n (by omega), ← Nat.cast_add_one, hz (n+1) (by omega)]
      simp
    have h := ih hd hz'
    change (f (d : ℤ))⁻¹ * f ((d : ℤ)+1) ∈ H.level (d+(k+1)) at h
    rw [hz d (by omega), inv_one, one_mul, ← Nat.cast_add_one] at h
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

lemma zero_of_initial {H : Filtration G} {k d : ℕ} {f : ℤ → G}
    (hterm : H.level (d+k) = ⊥) (hf : f ∈ polynomials H k)
    (hz : ∀ n < d, f (n : ℤ) = 1) : f = 1 := by
  induction d generalizing k f with
  | zero =>
    ext n
    have h := eval_mem hf n
    simpa [show H.level k = ⊥ by simpa using hterm] using h
  | succ d ih =>
    have hd := derivative_mem hf 1
    have hz' : ∀ n < d, (f⁻¹ * shift 1 f) (n : ℤ) = 1 := by
      intro n hn
      change (f (n : ℤ))⁻¹ * f ((n : ℤ)+1) = 1
      rw [hz n (by omega), ← Nat.cast_add_one, hz (n+1) (by omega)]
      simp
    have hterm' : H.level (d+(k+1)) = ⊥ := by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hterm
    have he := ih hterm' hd hz'
    have hstep (n : ℤ) : f (n+1) = f n := by
      have h := congrFun he n
      change (f n)⁻¹ * f (n+1) = 1 at h
      exact (inv_mul_eq_one.mp h).symm
    ext n
    change f n = 1
    have hp : Function.Periodic f 1 := hstep
    have hn : f n = f 0 := by simpa using hp.int_mul n 0
    exact hn.trans (hz 0 (by omega))

 

theorem determined_by_initial {H : Filtration G} {k d : ℕ} {f g : ℤ → G}
    (hterm : H.level (d+k) = ⊥)
    (hf : f ∈ polynomials H k) (hg : g ∈ polynomials H k)
    (he : ∀ n < d, f (n : ℤ) = g n) : f = g := by
  have hz : f⁻¹ * g = 1 := zero_of_initial hterm
    ((polynomials H k).mul_mem ((polynomials H k).inv_mem hf) hg) (by
      intro n hn
      change (f (n : ℤ))⁻¹ * g (n : ℤ) = 1
      rw [he n hn, inv_mul_cancel])
  exact inv_mul_eq_one.mp hz

 
def word (a : ℕ → G) : ℕ → (ℤ → G)
  | 0 => 1
  | d+1 => word a d * fun n : ℤ => a d ^ Ring.choose n d

lemma word_mem {H : Filtration G} {k : ℕ} (a : ℕ → G) (d : ℕ)
    (ha : ∀ j < d, a j ∈ H.level (j+k)) : word a d ∈ polynomials H k := by
  induction d with
  | zero => exact (polynomials H k).one_mem
  | succ d ih =>
    exact (polynomials H k).mul_mem (ih (fun j hj => ha j (by omega)))
      (binomial_mem d k (a d) (ha d (by omega)))

lemma word_congr {a b : ℕ → G} (d : ℕ) (hab : ∀ j < d, a j = b j) :
    word a d = word b d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [word,word, ih (fun j hj => hab j (by omega)),hab d (by omega)]

lemma word_update (a : ℕ → G) (d : ℕ) (g : G) :
    word (Function.update a d g) d = word a d := by
  apply word_congr
  intro j hj
  exact Function.update_of_ne (show j ≠ d by omega) g a

lemma partial_taylor {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hf : f ∈ polynomials H k) (d : ℕ) :
    ∃ a : ℕ → G, (∀ j < d, a j ∈ H.level (j+k)) ∧
      ∀ n < d, word a d (n : ℤ) = f n := by
  induction d with
  | zero => exact ⟨fun _ => 1,by simp,by simp⟩
  | succ d ih =>
    obtain ⟨a,ha,he⟩ := ih
    let r : ℤ → G := (word a d)⁻¹ * f
    have hr : r ∈ polynomials H k :=
      (polynomials H k).mul_mem ((polynomials H k).inv_mem (word_mem a d ha)) hf
    have hz : ∀ n < d, r (n : ℤ) = 1 := by
      intro n hn
      change (word a d (n : ℤ))⁻¹ * f (n : ℤ) = 1
      rw [he n hn,inv_mul_cancel]
    have hg : r (d : ℤ) ∈ H.level (d+k) := initial_value_mem hr d hz
    refine ⟨Function.update a d (r d),?_,?_⟩
    · intro j hj
      by_cases h : j = d
      · simpa [h] using hg
      · rw [Function.update_of_ne h]
        exact ha j (by omega)
    · intro n hn
      change (word (Function.update a d (r d)) d (n : ℤ)) *
        (Function.update a d (r d) d) ^ Ring.choose (n : ℤ) d = f n
      rw [word_update,Function.update_self,Ring.choose_natCast]
      by_cases h : n = d
      · subst n
        rw [Nat.choose_self,Nat.cast_one,zpow_one]
        change word a d (d : ℤ) * ((word a d (d : ℤ))⁻¹ * f d) = f d
        group
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < d),Nat.cast_zero,zpow_zero,mul_one]
        exact he n (by omega)

 

theorem exists_taylor {H : Filtration G} {k d : ℕ} {f : ℤ → G}
    (hterm : H.level (d+k) = ⊥) (hf : f ∈ polynomials H k) :
    ∃ a : ℕ → G, (∀ j < d, a j ∈ H.level (j+k)) ∧ f = word a d := by
  obtain ⟨a,ha,he⟩ := partial_taylor hf d
  exact ⟨a,ha,determined_by_initial hterm hf (word_mem a d ha) (fun n hn => (he n hn).symm)⟩

end
end NilpotentTaylor

end
end
end
end

end OAI
