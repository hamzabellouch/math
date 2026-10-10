import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.QuantumTorus

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ)
local instance homogenizeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance homogenizeAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance homogenizeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def homogenizeMonomial (m : M) : R →+ PowerSeries (Torus v Ω) :=
  (PowerSeries.monomial (δ m).toNat).toAddMonoidHom.comp
    {toFun:=Torus.monomial v Ω m,map_zero':=by simp,map_add':=by intros; simp}
def homogenize : Torus v Ω →+ PowerSeries (Torus v Ω) :=
  Finsupp.liftAddHom (homogenizeMonomial v Ω δ)
@[simp] lemma homogenize_monomial (m : M) (a : R) :
    homogenize v Ω δ (Torus.monomial v Ω m a)=
      PowerSeries.monomial (δ m).toNat (Torus.monomial v Ω m a) :=
  Finsupp.liftAddHom_apply_single _ _ _
lemma torus_sum_monomial (f : Torus v Ω) :
    ∑m∈f.support,Torus.monomial v Ω m (f m)=f := by
  classical
  exact Finsupp.sum_single f
lemma homogenize_coeff (f : Torus v Ω) (d : ℕ) (m : M) :
    coeff d (homogenize v Ω δ f) m=if d=(δ m).toNat then f m else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>
    rw [_root_.map_add,_root_.map_add]
    simp only [Finsupp.add_apply,hf,hg]
    split_ifs <;> simp
  | single n a=>
    change coeff d (homogenize v Ω δ (Torus.monomial v Ω n a)) m=_
    rw [homogenize_monomial,coeff_monomial]
    by_cases hm : m=n
    · subst n; split_ifs <;> simp [Torus.monomial]
    · split_ifs <;> simp [Torus.monomial,Finsupp.single_eq_of_ne hm]
lemma homogenize_monomial_mul (m n : M) (a b : R) (hm : 0≤δ m) (hn : 0≤δ n) :
    homogenize v Ω δ (Torus.monomial v Ω m a*Torus.monomial v Ω n b)=
      homogenize v Ω δ (Torus.monomial v Ω m a)*homogenize v Ω δ (Torus.monomial v Ω n b) := by
  rw [Torus.monomial_mul_monomial,homogenize_monomial,homogenize_monomial,
    homogenize_monomial,PowerSeries.monomial_mul_monomial,Torus.monomial_mul_monomial,_root_.map_add,
    Int.toNat_add hm hn]
lemma homo_sum_mul {A : Type*} (s : Finset A) (f : A → Torus v Ω) (g : Torus v Ω) :
    (∑i∈s,f i)*g=∑i∈s,f i*g := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty,Torus.zero_mul]
  | @insert a s ha ih=>simp only [Finset.sum_insert ha,Torus.add_mul,ih]
lemma homo_mul_sum {A : Type*} (s : Finset A) (f : A → Torus v Ω) (g : Torus v Ω) :
    g*(∑i∈s,f i)=∑i∈s,g*f i := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty,Torus.mul_zero]
  | @insert a s ha ih=>simp only [Finset.sum_insert ha,Torus.mul_add,ih]
lemma homogenize_mul (f g : Torus v Ω)
    (hf : ∀m,f m≠0 → 0≤δ m) (hg : ∀m,g m≠0 → 0≤δ m) :
    homogenize v Ω δ (f*g)=homogenize v Ω δ f*homogenize v Ω δ g := by
  classical
  calc
    _ = ∑m∈f.support,∑n∈g.support,
        homogenize v Ω δ (Torus.monomial v Ω m (f m)*Torus.monomial v Ω n (g n)) := by
      have H (s : Finset M) (a : M → Torus v Ω) :
          homogenize v Ω δ (∑m∈s,a m)=∑m∈s,homogenize v Ω δ (a m) :=
        _root_.map_sum (homogenize v Ω δ) a s
      simp_rw [←H]
      congr 1
      simp_rw [←homo_mul_sum]
      rw [torus_sum_monomial,←homo_sum_mul,torus_sum_monomial]
    _ = ∑m∈f.support,∑n∈g.support,
        homogenize v Ω δ (Torus.monomial v Ω m (f m))*
        homogenize v Ω δ (Torus.monomial v Ω n (g n)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact homogenize_monomial_mul v Ω δ m n _ _ (hf m (Finsupp.mem_support_iff.mp hm))
        (hg n (Finsupp.mem_support_iff.mp hn))
    _ = _ := by
      simp_rw [←Finset.mul_sum]
      rw [←Finset.sum_mul]
      congr 1
      · rw [←_root_.map_sum,torus_sum_monomial]
      · rw [←_root_.map_sum,torus_sum_monomial]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance biHomogenizeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance biHomogenizeAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance biHomogenizeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def biHomogenizeMonomial (m : M) : R →+ PowerSeries (PowerSeries (Torus v Ω)) :=
  (PowerSeries.monomial (δ m).toNat).toAddMonoidHom.comp
    ((PowerSeries.monomial (κ m).toNat).toAddMonoidHom.comp
      {toFun:=Torus.monomial v Ω m,map_zero':=by simp,map_add':=by intros; simp})
def biHomogenize : Torus v Ω →+ PowerSeries (PowerSeries (Torus v Ω)) :=
  Finsupp.liftAddHom (biHomogenizeMonomial v Ω δ κ)
@[simp] lemma biHomogenize_monomial (m : M) (a : R) :
    biHomogenize v Ω δ κ (Torus.monomial v Ω m a)=
      monomial (δ m).toNat (monomial (κ m).toNat (Torus.monomial v Ω m a)) :=
  Finsupp.liftAddHom_apply_single _ _ _
lemma biHomogenize_coeff (f : Torus v Ω) (d e : ℕ) (m : M) :
    coeff e (coeff d (biHomogenize v Ω δ κ f)) m=
      if d=(δ m).toNat ∧ e=(κ m).toNat then f m else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>
    rw [_root_.map_add,_root_.map_add,_root_.map_add]
    simp only [Finsupp.add_apply,hf,hg]
    split_ifs <;> simp
  | single n a=>
    change coeff e (coeff d (biHomogenize v Ω δ κ (Torus.monomial v Ω n a))) m=_
    rw [biHomogenize_monomial,coeff_monomial]
    by_cases hm : m=n
    · subst n
      by_cases hd : d=(δ m).toNat
      · rw [ite_eq_left hd,coeff_monomial]
        by_cases he : e=(κ m).toNat <;> simp [hd,he,Torus.monomial]
      · simp [hd]
    · by_cases hd : d=(δ n).toNat <;> by_cases he : e=(κ n).toNat <;>
        simp [hd,he,Torus.monomial,Finsupp.single_eq_of_ne hm,coeff_monomial]
lemma biHomogenize_monomial_mul (m n : M) (a b : R)
    (hm : 0≤δ m ∧ 0≤κ m) (hn : 0≤δ n ∧ 0≤κ n) :
    biHomogenize v Ω δ κ (Torus.monomial v Ω m a*Torus.monomial v Ω n b)=
      biHomogenize v Ω δ κ (Torus.monomial v Ω m a)*
        biHomogenize v Ω δ κ (Torus.monomial v Ω n b) := by
  rw [Torus.monomial_mul_monomial,biHomogenize_monomial,biHomogenize_monomial,
    biHomogenize_monomial,monomial_mul_monomial,monomial_mul_monomial,
    Torus.monomial_mul_monomial,map_add,map_add,Int.toNat_add hm.1 hn.1,Int.toNat_add hm.2 hn.2]
lemma biHomogenize_mul (f g : Torus v Ω)
    (hf : ∀m,f m≠0 → 0≤δ m ∧ 0≤κ m) (hg : ∀m,g m≠0 → 0≤δ m ∧ 0≤κ m) :
    biHomogenize v Ω δ κ (f*g)=biHomogenize v Ω δ κ f*biHomogenize v Ω δ κ g := by
  classical
  calc
    _ = ∑m∈f.support,∑n∈g.support,
        biHomogenize v Ω δ κ (Torus.monomial v Ω m (f m)*Torus.monomial v Ω n (g n)) := by
      have H (s : Finset M) (a : M → Torus v Ω) :
          biHomogenize v Ω δ κ (∑m∈s,a m)=∑m∈s,biHomogenize v Ω δ κ (a m) :=
        _root_.map_sum (biHomogenize v Ω δ κ) a s
      simp_rw [←H]
      congr 1
      simp_rw [←homo_mul_sum]
      rw [torus_sum_monomial,←homo_sum_mul,torus_sum_monomial]
    _ = ∑m∈f.support,∑n∈g.support,
        biHomogenize v Ω δ κ (Torus.monomial v Ω m (f m))*
        biHomogenize v Ω δ κ (Torus.monomial v Ω n (g n)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact biHomogenize_monomial_mul v Ω δ κ m n _ _ (hf m (Finsupp.mem_support_iff.mp hm))
        (hg n (Finsupp.mem_support_iff.mp hn))
    _ = _ := by
      simp_rw [←Finset.mul_sum]
      rw [←Finset.sum_mul]
      congr 1
      · rw [←_root_.map_sum,torus_sum_monomial]
      · rw [←_root_.map_sum,torus_sum_monomial]
lemma biHomogenize_one : biHomogenize v Ω δ κ 1=1 := by
  change biHomogenize v Ω δ κ (Torus.monomial v Ω 0 1)=_
  rw [biHomogenize_monomial,_root_.map_zero,_root_.map_zero,Int.toNat_zero,monomial_zero_eq_C_apply,monomial_zero_eq_C_apply]
  change C (C (1:Torus v Ω))=1
  simp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
