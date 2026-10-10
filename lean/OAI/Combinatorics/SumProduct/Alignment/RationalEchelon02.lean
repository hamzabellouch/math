import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalEchelon01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalMatrix
variable {n m k : ℕ}

def real (f : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ)) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  ∑ i : Fin n,(LinearMap.proj i).smulRight (fun j=>(f (Pi.single i 1) j:ℝ))

lemma real_apply (f : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ)) (x : Fin n → ℝ) (j : Fin m) :
    real f x j=∑ i : Fin n,x i*(f (Pi.single i 1) j:ℝ) := by
  simp [real,LinearMap.sum_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

lemma real_single (f : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ)) (i : Fin n) :
    real f (Pi.single i 1)=fun j=>(f (Pi.single i 1) j:ℝ) := by
  ext j
  simp [real_apply,Pi.single_apply]

lemma real_rat (f : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ)) (x : Fin n → ℚ) :
    real f (fun i=>(x i:ℝ))=fun j=>(f x j:ℝ) := by
  ext j
  rw [real_apply]
  conv_rhs=>rw [RationalEchelon.expansion x,map_sum]
  simp [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

lemma real_comp (f : (Fin m → ℚ) →ₗ[ℚ] (Fin k → ℚ))
    (g : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ)) :
    real (f.comp g)=(real f).comp (real g) := by
  apply (Pi.basisFun ℝ (Fin n)).ext
  intro i
  simp only [Pi.basisFun_apply,real_single,LinearMap.comp_apply]
  exact (real_rat f (g (Pi.single i 1))).symm

lemma real_id : real (LinearMap.id : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ))=LinearMap.id := by
  apply (Pi.basisFun ℝ (Fin n)).ext
  intro i
  ext j
  simp [real_single,Pi.basisFun_apply,Pi.single_apply,apply_ite]

lemma real_sub (f g : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ)) :
    real (f-g)=real f-real g := by
  ext x j
  simp [real_apply,mul_sub,Finset.sum_sub_distrib]

lemma real_injective : Function.Injective (@real n m) := by
  intro f g h
  apply (Pi.basisFun ℚ (Fin n)).ext
  intro i
  ext j
  have hh:=congrArg (fun p=>(p (Pi.single i 1)) j) h
  simpa only [real_single,Pi.basisFun_apply,Rat.cast_inj] using hh

lemma real_injective_of_injective (f : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ))
    (hf : Function.Injective f) : Function.Injective (real f) := by
  obtain ⟨g,hg⟩:=f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  have hh:=congrArg real hg
  rw [real_comp,real_id] at hh
  exact Function.LeftInverse.injective (fun x=>LinearMap.congr_fun hh x)

end RationalMatrix

namespace RationalEchelon.Chart
variable {n : ℕ} {W : Submodule ℚ (Fin n → ℚ)} (E : Chart W)

def coords : (Fin n → ℚ) →ₗ[ℚ] (Fin E.dim → ℚ) where
  toFun x i:=x (E.pivot i)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

lemma coords_embed (x : Fin E.dim → ℚ) : E.coords (E.embed x)=x := by
  ext i
  exact E.at_pivot x i

lemma embed_coords {x : Fin n → ℚ} (hx : x∈W) : E.embed (E.coords x)=x := by
  obtain ⟨y,rfl⟩:=E.onto x hx
  rw [coords_embed]

lemma real_coords (x : Fin n → ℝ) (i : Fin E.dim) :
    RationalMatrix.real E.coords x i=x (E.pivot i) := by
  simp [RationalMatrix.real_apply,coords,Pi.single_apply,apply_ite]

lemma real_at_pivot (x : Fin E.dim → ℝ) (i : Fin E.dim) :
    RationalMatrix.real E.embed x (E.pivot i)=x i := by
  simp [RationalMatrix.real_apply,E.at_pivot,Pi.single_apply,apply_ite]

lemma coeff_zero (j : Fin n) (i : Fin E.dim) (hji : j<E.pivot i) :
    E.embed (Pi.single i 1) j=0 := by
  have hh:=E.prefix_eq j (Pi.single i 1) 0 (by
    intro l hl
    have hli : l≠i:=by intro he; subst l; exact (not_le_of_gt hji hl)
    simp [hli])
  simpa using hh

lemma real_prefix (j : Fin n) (x y : Fin E.dim → ℝ)
    (hxy : ∀ i,E.pivot i ≤ j → x i=y i) :
    RationalMatrix.real E.embed x j=RationalMatrix.real E.embed y j := by
  simp only [RationalMatrix.real_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hij : E.pivot i≤j
  · rw [hxy i hij]
  · rw [E.coeff_zero j i (lt_of_not_ge hij),Rat.cast_zero,mul_zero,mul_zero]

 

def normal : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) := LinearMap.id-E.embed.comp E.coords

lemma normal_apply (x : Fin n → ℚ) : E.normal x=x-E.embed (E.coords x) := rfl

lemma normal_pivot (x : Fin n → ℚ) (i : Fin E.dim) : E.normal x (E.pivot i)=0 := by
  simp [normal,coords,E.at_pivot]

lemma normal_sub (x : Fin n → ℚ) : x-E.normal x∈W := by
  simpa [normal] using E.mem (E.coords x)

lemma normal_eq_zero_iff (x : Fin n → ℚ) : E.normal x=0 ↔ x∈W := by
  constructor
  · intro h
    simpa [h] using E.normal_sub x
  · intro hx
    rw [normal_apply,E.embed_coords hx,sub_self]

lemma real_normal (x : Fin n → ℝ) :
    RationalMatrix.real E.normal x=x-RationalMatrix.real E.embed (fun i=>x (E.pivot i)) := by
  rw [normal,RationalMatrix.real_sub,RationalMatrix.real_id,RationalMatrix.real_comp]
  have hh : RationalMatrix.real E.coords x=(fun i=>x (E.pivot i)):=funext (E.real_coords x)
  change x-RationalMatrix.real E.embed (RationalMatrix.real E.coords x)=_
  rw [hh]

lemma real_normal_pivot (x : Fin n → ℝ) (i : Fin E.dim) :
    RationalMatrix.real E.normal x (E.pivot i)=0 := by
  rw [E.real_normal]
  simp [E.real_at_pivot]

lemma real_normal_tail (q : ℕ) (x : Fin n → ℝ) (hx : ∀ j : Fin n,j.val<q → x j=0) :
    ∀ j : Fin n,j.val<q → RationalMatrix.real E.normal x j=0 := by
  intro j hj
  rw [E.real_normal]
  change x j-RationalMatrix.real E.embed (fun i=>x (E.pivot i)) j=0
  rw [hx j hj]
  have he:=E.real_prefix j (fun i=>x (E.pivot i)) 0 (by
    intro i hi
    exact hx _ (lt_of_le_of_lt hi hj))
  simpa using congrArg Neg.neg he

end RationalEchelon.Chart
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalMatrix
variable {a b : ℕ}
def select (u : Fin a → Fin b) : (Fin b → ℚ) →ₗ[ℚ] (Fin a → ℚ) where
  toFun x i:=x (u i)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
lemma real_select (u : Fin a → Fin b) (x : Fin b → ℝ) (i : Fin a) :
    real (select u) x i=x (u i) := by
  simp [real_apply,select,Pi.single_apply,apply_ite]
end RationalMatrix

namespace RationalEchelon.Chart
variable {n : ℕ} {W : Submodule ℚ (Fin n → ℚ)} (E : Chart W)

def freeSet : Finset (Fin n):=Finset.univ.filter (fun j=>j∉Set.range E.pivot)
def free : Fin E.freeSet.card ↪o Fin n:=E.freeSet.orderEmbOfFin rfl

lemma free_ne_pivot (i : Fin E.freeSet.card) (j : Fin E.dim) : E.free i≠E.pivot j := by
  have hh:=(Finset.mem_filter.mp (E.freeSet.orderEmbOfFin_mem rfl i)).2
  exact fun he=>hh ⟨j,he.symm⟩

lemma pivot_or_free (j : Fin n) :
    (∃ i : Fin E.dim,E.pivot i=j) ∨ ∃ i : Fin E.freeSet.card,E.free i=j := by
  by_cases h : j∈Set.range E.pivot
  · exact Or.inl h
  · right
    have hh : j∈E.freeSet:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    have he:=E.freeSet.range_orderEmbOfFin rfl
    change j∈Set.range E.free
    rw [show Set.range E.free=E.freeSet from he]
    exact hh

def sectionMap : (Fin E.freeSet.card → ℚ) →ₗ[ℚ] (Fin n → ℚ):=
  ∑ i : Fin E.freeSet.card,(LinearMap.proj i).smulRight (Pi.single (E.free i) 1)

def quotientMap : (Fin n → ℚ) →ₗ[ℚ] (Fin E.freeSet.card → ℚ):=
  (RationalMatrix.select E.free).comp E.normal

lemma section_apply (x : Fin E.freeSet.card → ℚ) (j : Fin n) :
    E.sectionMap x j=∑ i : Fin E.freeSet.card,x i*(Pi.single (E.free i) 1 : Fin n → ℚ) j := by
  simp [sectionMap,LinearMap.sum_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

lemma section_free (x : Fin E.freeSet.card → ℚ) (i : Fin E.freeSet.card) :
    E.sectionMap x (E.free i)=x i := by
  simp [E.section_apply,Pi.single_apply,E.free.injective.eq_iff]

lemma section_pivot (x : Fin E.freeSet.card → ℚ) (j : Fin E.dim) :
    E.sectionMap x (E.pivot j)=0 := by
  rw [E.section_apply]
  apply Finset.sum_eq_zero
  intro i hi
  simp [(E.free_ne_pivot i j).symm]

lemma normal_section (x : Fin E.freeSet.card → ℚ) : E.normal (E.sectionMap x)=E.sectionMap x := by
  have he : E.coords (E.sectionMap x)=0:=funext (E.section_pivot x)
  rw [normal_apply,he,map_zero,sub_zero]

lemma quotient_section (x : Fin E.freeSet.card → ℚ) : E.quotientMap (E.sectionMap x)=x := by
  change (RationalMatrix.select E.free) (E.normal (E.sectionMap x))=x
  rw [E.normal_section]
  ext i
  exact E.section_free x i

lemma section_quotient (x : Fin n → ℚ) : E.sectionMap (E.quotientMap x)=E.normal x := by
  ext j
  rcases E.pivot_or_free j with ⟨i,rfl⟩|⟨i,rfl⟩
  · rw [E.section_pivot,E.normal_pivot]
  · rw [E.section_free]
    rfl

lemma quotient_eq_zero_iff (x : Fin n → ℚ) : E.quotientMap x=0 ↔ x∈W := by
  rw [← E.normal_eq_zero_iff,← E.section_quotient]
  constructor
  · intro h
    rw [h,map_zero]
  · intro hx
    have hh:=congrArg E.quotientMap hx
    simpa only [E.quotient_section,map_zero] using hh

lemma remainder_mem (x : Fin n → ℚ) : x-E.sectionMap (E.quotientMap x)∈W := by
  rw [E.section_quotient]
  exact E.normal_sub x

lemma real_quotient (x : Fin n → ℝ) (i : Fin E.freeSet.card) :
    RationalMatrix.real E.quotientMap x i=RationalMatrix.real E.normal x (E.free i) := by
  rw [quotientMap,RationalMatrix.real_comp]
  exact RationalMatrix.real_select E.free _ i

lemma real_section_free (x : Fin E.freeSet.card → ℝ) (i : Fin E.freeSet.card) :
    RationalMatrix.real E.sectionMap x (E.free i)=x i := by
  simp [RationalMatrix.real_apply,E.section_free,Pi.single_apply,apply_ite]

lemma real_section_pivot (x : Fin E.freeSet.card → ℝ) (j : Fin E.dim) :
    RationalMatrix.real E.sectionMap x (E.pivot j)=0 := by
  simp [RationalMatrix.real_apply,E.section_pivot]

lemma real_quotient_section (x : Fin E.freeSet.card → ℝ) :
    RationalMatrix.real E.quotientMap (RationalMatrix.real E.sectionMap x)=x := by
  have he : E.quotientMap.comp E.sectionMap=LinearMap.id:=LinearMap.ext E.quotient_section
  have hh:=congrArg RationalMatrix.real he
  rw [RationalMatrix.real_comp,RationalMatrix.real_id] at hh
  exact LinearMap.congr_fun hh x

lemma real_section_quotient (x : Fin n → ℝ) :
    RationalMatrix.real E.sectionMap (RationalMatrix.real E.quotientMap x)=RationalMatrix.real E.normal x := by
  have he : E.sectionMap.comp E.quotientMap=E.normal:=LinearMap.ext E.section_quotient
  have hh:=congrArg RationalMatrix.real he
  rw [RationalMatrix.real_comp] at hh
  exact LinearMap.congr_fun hh x

lemma real_normal_level (w : Fin n → ℕ) (hw : Monotone w) (l : ℕ) (x : Fin n → ℝ)
    (hx : ∀ j,w j<l → x j=0) : ∀ j,w j<l → RationalMatrix.real E.normal x j=0 := by
  intro j hj
  rw [E.real_normal]
  change x j-RationalMatrix.real E.embed (fun i=>x (E.pivot i)) j=0
  rw [hx j hj]
  have he:=E.real_prefix j (fun i=>x (E.pivot i)) 0 (by
    intro i hi
    exact hx _ (lt_of_le_of_lt (hw hi) hj))
  simpa using congrArg Neg.neg he

lemma real_quotient_level (w : Fin n → ℕ) (hw : Monotone w) (l : ℕ) (x : Fin n → ℝ)
    (hx : ∀ j,w j<l → x j=0) :
    ∀ i,w (E.free i)<l → RationalMatrix.real E.quotientMap x i=0 := by
  intro i hi
  rw [E.real_quotient]
  exact E.real_normal_level w hw l x hx (E.free i) hi

lemma real_section_level (w : Fin n → ℕ) (l : ℕ) (x : Fin E.freeSet.card → ℝ)
    (hx : ∀ i,w (E.free i)<l → x i=0) :
    ∀ j,w j<l → RationalMatrix.real E.sectionMap x j=0 := by
  intro j hj
  rcases E.pivot_or_free j with ⟨i,rfl⟩|⟨i,rfl⟩
  · exact E.real_section_pivot x i
  · rw [E.real_section_free]
    exact hx i hj

variable {m : ℕ} (p : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ)) (hW : W=LinearMap.ker p)
include hW in
lemma section_map_injective : Function.Injective (p.comp E.sectionMap) := by
  have hmem (z : Fin n → ℚ) : z∈W ↔ p z=0 := by rw [hW]; rfl
  intro x y hxy
  have hh : E.sectionMap (x-y)∈W := by
    rw [hmem,map_sub,map_sub,sub_eq_zero]
    exact hxy
  have hz:=(E.quotient_eq_zero_iff _).mpr hh
  rw [E.quotient_section] at hz
  exact sub_eq_zero.mp hz

include hW in
lemma map_section_quotient (x : Fin n → ℚ) : p (E.sectionMap (E.quotientMap x))=p x := by
  have hmem (z : Fin n → ℚ) : z∈W ↔ p z=0 := by rw [hW]; rfl
  have hh:=E.remainder_mem x
  rw [hmem,map_sub,sub_eq_zero] at hh
  exact hh.symm

include hW in
lemma real_map_section_quotient (x : Fin n → ℝ) :
    RationalMatrix.real p (RationalMatrix.real E.sectionMap (RationalMatrix.real E.quotientMap x))=
      RationalMatrix.real p x := by
  have he : (p.comp E.sectionMap).comp E.quotientMap=p:=LinearMap.ext (E.map_section_quotient p hW)
  have hh:=congrArg RationalMatrix.real he
  rw [RationalMatrix.real_comp,RationalMatrix.real_comp] at hh
  exact LinearMap.congr_fun hh x

include hW in
lemma real_kernel_iff (x : Fin n → ℝ) :
    RationalMatrix.real p x=0 ↔ RationalMatrix.real E.quotientMap x=0 := by
  have hi:=RationalMatrix.real_injective_of_injective _ (E.section_map_injective p hW)
  rw [RationalMatrix.real_comp] at hi
  constructor
  · intro hx
    apply hi
    simpa only [LinearMap.comp_apply,map_zero,E.real_map_section_quotient p hW] using hx
  · intro hx
    rw [← E.real_map_section_quotient p hW x,hx,map_zero,map_zero]

end RationalEchelon.Chart

end
end
end

end OAI
