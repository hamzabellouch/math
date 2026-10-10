import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceCoefficients
import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily IdealMobiusDivisorSum UniqueFactorizationMonoid
open InverseInitialConjugateEnergy InverseInitialPoissonBridge
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem tuple_product_squarefree (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Squarefree (∏i,P i) := by
  have hs:∀Q∈Finset.univ.image P,Prime Q := by
    intro Q hQ
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hQ
    exact hP i
  have he:(∏Q∈Finset.univ.image P,Q)=∏i,P i :=
    Finset.prod_image (fun i hi j hj h=>hinj h)
  rw [←he]
  exact InverseInitialExcludedPolynomial.prime_product_squarefree _ hs

omit [DecidableEq ι] in
theorem tuple_product_support (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (_hinj:Function.Injective P) : primeSupport (∏i,P i)=Finset.univ.image P := by
  have hn:(∏i,P i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i hi=>(hP i).ne_zero)
  ext Q
  rw [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hn,Finset.mem_image]
  constructor
  · rintro ⟨hQ,hd⟩
    obtain ⟨i,hi,hd⟩:=(hQ.dvd_finsetProd_iff P).mp hd
    have he:Q=P i:=associated_iff_eq.mp (hQ.associated_of_dvd (hP i) hd)
    exact ⟨i,hi,he.symm⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hP i,Finset.dvd_prod_of_mem P hi⟩

omit [DecidableEq ι] in
theorem tuple_divisors_eq_subsets (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) :
    idealDivisors (∏i,P i)=Finset.univ.powerset.image (fun J:Finset ι=>∏i∈J,P i) := by
  have hs:=tuple_product_squarefree P hP hinj
  have hf:(idealDivisors (∏i,P i)).filter Squarefree=idealDivisors (∏i,P i) := by
    apply Finset.filter_eq_self.mpr
    intro J hJ
    exact hs.squarefree_of_dvd ((mem_idealDivisors hs.ne_zero).mp hJ)
  rw [←hf,squarefree_divisors_eq_image _ hs.ne_zero,tuple_product_support P hP hinj,
    Finset.powerset_image,Finset.image_image]
  congr 1
  funext J
  exact Finset.prod_image (fun i hi j hj h=>hinj h)

omit [Fintype ι] in
theorem tuple_subset_product_injective (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Function.Injective (fun J:Finset ι=>∏i∈J,P i) := by
  let:∀i,(P i).IsMaximal:=fun i=>(Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  exact FirstCauchyArithmetic.family_product_injective P hinj

theorem sum_tuple_divisors (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P)(f:Ideal O→ℂ) :
    (∑j∈idealDivisors (∏i,P i),f j)=∑J∈Finset.univ.powerset,f (∏i∈J,P i) := by
  rw [tuple_divisors_eq_subsets P hP hinj,Finset.sum_image
    (fun J hJ K hK he=>tuple_subset_product_injective P hP hinj he)]

theorem originalTotal_slot_subsets (S:Finset (Ideal O))
    (P:ι→Ideal O)(hP:∀i,Prime (P i))(hinj:Function.Injective P)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    originalTotalPolynomial S (∏i,P i) η a W Z r z u=
      ∑J∈Finset.univ.powerset,
        originalFixedPolynomial S (∏i,P i) (∏i∈J,P i) η a W Z r z u := by
  rw [originalTotalPolynomial_eq_sectors S (tuple_product_squarefree P hP hinj)
    η a W hZ r z (fun _=>0),sum_tuple_divisors P hP hinj]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
