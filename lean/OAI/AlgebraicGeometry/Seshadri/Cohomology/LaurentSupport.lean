import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlaneFreeCech

namespace OAI


                                        
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

lemma laurentSupported_eq_span (S : Set (ℤ × ℤ)) :
    laurentSupported (K := K) S = Submodule.span K (T '' S) := by
  rw [laurentSupported,Submodule.comap_equiv_eq_map_symm,
    Finsupp.supported_eq_span_single,Submodule.map_span,Set.image_image]
  rfl

lemma supported_monomial_mul (S U : Set (ℤ × ℤ)) (z : ℤ × ℤ)
    (h : ∀ w ∈ S, z+w ∈ U) (r : LaurentPlane.Ring K) (hr : r ∈ laurentSupported S) :
    T z * r ∈ laurentSupported U := by
  rw [laurentSupported_eq_span] at hr ⊢
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨w,hw,rfl⟩ := hr
    rw [← T_add]
    exact Submodule.subset_span ⟨z+w,h w hw,rfl⟩
  | zero => simp
  | add r s hr hs ih ih' => simpa only [mul_add] using (Submodule.span K (T '' U)).add_mem ih ih'
  | smul a r hr ih => simpa only [mul_smul_comm] using (Submodule.span K (T '' U)).smul_mem a ih

lemma supported_of_support (r : LaurentPlane.Ring K) (S : Set (ℤ × ℤ))
    (h : ∀ w ∈ r.coeff.support, w ∈ S) : r ∈ laurentSupported S := by
  exact (Finsupp.mem_supported K r.coeff).mpr h

lemma support_bound {ι : Type*} [Fintype ι] (m : ι → LaurentPlane.Ring K) :
    ∃ n : ℕ, ∀ i w, w ∈ (m i).coeff.support →
      -(n : ℤ) ≤ w.1 ∧ w.1 ≤ n ∧ -(n : ℤ) ≤ w.2 ∧ w.2 ≤ n := by
  classical
  let n := Finset.univ.sup (fun i => (m i).coeff.support.sup (fun w => w.1.natAbs+w.2.natAbs))
  refine ⟨n,?_⟩
  intro i w hw
  have hn : w.1.natAbs+w.2.natAbs ≤ n :=
    (Finset.le_sup (f := fun w : ℤ × ℤ => w.1.natAbs+w.2.natAbs) hw).trans
      (Finset.le_sup (f := fun i => (m i).coeff.support.sup (fun w => w.1.natAbs+w.2.natAbs))
        (Finset.mem_univ i))
  have ha := Int.natCast_natAbs w.1
  have hb := Int.natCast_natAbs w.2
  have ha' : w.1 ≤ (w.1.natAbs : ℤ) := Int.le_natAbs
  have hb' : w.2 ≤ (w.2.natAbs : ℤ) := Int.le_natAbs
  have haa : -w.1 ≤ (w.1.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -w.1))
  have hbb : -w.2 ≤ (w.2.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -w.2))
  omega

lemma freeA_stable {ι : Type*} (z : ℤ × ℤ) (hz : 0 ≤ z.2)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeA ι) : T (K := K) z • m ∈ freeA ι := by
  intro i hi
  exact supported_monomial_mul coneA coneA z (by intro w hw; change 0 ≤ z.2+w.2; exact add_nonneg hz hw)
    (m i) (hm i hi)

lemma freeB_stable {ι : Type*} (z : ℤ × ℤ) (hz : 0 ≤ z.1)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeB ι) : T (K := K) z • m ∈ freeB ι := by
  intro i hi
  exact supported_monomial_mul coneB coneB z (by intro w hw; change 0 ≤ z.1+w.1; exact add_nonneg hz hw)
    (m i) (hm i hi)

lemma freeC_stable {ι : Type*} (d : ℤ) (z : ℤ × ℤ) (hz : z.1+z.2 ≤ 0)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeC ι d) : T (K := K) z • m ∈ freeC ι d := by
  intro i hi
  apply supported_monomial_mul (coneC d) (coneC d) z _ (m i) (hm i hi)
  intro w hw
  change w.1+w.2 ≤ d at hw
  change z.1+w.1+(z.2+w.2) ≤ d
  omega

lemma freeA_clearing {ι : Type*} [Fintype ι] (m : ι → LaurentPlane.Ring K) :
    ∃ n : ℕ, T (K := K) (0,(n : ℤ)) • m ∈ freeA ι := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨n,fun i hi => ?_⟩
  apply supported_monomial_mul ((m i).coeff.support : Set (ℤ × ℤ)) coneA (0,(n : ℤ)) _ (m i)
    (supported_of_support (m i) _ (fun w hw => hw))
  intro w hw
  change 0 ≤ (n : ℤ)+w.2
  have := (hn i w hw).2.2.1
  omega

lemma freeB_clearing {ι : Type*} [Fintype ι] (m : ι → LaurentPlane.Ring K) :
    ∃ n : ℕ, T (K := K) ((n : ℤ),0) • m ∈ freeB ι := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨n,fun i hi => ?_⟩
  apply supported_monomial_mul ((m i).coeff.support : Set (ℤ × ℤ)) coneB ((n : ℤ),0) _ (m i)
    (supported_of_support (m i) _ (fun w hw => hw))
  intro w hw
  change 0 ≤ (n : ℤ)+w.1
  have := (hn i w hw).1
  omega

lemma freeC_clearing {ι : Type*} [Fintype ι] (d : ℤ) (m : ι → LaurentPlane.Ring K) :
    ∃ n : ℕ, T (K := K) (0,-(n : ℤ)) • m ∈ freeC ι d := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨2*n+(-d).toNat,fun i hi => ?_⟩
  apply supported_monomial_mul ((m i).coeff.support : Set (ℤ × ℤ)) (coneC d)
    (0,-((2*n+(-d).toNat : ℕ) : ℤ)) _ (m i)
    (supported_of_support (m i) _ (fun w hw => hw))
  intro w hw
  change 0+w.1+(-((2*n+(-d).toNat : ℕ) : ℤ)+w.2) ≤ d
  have := (hn i w hw).2.1
  have := (hn i w hw).2.2.2
  omega

theorem laurent_noetherian : IsNoetherianRing (LaurentPlane.Ring K) := by
  let : Algebra.FiniteType K (LaurentPlane.Ring K) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing K _

theorem submodule_top_finite {ι : Type*} [Fintype ι]
    (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    Module.Finite K (N ⧸
      (((freeA ι).comap (N.subtype.restrictScalars K) ⊔
        (freeB ι).comap (N.subtype.restrictScalars K)) ⊔
        (freeC ι d).comap (N.subtype.restrictScalars K))) := by
  let : IsNoetherianRing (LaurentPlane.Ring K) := laurent_noetherian
  let : Module.Finite (LaurentPlane.Ring K) N := inferInstance
  apply LaurentPlane.quotient_finite (K := K) (M := N)
  · intro z hz x hx
    change (x : ι → LaurentPlane.Ring K) ∈ freeA ι at hx
    change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeA ι
    exact freeA_stable (K := K) (ι := ι) z hz (x : ι → LaurentPlane.Ring K) hx
  · intro z hz x hx
    change (x : ι → LaurentPlane.Ring K) ∈ freeB ι at hx
    change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeB ι
    exact freeB_stable (K := K) (ι := ι) z hz (x : ι → LaurentPlane.Ring K) hx
  · intro z hz x hx
    change (x : ι → LaurentPlane.Ring K) ∈ freeC ι d at hx
    change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeC ι d
    exact freeC_stable (K := K) (ι := ι) d z hz (x : ι → LaurentPlane.Ring K) hx
  · intro x
    exact freeA_clearing (x : ι → LaurentPlane.Ring K)
  · intro x
    exact freeB_clearing (x : ι → LaurentPlane.Ring K)
  · intro x
    exact freeC_clearing d (x : ι → LaurentPlane.Ring K)

end
end MaximalSeshadri.PlaneCech

end


end OAI
