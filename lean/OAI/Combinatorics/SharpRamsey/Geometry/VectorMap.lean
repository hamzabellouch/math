import Mathlib

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
namespace SharpLogRamsey.ProjectiveBaseChange
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
def vectorMap : (Fin n → K) →ₗ[K] (Fin n → E) where
  toFun v i := algebraMap K E (v i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp [Algebra.smul_def]

@[simp] lemma vectorMap_apply (v : Fin n → K) (i : Fin n) :
    vectorMap (K := K) (E := E) v i = algebraMap K E (v i) := rfl

lemma vectorMap_injective : Function.Injective (vectorMap (K := K) (E := E) (n := n)) := by
  intro v w h
  ext i
  exact (algebraMap K E).injective (congrFun h i)

def vectorSemi : (Fin n → K) →ₛₗ[algebraMap K E] (Fin n → E) where
  toFun v i := algebraMap K E (v i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

@[simp] lemma vectorSemi_apply (v : Fin n → K) (i : Fin n) :
    vectorSemi (K := K) (E := E) v i = algebraMap K E (v i) := rfl

lemma vectorSemi_injective : Function.Injective (vectorSemi (K := K) (E := E) (n := n)) :=
  vectorMap_injective

def pointMap : Projectivization K (Fin n → K) → Projectivization E (Fin n → E) :=
  Projectivization.map vectorSemi vectorSemi_injective

lemma pointMap_injective : Function.Injective (pointMap (K := K) (E := E) (n := n)) := by
  intro P Q h
  induction P using Projectivization.ind with | h p hp =>
    induction Q using Projectivization.ind with | h q hq =>
      simp only [pointMap, Projectivization.map_mk, Projectivization.mk_eq_mk_iff'] at h ⊢
      obtain ⟨c,hc⟩ := h
      obtain ⟨i,hi⟩ : ∃ i, q i ≠ 0 := by simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hq
      have hqi : algebraMap K E (q i) ≠ 0 := (map_ne_zero (algebraMap K E)).mpr hi
      have hci : c = algebraMap K E (p i / q i) := by
        have he := congrFun hc i
        simp only [Pi.smul_apply, smul_eq_mul, vectorSemi_apply] at he
        rw [map_div₀]
        exact (eq_div_iff hqi).mpr he
      refine ⟨p i / q i, ?_⟩
      ext j
      apply (algebraMap K E).injective
      have he := congrFun hc j
      simpa only [hci, map_mul, Pi.smul_apply, smul_eq_mul, vectorSemi_apply] using he

lemma coordinate_decomposition (v : Fin n → K) :
    (∑ i, v i • Pi.single i (1 : K)) = v := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

def extendDual (f : (Fin n → K) →ₗ[K] K) : (Fin n → E) →ₗ[E] E :=
  ∑ i, algebraMap K E (f (Pi.single i 1)) • LinearMap.proj i

lemma extendDual_map (f : (Fin n → K) →ₗ[K] K) (v : Fin n → K) :
    extendDual (E := E) f (vectorMap v) = algebraMap K E (f v) := by
  have hf : f v = ∑ i, v i*f (Pi.single i 1) := by
    conv_lhs => rw [← coordinate_decomposition v]
    simp
  rw [hf, map_sum]
  simp only [extendDual, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, vectorMap_apply, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

def extendSpace (W : Submodule K (Fin n → K)) : Submodule E (Fin n → E) :=
  Submodule.span E (vectorMap '' (W : Set (Fin n → K)))

theorem mem_extendSpace (W : Submodule K (Fin n → K)) (v : Fin n → K) :
    vectorMap (E := E) v ∈ extendSpace (E := E) W ↔ v ∈ W := by
  constructor
  · intro hv
    by_contra hn
    obtain ⟨f,hf,hfW⟩ := W.exists_dual_map_eq_bot_of_notMem hn inferInstance
    have hW : extendSpace (E := E) W ≤ LinearMap.ker (extendDual (E := E) f) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨w,hw,rfl⟩
      change extendDual f (vectorMap w) = 0
      rw [extendDual_map]
      have hh : f w = 0 := by
        have hm : f w ∈ W.map f := Submodule.mem_map.mpr ⟨w,hw,rfl⟩
        simpa only [hfW, Submodule.mem_bot] using hm
      simp [hh]
    have he := hW hv
    rw [LinearMap.mem_ker, extendDual_map] at he
    exact hf ((algebraMap K E).injective (by simpa using he))
  · intro hv
    exact Submodule.subset_span ⟨v,hv,rfl⟩

theorem rational_hyperplane (f : (Fin n → E) →ₗ[E] E) (hf : f ≠ 0) :
    ∃ g : (Fin n → K) →ₗ[K] K, g ≠ 0 ∧
      ∀ v, f (vectorMap (K := K) v) = 0 → g v = 0 := by
  have hex : ∃ i : Fin n, f (Pi.single i 1) ≠ 0 := by
    by_contra! h
    apply hf
    apply LinearMap.ext
    intro v
    rw [← coordinate_decomposition v, map_sum]
    simp [h]
  obtain ⟨i,hi⟩ := hex
  obtain ⟨z,hz⟩ := Module.Projective.exists_dual_ne_zero K hi
  let g : (Fin n → K) →ₗ[K] K := z.comp ((f.restrictScalars K).comp vectorMap)
  refine ⟨g, ?_, ?_⟩
  · intro hg
    apply hz
    have hh := LinearMap.congr_fun hg (Pi.single i 1)
    have hsingle : vectorMap (K := K) (E := E) (Pi.single i 1) = Pi.single i 1 := by
      ext j
      by_cases hj : j = i <;> simp [vectorMap, hj]
    change z (f (vectorMap (Pi.single i 1))) = 0 at hh
    rw [hsingle] at hh
    exact hh
  · intro v hv
    change z (f (vectorMap v)) = 0
    simp [hv]

end
end SharpLogRamsey.ProjectiveBaseChange
end

section

namespace SharpLogRamsey.ProjectiveAffineChart
open scoped BigOperators
open Finset Classical
noncomputable section
variable {E : Type*} [Field E] {n : ℕ}

def first (a : Fin n → E) : (Fin (n+1) → E) →ₗ[E] E :=
  LinearMap.proj 0 + ∑ i, a i • LinearMap.proj i.succ

lemma first_apply (a : Fin n → E) (v : Fin (n+1) → E) :
    first a v = v 0 + ∑ i, a i*v i.succ := by simp [first]

def lift (a x : Fin n → E) : Fin (n+1) → E :=
  Fin.cons (1-∑ i, a i*x i) x

@[simp] lemma lift_zero (a x : Fin n → E) : lift a x 0 = 1-∑ i, a i*x i := rfl
@[simp] lemma lift_succ (a x : Fin n → E) (i : Fin n) : lift a x i.succ = x i := rfl
@[simp] lemma first_lift (a x : Fin n → E) : first a (lift a x) = 1 := by
  rw [first_apply]
  simp

lemma lift_ne_zero (a x : Fin n → E) : lift a x ≠ 0 := by
  intro h
  have hh := first_lift a x
  rw [h, map_zero] at hh
  exact zero_ne_one hh

def chart (a : Fin n → E) (P : Projectivization E (Fin (n+1) → E)) : Fin n → E :=
  fun i => (first a P.rep)⁻¹ * P.rep i.succ

lemma normalize_eq_lift (a : Fin n → E) (P : Projectivization E (Fin (n+1) → E))
    (hP : first a P.rep ≠ 0) :
    (first a P.rep)⁻¹ • P.rep = lift a (chart a P) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (first a P.rep)⁻¹ * P.rep 0 = 1-∑ j, a j*((first a P.rep)⁻¹*P.rep j.succ)
    have ht : ∑ j, a j*((first a P.rep)⁻¹*P.rep j.succ) =
        (first a P.rep)⁻¹ * ∑ j, a j*P.rep j.succ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [ht]
    have hh : (first a P.rep)⁻¹ * (P.rep 0 + ∑ j, a j*P.rep j.succ) = 1 := by
      rw [← first_apply, inv_mul_cancel₀ hP]
    linear_combination hh
  · rfl

lemma mk_lift_chart (a : Fin n → E) (P : Projectivization E (Fin (n+1) → E))
    (hP : first a P.rep ≠ 0) :
    Projectivization.mk E (lift a (chart a P)) (lift_ne_zero _ _) = P := by
  calc
    _ = Projectivization.mk E P.rep P.rep_nonzero := by
      apply (Projectivization.mk_eq_mk_iff' E _ _ _ _).mpr
      exact ⟨(first a P.rep)⁻¹, normalize_eq_lift a P hP⟩
    _ = P := P.mk_rep

lemma chart_injOn (a : Fin n → E) :
    Set.InjOn (chart a) {P | first a P.rep ≠ 0} := by
  intro P hP Q hQ he
  rw [← mk_lift_chart a P hP, ← mk_lift_chart a Q hQ]
  congr 1
  exact congrArg (lift a) he

lemma lift_mem_iff (a : Fin n → E) (P : Projectivization E (Fin (n+1) → E))
    (hP : first a P.rep ≠ 0) (W : Submodule E (Fin (n+1) → E)) :
    lift a (chart a P) ∈ W ↔ P.submodule ≤ W := by
  have hp := congrArg Projectivization.submodule (mk_lift_chart a P hP)
  rw [Projectivization.submodule_mk] at hp
  rw [← hp, Submodule.span_singleton_le_iff_mem]

theorem lift_mem_span_pair (a x y z : Fin n → E) :
    lift a z ∈ Submodule.span E {lift a x, lift a y} ↔
      ∃ t : E, z = x+t • (y-x) := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨u,v,hh⟩
    have huv := congrArg (first a) hh
    simp only [map_add, map_smul, first_lift, smul_eq_mul, mul_one] at huv
    refine ⟨v, ?_⟩
    ext i
    have hi := congrFun hh i.succ
    simp only [Pi.add_apply, Pi.smul_apply, lift_succ, smul_eq_mul] at hi ⊢
    simp only [Pi.sub_apply]
    linear_combination -hi + x i * huv
  · rintro ⟨t,rfl⟩
    refine ⟨1-t,t,?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.add_apply, Pi.smul_apply, lift_zero, smul_eq_mul]
      simp only [Pi.sub_apply]
      simp_rw [mul_add, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have he : ∑ j, a j*(t*y j) = t*∑ j, a j*y j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hx : ∑ j, a j*(t*x j) = t*∑ j, a j*x j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he,hx]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, lift_succ, Pi.sub_apply, smul_eq_mul]
      ring

theorem exists_avoiding [Infinite E] (S : Finset (Projectivization E (Fin (n+1) → E))) :
    ∃ a : Fin n → E, ∀ P ∈ S, first a P.rep ≠ 0 := by
  classical
  let F (v : Fin (n+1) → E) : MvPolynomial (Fin n) E :=
    MvPolynomial.C (v 0) + ∑ i, MvPolynomial.C (v i.succ)*MvPolynomial.X i
  have hF (v : Fin (n+1) → E) (hv : v ≠ 0) : F v ≠ 0 := by
    intro h
    have h0 := congrArg (MvPolynomial.eval (fun _ => (0:E))) h
    simp [F] at h0
    have hs (i : Fin n) : v i.succ = 0 := by
      have hi := congrArg (MvPolynomial.eval (Pi.single i (1:E))) h
      simpa [F, h0, Pi.single_apply] using hi
    apply hv
    ext i
    exact Fin.cases h0 hs i
  have hprod : (∏ P ∈ S, F P.rep) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P _ => hF P.rep P.rep_nonzero)
  have hex : ∃ a : Fin n → E, MvPolynomial.eval a (∏ P ∈ S, F P.rep) ≠ 0 := by
    by_contra! hh
    apply hprod
    apply MvPolynomial.funext
    intro a
    simpa using hh a
  obtain ⟨a,ha⟩ := hex
  refine ⟨a, ?_⟩
  intro P hPS hP
  apply ha
  rw [map_prod]
  apply Finset.prod_eq_zero hPS
  simpa [F, first_apply, mul_comm] using hP

end
end SharpLogRamsey.ProjectiveAffineChart
end

section

namespace SharpLogRamsey.AffinePlaneCoefficients
open scoped BigOperators
open MvPolynomial Finset Classical
noncomputable section
variable {E : Type*} [Field E] {n : ℕ}

theorem degree_one_form (F : MvPolynomial (Fin n) E) (hF : F.totalDegree ≤ 1) :
    F = C (F.coeff 0)+∑ i, C (F.coeff (Finsupp.single i 1))*X i := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d = 0
  · subst d
    simp [coeff_C_mul, coeff_X]
  by_cases hi : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i,rfl⟩ := hi
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C,
      ite_eq_right (Ne.symm hd), zero_add, coeff_sum,
      coeff_C_mul, coeff_X]
    have he (j : Fin n) : ((Finsupp.single j 1 : Fin n →₀ ℕ) = Finsupp.single i 1) ↔ j = i :=
      (Finsupp.single_left_injective (by decide : (1:ℕ) ≠ 0)).eq_iff
    simp_rw [he]
    simp
  · have hc : F.coeff d = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      have hdeg : d.sum (fun (_ : Fin n) k => k) ≠ 0 := by
        exact fun hh => hd ((Finsupp.degree_eq_zero_iff d).mp hh)
      have hne : d.sum (fun (_ : Fin n) k => k) ≠ 1 := by
        exact fun hh => hi ((Finsupp.sum_eq_one_iff d).mp hh)
      have hh : 1 < d.sum (fun (_ : Fin n) k => k) := by omega
      exact hF.trans_lt hh
    rw [hc]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C,
      ite_eq_right (Ne.symm hd), zero_add, coeff_sum, coeff_C_mul, coeff_X]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun hh => hi ⟨i,hh.symm⟩), mul_zero]

lemma eval_degree_one (F : MvPolynomial (Fin n) E) (hF : F.totalDegree ≤ 1)
    (x : Fin n → E) :
    eval x F = F.coeff 0+∑ i, F.coeff (Finsupp.single i 1)*x i := by
  conv_lhs => rw [degree_one_form F hF]
  simp

end
end SharpLogRamsey.AffinePlaneCoefficients
end

section

namespace SharpLogRamsey.RationalAffineChart
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.ProjectiveBaseChange SharpLogRamsey.ProjectiveAffineChart
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

lemma map_submodule (P : Projectivization K (Fin n → K)) :
    (pointMap (E := E) P).submodule = Submodule.span E {vectorMap (E := E) P.rep} := by
  conv_lhs => rw [← P.mk_rep]
  simp only [pointMap, Projectivization.map_mk, Projectivization.submodule_mk]
  rfl

lemma map_submodule_le (P : Projectivization K (Fin n → K))
    (W : Submodule K (Fin n → K)) :
    (pointMap (E := E) P).submodule ≤ extendSpace (E := E) W ↔ P.submodule ≤ W := by
  rw [map_submodule, Submodule.span_singleton_le_iff_mem, mem_extendSpace,
    Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]

abbrev coord (a : Fin n → E) (P : Projectivization K (Fin (n+1) → K)) : Fin n → E :=
  chart a (pointMap (E := E) P)

def Avoids (a : Fin n → E) (P : Projectivization K (Fin (n+1) → K)) : Prop :=
  first a (pointMap (E := E) P).rep ≠ 0

lemma coord_injOn (a : Fin n → E) : Set.InjOn (coord (K := K) a) (Avoids (K := K) a) := by
  intro P hP Q hQ hh
  apply pointMap_injective (E := E)
  exact chart_injOn a hP hQ hh

lemma lift_coord_mem (a : Fin n → E) (P : Projectivization K (Fin (n+1) → K))
    (hP : Avoids a P) (W : Submodule K (Fin (n+1) → K)) :
    lift a (coord a P) ∈ extendSpace (E := E) W ↔ P.submodule ≤ W := by
  rw [lift_mem_iff a _ hP, map_submodule_le]

lemma lift_coord_kernel (a : Fin n → E) (P : Projectivization K (Fin (n+1) → K))
    (hP : Avoids a P) (f : (Fin (n+1) → E) →ₗ[E] E) :
    f (lift a (coord a P)) = 0 ↔ f (vectorMap (E := E) P.rep) = 0 := by
  change lift a (coord a P) ∈ f.ker ↔ vectorMap (E := E) P.rep ∈ f.ker
  rw [lift_mem_iff a _ hP, map_submodule, Submodule.span_singleton_le_iff_mem]

lemma exists_avoiding [Infinite E] (S : Finset (Projectivization K (Fin (n+1) → K))) :
    ∃ a : Fin n → E, ∀ P ∈ S, Avoids a P := by
  classical
  obtain ⟨a,ha⟩ := ProjectiveAffineChart.exists_avoiding (S.image (pointMap (E := E)))
  exact ⟨a,fun P hP => ha _ (mem_image.mpr ⟨P,hP,rfl⟩)⟩

def homogeneousPlane (a : Fin n → E) (F : MvPolynomial (Fin n) E) :
    (Fin (n+1) → E) →ₗ[E] E :=
  F.coeff 0 • first a +
    ∑ i, F.coeff (Finsupp.single i 1) • LinearMap.proj i.succ

lemma homogeneousPlane_lift (a x : Fin n → E) (F : MvPolynomial (Fin n) E)
    (hF : F.totalDegree ≤ 1) :
    homogeneousPlane a F (lift a x) = MvPolynomial.eval x F := by
  rw [AffinePlaneCoefficients.eval_degree_one F hF]
  simp [homogeneousPlane]

lemma homogeneousPlane_ne_zero [Infinite E] (a : Fin n → E) (F : MvPolynomial (Fin n) E)
    (hF : F.totalDegree = 1) : homogeneousPlane a F ≠ 0 := by
  intro hh
  have hpoly : F = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [← homogeneousPlane_lift a x F hF.le, hh]
    simp
  rw [hpoly, MvPolynomial.totalDegree_zero] at hF
  exact Nat.zero_ne_one hF

theorem plane_cap_transfer [Infinite E]
    (S : Finset (Projectivization K (Fin (n+1) → K))) (a : Fin n → E)
    (ha : ∀ P ∈ S, Avoids a P) (Kp : ℕ)
    (hcap : ∀ g : (Fin (n+1) → K) →ₗ[K] K, g ≠ 0 →
      (S.filter (fun P => g P.rep = 0)).card ≤ Kp)
    (F : MvPolynomial (Fin n) E) (hF : F.totalDegree = 1) :
    ((S.image (coord (K := K) a)).filter (fun x => MvPolynomial.eval x F = 0)).card ≤ Kp := by
  classical
  obtain ⟨g,hg,hfg⟩ := rational_hyperplane (K := K) (homogeneousPlane a F) (homogeneousPlane_ne_zero a F hF)
  let Z := S.filter (fun P => g P.rep = 0)
  have hsub : ((S.image (coord (K := K) a)).filter (fun x => MvPolynomial.eval x F = 0)) ⊆
      Z.image (coord (K := K) a) := by
    intro x hx
    obtain ⟨P,hPS,rfl⟩ := mem_image.mp (mem_filter.mp hx).1
    refine mem_image.mpr ⟨P,mem_filter.mpr ⟨hPS,?_⟩,rfl⟩
    apply hfg
    apply (lift_coord_kernel a P (ha P hPS) _).mp
    rw [homogeneousPlane_lift a _ F hF.le]
    exact (mem_filter.mp hx).2
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (hcap g hg))

end
end SharpLogRamsey.RationalAffineChart
end

section

namespace SharpLogRamsey.ProjectiveLineChart
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.ProjectiveBaseChange SharpLogRamsey.ProjectiveAffineChart
  SharpLogRamsey.RationalAffineChart
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

lemma extendSpace_span_pair (u v : Fin n → K) :
    extendSpace (E := E) (Submodule.span K {u,v}) =
      Submodule.span E {vectorMap (E := E) u, vectorMap (E := E) v} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hw
    apply Submodule.mem_span_pair.mpr
    refine ⟨algebraMap K E a,algebraMap K E b,?_⟩
    ext i
    simp [Algebra.smul_def]
  · apply Submodule.span_le.mpr
    intro w hw
    rcases hw with rfl | rfl
    · exact (mem_extendSpace _ _).mpr (Submodule.subset_span (Set.mem_insert _ _))
    · exact (mem_extendSpace _ _).mpr (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

end
end SharpLogRamsey.ProjectiveLineChart
end
end

end OAI
