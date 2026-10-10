import Mathlib

namespace OAI

/-! Binary sums, jet relations and their layer quotients. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
open scoped BigOperators Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

 
def binarySum (x y : R) (n : ℕ) : (Fin (n+1) → M) →ₗ[R] M :=
  ∑ i : Fin (n+1), (x^i.val * y^(n-i.val)) • LinearMap.proj i

lemma binarySum_apply (x y : R) (n : ℕ) (v : Fin (n+1) → M) :
    binarySum x y n v = ∑ i : Fin (n+1), (x^i.val * y^(n-i.val)) • v i := by
  simp [binarySum]

lemma binarySum_zero (x y : R) (v : Fin 1 → M) : binarySum x y 0 v = v 0 := by
  simp [binarySum_apply]

lemma binarySum_succ (x y : R) (n : ℕ) (v : Fin (n+2) → M) :
    binarySum x y (n+1) v = y^(n+1) • v 0 + x • binarySum x y n (fun i => v i.succ) := by
  rw [binarySum_apply, Fin.sum_univ_succ, binarySum_apply, Finset.smul_sum]
  simp only [Fin.val_zero, pow_zero, Nat.sub_zero, one_mul, Fin.val_succ, Nat.add_sub_add_right]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ, mul_comm (x^i.val) x, mul_assoc, mul_smul]

lemma binarySum_single_zero (x y : R) (n : ℕ) (v : M) :
    binarySum x y n (Pi.single 0 v) = y^n • v := by
  classical
  rw [binarySum_apply, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

 
def pairRelation (x y : R) : Submodule R M :=
  x • (⊤ : Submodule R M) ⊔ y • (⊤ : Submodule R M)

lemma x_smul_mem_pairRelation (x y : R) (v : M) : x • v ∈ pairRelation x y :=
  (show x • (⊤ : Submodule R M) ≤ pairRelation x y from le_sup_left)
    (Submodule.smul_mem_pointwise_smul v x ⊤ (by trivial))

lemma y_smul_mem_pairRelation (x y : R) (v : M) : y • v ∈ pairRelation x y :=
  (show y • (⊤ : Submodule R M) ≤ pairRelation x y from le_sup_right)
    (Submodule.smul_mem_pointwise_smul v y ⊤ (by trivial))

lemma regular_pair_y_pow (x y : R)
    (hy : ∀ v n : M, y • v = x • n → ∃ w : M, v = x • w)
    (j : ℕ) (v n : M) (h : y^j • v = x • n) : ∃ w : M, v = x • w := by
  induction j generalizing n with
  | zero => exact ⟨n, by simpa using h⟩
  | succ j ih =>
    obtain ⟨w,hw⟩ := hy (y^j • v) n (by simpa only [pow_succ', mul_smul] using h)
    exact ih w hw

 

theorem binarySum_kernel_coefficients (x y : R)
    (hx : Function.Injective (fun m : M => x • m))
    (hy : ∀ v n : M, y • v = x • n → ∃ w : M, v = x • w)
    (j : ℕ) (v : Fin (j+1) → M) (hv : binarySum x y j v = 0) :
    ∀ i, v i ∈ pairRelation x y := by
  classical
  induction j with
  | zero =>
    intro i
    have hi : i = 0 := Fin.ext (by omega)
    rw [binarySum_zero] at hv
    rw [hi, hv]
    exact Submodule.zero_mem _
  | succ j ih =>
    have h0 : y^(j+1) • v 0 = x • (-binarySum x y j (fun i => v i.succ)) := by
      rw [smul_neg]
      exact eq_neg_of_add_eq_zero_left ((binarySum_succ x y j v) ▸ hv)
    obtain ⟨w,hw⟩ := regular_pair_y_pow x y hy (j+1) (v 0) _ h0
    let v' : Fin (j+1) → M := (fun i => v i.succ) + Pi.single 0 (y • w)
    have hv' : binarySum x y j v' = 0 := by
      apply hx
      change x • binarySum x y j v' = x • (0 : M)
      rw [smul_zero]
      have he : x • binarySum x y j v' = binarySum x y (j+1) v := by
        change x • binarySum x y j ((fun i => v i.succ) + Pi.single 0 (y • w)) = _
        rw [map_add, binarySum_single_zero, smul_add, binarySum_succ, hw]
        rw [smul_comm (y^(j+1)) x, ← mul_smul (y^j) y w, ← pow_succ]
        exact add_comm _ _
      exact he.trans hv
    have hc := ih v' hv'
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hw]
      exact x_smul_mem_pairRelation x y w
    · have hu : (Pi.single (0 : Fin (j+1)) (y • w) : Fin (j+1) → M) i ∈ pairRelation x y := by
        by_cases hi : i = 0
        · subst i
          simpa using y_smul_mem_pairRelation x y w
        · simp [Pi.single_eq_of_ne hi]
      have hh := (pairRelation (M := M) x y).sub_mem (hc i) hu
      simpa only [v', Pi.add_apply, add_sub_cancel_right] using hh

lemma binarySum_succ_last (x y : R) (n : ℕ) (v : Fin (n+2) → M) :
    binarySum x y (n+1) v = y • binarySum x y n (fun i => v i.castSucc) + x^(n+1) • v (Fin.last _) := by
  rw [binarySum_apply, Fin.sum_univ_castSucc, binarySum_apply, Finset.smul_sum]
  simp only [Fin.val_last, Nat.sub_self, pow_zero, mul_one, Fin.val_castSucc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : n+1-i.val = (n-i.val)+1 := by omega
  rw [hi, pow_succ, ← mul_assoc, mul_comm (x^i.val * y^(n-i.val)) y, mul_smul]

lemma binarySum_prepend_zero (x y : R) (n : ℕ) (v : Fin (n+1) → M) :
    binarySum x y (n+1) (Fin.cons 0 v) = x • binarySum x y n v := by
  rw [binarySum_succ]
  simp

lemma binarySum_append_zero (x y : R) (n : ℕ) (v : Fin (n+1) → M) :
    binarySum x y (n+1) (Fin.snoc v 0) = y • binarySum x y n v := by
  rw [binarySum_succ_last]
  simp

 
def jetRelation (x y : R) (j : ℕ) : Submodule R M := (binarySum x y j).range

lemma jetRelation_zero (x y : R) : jetRelation (M := M) x y 0 = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro m
  exact ⟨fun _ => m, binarySum_zero x y _⟩

lemma mem_pairRelation (x y : R) (m : M) : m ∈ pairRelation x y ↔ ∃ a b : M, m = x • a + y • b := by
  constructor
  · intro h
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨a',_,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists a x ⊤).mp ha
    obtain ⟨b',_,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists b y ⊤).mp hb
    exact ⟨a',b',rfl⟩
  · rintro ⟨a,b,rfl⟩
    exact (pairRelation x y).add_mem (x_smul_mem_pairRelation x y a) (y_smul_mem_pairRelation x y b)

lemma jetRelation_one (x y : R) : jetRelation (M := M) x y 1 = pairRelation x y := by
  ext m
  constructor
  · rintro ⟨v,rfl⟩
    rw [binarySum_succ, binarySum_zero]
    simpa only [Nat.zero_add, pow_one] using
      (pairRelation x y).add_mem (y_smul_mem_pairRelation x y (v 0))
        (x_smul_mem_pairRelation x y (v (Fin.succ 0)))
  · intro hm
    obtain ⟨a,b,rfl⟩ := (mem_pairRelation x y m).mp hm
    refine ⟨Fin.cons b (fun _ => a), ?_⟩
    rw [binarySum_succ, binarySum_zero]
    simp [add_comm]

lemma jetRelation_succ_le (x y : R) (j : ℕ) :
    jetRelation (M := M) x y (j+1) ≤ jetRelation x y j := by
  rintro m ⟨v,rfl⟩
  refine ⟨x • (fun i => v i.succ) + Pi.single 0 (y • v 0), ?_⟩
  rw [map_add, map_smul, binarySum_single_zero, binarySum_succ, ← mul_smul, ← pow_succ]
  exact add_comm _ _

lemma binarySum_pairRelation (x y : R) (j : ℕ) (v : Fin (j+1) → M)
    (hv : ∀ i, v i ∈ pairRelation x y) :
    binarySum x y j v ∈ jetRelation x y (j+1) := by
  classical
  choose a b hab using fun i => (mem_pairRelation x y (v i)).mp (hv i)
  have he : v = x • a + y • b := funext hab
  rw [he, map_add, map_smul, map_smul]
  apply (jetRelation x y (j+1)).add_mem
  · exact ⟨Fin.cons 0 a, binarySum_prepend_zero x y j a⟩
  · exact ⟨Fin.snoc b 0, binarySum_append_zero x y j b⟩

 

theorem binarySum_mem_next_iff (x y : R)
    (hx : Function.Injective (fun m : M => x • m))
    (hy : ∀ v n : M, y • v = x • n → ∃ w : M, v = x • w)
    (j : ℕ) (v : Fin (j+1) → M) :
    binarySum x y j v ∈ jetRelation x y (j+1) ↔ ∀ i, v i ∈ pairRelation x y := by
  constructor
  · rintro ⟨w,hw⟩
    let c : Fin (j+1) → M := x • (fun i => w i.succ) + Pi.single 0 (y • w 0)
    have hc : ∀ i, c i ∈ pairRelation x y := by
      intro i
      apply (pairRelation x y).add_mem (x_smul_mem_pairRelation x y _)
      classical
      by_cases hi : i = 0
      · subst i
        simp only [Pi.single_eq_same]
        exact y_smul_mem_pairRelation x y _
      · simp [Pi.single_eq_of_ne hi]
    have hbc : binarySum x y j c = binarySum x y (j+1) w := by
      change binarySum x y j (x • (fun i => w i.succ) + Pi.single 0 (y • w 0)) = _
      rw [map_add, map_smul, binarySum_single_zero, binarySum_succ, ← mul_smul, ← pow_succ]
      exact add_comm _ _
    have hz : binarySum x y j (v-c) = 0 := by rw [map_sub, hbc, hw, sub_self]
    have hh := binarySum_kernel_coefficients x y hx hy j (v-c) hz
    intro i
    have hi := (pairRelation x y).add_mem (hh i) (hc i)
    simpa only [Pi.sub_apply, sub_add_cancel] using hi
  · exact binarySum_pairRelation x y j v

abbrev jetLayer (x y : R) (j : ℕ) :=
  (jetRelation (M := M) x y j) ⧸
    ((jetRelation x y (j+1)).comap (jetRelation x y j).subtype)

def jetLayerMap (x y : R) (j : ℕ) : (Fin (j+1) → M) →ₗ[R] jetLayer (M := M) x y j :=
  ((jetRelation x y (j+1)).comap (jetRelation x y j).subtype).mkQ.comp
    (binarySum x y j).rangeRestrict

lemma jetLayerMap_surjective (x y : R) (j : ℕ) :
    Function.Surjective (jetLayerMap (M := M) x y j) :=
  ((jetRelation x y (j+1)).comap (jetRelation x y j).subtype).mkQ_surjective.comp
    (by rintro ⟨m,v,rfl⟩; exact ⟨v,rfl⟩)

lemma jetLayerMap_eq_zero_iff (x y : R) (j : ℕ) (v : Fin (j+1) → M) :
    jetLayerMap x y j v = 0 ↔ binarySum x y j v ∈ jetRelation x y (j+1) := by
  exact Submodule.Quotient.mk_eq_zero _

def originCoefficientMap (x y : R) (j : ℕ) :
    (Fin (j+1) → M) →ₗ[R] (Fin (j+1) → (M ⧸ pairRelation (M := M) x y)) :=
  LinearMap.pi (fun i => (pairRelation x y).mkQ.comp (LinearMap.proj i))

lemma originCoefficientMap_surjective (x y : R) (j : ℕ) :
    Function.Surjective (originCoefficientMap (M := M) x y j) := by
  intro v
  choose w hw using fun i => (pairRelation (M := M) x y).mkQ_surjective (v i)
  exact ⟨w, funext hw⟩

lemma originCoefficientMap_eq_zero_iff (x y : R) (j : ℕ) (v : Fin (j+1) → M) :
    originCoefficientMap x y j v = 0 ↔ ∀ i, v i ∈ pairRelation x y := by
  constructor
  · intro h i
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrFun h i)
  · intro h
    ext i
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h i)

lemma jetLayerMap_ker (x y : R)
    (hx : Function.Injective (fun m : M => x • m))
    (hy : ∀ v n : M, y • v = x • n → ∃ w : M, v = x • w) (j : ℕ) :
    (jetLayerMap (M := M) x y j).ker = (originCoefficientMap x y j).ker := by
  ext v
  exact (jetLayerMap_eq_zero_iff x y j v).trans
    ((binarySum_mem_next_iff x y hx hy j v).trans
      (originCoefficientMap_eq_zero_iff x y j v).symm)

 

noncomputable def jetLayerEquiv (x y : R)
    (hx : Function.Injective (fun m : M => x • m))
    (hy : ∀ v n : M, y • v = x • n → ∃ w : M, v = x • w) (j : ℕ) :
    (Fin (j+1) → (M ⧸ pairRelation (M := M) x y)) ≃ₗ[R] jetLayer (M := M) x y j :=
  ((originCoefficientMap x y j).quotKerEquivOfSurjective
    (originCoefficientMap_surjective x y j)).symm ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ (jetLayerMap_ker x y hx hy j).symm) ≪≫ₗ
    (jetLayerMap x y j).quotKerEquivOfSurjective (jetLayerMap_surjective x y j)

lemma jetLayerEquiv_apply (x y : R)
    (hx : Function.Injective (fun m : M => x • m))
    (hy : ∀ v n : M, y • v = x • n → ∃ w : M, v = x • w)
    (j : ℕ) (v : Fin (j+1) → M) :
    jetLayerEquiv x y hx hy j (originCoefficientMap x y j v) = jetLayerMap x y j v := by
  simp only [jetLayerEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
end FiberFunctorProof
end

end OAI
