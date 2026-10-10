import OAI.NumberTheory.PowerFree.AdaptiveFibres

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

noncomputable def physicalBranchAllowance {r : ℕ} (n : ℕ) (d : ℕ → ℕ) (A h e : ℕ)
    (B : Fin r → Finset ℕ) (M b q : Fin r → ℕ) (i : Fin r) : ℕ :=
  (2^(B i).card * ((pathDegreeBudget n d A h e i.val+1)^n)^(B i).card *
    M i ^ (q i*(B i).card+n*b i)) *
  (kernelCountBudget (d i.val) h (pathDegreeBudget n d A h e i.val) *
    patchCountBudget n A h (kernelDegreeBudget (d i.val) h (pathDegreeBudget n d A h e i.val)))

theorem physical_forest_count {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (S : Finset G.points) (stop : G.points → ℕ) (M b q : Fin r → ℕ)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)) (T : ℕ)
    (hstart : ∀ z ∈ S, start z ∈ L) (hstop : ∀ z ∈ S, stop z ≤ r)
    (hM : ∀ i, 1 ≤ M i) (hprime : ∀ i, ∀ p ∈ B i, p.Prime)
    (hupper : ∀ i, ∀ p ∈ B i, p ≤ M i)
    (hdim : ∀ i : Fin r, ∀ z ∈ S, i.val < stop z →
      affineDimension (physicalStateAt (E := E) G d A h e start B i.val z).1 ≤ q i)
    (hbad : ∀ i : Fin r, ∀ z ∈ S, i.val < stop z →
      ((B i).filter fun p : ℕ => (p : ℤ) ∣ eval z.val
        (physicalStateAt (E := E) G d A h e start B i.val z).2.minor).card ≤ b i)
    (hterminal : ∀ i ≤ r, ∀ z ∈ S, stop z = i →
      (S.filter fun w => stop w = i ∧ physicalNode (E := E) G d A h e start B i w =
        physicalNode (E := E) G d A h e start B i z).card ≤ T) :
    S.card ≤ (∑ i ∈ Finset.range (r+1),
      L.length * ∏ j ∈ Finset.range i,
        if hj : j < r then physicalBranchAllowance n d A h e B M b q ⟨j,hj⟩ else 1) * T := by
  classical
  let node := physicalNode (E := E) G d A h e start B
  let C := fun j : ℕ => if hj : j < r then physicalBranchAllowance n d A h e B M b q ⟨j,hj⟩ else 1
  have hzero : ((activePoints S stop 0).image (node 0)).card ≤ L.length := by
    apply physical_initial_node_count G d A h e start B _ L
    intro z hz
    exact hstart z (Finset.mem_filter.mp hz).1
  have hchild : ∀ j < r, ∀ a ∈ (activePoints S stop (j+1)).image (node j),
      (((activePoints S stop (j+1)).filter fun z => node j z = a).image (node (j+1))).card ≤ C j := by
    intro j hj a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hz,hjstop⟩ := Finset.mem_filter.mp hz
    have hcount := physical_node_branch_bound G d A h e start hs B ⟨j,hj⟩ z
      ((activePoints S stop (j+1)).filter fun z' => node j z' = node j z)
      (fun w hw => (Finset.mem_filter.mp hw).2) (q ⟨j,hj⟩) (M ⟨j,hj⟩) (b ⟨j,hj⟩)
      (hM ⟨j,hj⟩) (hdim ⟨j,hj⟩ z hz (by change j < stop z; omega)) (hprime ⟨j,hj⟩) (hupper ⟨j,hj⟩)
      (fun w hw => hbad ⟨j,hj⟩ w (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
        (by change j < stop w; have := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2; omega))
    simpa only [C,dite_eq_left hj,physicalBranchAllowance] using hcount
  have hnodes := active_node_count S stop node C r L.length hzero hchild
  apply active_stopping_count S stop node (fun i => L.length*∏ j ∈ Finset.range i, C j) r T hstop hnodes
  intro i hi a ha
  by_cases he : ∃ z ∈ S, stop z = i ∧ node i z = a
  · obtain ⟨z,hz,hzi,rfl⟩ := he
    convert hterminal i hi z hz hzi using 1
  · have hempty : (S.filter fun z => stop z = i ∧ node i z = a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact he ⟨z,(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2⟩
    have hh := Finset.card_eq_zero.mpr hempty
    apply (show _ = 0 by convert hh using 1).le.trans
    exact Nat.zero_le _

end

open MvPolynomial
open scoped BigOperators
theorem pow_sum_dvd_det_of_row_dvd {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (q : R) (w : ι → ℕ) (A : Matrix ι ι R)
    (hA : ∀ i j, q ^ w i ∣ A i j) : q ^ (∑ i, w i) ∣ A.det := by
  choose B hB using hA
  have hmatrix : A = Matrix.of (fun i j => q ^ w i * B i j) := by
    ext i j
    exact hB i j
  rw [hmatrix]
  change q ^ (∑ i, w i) ∣ (Matrix.of (fun i j => q ^ w i * (Matrix.of B) i j)).det
  rw [Matrix.det_mul_column, Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_right _ _

theorem determinant_dvd_of_local_expansion
    {ι τ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [CommRing R]
    (q : R) (m : ℕ) (w : τ → ℕ)
    (v : τ → ι → R) (c : ι → τ → R)
    (hv : ∀ a j, q ^ w a ∣ v a j)
    (hm : ∀ r : ι → τ, Function.Injective r → m ≤ ∑ i, w (r i)) :
    q ^ m ∣ (Matrix.of (fun i j => ∑ a, c i a * v a j)).det := by
  classical
  let L := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R)
  have hexpand : (Matrix.of (fun i j => ∑ a, c i a * v a j)).det =
      ∑ r : ι → τ, (∏ i, c i (r i)) * (Matrix.of (fun i => v (r i))).det := by
    change L (fun i j => ∑ a, c i a * v a j) =
      ∑ r : ι → τ, (∏ i, c i (r i)) * L (fun i => v (r i))
    have h := L.toMultilinearMap.map_sum (fun i a => c i a • v a)
    simp only [AlternatingMap.coe_multilinearMap] at h
    have hfun : (fun i => ∑ a, c i a • v a) =
        (fun i j => ∑ a, c i a * v a j) := by
      funext i j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun] at h
    simpa only [AlternatingMap.map_smul_univ, smul_eq_mul] using h
  rw [hexpand]
  apply Finset.dvd_sum
  intro r _
  by_cases hr : Function.Injective r
  · apply dvd_mul_of_dvd_right
    exact (pow_dvd_pow q (hm r hr)).trans
      (pow_sum_dvd_det_of_row_dvd q (fun i => w (r i)) _ (fun i j => hv (r i) j))
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hr
    have hz : (Matrix.of (fun i => v (r i))).det = 0 := by
      exact L.map_eq_zero_of_eq (fun i => v (r i)) (congrArg v hab) hne
    rw [hz, mul_zero]
    exact dvd_zero _

theorem determinant_dvd_polynomial_eval {σ ι R : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] (q : R) (m : ℕ)
    (P : ι → MvPolynomial σ R) (x : ι → σ → R)
    (hx : ∀ j a, q ∣ x j a)
    (hm : ∀ r : ι → (σ →₀ ℕ), Function.Injective r →
      m ≤ ∑ i, (r i).sum (fun _ e => e)) :
    q ^ m ∣ (Matrix.of (fun i j => eval (x j) (P i))).det := by
  classical
  let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion (fun i => (P i).support)
  let v : s → ι → R := fun a j => a.val.prod (fun l e => x j l ^ e)
  let c : ι → s → R := fun i a => (P i).coeff a.val
  have hv : ∀ a j, q ^ a.val.sum (fun _ e => e) ∣ v a j := by
    intro a j
    dsimp [v, Finsupp.sum, Finsupp.prod]
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun l _ => pow_dvd_pow_of_dvd (hx j l) _)
  have hweight : ∀ r : ι → s, Function.Injective r →
      m ≤ ∑ i, (r i).val.sum (fun _ e => e) := by
    intro r hr
    exact hm (fun i => (r i).val) (Subtype.val_injective.comp hr)
  have heq : (Matrix.of (fun i j => eval (x j) (P i))) =
      Matrix.of (fun i j => ∑ a : s, c i a * v a j) := by
    ext i j
    simp only [Matrix.of_apply, c, v, Finsupp.prod, eval_eq]
    rw [Finset.sum_coe_sort s (fun a => (P i).coeff a * ∏ l ∈ a.support, x j l ^ a l)]
    apply Finset.sum_subset
    · intro a ha
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩
    · intro a _ ha
      have hz : (P i).coeff a = 0 := by
        simpa only [MvPolynomial.mem_support_iff, not_not] using ha
      simp only [hz, zero_mul]
  rw [heq]
  exact determinant_dvd_of_local_expansion q m (fun a : s => a.val.sum (fun _ e => e))
    v c hv hweight

theorem smooth_patch_determinant_zero {ι κ α R : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α] [CommRing R]
    (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    (hunit : IsUnit (implicitJacobian G).det)
    (q : R) (m : ℕ) (hqm : q ^ m = 0)
    (P : α → MvPolynomial (ι ⊕ κ) R) (x : α → ι → R) (y : α → κ → R)
    (hx : ∀ a i, q ∣ x a i) (hy : ∀ a j, q ∣ y a j)
    (hroot : ∀ a j, eval (Sum.elim (x a) (y a)) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))).det = 0 := by
  obtain ⟨F, _, hF⟩ := smooth_patch_polynomial_approx G hzero hunit q m
  have heval : ∀ a j, y a j = eval (x a) (F j) := by
    intro a j
    have h := hF (x a) (y a) (hx a) (hy a) (hroot a) j
    simpa only [pow_succ, hqm, zero_mul, zero_dvd_iff, sub_eq_zero] using h
  let Q : α → MvPolynomial ι R := fun a => eval₂ C (Sum.elim X F) (P a)
  have heq : (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))) =
      Matrix.of (fun a b => eval (x b) (Q a)) := by
    ext a b
    dsimp only [Q, Matrix.of_apply]
    rw [mv_eval_substitute]
    congr 2
    funext c
    cases c with
    | inl c => simp
    | inr c => exact heval b c
  rw [heq]
  have h := determinant_dvd_polynomial_eval q m Q x hx hm
  simpa only [hqm, zero_dvd_iff] using h

theorem mv_eval_map_at {σ R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : MvPolynomial σ R) (x : σ → R) :
    eval (fun i => φ (x i)) (map φ P) = φ (eval x P) := by
  rw [eval_map, eval₂_comp]
  rfl

theorem intCast_isUnit_prime_power {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) : IsUnit (a : ZMod (p ^ m)) := by
  have hn : ¬ p ∣ a.natAbs := by simpa only [← Int.natCast_dvd] using ha
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow hp hm).mpr hn
  have hu' : IsUnit (((a.natAbs : ℕ) : ℤ) : ZMod (p ^ m)) := by
    simpa only [Int.cast_natCast] using hu
  rw [Int.natCast_natAbs] at hu'
  rcases le_total 0 a with hpos | hneg
  · rwa [abs_of_nonneg hpos] at hu'
  · rw [abs_of_nonpos hneg, Int.cast_neg] at hu'
    simpa only [neg_neg] using hu'.neg

theorem smooth_patch_determinant_dvd {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    {p : ℕ} (hp : p.Prime) (hgood : ¬ (p : ℤ) ∣ (implicitJacobian G).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ)
    (x : α → ι → ℤ) (y : α → κ → ℤ)
    (hx : ∀ a i, (p : ℤ) ∣ x a i) (hy : ∀ a j, (p : ℤ) ∣ y a j)
    (hroot : ∀ a j, eval (Sum.elim (x a) (y a)) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (p : ℤ) ^ m ∣
      (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))).det := by
  classical
  by_cases hm0 : m = 0
  · simp [hm0]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  let R := ZMod (p ^ m)
  let φ : ℤ →+* R := Int.castRingHom R
  let G' : κ → MvPolynomial (ι ⊕ κ) R := fun j => map φ (G j)
  let P' : α → MvPolynomial (ι ⊕ κ) R := fun a => map φ (P a)
  let x' : α → ι → R := fun a i => φ (x a i)
  let y' : α → κ → R := fun a j => φ (y a j)
  have hzero' : ∀ j, eval (fun _ => 0) (G' j) = 0 := by
    intro j
    have h := mv_eval_map_at φ (G j) (fun _ => 0)
    simpa only [G', map_zero, hzero] using h
  have hjac : implicitJacobian G' = φ.mapMatrix (implicitJacobian G) := by
    ext j a
    change eval (fun _ => 0) (pderiv (Sum.inr a) (map φ (G j))) =
      φ (eval (fun _ => 0) (pderiv (Sum.inr a) (G j)))
    rw [pderiv_map]
    simpa only [map_zero] using mv_eval_map_at φ (pderiv (Sum.inr a) (G j)) (fun _ => 0)
  have hunit : IsUnit (implicitJacobian G').det := by
    rw [hjac, ← φ.map_det]
    exact intCast_isUnit_prime_power hp hmpos _ hgood
  have hqm : (φ (p : ℤ)) ^ m = 0 := by
    change (((p : ℕ) : ℤ) : ZMod (p ^ m)) ^ m = 0
    rw [Int.cast_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  have hx' : ∀ a i, φ (p : ℤ) ∣ x' a i := fun a i => map_dvd φ (hx a i)
  have hy' : ∀ a j, φ (p : ℤ) ∣ y' a j := fun a j => map_dvd φ (hy a j)
  have heval (a : α) (T : MvPolynomial (ι ⊕ κ) ℤ) :
      eval (Sum.elim (x' a) (y' a)) (map φ T) =
        φ (eval (Sum.elim (x a) (y a)) T) := by
    have hf : (fun i => φ ((Sum.elim (x a) (y a)) i)) = Sum.elim (x' a) (y' a) := by
      funext i
      cases i <;> rfl
    rw [← hf]
    exact mv_eval_map_at φ T _
  have hroot' : ∀ a j, eval (Sum.elim (x' a) (y' a)) (G' j) = 0 := by
    intro a j
    rw [show G' j = map φ (G j) from rfl, heval, hroot, map_zero]
  have hdet := smooth_patch_determinant_zero G' hzero' hunit (φ (p : ℤ)) m hqm
    P' x' y' hx' hy' hroot' hm
  let A : Matrix α α ℤ := Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))
  have hA : φ.mapMatrix A = Matrix.of (fun a b => eval (Sum.elim (x' b) (y' b)) (P' a)) := by
    ext a b
    exact (heval b (P a)).symm
  have hz : (A.det : ZMod (p ^ m)) = 0 := by
    change φ A.det = 0
    rw [φ.map_det, hA]
    exact hdet
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd A.det (p ^ m)).mp hz
  simpa only [Nat.cast_pow] using hd

noncomputable def shiftVariables {σ R : Type*} [CommRing R]
    (z : σ → R) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  eval₂ C (fun i => X i + C (z i)) P

theorem eval_shiftVariables {σ R : Type*} [CommRing R]
    (z x : σ → R) (P : MvPolynomial σ R) :
    eval x (shiftVariables z P) = eval (fun i => x i + z i) P := by
  rw [shiftVariables, mv_eval_substitute]
  simp only [map_add, eval_X, eval_C]

theorem pderiv_shiftVariables {σ R : Type*} [CommRing R]
    (z : σ → R) (P : MvPolynomial σ R) (i : σ) :
    pderiv i (shiftVariables z P) = shiftVariables z (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [shiftVariables]
  | add P Q hP hQ => simpa only [shiftVariables, eval₂_add, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P j hP =>
    by_cases h : i = j
    · subst j
      simpa only [shiftVariables, eval₂_mul, eval₂_X, pderiv_mul, map_add, pderiv_X,
        Pi.single_eq_same, pderiv_C, add_zero, mul_one, eval₂_add, eval₂_one, eval₂_zero,
        mul_zero, add_zero] using congrArg (fun T => T * (X i + C (z i)) +
          shiftVariables z P) hP
    · have h' : j ≠ i := Ne.symm h
      simpa only [shiftVariables, eval₂_mul, eval₂_X, pderiv_mul, map_add, pderiv_X,
        Pi.single_eq_of_ne h', pderiv_C, add_zero, mul_zero, eval₂_add, eval₂_one,
        eval₂_zero, mul_zero, add_zero] using congrArg (fun T => T * (X j + C (z j))) hP

theorem smooth_residue_determinant_dvd {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0)
    {p : ℕ} (hp : p.Prime)
    (hgood : ¬ (p : ℤ) ∣ (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : α → (ι ⊕ κ) → ℤ)
    (hw : ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (p : ℤ) ^ m ∣ (Matrix.of (fun a b => eval (w b) (P a))).det := by
  let G' : κ → MvPolynomial (ι ⊕ κ) ℤ := fun j => shiftVariables z (G j)
  let P' : α → MvPolynomial (ι ⊕ κ) ℤ := fun a => shiftVariables z (P a)
  let x : α → ι → ℤ := fun a i => w a (Sum.inl i) - z (Sum.inl i)
  let y : α → κ → ℤ := fun a j => w a (Sum.inr j) - z (Sum.inr j)
  have hzero : ∀ j, eval (fun _ => 0) (G' j) = 0 := by
    intro j
    simpa only [G', eval_shiftVariables, zero_add] using hz j
  have hjac : implicitJacobian G' =
      Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j))) := by
    ext j a
    simp only [implicitJacobian, Matrix.of_apply, G', pderiv_shiftVariables,
      eval_shiftVariables, zero_add]
  have hgood' : ¬ (p : ℤ) ∣ (implicitJacobian G').det := by rwa [hjac]
  have hs (a : α) (T : MvPolynomial (ι ⊕ κ) ℤ) :
      eval (Sum.elim (x a) (y a)) (shiftVariables z T) = eval (w a) T := by
    rw [eval_shiftVariables]
    congr 2
    funext i
    cases i <;> simp [x, y]
  have hx : ∀ a i, (p : ℤ) ∣ x a i := fun a i => hw a (Sum.inl i)
  have hy : ∀ a j, (p : ℤ) ∣ y a j := fun a j => hw a (Sum.inr j)
  have hroot' : ∀ a j, eval (Sum.elim (x a) (y a)) (G' j) = 0 := by
    intro a j
    rw [show G' j = shiftVariables z (G j) from rfl, hs, hroot]
  have h := smooth_patch_determinant_dvd G' hzero hp hgood' m P' x y hx hy hroot' hm
  have heq : (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P' a))) =
      Matrix.of (fun a b => eval (w b) (P a)) := by
    ext a b
    exact hs b (P a)
  rwa [heq] at h

theorem sum_min_eq_sum_card_filter {α : Type*} (s : Finset α) (f : α → ℕ) (t : ℕ) :
    ∑ a ∈ s, min (f a) t = ∑ j ∈ Finset.range t, (s.filter (fun a => j < f a)).card := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> omega

theorem monomial_order_lower_bound {ι α : Type*} [Fintype ι] [Fintype α]
    (r : α → (ι →₀ ℕ)) (hr : Function.Injective r) (t : ℕ) :
    t * Fintype.card α ≤ (∑ a, monomialOrder (r a)) +
      ∑ j ∈ Finset.range t, (j + Fintype.card ι).choose (Fintype.card ι) := by
  classical
  have hcard (j : ℕ) : (Finset.univ.filter (fun a => monomialOrder (r a) ≤ j)).card ≤
      (j + Fintype.card ι).choose (Fintype.card ι) := by
    rw [← card_monomialsUpTo ι j]
    exact Finset.card_le_card_of_injOn r
      (fun a ha => mem_monomialsUpTo.mpr (Finset.mem_filter.mp ha).2)
      (fun _ _ _ _ h => hr h)
  have hsum : t * Fintype.card α ≤
      (∑ a, monomialOrder (r a)) +
        ∑ j ∈ Finset.range t, (Finset.univ.filter (fun a => monomialOrder (r a) ≤ j)).card := by
    have hmin := sum_min_eq_sum_card_filter Finset.univ (fun a => monomialOrder (r a)) t
    have hcompl (j : ℕ) :
        (Finset.univ.filter (fun a => j < monomialOrder (r a))).card +
        (Finset.univ.filter (fun a => monomialOrder (r a) ≤ j)).card = Fintype.card α := by
      simpa only [not_lt, Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a => j < monomialOrder (r a))
    have heq : (∑ a, min (monomialOrder (r a)) t) +
        ∑ j ∈ Finset.range t, (Finset.univ.filter (fun a => monomialOrder (r a) ≤ j)).card =
        t * Fintype.card α := by
      rw [hmin, ← Finset.sum_add_distrib]
      simp_rw [hcompl]
      simp
    rw [← heq]
    exact Nat.add_le_add_right (Finset.sum_le_sum (fun a _ => min_le_left _ _)) _
  exact hsum.trans (Nat.add_le_add_left (Finset.sum_le_sum (fun j _ => hcard j)) _)

theorem sum_simplex_card (h t : ℕ) :
    (∑ j ∈ Finset.range t, (j + h).choose h) = (t + h).choose (h + 1) := by
  cases t with
  | zero => simp
  | succ t => simpa only [Nat.succ_eq_add_one, Nat.add_right_comm t 1 h]
      using Nat.sum_range_add_choose t h

theorem monomial_order_simplex_bound {ι α : Type*} [Fintype ι] [Fintype α]
    (r : α → (ι →₀ ℕ)) (hr : Function.Injective r) (t : ℕ)
    (hcard : (t + Fintype.card ι).choose (Fintype.card ι) ≤ Fintype.card α) :
    Fintype.card ι * (t + Fintype.card ι).choose (Fintype.card ι + 1) ≤
      ∑ a, monomialOrder (r a) := by
  have h := monomial_order_lower_bound r hr t
  rw [sum_simplex_card] at h
  have heq := Nat.choose_succ_right_eq (t + Fintype.card ι) (Fintype.card ι)
  rw [Nat.add_sub_cancel_right] at heq
  have hmul := Nat.mul_le_mul_left t hcard
  nlinarith

open Matrix

theorem det_row_sum {ι τ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [CommRing R]
    (v : τ → ι → R) (c : ι → τ → R) :
    (Matrix.of (fun i j => ∑ a, c i a * v a j)).det =
      ∑ r : ι → τ, (∏ i, c i (r i)) * (Matrix.of (fun i => v (r i))).det := by
  classical
  let L := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R)
  change L (fun i j => ∑ a, c i a * v a j) =
    ∑ r : ι → τ, (∏ i, c i (r i)) * L (fun i => v (r i))
  have h := L.toMultilinearMap.map_sum (fun i a => c i a • v a)
  simp only [AlternatingMap.coe_multilinearMap] at h
  have hfun : (fun i => ∑ a, c i a • v a) =
      (fun i j => ∑ a, c i a * v a j) := by
    funext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun] at h
  simpa only [AlternatingMap.map_smul_univ, smul_eq_mul] using h

theorem exists_relation_of_eval_dets_zero {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (v : ι → α → ℚ)
    (hdet : ∀ r : ι → α, (Matrix.of (fun i j => v i (r j))).det = 0) :
    ∃ c : ι → ℚ, c ≠ 0 ∧ ∀ a, ∑ i, c i * v i a = 0 := by
  classical
  let A : Matrix ι α ℚ := Matrix.of v
  have hgram : (A * A.transpose).det = 0 := by
    change (Matrix.of (fun i j => ∑ a, v i a * v j a)).det = 0
    rw [det_row_sum (fun a j => v j a) v]
    apply Finset.sum_eq_zero
    intro r _
    have hr : (Matrix.of (fun i j => v j (r i))).det = 0 := by
      change ((Matrix.of (fun i j => v i (r j))).transpose).det = 0
      rw [Matrix.det_transpose, hdet r]
    rw [hr, mul_zero]
  obtain ⟨c, hc, hzc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hgram
  refine ⟨c, hc, ?_⟩
  have hzero : A.transpose *ᵥ c = 0 := by
    rw [← Matrix.mulVec_mulVec] at hzc
    have h := congrArg (fun v => dotProduct c v) hzc
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_zero, dotProduct_self_eq_zero] at h
    exact h
  intro a
  have h := congrFun hzero a
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply,
    A, Matrix.of_apply, mul_comm] using h

open Matrix

theorem smooth_residue_determinant_simplex {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0)
    {p : ℕ} (hp : p.Prime)
    (hgood : ¬ (p : ℤ) ∣ (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (t : ℕ) (hcard : (t + Fintype.card ι).choose (Fintype.card ι) ≤ Fintype.card α)
    (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : α → (ι ⊕ κ) → ℤ)
    (hw : ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0) :
    (p : ℤ) ^ (Fintype.card ι * (t + Fintype.card ι).choose (Fintype.card ι + 1)) ∣
      (Matrix.of (fun a b => eval (w b) (P a))).det := by
  apply smooth_residue_determinant_dvd G z hz hp hgood _ P w hw hroot
  intro r hr
  exact monomial_order_simplex_bound r hr t hcard

theorem simultaneous_residue_determinant_dvd {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0) (Q : Finset ℕ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p : ℤ) ∣
      (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : α → (ι ⊕ κ) → ℤ)
    (hw : ∀ p ∈ Q, ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (∏ p ∈ Q, (p : ℤ)) ^ m ∣ (Matrix.of (fun a b => eval (w b) (P a))).det := by
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_nat_coprime]
    simpa only [Int.natAbs_natCast] using (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  · intro p hp
    exact smooth_residue_determinant_dvd G z hz (hprime p hp) (hgood p hp) m P w
      (hw p hp) hroot hm

theorem simultaneous_residue_determinant_zero {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0) (Q : Finset ℕ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p : ℤ) ∣
      (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : α → (ι ⊕ κ) → ℤ)
    (hw : ∀ p ∈ Q, ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e))
    (B : α → ℝ) (hB : ∀ a b, |(eval (w b) (P a) : ℝ)| ≤ B a)
    (hlt : (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, B a < (∏ p ∈ Q, (p : ℝ)) ^ m) :
    (Matrix.of (fun a b => eval (w b) (P a))).det = 0 := by
  let A : Matrix α α ℤ := Matrix.of (fun a b => eval (w b) (P a))
  have hdiv : (∏ p ∈ Q, (p : ℤ)) ^ m ∣ A.det :=
    simultaneous_residue_determinant_dvd G z hz Q hprime hgood m P w hw hroot hm
  apply Int.eq_zero_of_abs_lt_dvd hdiv
  have hB' := det_abs_le_row_product ((Int.castRingHom ℝ).mapMatrix A) B hB
  rw [← (Int.castRingHom ℝ).map_det] at hB'
  change |(A.det : ℝ)| ≤ _ at hB'
  have h := hB'.trans_lt hlt
  apply (Int.cast_lt (R := ℝ)).mp
  simpa only [Int.cast_abs, Int.cast_pow, Int.cast_prod, Int.cast_natCast] using h

theorem simultaneous_residue_relation {ι κ α β : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [Fintype β] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0) (Q : Finset ℕ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p : ℤ) ∣
      (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : β → (ι ⊕ κ) → ℤ)
    (hw : ∀ p ∈ Q, ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e))
    (B : α → ℝ) (hB : ∀ a b, |(eval (w b) (P a) : ℝ)| ≤ B a)
    (hlt : (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, B a < (∏ p ∈ Q, (p : ℝ)) ^ m) :
    ∃ c : α → ℚ, c ≠ 0 ∧ ∀ b, ∑ a, c a * (eval (w b) (P a) : ℚ) = 0 := by
  apply exists_relation_of_eval_dets_zero
  intro r
  have hzero := simultaneous_residue_determinant_zero G z hz Q hprime hgood m P
    (fun a => w (r a)) (fun p hp a i => hw p hp (r a) i)
    (fun a j => hroot (r a) j) hm B (fun a b => hB a (r b)) hlt
  have h := congrArg (Int.castRingHom ℚ) hzero
  rw [(Int.castRingHom ℚ).map_det, map_zero] at h
  exact h

end QuarticPowerFree

end OAI
