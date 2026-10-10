import OAI.Geometry.Coboundary.Windows

namespace OAI

/-!
Bounded and full chambers, codistance, descent cores, and their affine-window descriptions.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
lemma powerLinear_injective (m : ℕ) : Function.Injective (powerLinear (K := K) (N := N) m) := by
  intro v w h
  funext i
  have hi := congrFun h i
  change (Polynomial.X^m : K[X]) * v i = (Polynomial.X^m : K[X]) * w i at hi
  exact mul_left_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) hi
lemma powerShift_strictMono (m : ℕ) : StrictMono (fun A : Submodule K[X] (V K N) => powerShift A m) :=
  Submodule.map_strictMono_of_injective (powerLinear_injective m)
lemma powerShift_mono (m : ℕ) : Monotone (fun A : Submodule K[X] (V K N) => powerShift A m) :=
  (powerShift_strictMono m).monotone

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))
def nextIndex (_C : ResidueChamber (K := K) (N := N)) (hN : 0 < N) : Fin (N+1) := ⟨1,by omega⟩
noncomputable def rotateStage (hN : 0 < N) (r : Fin (N+1)) : Submodule K[X] (V K N) :=
  if hr : r.val < N then C.stage ⟨r.val+1,by omega⟩
  else powerShift (C.stage (C.nextIndex hN)) 1
lemma rotateStage_castSucc (hN : 0 < N) (r : Fin N) :
    C.rotateStage hN r.castSucc = C.stage r.succ := by
  apply (dite_eq_left r.isLt).trans
  rfl
lemma rotateStage_last (hN : 0 < N) :
    C.rotateStage hN (Fin.last N) = powerShift (C.stage (C.nextIndex hN)) 1 := by
  exact dite_eq_right (Nat.lt_irrefl N)
lemma rotateStage_has (hN : 0 < N) (r : Fin (N+1)) : HasPivots (C.rotateStage hN r) := by
  unfold rotateStage
  split_ifs
  · exact C.hasStage _
  · exact powerShift_hasPivots _ (C.hasStage _) 1
lemma rotateStage_strict (hN : 0 < N) : StrictAnti (C.rotateStage hN) := by
  intro r s hrs
  have hr : r.val < N := by have := s.isLt; change r.val < s.val at hrs; omega
  rw [show C.rotateStage hN r = C.stage ⟨r.val+1,by omega⟩ from dite_eq_left hr]
  unfold rotateStage
  split_ifs with hs
  · exact C.strict (show (⟨r.val+1,by omega⟩ : Fin (N+1)) < ⟨s.val+1,by omega⟩ by
      change r.val < s.val at hrs; change r.val+1 < s.val+1; omega)
  · have hlt : powerShift (C.stage (C.nextIndex hN)) 1 < powerShift C.top 1 := by
      rw [← C.initial]
      apply powerShift_strictMono 1
      exact C.strict (show (0 : Fin (N+1)) < C.nextIndex hN from by change 0 < 1; omega)
    rw [← C.terminal] at hlt
    exact hlt.trans_le (C.strict.antitone (Fin.le_last _))
lemma rotateStage_lower (hN : 0 < N) (r : Fin (N+1)) :
    powerShift (C.stage (C.nextIndex hN)) 1 ≤ C.rotateStage hN r := by
  unfold rotateStage
  split_ifs
  · apply le_trans _ (C.lower _)
    apply powerShift_mono 1
    rw [← C.initial]
    exact C.strict.antitone (Fin.zero_le _)
  · exact le_rfl
noncomputable def rotate (hN : 0 < N) : ResidueChamber (K := K) (N := N) where
  top := C.stage (C.nextIndex hN)
  hasTop := C.hasStage _
  stage := C.rotateStage hN
  hasStage := C.rotateStage_has hN
  strict := C.rotateStage_strict hN
  initial := by
    apply (dite_eq_left hN).trans
    rfl
  lower := C.rotateStage_lower hN

lemma step_degree (r : Fin N) (i : Fin N) :
    pivotDegree (C.stage r.succ) (C.hasStage r.succ) i =
      pivotDegree (C.stage r.castSucc) (C.hasStage r.castSucc) i +
        if i = C.word r then 1 else 0 := by
  classical
  rw [C.stage_degree,C.stage_degree]
  by_cases he : i = C.word r
  · subst i
    simp
  · have hne : (C.word.symm i).val ≠ r.val := by
      intro hh
      apply he
      have hi := congrArg C.word (Fin.ext hh)
      simpa only [Equiv.apply_symm_apply] using hi
    simp only [Fin.val_succ,Fin.val_castSucc,ite_eq_right he]
    split_ifs <;> omega
lemma word_eq_iff (r : Fin N) (i : Fin N) : C.word r = i ↔
    pivotDegree (C.stage r.castSucc) (C.hasStage r.castSucc) i <
      pivotDegree (C.stage r.succ) (C.hasStage r.succ) i := by
  rw [C.step_degree]
  by_cases hi : i = C.word r
  · simp [hi]
  · simp [hi,Ne.symm hi]

variable {M : ℕ}
lemma rotate_word (C : ResidueChamber (K := K) (N := M+1)) (r : Fin (M+1)) :
    (C.rotate (Nat.zero_lt_succ M)).word r = C.word (finRotate (M+1) r) := by
  classical
  apply ((C.rotate (Nat.zero_lt_succ M)).word_eq_iff r _).mpr
  by_cases hr : r.val < M
  · have he : finRotate (M+1) r = ⟨r.val+1,by omega⟩ := finRotate_of_lt hr
    rw [he]
    let r' : Fin (M+1) := ⟨r.val+1,by omega⟩
    change pivotDegree (C.rotateStage (Nat.zero_lt_succ M) r.castSucc) _ (C.word r') <
      pivotDegree (C.rotateStage (Nat.zero_lt_succ M) r.succ) _ (C.word r')
    have hs0 : C.rotateStage (Nat.zero_lt_succ M) r.castSucc = C.stage r'.castSucc := by
      exact C.rotateStage_castSucc _ r
    have hs1 : C.rotateStage (Nat.zero_lt_succ M) r.succ = C.stage r'.succ := by
      exact dite_eq_left (show r.succ.val < M+1 from by simp only [Fin.val_succ]; omega)
    simp only [hs0,hs1]
    exact (C.word_eq_iff r' _).mp rfl
  · have hr' : r = Fin.last M := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
    subst r
    rw [finRotate_last]
    change pivotDegree (C.rotateStage (Nat.zero_lt_succ M) (Fin.last M).castSucc) _ (C.word 0) <
      pivotDegree (C.rotateStage (Nat.zero_lt_succ M) (Fin.last M).succ) _ (C.word 0)
    have he0 : C.rotateStage (Nat.zero_lt_succ M) (Fin.last M).castSucc = powerShift C.top 1 := by
      rw [C.rotateStage_castSucc]
      exact C.terminal
    have he1 : C.rotateStage (Nat.zero_lt_succ M) (Fin.last M).succ =
        powerShift (C.stage (C.nextIndex (Nat.zero_lt_succ M))) 1 := C.rotateStage_last _
    simp only [he0,he1]
    have hp0 := pivotDegree_powerShift C.top C.hasTop 1 (C.word 0)
    have hp1 := pivotDegree_powerShift (C.stage (C.nextIndex (Nat.zero_lt_succ M)))
      (C.hasStage _) 1 (C.word 0)
    simp only [nextIndex] at hp1 ⊢
    have hh := C.stage_degree (C.nextIndex (Nat.zero_lt_succ M)) (C.word 0)
    simp only [Equiv.symm_apply_apply,nextIndex,Fin.val_mk,Fin.val_zero,
      show (0:ℕ) < 1 by omega,ite_true] at hh
    omega

lemma rotate_window_castSucc (C : ResidueChamber (K := K) (N := M+1)) (r : Fin M) :
    (C.rotate (Nat.zero_lt_succ M)).window r.castSucc = C.window r.succ := by
  have he : finRotate (M+1) r.castSucc = r.succ := finRotate_of_lt r.isLt
  simp only [window,C.rotate_word,he]
  change (((M+1)*pivotDegree (C.stage (C.nextIndex (Nat.zero_lt_succ M))) (C.hasStage _) (C.word r.succ)+
    (C.word r.succ).val : ℕ) : ℤ) = _
  rw [C.stage_degree]
  simp only [Equiv.symm_apply_apply,nextIndex,Fin.val_mk,Fin.val_succ,show ¬r.val+1 < 1 by omega,ite_false,Nat.add_zero]
lemma rotate_window_last (C : ResidueChamber (K := K) (N := M+1)) :
    (C.rotate (Nat.zero_lt_succ M)).window (Fin.last M) = C.window 0 + (M+1) := by
  simp only [window,C.rotate_word,finRotate_last]
  change (((M+1)*pivotDegree (C.stage (C.nextIndex (Nat.zero_lt_succ M))) (C.hasStage _) (C.word 0)+
    (C.word 0).val : ℕ) : ℤ) = _
  rw [C.stage_degree]
  simp only [Equiv.symm_apply_apply,nextIndex,Fin.val_mk,Fin.val_zero,show (0:ℕ) < 1 by omega,ite_true]
  push_cast
  ring
lemma window_mod (_ : 0 < N) (r : Fin N) : C.window r % N = (C.word r).val := by
  unfold window
  push_cast
  have h0 : 0 ≤ ((C.word r).val : ℤ) := Int.natCast_nonneg _
  have hlt : ((C.word r).val : ℤ) < N := by exact_mod_cast (C.word r).isLt
  simp only [Int.add_emod,Int.mul_emod_right,Int.zero_add,Int.emod_eq_of_lt h0 hlt]

theorem rotate_length (C : ResidueChamber (K := K) (N := M+1)) :
    (C.rotate (Nat.zero_lt_succ M)).length = C.length := by
  unfold length
  rw [List.ofFn_succ',List.concat_eq_append]
  simp only [C.rotate_window_castSucc,C.rotate_window_last]
  rw [List.ofFn_succ (f := C.window)]
  apply AffineWindow.inversion_rotate (Nat.zero_lt_succ M)
  intro b hb
  obtain ⟨r,hr⟩ := List.mem_ofFn.mp hb
  rw [← hr,C.window_mod (Nat.zero_lt_succ M),C.window_mod (Nat.zero_lt_succ M)]
  intro he
  have hh : (0 : Fin (M+1)) = r.succ := C.word.injective (Fin.ext (by exact_mod_cast he))
  have hv := congrArg Fin.val hh
  simp only [Fin.val_zero,Fin.val_succ] at hv
  omega

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma leading_combination_max (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (f : Fin N → K[X])
    (i : Fin N) (hfi : f i ≠ 0)
    (hmax : ∀ j, f j ≠ 0 → N*(a j+(f j).natDegree)+j.val ≤ N*(a i+(f i).natDegree)+i.val) :
    Leading (∑ j, f j • b j) i (a i+(f i).natDegree) := by
  classical
  have hi := leading_mul (hb i) (f i) hfi
  constructor
  · have hh : ((∑ j, f j • b j) i).coeff (a i+(f i).natDegree) =
        ((f i • b i) i).coeff (a i+(f i).natDegree) := by
      simp only [Finset.sum_apply,Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_cases hj : f j = 0
        · simp [hj]
        · apply (leading_mul (hb j) (f j) hj).2
          have hle := hmax j hj
          have hne : N*(a j+(f j).natDegree)+j.val ≠ N*(a i+(f i).natDegree)+i.val := by
            intro he
            exact hji (weight_injective he).1
          omega
      · simp
    exact hh ▸ hi.1
  · intro k e he
    simp only [Finset.sum_apply,Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : f j = 0
    · simp [hj]
    · exact (leading_mul (hb j) (f j) hj).2 k e (lt_of_le_of_lt (hmax j hj) he)

lemma combination_lowest_pivot (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (f : Fin N → K[X]) (i : Fin N)
    (hl : Leading (∑ j, f j • b j) i (a i)) :
    f i ≠ 0 ∧ (f i).natDegree = 0 ∧
      ∀ j, N*a i+i.val < N*a j+j.val → f j = 0 := by
  classical
  let s := Finset.univ.filter (fun j => f j ≠ 0)
  have hs : s.Nonempty := by
    by_contra hn
    have hz : ∀ j, f j = 0 := by
      intro j
      by_contra hj
      exact hn ⟨j,by simp [s,hj]⟩
    have he : (∑ j, f j • b j) = 0 := by simp [hz]
    exact leading_ne_zero hl he
  let w (j : Fin N) := N*(a j+(f j).natDegree)+j.val
  obtain ⟨j,hjs,hmax⟩ := Finset.exists_max_image s w hs
  have hj : f j ≠ 0 := (Finset.mem_filter.mp hjs).2
  have hl' := leading_combination_max b a hb f j hj
    (fun k hk => hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩))
  obtain ⟨hji,he⟩ := leading_unique hl' hl
  subst j
  have hdegree : (f i).natDegree = 0 := by omega
  refine ⟨hj,hdegree,?_⟩
  intro j hlt
  by_contra hjz
  have hh := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjz⟩)
  dsimp only [w] at hh
  rw [hdegree,Nat.add_zero] at hh
  have hh' := Nat.mul_le_mul_left N (Nat.le_add_right (a j) (f j).natDegree)
  omega

lemma lowest_vector_mem_panel (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i))
    (A C D : Submodule K[X] (V K N))
    (hspan : Submodule.span K[X] (Set.range b) = A)
    (hCD : C ≤ D) (hDA : D ≤ A)
    (i j : Fin N) (hij : N*a i+i.val < N*a j+j.val)
    (hothers : ∀ k, k ≠ i → k ≠ j → b k ∈ C)
    (v : V K N) (hv : v ∈ D) (hl : Leading v i (a i)) : b i ∈ D := by
  classical
  have hvA : v ∈ Submodule.span K[X] (Set.range b) := by rw [hspan]; exact hDA hv
  obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp hvA
  have hlead : Leading (∑ k, f k • b k) i (a i) := hf.symm ▸ hl
  obtain ⟨hfi,hdeg,hzero⟩ := combination_lowest_pivot b a hb f i hlead
  have hfj := hzero j hij
  have hrest : (∑ k ∈ Finset.univ.erase i, f k • b k) ∈ D := by
    apply D.sum_mem
    intro k hk
    have hki := (Finset.mem_erase.mp hk).1
    by_cases hkj : k = j
    · subst k; simp [hfj]
    · exact D.smul_mem _ (hCD (hothers k hki hkj))
  have hsum := Finset.sum_erase_add Finset.univ (fun k => f k • b k) (Finset.mem_univ i)
  have hfv : f i • b i ∈ D := by
    have ht := D.sub_mem hv hrest
    rw [← hf,← hsum] at ht
    simpa only [add_sub_cancel_left] using ht
  have heq := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hconst : (f i).coeff 0 ≠ 0 := by
    intro hz
    apply hfi
    rw [heq,hz,Polynomial.C_0]
  have ht := D.smul_mem (Polynomial.C ((f i).coeff 0)⁻¹) hfv
  rw [smul_smul,heq,Polynomial.coeff_C_zero,← Polynomial.C_mul,inv_mul_cancel₀ hconst,Polynomial.C_1,one_smul] at ht
  exact ht

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma combination_pivot_degree (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (f : Fin N → K[X]) (i : Fin N) (e : ℕ)
    (hl : Leading (∑ j, f j • b j) i e) : f i ≠ 0 ∧ e = a i+(f i).natDegree := by
  classical
  let s := Finset.univ.filter (fun j => f j ≠ 0)
  have hs : s.Nonempty := by
    by_contra hn
    have hz : ∀ j, f j = 0 := by
      intro j
      by_contra hj
      exact hn ⟨j,by simp [s,hj]⟩
    have he : (∑ j, f j • b j) = 0 := by simp [hz]
    exact leading_ne_zero hl he
  let w (j : Fin N) := N*(a j+(f j).natDegree)+j.val
  obtain ⟨j,hjs,hmax⟩ := Finset.exists_max_image s w hs
  have hj : f j ≠ 0 := (Finset.mem_filter.mp hjs).2
  have hl' := leading_combination_max b a hb f j hj
    (fun k hk => hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩))
  obtain ⟨hji,he⟩ := leading_unique hl' hl
  subst j
  exact ⟨hj,he.symm⟩

lemma span_hasPivots (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) :
    HasPivots (Submodule.span K[X] (Set.range b)) :=
  fun i => ⟨a i,b i,Submodule.subset_span ⟨i,rfl⟩,hb i⟩

lemma span_pivotDegree (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (i : Fin N) :
    pivotDegree (Submodule.span K[X] (Set.range b)) (span_hasPivots b a hb) i = a i := by
  let hA := span_hasPivots b a hb
  apply le_antisymm
  · exact pivotDegree_min _ hA i (Submodule.subset_span ⟨i,rfl⟩) (hb i)
  · obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp (pivot_mem _ hA i)
    have hl : Leading (∑ j, f j • b j) i (pivotDegree _ hA i) := hf.symm ▸ pivot_leading _ hA i
    have he := (combination_pivot_degree b a hb f i _ hl).2
    omega

noncomputable def diagonalFamily (b : Fin N → V K N) (s : Finset (Fin N)) (i : Fin N) : V K N :=
  if i ∈ s then (Polynomial.X : K[X]) • b i else b i

noncomputable def diagonalModule (b : Fin N → V K N) (s : Finset (Fin N)) : Submodule K[X] (V K N) :=
  Submodule.span K[X] (Set.range (diagonalFamily b s))

lemma diagonal_leading (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (s : Finset (Fin N)) (i : Fin N) :
    Leading (diagonalFamily b s i) i (a i + if i ∈ s then 1 else 0) := by
  classical
  dsimp [diagonalFamily]
  split_ifs
  · simpa using leading_X_pow (hb i) 1
  · simpa using hb i

lemma diagonal_hasPivots (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (s : Finset (Fin N)) :
    HasPivots (diagonalModule b s) :=
  span_hasPivots (diagonalFamily b s) _ (diagonal_leading b a hb s)

lemma diagonal_pivotDegree (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (s : Finset (Fin N)) (i : Fin N) :
    pivotDegree (diagonalModule b s) (diagonal_hasPivots b a hb s) i =
      a i + if i ∈ s then 1 else 0 :=
  span_pivotDegree _ _ (diagonal_leading b a hb s) i

lemma diagonal_antitone (b : Fin N → V K N) {s t : Finset (Fin N)} (hst : s ⊆ t) :
    diagonalModule b t ≤ diagonalModule b s := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  by_cases his : i ∈ s
  · have hit := hst his
    exact Submodule.subset_span ⟨i,by simp [diagonalFamily,his,hit]⟩
  · by_cases hit : i ∈ t
    · have hi : b i ∈ diagonalModule b s :=
        Submodule.subset_span ⟨i,by simp [diagonalFamily,his]⟩
      simpa [diagonalFamily,hit] using (diagonalModule b s).smul_mem Polynomial.X hi
    · exact Submodule.subset_span ⟨i,by simp [diagonalFamily,his,hit]⟩

lemma diagonal_le_span (b : Fin N → V K N) (s : Finset (Fin N)) :
    diagonalModule b s ≤ Submodule.span K[X] (Set.range b) := by
  have hh := diagonal_antitone b (Finset.empty_subset s)
  have he : diagonalFamily b ∅ = b := by funext i; simp [diagonalFamily]
  simpa only [diagonalModule,he] using hh

lemma diagonal_eq_span (b : Fin N → V K N) :
    diagonalModule b ∅ = Submodule.span K[X] (Set.range b) := by
  have he : diagonalFamily b ∅ = b := by funext i; simp [diagonalFamily]
  simp only [diagonalModule,he]

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma diagonal_eq_powerShift (b : Fin N → V K N) :
    diagonalModule b Finset.univ = powerShift (Submodule.span K[X] (Set.range b)) 1 := by
  classical
  unfold diagonalModule powerShift
  rw [Submodule.map_span,← Set.range_comp]
  congr 2
  funext i
  simp [diagonalFamily,powerLinear]

lemma diagonal_injective (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) : Function.Injective (diagonalModule b) := by
  classical
  intro s t he
  ext i
  have hs := diagonal_pivotDegree b a hb s i
  have ht := diagonal_pivotDegree b a hb t i
  simp only [he] at hs
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;> simp_all

lemma diagonal_strictAnti (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) : StrictAnti (diagonalModule b) := by
  intro s t hst
  exact lt_of_le_of_ne (diagonal_antitone b hst.le)
    (fun he => hst.ne ((diagonal_injective b a hb he).symm))

noncomputable def wordPrefix (π : Equiv.Perm (Fin N)) (r : Fin (N+1)) : Finset (Fin N) :=
  Finset.univ.filter fun i => (π.symm i).val < r.val

lemma wordPrefix_strict (π : Equiv.Perm (Fin N)) : StrictMono (wordPrefix π) := by
  classical
  intro r s hrs
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans hh hrs⟩
  · intro he
    let j : Fin N := ⟨r.val,by have := s.isLt; change r.val < s.val at hrs; omega⟩
    have hj : π j ∈ wordPrefix π s := by
      simp only [wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply]
      exact hrs
    rw [← he] at hj
    simp [wordPrefix,j] at hj

lemma wordPrefix_zero (π : Equiv.Perm (Fin N)) : wordPrefix π 0 = ∅ := by
  classical
  simp [wordPrefix]
lemma wordPrefix_last (π : Equiv.Perm (Fin N)) : wordPrefix π (Fin.last N) = Finset.univ := by
  classical
  ext i
  simp [wordPrefix]

noncomputable def diagonalChamber (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (π : Equiv.Perm (Fin N)) : ResidueChamber (K := K) (N := N) where
  top := Submodule.span K[X] (Set.range b)
  hasTop := span_hasPivots b a hb
  stage r := diagonalModule b (wordPrefix π r)
  hasStage r := diagonal_hasPivots b a hb _
  strict := by
    intro r s hrs
    exact diagonal_strictAnti b a hb (wordPrefix_strict π hrs)
  initial := by rw [wordPrefix_zero,diagonal_eq_span]
  lower r := by
    rw [← diagonal_eq_powerShift]
    exact diagonal_antitone b (Finset.subset_univ _)

lemma diagonalChamber_word (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (π : Equiv.Perm (Fin N)) :
    (diagonalChamber b a hb π).word = π := by
  classical
  apply Equiv.ext
  intro r
  apply ((diagonalChamber b a hb π).word_eq_iff r (π r)).mpr
  change pivotDegree (diagonalModule b (wordPrefix π r.castSucc)) _ (π r) <
    pivotDegree (diagonalModule b (wordPrefix π r.succ)) _ (π r)
  rw [diagonal_pivotDegree b a hb,diagonal_pivotDegree b a hb]
  simp [wordPrefix]

lemma diagonalChamber_window (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (π : Equiv.Perm (Fin N)) (r : Fin N) :
    (diagonalChamber b a hb π).window r = (N*a (π r)+(π r).val : ℕ) := by
  unfold ResidueChamber.window
  rw [diagonalChamber_word]
  change ((N*pivotDegree (Submodule.span K[X] (Set.range b)) _ (π r)+(π r).val : ℕ) : ℤ) = _
  rw [span_pivotDegree b a hb]

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))

theorem diagonal_representation :
    ∃ b : Fin N → V K N,
      (∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i)) ∧
      (∀ i, (b i i).coeff (pivotDegree C.top C.hasTop i) = 1) ∧
      Submodule.span K[X] (Set.range b) = C.top ∧
      ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r) := by
  classical
  obtain ⟨b,hmem,hlead,hmonic,hstage⟩ := simultaneous_minimal_basis C.top C.hasTop C.stage
    C.hasStage C.strict.antitone C.initial C.lower
  refine ⟨b,hlead,hmonic,?_,?_⟩
  · have hh := hstage 0
    simpa only [C.initial,ite_true] using hh
  · intro r
    rw [← hstage r]
    unfold diagonalModule
    congr 2
    funext i
    rw [C.stage_degree]
    simp only [diagonalFamily,wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> simp_all

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {M : ℕ}

lemma prefix_first_swap (π : Equiv.Perm (Fin (M+2))) (r : Fin (M+3)) (hr : r.val ≠ 1) :
    wordPrefix ((Equiv.swap 0 (1 : Fin (M+2))).trans π) r = wordPrefix π r := by
  classical
  ext i
  simp only [wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [Equiv.symm_trans,Equiv.trans_apply,Equiv.symm_swap]
  by_cases he0 : π.symm i = 0
  · rw [he0,Equiv.swap_apply_left]
    have h1 : (1 : Fin (M+2)).val = 1 := by rfl
    simp only [h1,Fin.val_zero]
    omega
  · by_cases he1 : π.symm i = 1
    · rw [he1,Equiv.swap_apply_right]
      have h1 : (1 : Fin (M+2)).val = 1 := by rfl
      simp only [h1,Fin.val_zero]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne he0 he1]

namespace ResidueChamber

theorem first_panel_lower (C : ResidueChamber (K := K) (N := M+2))
    (hdesc : C.window 1 < C.window 0) :
    ∃ D : ResidueChamber (K := K) (N := M+2),
      D.top = C.top ∧ (∀ r : Fin (M+3), r.val ≠ 1 → D.stage r = C.stage r) ∧
      D.stage 1 ≠ C.stage 1 ∧ D.length + 1 = C.length := by
  classical
  obtain ⟨b,hb,_,htop,hstage⟩ := C.diagonal_representation
  let π := (Equiv.swap 0 (1 : Fin (M+2))).trans C.word
  let D := diagonalChamber b (pivotDegree C.top C.hasTop) hb π
  have hwin (r : Fin (M+2)) : D.window r = C.window (Equiv.swap 0 (1 : Fin (M+2)) r) := by
    rw [diagonalChamber_window]
    rfl
  have h0 : D.window 0 = C.window 1 := by rw [hwin,Equiv.swap_apply_left]
  have h1 : D.window (1 : Fin (M+2)) = C.window 0 := by rw [hwin,Equiv.swap_apply_right]
  have hrest (i : Fin M) : D.window i.succ.succ = C.window i.succ.succ := by
    rw [hwin,Equiv.swap_apply_of_ne_of_ne]
    · intro he
      have h := congrArg Fin.val he
      simp only [Fin.val_succ,Fin.val_zero] at h
      omega
    · intro he
      have h := congrArg Fin.val he
      change i.val+1+1 = 1 at h
      omega
  refine ⟨D,htop,?_,?_,?_⟩
  · intro r hr
    change diagonalModule b (wordPrefix π r) = C.stage r
    rw [hstage,prefix_first_swap C.word r hr]
  · intro he
    have hpre : wordPrefix π (1 : Fin (M+3)) = wordPrefix C.word (1 : Fin (M+3)) := by
      apply diagonal_injective b _ hb
      change D.stage 1 = _
      rw [he,hstage]
    have hh : C.word 0 ∈ wordPrefix C.word (1 : Fin (M+3)) := by simp [wordPrefix]
    rw [← hpre] at hh
    have hh' := (Finset.mem_filter.mp hh).2
    simp only [π,Equiv.symm_trans,Equiv.trans_apply,Equiv.symm_swap,
      Equiv.symm_apply_apply,Equiv.swap_apply_left] at hh'
    have hval : (1 : Fin (M+2)).val = 1 := rfl
    have hrval : (1 : Fin (M+3)).val = 1 := rfl
    rw [hval,hrval] at hh'
    exact (lt_irrefl _ hh')
  · have hlistD : List.ofFn D.window = D.window 0 :: D.window 1 ::
        List.ofFn (fun i : Fin M => D.window i.succ.succ) := by
      rw [List.ofFn_succ,List.ofFn_succ]
      rfl
    have hlistC : List.ofFn C.window = C.window 0 :: C.window 1 ::
        List.ofFn (fun i : Fin M => C.window i.succ.succ) := by
      rw [List.ofFn_succ,List.ofFn_succ]
      rfl
    unfold length
    rw [hlistD,hlistC,h0,h1,show (fun i : Fin M => D.window i.succ.succ) =
      (fun i : Fin M => C.window i.succ.succ) from funext hrest]
    symm
    apply AffineWindow.inversion_adjacent_increase (by omega : 0 < M+2) []
    · rw [C.window_mod (by omega),C.window_mod (by omega)]
      intro he
      have h := C.word.injective (Fin.ext (by exact_mod_cast he))
      have hv := congrArg Fin.val h
      change 1 = 0 at hv
      omega
    · exact hdesc

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial
variable {K : Type} [Field K] {N : ℕ}
lemma ext_stage {C D : ResidueChamber (K := K) (N := N)}
    (ht : C.top = D.top) (hs : C.stage = D.stage) : C = D := by
  cases C
  cases D
  simp_all
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}

namespace FullChamber
variable (C : FullChamber K (M+3) (by omega))
lemma panel_realization (D : ResidueChamber (K := K) (N := M+3))
    (ht : D.top = C.polynomialChamber.top)
    (hs : ∀ r : Fin (M+4), r.val ≠ 1 → D.stage r = C.polynomialChamber.stage r) :
    ∃ E : FullChamber K (M+3) (by omega), E.polynomialChamber = D ∧
      ∀ r : Fin (M+3), r.val ≠ 1 → E.vertex r = C.vertex r := by
  classical
  let L (r : Fin (M+4)) : LatticeSpace K (M+3) := (D.stage r).map (polynomialEmbedding K (M+3))
  have hother (r : Fin (M+3)) (hr : r.val ≠ 1) : L r.castSucc = (C.vertex r).val := by
    dsimp only [L]
    rw [hs r.castSucc hr]
    change (C.stage r.castSucc).map _ = _
    rw [C.stage_castSucc,polynomialLattice_map]
  have htop : D.top.map (polynomialEmbedding K (M+3)) = (C.vertex C.topIndex).val := by
    rw [ht]
    exact polynomialLattice_map K (M+3) _
  have hLmono : StrictAnti L := by
    intro r s hrs
    exact (Submodule.map_strictMono_of_injective (polynomialEmbedding_injective K (M+3))) (D.strict hrs)
  have hzero : L 0 = (C.vertex C.topIndex).val := by
    change (D.stage 0).map _ = _
    rw [D.initial,htop]
  have hlower (r : Fin (M+4)) : shift K (M+3) (C.vertex C.topIndex).val ≤ L r := by
    rw [← htop]
    change level (shift K (M+3)) (D.top.map (polynomialEmbedding K (M+3))) 1 ≤ _
    rw [← powerShift_map_embedding]
    exact Submodule.map_mono (D.lower r)
  have hnormalized (r : Fin (M+3)) : ¬ L r.castSucc ≤ shift K (M+3) (standard K (M+3)) := by
    by_cases hr : r.val = 1
    · intro he
      have hr2 : r.castSucc < (2 : Fin (M+4)) := by change r.val < 2; omega
      have hle : L (2 : Fin (M+4)) ≤ L r.castSucc := hLmono.antitone hr2.le
      have h2 : L (2 : Fin (M+4)) = (C.vertex (2 : Fin (M+3))).val :=
        hother 2 (by change (2:ℕ) ≠ 1; omega)
      rw [h2] at hle
      exact vertex_normalized (shift K (M+3)) (standard K (M+3)) _ (hle.trans he)
    · rw [hother r hr]
      exact vertex_normalized (shift K (M+3)) (standard K (M+3)) _
  obtain ⟨m,hm⟩ := vertex_bounded (shift K (M+3)) (standard K (M+3)) (C.vertex C.topIndex)
  let v (r : Fin (M+3)) : Vertex K (M+3) := ⟨L r.castSucc,
    (by apply le_trans (hLmono.antitone (Fin.zero_le _)); rw [hzero]; exact vertex_le _ _ _),
    hnormalized r,⟨m+1,(shift K (M+3)).monotone hm |>.trans (hlower r.castSucc)⟩,
    shift_le_self K (M+3) _⟩
  have hv (r : Fin (M+3)) (hr : r.val ≠ 1) : v r = C.vertex r := Subtype.ext (hother r hr)
  let E : FullChamber K (M+3) (by omega) := {
    vertex := v
    strict := by intro r s hrs; exact hLmono (Fin.castSucc_lt_castSucc_iff.mpr hrs)
    lower := by
      intro r
      change shift K (M+3) (L 0) ≤ L r.castSucc
      rw [hzero]
      exact hlower _ }
  refine ⟨E,?_,hv⟩
  apply ResidueChamber.ext_stage
  · change polynomialLattice K (M+3) (v E.topIndex) = D.top
    have hv0 : v E.topIndex = C.vertex C.topIndex := hv _ (by change (0:ℕ) ≠ 1; omega)
    rw [hv0,ht]
    rfl
  · funext r
    by_cases hr : r.val < M+3
    · let j : Fin (M+3) := ⟨r.val,hr⟩
      have he : j.castSucc = r := Fin.ext rfl
      rw [← he]
      change E.stage j.castSucc = _
      rw [E.stage_castSucc]
      change (L j.castSucc).comap (polynomialEmbedding K (M+3)) = _
      exact Submodule.comap_map_eq_of_injective (polynomialEmbedding_injective K (M+3)) _
    · have he : r = Fin.last (M+3) := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
      rw [he]
      change E.stage (Fin.last (M+3)) = _
      rw [E.stage_last,D.terminal]
      congr 1
      change polynomialLattice K (M+3) (v E.topIndex) = D.top
      have hv0 : v E.topIndex = C.vertex C.topIndex := hv _ (by change (0:ℕ) ≠ 1; omega)
      rw [hv0,ht]
      rfl

theorem first_panel_previous
    (hd : C.polynomialChamber.window 1 < C.polynomialChamber.window 0) :
    C.face.erase (C.vertex 1) ∈ codistanceStage K (M+3) (by omega) (C.length-1) := by
  classical
  obtain ⟨D,ht,hs,_,hlen⟩ := C.polynomialChamber.first_panel_lower hd
  obtain ⟨E,he,hvertex⟩ := C.panel_realization D ht hs
  refine ⟨E,?_,?_⟩
  · change E.polynomialChamber.length ≤ C.polynomialChamber.length-1
    rw [he]
    omega
  · intro v hv
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hv
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hmem
    have hr : r.val ≠ 1 := by
      intro hh
      have hr1 : r = 1 := Fin.ext hh
      exact hne (congrArg C.vertex hr1)
    apply Finset.mem_image.mpr
    exact ⟨r,Finset.mem_univ _,hvertex r hr⟩

end FullChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
lemma powerShift_add (A : Submodule K[X] (V K N)) (a b : ℕ) :
    powerShift (powerShift A a) b = powerShift A (a+b) := by
  unfold powerShift
  rw [← Submodule.map_comp]
  apply congrArg (fun f : V K N →ₗ[K[X]] V K N => A.map f)
  apply LinearMap.ext
  intro v
  funext i
  change (Polynomial.X^b : K[X]) * ((Polynomial.X^a : K[X])*v i) =
    (Polynomial.X^(a+b) : K[X])*v i
  rw [pow_add]
  ring
lemma powerShift_zero (A : Submodule K[X] (V K N)) : powerShift A 0 = A := by
  have he : powerLinear (K := K) (N := N) 0 = LinearMap.id := by
    ext v i
    simp [powerLinear]
  simp [powerShift,he]

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))
noncomputable def scale (m : ℕ) : ResidueChamber (K := K) (N := N) where
  top := powerShift C.top m
  hasTop := powerShift_hasPivots _ C.hasTop m
  stage r := powerShift (C.stage r) m
  hasStage r := powerShift_hasPivots _ (C.hasStage r) m
  strict := by intro r s h; exact powerShift_strictMono m (C.strict h)
  initial := by rw [C.initial]
  lower r := by
    rw [powerShift_add,show m+1 = 1+m by omega,← powerShift_add]
    exact powerShift_mono m (C.lower r)
lemma scale_word (m : ℕ) (r : Fin N) : (C.scale m).word r = C.word r := by
  apply ((C.scale m).word_eq_iff r _).mpr
  change pivotDegree (powerShift (C.stage r.castSucc) m) _ (C.word r) <
    pivotDegree (powerShift (C.stage r.succ) m) _ (C.word r)
  rw [pivotDegree_powerShift _ (C.hasStage r.castSucc),pivotDegree_powerShift _ (C.hasStage r.succ)]
  exact Nat.add_lt_add_right ((C.word_eq_iff r _).mp rfl) m
lemma scale_window (m : ℕ) (r : Fin N) : (C.scale m).window r = C.window r + N*m := by
  simp only [window,C.scale_word]
  change ((N*pivotDegree (powerShift C.top m) _ (C.word r)+(C.word r).val : ℕ) : ℤ) = _
  rw [pivotDegree_powerShift _ C.hasTop]
  push_cast
  ring
lemma scale_length (m : ℕ) : (C.scale m).length = C.length := by
  unfold length
  have he : List.ofFn (C.scale m).window = (List.ofFn C.window).map (·+(N*m : ℤ)) := by
    rw [List.map_ofFn]
    congr 1
    funext r
    exact C.scale_window m r
  rw [he,AffineWindow.inversion_shift]
end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N : ℕ}

lemma polynomial_map_le_standard (A : Submodule K[X] (PolynomialVectors.V K N)) :
    A.map (polynomialEmbedding K N) ≤ standard K N := by
  rintro v ⟨w,hw,rfl⟩ i
  exact ⟨w i,rfl⟩

def PolyBounded (A : Submodule K[X] (PolynomialVectors.V K N)) : Prop :=
  ∃ m, level (shift K N) (standard K N) m ≤ A.map (polynomialEmbedding K N)

lemma PolyBounded.mono {A B : Submodule K[X] (PolynomialVectors.V K N)}
    (hA : PolyBounded A) (hAB : A ≤ B) : PolyBounded B := by
  obtain ⟨m,hm⟩ := hA
  exact ⟨m,hm.trans (Submodule.map_mono hAB)⟩

lemma PolyBounded.powerShift {A : Submodule K[X] (PolynomialVectors.V K N)}
    (hA : PolyBounded A) (r : ℕ) : PolyBounded (powerShift A r) := by
  obtain ⟨m,hm⟩ := hA
  refine ⟨m+r,?_⟩
  rw [powerShift_map_embedding,level_add]
  exact level_mono _ _ hm

lemma polyBounded_vertex (A : Vertex K N) : PolyBounded (polynomialLattice K N A) := by
  unfold PolyBounded
  rw [polynomialLattice_map]
  exact vertex_bounded _ _ A

lemma normalizedPolynomial_exists (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) :
    ∃ B : Vertex K N, ∃ m, A.map (polynomialEmbedding K N) = level (shift K N) B.val m := by
  obtain ⟨m,hm⟩ := hA
  obtain ⟨B,j,_,hj⟩ := exists_normalized (shift K N) (standard K N)
    (shift_standard_le K N) (standard_not_le_shift K N hN) m
    (A.map (polynomialEmbedding K N)) (polynomial_map_le_standard A) hm (shift_le_self K N _)
  exact ⟨B,j,hj⟩

noncomputable def normalizedPolynomial (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) : Vertex K N :=
  (normalizedPolynomial_exists hN A hA).choose
lemma normalizedPolynomial_spec (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) :
    ∃ m, A.map (polynomialEmbedding K N) =
      level (shift K N) (normalizedPolynomial hN A hA).val m :=
  (normalizedPolynomial_exists hN A hA).choose_spec
lemma normalizedPolynomial_homothetic (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) :
    Homothetic (shift K N) (A.map (polynomialEmbedding K N)) (normalizedPolynomial hN A hA).val := by
  obtain ⟨m,hm⟩ := normalizedPolynomial_spec hN A hA
  exact ⟨0,m,hm⟩
lemma normalizedPolynomial_eq (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) (B : Vertex K N)
    (he : Homothetic (shift K N) (A.map (polynomialEmbedding K N)) B.val) :
    normalizedPolynomial hN A hA = B := by
  apply (homothetic_normalized_iff _ _ (shift_standard_le K N) _ _).mp
  exact homothetic_trans _ (homothetic_symm _ (normalizedPolynomial_homothetic hN A hA)) he
lemma normalizedPolynomial_vertex (hN : 0 < N) (B : Vertex K N) :
    normalizedPolynomial hN (polynomialLattice K N B) (polyBounded_vertex B) = B := by
  apply normalizedPolynomial_eq
  rw [polynomialLattice_map]
  exact homothetic_refl _ _
lemma normalizedPolynomial_power (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) (m : ℕ) :
    normalizedPolynomial hN (powerShift A m) (hA.powerShift m) = normalizedPolynomial hN A hA := by
  apply normalizedPolynomial_eq
  apply homothetic_trans _ _ (normalizedPolynomial_homothetic hN A hA)
  rw [powerShift_map_embedding]
  exact ⟨0,m,rfl⟩

namespace BoundedChamber
variable (C : ResidueChamber (K := K) (N := N)) (hC : PolyBounded C.top)
include hC in
lemma stage_bounded (r : Fin (N+1)) : PolyBounded (C.stage r) :=
  (hC.powerShift 1).mono (C.lower r)

noncomputable def vertex (hN : 0 < N) (r : Fin N) : Vertex K N :=
  normalizedPolynomial hN (C.stage r.castSucc) (stage_bounded C hC r.castSucc)
noncomputable def face (hN : 0 < N) : Finset (Vertex K N) :=
  Finset.univ.image (vertex C hC hN)
lemma vertex_homothetic (hN : 0 < N) (r : Fin N) :
    Homothetic (shift K N) ((C.stage r.castSucc).map (polynomialEmbedding K N))
      (vertex C hC hN r).val := normalizedPolynomial_homothetic _ _ _
lemma nonterminal_ne (r : Fin N) : C.stage r.castSucc ≠ powerShift C.top 1 := by
  rw [← C.terminal]
  exact (C.strict (show r.castSucc < Fin.last N by exact r.isLt)).ne'

lemma vertex_injective (hN : 0 < N) : Function.Injective (vertex C hC hN) := by
  let L := C.top.map (polynomialEmbedding K N)
  let v (r : Fin N) : AffineLattices.Vertex (shift K N) L := ⟨
    (C.stage r.castSucc).map (polynomialEmbedding K N),
    (by apply Submodule.map_mono; rw [← C.initial]; exact C.strict.antitone (Fin.zero_le _)),
    (by
      intro he
      have hh : (C.stage r.castSucc).map (polynomialEmbedding K N) = shift K N L :=
        le_antisymm he (by
          change level (shift K N) (C.top.map (polynomialEmbedding K N)) 1 ≤ _
          rw [← powerShift_map_embedding]
          exact Submodule.map_mono (C.lower _))
      have heq : C.stage r.castSucc = powerShift C.top 1 := by
        apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K N)
        rw [powerShift_map_embedding]
        exact hh
      exact nonterminal_ne C r heq),
    ⟨1,(by
      change level (shift K N) (C.top.map (polynomialEmbedding K N)) 1 ≤ _
      rw [← powerShift_map_embedding]
      exact Submodule.map_mono (C.lower _))⟩,
    shift_le_self K N _⟩
  intro r s hrs
  have he : Homothetic (shift K N) (v r).val (v s).val :=
    homothetic_trans _ (vertex_homothetic C hC hN r)
      (hrs ▸ homothetic_symm _ (vertex_homothetic C hC hN s))
  have hh := (homothetic_normalized_iff (shift K N) L (shift_le_self K N L) _ _).mp he
  have hmap := congrArg (fun Z : AffineLattices.Vertex (shift K N) L => Z.val) hh
  have hs := Submodule.map_injective_of_injective (polynomialEmbedding_injective K N) hmap
  exact Fin.castSucc_injective _ (C.strict.injective hs)

lemma card_face (hN : 0 < N) : (face C hC hN).card = N := by
  classical
  rw [face,Finset.card_image_of_injective _ (vertex_injective C hC hN)]
  simp
lemma face_mem (hN : 0 < N) : face C hC hN ∈ (building K N).faces := by
  classical
  apply (isFace_iff_compatible (shift K N) (standard K N) (shift_standard_le K N) _).mpr
  intro A hA B hB
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hB
  apply compatible_homothetic _ (vertex_homothetic C hC hN r) (vertex_homothetic C hC hN s)
  have hlow (r s : Fin N) : shift K N ((C.stage r.castSucc).map (polynomialEmbedding K N)) ≤
      (C.stage s.castSucc).map (polynomialEmbedding K N) := by
    apply le_trans _ (Submodule.map_mono (C.lower s.castSucc))
    rw [powerShift_map_embedding]
    change shift K N _ ≤ shift K N _
    apply (shift K N).monotone
    apply Submodule.map_mono
    rw [← C.initial]
    exact C.strict.antitone (Fin.zero_le _)
  rcases le_total r s with hrs | hsr
  · exact ⟨0,0,hlow r s,Submodule.map_mono (C.strict.antitone (Fin.castSucc_le_castSucc_iff.mpr hrs))⟩
  · apply compatible_symm
    exact ⟨0,0,hlow s r,Submodule.map_mono (C.strict.antitone (Fin.castSucc_le_castSucc_iff.mpr hsr))⟩
end BoundedChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial
variable {K : Type} [Field K] {N : ℕ}
noncomputable def reroot (C : ResidueChamber (K := K) (N := N)) (hN : 0 < N) (j : ℕ) :
    ResidueChamber (K := K) (N := N) := (fun D : ResidueChamber (K := K) (N := N) => D.rotate hN)^[j] C
@[simp] lemma reroot_zero (C : ResidueChamber (K := K) (N := N)) (hN : 0 < N) : C.reroot hN 0 = C := rfl
lemma reroot_succ (C : ResidueChamber (K := K) (N := N)) (hN : 0 < N) (j : ℕ) :
    C.reroot hN (j+1) = (C.reroot hN j).rotate hN := Function.iterate_succ_apply' _ _ _
lemma reroot_stage (C : ResidueChamber (K := K) (N := N)) (hN : 0 < N)
    (j : ℕ) (r : Fin (N+1)) (hjr : j+r.val ≤ N) :
    (C.reroot hN j).stage r = C.stage ⟨j+r.val,by omega⟩ := by
  induction j generalizing r with
  | zero => simp only [reroot_zero,Nat.zero_add]
  | succ j ih =>
    rw [reroot_succ]
    change (C.reroot hN j).rotateStage hN r = _
    have hr : r.val < N := by omega
    rw [show (C.reroot hN j).rotateStage hN r =
      (C.reroot hN j).stage ⟨r.val+1,by omega⟩ from dite_eq_left hr]
    rw [ih _ (by dsimp only; omega)]
    congr 1
    apply Fin.ext
    dsimp only
    omega
lemma reroot_top (C : ResidueChamber (K := K) (N := N)) (hN : 0 < N)
    (j : ℕ) (hj : j ≤ N) : (C.reroot hN j).top = C.stage ⟨j,by omega⟩ := by
  rw [← (C.reroot hN j).initial,C.reroot_stage hN j 0 (by simpa using hj)]
  rfl
lemma reroot_length {M : ℕ} (C : ResidueChamber (K := K) (N := M+1)) (j : ℕ) :
    (C.reroot (Nat.zero_lt_succ M) j).length = C.length := by
  induction j with
  | zero => rfl
  | succ j ih => rw [reroot_succ,rotate_length,ih]
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N M : ℕ}
variable (C : ResidueChamber (K := K) (N := N)) (hC : PolyBounded C.top)
include hC in
lemma rotate_bounded (hN : 0 < N) : PolyBounded (C.rotate hN).top := stage_bounded C hC _
lemma scale_vertex (m : ℕ) (hN : 0 < N) (r : Fin N) :
    vertex (C.scale m) (hC.powerShift m) hN r = vertex C hC hN r := by
  exact normalizedPolynomial_power hN _ (stage_bounded C hC r.castSucc) m
lemma scale_face (m : ℕ) (hN : 0 < N) :
    face (C.scale m) (hC.powerShift m) hN = face C hC hN := by
  unfold face
  congr 1
  exact funext (scale_vertex C hC m hN)

lemma rotate_vertex (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top)
    (r : Fin (M+1)) : vertex (C.rotate (Nat.zero_lt_succ M))
      (rotate_bounded C hC _) (Nat.zero_lt_succ M) r =
      vertex C hC (Nat.zero_lt_succ M) (finRotate (M+1) r) := by
  apply normalizedPolynomial_eq
  change Homothetic (shift K (M+1))
    (((C.rotate (Nat.zero_lt_succ M)).stage r.castSucc).map _) _
  change Homothetic (shift K (M+1)) ((C.rotateStage _ r.castSucc).map _) _
  rw [C.rotateStage_castSucc]
  by_cases hr : r.val < M
  · rw [finRotate_of_lt hr]
    exact vertex_homothetic C hC _ ⟨r.val+1,by omega⟩
  · have he : r = Fin.last M := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
    subst r
    rw [finRotate_last]
    have he : (Fin.last M).succ = Fin.last (M+1) := Fin.ext rfl
    rw [he,C.terminal,powerShift_map_embedding]
    apply homothetic_trans _ ⟨0,1,rfl⟩
    have hh := vertex_homothetic C hC (Nat.zero_lt_succ M) 0
    rw [show (0 : Fin (M+1)).castSucc = 0 from rfl,C.initial] at hh
    exact hh
lemma rotate_face (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top) :
    face (C.rotate (Nat.zero_lt_succ M)) (rotate_bounded C hC _) (Nat.zero_lt_succ M) =
      face C hC (Nat.zero_lt_succ M) := by
  classical
  ext v
  simp only [face,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨finRotate (M+1) r, (rotate_vertex C hC r).symm.trans hr⟩
  · rintro ⟨r,hr⟩
    obtain ⟨s,hs⟩ := (finRotate (M+1)).surjective r
    exact ⟨s,by rw [rotate_vertex,hs]; exact hr⟩
include hC in
lemma reroot_bounded (hN : 0 < N) (j : ℕ) : PolyBounded (C.reroot hN j).top := by
  induction j with
  | zero => exact hC
  | succ j ih => rw [C.reroot_succ]; exact rotate_bounded _ ih _
lemma reroot_face (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top) (j : ℕ) :
    face (C.reroot (Nat.zero_lt_succ M) j) (reroot_bounded C hC _ j) (Nat.zero_lt_succ M) =
      face C hC (Nat.zero_lt_succ M) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [C.reroot_succ]
    exact (rotate_face _ (reroot_bounded C hC _ j)).trans ih

end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N : ℕ}
lemma homothetic_interval_eq (T A B : LatticeSpace K N)
    (hAT : A ≤ T) (hBT : B ≤ T) (hTA : shift K N T ≤ A) (hTB : shift K N T ≤ B)
    (hneA : A ≠ shift K N T) (hneB : B ≠ shift K N T)
    (hh : Homothetic (shift K N) A B) : A = B := by
  let VA : AffineLattices.Vertex (shift K N) T :=
    ⟨A,hAT,fun h => hneA (le_antisymm h hTA),⟨1,hTA⟩,shift_le_self K N A⟩
  let VB : AffineLattices.Vertex (shift K N) T :=
    ⟨B,hBT,fun h => hneB (le_antisymm h hTB),⟨1,hTB⟩,shift_le_self K N B⟩
  exact congrArg (fun Z : AffineLattices.Vertex (shift K N) T => Z.val)
    ((homothetic_normalized_iff (shift K N) T (shift_le_self K N T) VA VB).mp hh)

namespace BoundedChamber
variable (C D : ResidueChamber (K := K) (N := N))
variable (hC : PolyBounded C.top) (hD : PolyBounded D.top) (hN : 0 < N)
lemma stage_top_le (r : Fin (N+1)) : C.stage r ≤ C.top := by
  rw [← C.initial]
  exact C.strict.antitone (Fin.zero_le _)
lemma mapped_lower (r : Fin (N+1)) : shift K N (C.top.map (polynomialEmbedding K N)) ≤
    (C.stage r).map (polynomialEmbedding K N) := by
  change level (shift K N) (C.top.map (polynomialEmbedding K N)) 1 ≤ _
  rw [← powerShift_map_embedding]
  exact Submodule.map_mono (C.lower r)
lemma mapped_nonterminal (r : Fin N) :
    (C.stage r.castSucc).map (polynomialEmbedding K N) ≠ shift K N (C.top.map (polynomialEmbedding K N)) := by
  intro he
  apply nonterminal_ne C r
  apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K N)
  rw [powerShift_map_embedding]
  exact he

lemma stage_eq_of_vertex_eq (ht : C.top = D.top) (r s : Fin N)
    (he : vertex C hC hN r = vertex D hD hN s) : C.stage r.castSucc = D.stage s.castSucc := by
  apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K N)
  apply homothetic_interval_eq (C.top.map (polynomialEmbedding K N))
  · exact Submodule.map_mono (stage_top_le C _)
  · rw [ht]; exact Submodule.map_mono (stage_top_le D _)
  · exact mapped_lower C _
  · rw [ht]; exact mapped_lower D _
  · exact mapped_nonterminal C _
  · rw [ht]; exact mapped_nonterminal D _
  · exact homothetic_trans _ (vertex_homothetic C hC hN r)
      (he ▸ homothetic_symm _ (vertex_homothetic D hD hN s))

lemma eq_of_face_of_top (ht : C.top = D.top) (hf : face C hC hN = face D hD hN) : C = D := by
  classical
  have hrange : Set.range (fun r : Fin N => C.stage r.castSucc) =
      Set.range (fun r : Fin N => D.stage r.castSucc) := by
    ext A
    constructor
    · rintro ⟨r,rfl⟩
      have hm : vertex C hC hN r ∈ face C hC hN := Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
      rw [hf] at hm
      obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hm
      exact ⟨s,(stage_eq_of_vertex_eq C D hC hD hN ht r s hs.symm).symm⟩
    · rintro ⟨s,rfl⟩
      have hm : vertex D hD hN s ∈ face D hD hN := Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩
      rw [← hf] at hm
      obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hm
      exact ⟨r,stage_eq_of_vertex_eq C D hC hD hN ht r s hr⟩
  let eC : Fin N ↪o OrderDual (Submodule K[X] (PolynomialVectors.V K N)) :=
    OrderEmbedding.ofStrictMono (fun r => C.stage r.castSucc)
      (fun r s hrs => C.strict (Fin.castSucc_lt_castSucc_iff.mpr hrs))
  let eD : Fin N ↪o OrderDual (Submodule K[X] (PolynomialVectors.V K N)) :=
    OrderEmbedding.ofStrictMono (fun r => D.stage r.castSucc)
      (fun r s hrs => D.strict (Fin.castSucc_lt_castSucc_iff.mpr hrs))
  have he : eC = eD := OrderEmbedding.range_eq_iff.mp hrange
  apply ResidueChamber.ext_stage ht
  funext r
  refine Fin.lastCases ?_ (fun s => ?_) r
  · rw [C.terminal,D.terminal,ht]
  · exact congrArg (fun e : Fin N ↪o OrderDual (Submodule K[X] (PolynomialVectors.V K N)) => e s) he

lemma full_vertex {hN : 0 < N} (E : FullChamber K N hN) (r : Fin N) :
    vertex E.polynomialChamber (polyBounded_vertex _) hN r = E.vertex r := by
  apply normalizedPolynomial_eq
  change Homothetic (shift K N) ((E.stage r.castSucc).map _) _
  rw [E.stage_castSucc,polynomialLattice_map]
  exact homothetic_refl _ _
lemma full_face {hN : 0 < N} (E : FullChamber K N hN) :
    face E.polynomialChamber (polyBounded_vertex _) hN = E.face := by
  unfold face FullChamber.face
  congr 1
  exact funext (full_vertex E)

theorem normalization {M : ℕ} (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top) :
    ∃ E : FullChamber K (M+1) (Nat.zero_lt_succ M),
      E.face = face C hC (Nat.zero_lt_succ M) ∧ E.length = C.length := by
  classical
  let hN := Nat.zero_lt_succ M
  obtain ⟨E,hE⟩ := ambient_face_in_chamber K (M+1) hN (face C hC hN) (face_mem C hC hN)
  have hface : E.face = face C hC hN := (Finset.eq_of_subset_of_card_le hE
    (by rw [E.card_face,card_face])).symm
  have hA : normalizedPolynomial hN C.top hC ∈ E.face := by
    rw [hface]
    apply Finset.mem_image.mpr
    refine ⟨0,Finset.mem_univ _,?_⟩
    change normalizedPolynomial hN (C.stage 0) _ = _
    simp only [C.initial]
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hA
  obtain ⟨m,hm⟩ := normalizedPolynomial_spec hN C.top hC
  let R := (E.polynomialChamber.reroot hN j.val).scale m
  have hb : PolyBounded R.top := (reroot_bounded E.polynomialChamber (polyBounded_vertex _) hN j.val).powerShift m
  have ht : R.top = C.top := by
    apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+1))
    change (powerShift (E.polynomialChamber.reroot hN j.val).top m).map _ = _
    rw [powerShift_map_embedding,E.polynomialChamber.reroot_top hN j.val j.isLt.le]
    change level (shift K (M+1)) ((E.stage j.castSucc).map _) m = _
    rw [E.stage_castSucc,polynomialLattice_map,hj]
    exact hm.symm
  have hf : face R hb hN = face C hC hN := by
    rw [show face R hb hN = face (E.polynomialChamber.reroot hN j.val)
      (reroot_bounded E.polynomialChamber (polyBounded_vertex _) hN j.val) hN from scale_face _ _ m hN]
    rw [reroot_face E.polynomialChamber (polyBounded_vertex _) j.val,full_face E,hface]
  have heq : R = C := eq_of_face_of_top R C hb hC hN ht hf
  refine ⟨E,hface,?_⟩
  change E.polynomialChamber.length = C.length
  rw [← heq]
  change _ = ((E.polynomialChamber.reroot hN j.val).scale m).length
  rw [ResidueChamber.scale_length,ResidueChamber.reroot_length]
end BoundedChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}

theorem rooted_panel_previous (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
    (hd : C.window 1 < C.window 0) :
    (face C hC (by omega)).erase (vertex C hC (by omega) 1) ∈
      codistanceStage K (M+2) (by omega) (C.length-1) := by
  classical
  obtain ⟨D,ht,hs,_,hlen⟩ := C.first_panel_lower hd
  have hD : PolyBounded D.top := by rw [ht]; exact hC
  obtain ⟨E,hface,hLength⟩ := normalization D hD
  refine ⟨E,?_,?_⟩
  · rw [hLength]
    omega
  · intro v hv
    rw [hface]
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hv
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hmem
    have hr1 : r.val ≠ 1 := by
      intro he
      have hh : r = 1 := Fin.ext he
      exact hne (hr.symm.trans (congrArg (vertex C hC (by omega)) hh))
    refine Finset.mem_image.mpr ⟨r,Finset.mem_univ _,?_⟩
    apply Eq.trans _ hr
    change normalizedPolynomial _ (D.stage r.castSucc) _ = normalizedPolynomial _ (C.stage r.castSucc) _
    simp only [hs r.castSucc hr1]

theorem full_rooted_panel_previous (E : FullChamber K (M+2) (by omega)) (j : ℕ)
    (hd : (E.polynomialChamber.reroot (by omega) j).window 1 <
      (E.polynomialChamber.reroot (by omega) j).window 0) :
    E.face.erase (vertex (E.polynomialChamber.reroot (by omega) j)
      (reroot_bounded E.polynomialChamber (polyBounded_vertex _) (by omega) j) (by omega) 1) ∈
      codistanceStage K (M+2) (by omega) (E.length-1) := by
  have hh := rooted_panel_previous (E.polynomialChamber.reroot (by omega) j)
    (reroot_bounded E.polynomialChamber (polyBounded_vertex _) (by omega) j) hd
  rw [reroot_face E.polynomialChamber (polyBounded_vertex _) j,full_face E,
    ResidueChamber.reroot_length] at hh
  exact hh
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {M : ℕ}
lemma reroot_window_nonwrap (C : ResidueChamber (K := K) (N := M+1))
    (j : ℕ) (r : Fin (M+1)) (hjr : j+r.val < M+1) :
    (C.reroot (Nat.zero_lt_succ M) j).window r = C.window ⟨j+r.val,by omega⟩ := by
  induction j generalizing r with
  | zero => simp only [reroot_zero,Nat.zero_add,Fin.eta]
  | succ j ih =>
    rw [reroot_succ]
    have hr : r.val < M := by omega
    have he := (C.reroot (Nat.zero_lt_succ M) j).rotate_window_castSucc ⟨r.val,hr⟩
    change ((C.reroot (Nat.zero_lt_succ M) j).rotate _).window r = _ at he
    rw [he,ih _ (by simp only [Fin.val_succ]; omega)]
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
lemma reroot_period (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top) :
    C.reroot (Nat.zero_lt_succ M) (M+1) = C.scale 1 := by
  apply eq_of_face_of_top _ _ (reroot_bounded C hC _ (M+1)) (hC.powerShift 1) (Nat.zero_lt_succ M)
  · rw [C.reroot_top _ _ le_rfl]
    exact C.terminal
  · rw [reroot_face C hC,scale_face C hC]
lemma reroot_vertex_nonwrap (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top)
    (j : ℕ) (r : Fin (M+1)) (hjr : j+r.val < M+1) :
    vertex (C.reroot (Nat.zero_lt_succ M) j) (reroot_bounded C hC _ j) (Nat.zero_lt_succ M) r =
      vertex C hC (Nat.zero_lt_succ M) ⟨j+r.val,by omega⟩ := by
  change normalizedPolynomial _ ((C.reroot _ j).stage r.castSucc) _ = _
  simp only [C.reroot_stage _ j r.castSucc (by simp only [Fin.val_castSucc]; omega)]
  rfl
lemma last_root_window_one (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top) :
    (C.reroot (by omega) (M+1)).window 1 = C.window 0 + (M+2) := by
  have he := (C.reroot (by omega) (M+1)).rotate_window_castSucc (0 : Fin (M+1))
  change ((C.reroot (by omega) (M+1)).rotate _).window 0 =
    (C.reroot (by omega) (M+1)).window 1 at he
  rw [← he,← C.reroot_succ,reroot_period C hC]
  rw [ResidueChamber.scale_window]
  simp
lemma last_root_vertex_one (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top) :
    vertex (C.reroot (by omega) (M+1)) (reroot_bounded C hC _ (M+1)) (by omega) 1 =
      vertex C hC (by omega) 0 := by
  have he := rotate_vertex (C.reroot (by omega) (M+1)) (reroot_bounded C hC _ (M+1)) 0
  rw [finRotate_apply_zero] at he
  rw [← he]
  simp only [← C.reroot_succ,reroot_period C hC]
  exact scale_vertex C hC 1 _ 0
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
lemma reroot_window_zero (C : ResidueChamber (K := K) (N := M+2)) (r : Fin (M+2)) :
    (C.reroot (by omega) r.val).window 0 = C.window r := by
  simpa only [Fin.val_zero,Nat.add_zero,Fin.eta] using
    C.reroot_window_nonwrap r.val 0 (by simpa only [Fin.val_zero,Nat.add_zero] using r.isLt)
lemma reroot_window_one (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
    (r : Fin (M+2)) : (C.reroot (by omega) r.val).window 1 =
      AffineWindow.periodicEnd (by omega) C.window r.succ := by
  classical
  by_cases hr : r.val < M+1
  · have hn : r.val+1 < M+2 := by omega
    rw [AffineWindow.periodicEnd,dite_eq_left (show r.succ.val < M+2 from hn)]
    have hh := C.reroot_window_nonwrap r.val 1
      (show r.val+(1:Fin (M+2)).val < M+2 by simpa using hn)
    simpa using hh
  · have he : r.val = M+1 := by have := r.isLt; omega
    have hs : r.succ = Fin.last (M+2) := Fin.ext (by change r.val+1 = M+2; omega)
    rw [he,hs,AffineWindow.periodicEnd_last,last_root_window_one C hC]
    simp
lemma reroot_vertex_one (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
    (r : Fin (M+2)) :
    vertex (C.reroot (by omega) r.val) (reroot_bounded C hC _ r.val) (by omega) 1 =
      vertex C hC (by omega) (finRotate (M+2) r) := by
  by_cases hr : r.val < M+1
  · rw [finRotate_of_lt hr]
    have hh := reroot_vertex_nonwrap C hC r.val 1
      (show r.val+(1:Fin (M+2)).val < M+2 by simp; omega)
    simpa using hh
  · have he : r = Fin.last (M+1) := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
    subst r
    exact (last_root_vertex_one C hC).trans (congrArg _ finRotate_last.symm)

theorem descent_panel_previous (E : FullChamber K (M+2) (by omega))
    (r : Fin (M+2)) (hr : r ∈ AffineWindow.descents (by omega) E.polynomialChamber.window) :
    E.face.erase (E.vertex (finRotate (M+2) r)) ∈ codistanceStage K (M+2) (by omega) (E.length-1) := by
  have hd := (Finset.mem_filter.mp hr).2
  have hh := full_rooted_panel_previous E r.val
    (by rw [reroot_window_zero,reroot_window_one _ (polyBounded_vertex _)]; exact hd)
  rw [reroot_vertex_one _ (polyBounded_vertex _),full_vertex] at hh
  exact hh
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.FullChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
noncomputable def descentCore (E : FullChamber K (M+2) (by omega)) : Finset (Vertex K (M+2)) :=
  (AffineWindow.descents (by omega) E.polynomialChamber.window).image
    (fun r => E.vertex (finRotate (M+2) r))
lemma descentCore_subset (E : FullChamber K (M+2) (by omega)) : E.descentCore ⊆ E.face := by
  intro v hv
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hv
  exact E.mem_face _
lemma descentCore_nonempty (E : FullChamber K (M+2) (by omega)) (hE : 0 < E.length) :
    E.descentCore.Nonempty := by
  apply Finset.Nonempty.image
  apply AffineWindow.descents_nonempty
  · intro r s he
    dsimp only at he
    rw [E.polynomialChamber.window_mod (by omega),E.polynomialChamber.window_mod (by omega)] at he
    exact E.polynomialChamber.word.injective (Fin.ext (by exact_mod_cast he))
  · exact hE
lemma descentCore_ne_face (E : FullChamber K (M+2) (by omega)) : E.descentCore ≠ E.face := by
  classical
  intro he
  apply AffineWindow.descents_ne_univ (by omega) E.polynomialChamber.window
  apply Finset.eq_univ_of_forall
  intro r
  have hh : E.vertex (finRotate (M+2) r) ∈ E.descentCore := he ▸ E.mem_face _
  obtain ⟨s,hs,hes⟩ := Finset.mem_image.mp hh
  have hsr := (finRotate (M+2)).injective (E.vertex_injective hes)
  exact hsr ▸ hs

theorem face_missing_descent_previous (E : FullChamber K (M+2) (by omega))
    {s : Finset (Vertex K (M+2))} (hs : s ⊆ E.face) (hcore : ¬ E.descentCore ⊆ s) :
    s ∈ codistanceStage K (M+2) (by omega) (E.length-1) := by
  classical
  obtain ⟨v,hv,hvs⟩ := Finset.not_subset.mp hcore
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
  apply codistanceStage_downward K (M+2) (by omega) (E.length-1)
    (BoundedChamber.descent_panel_previous E r hr)
  intro v hv
  exact Finset.mem_erase.mpr ⟨fun he => hvs (he ▸ hv),hs hv⟩
end CoboundaryExpanders.RationalLattices.FullChamber

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}

theorem inversion_sorted_blocks (hN : 0 < N) (p q : List (List ℤ))
    (h : List.Forall₂ (fun a b => a.Perm b ∧ a.Pairwise (· ≤ ·) ∧
      b.Pairwise (fun x y => x % (N : ℤ) ≠ y % (N : ℤ))) p q)
    (l r : List ℤ) :
    inversion (N := N) (l ++ q.flatten ++ r) =
      inversion (N := N) (l ++ p.flatten ++ r) + (q.map (pairs disorder)).sum := by
  induction h generalizing l r with
  | nil => simp
  | @cons a b p q hh ht ih =>
    have hb := inversion_sorted_middle hN l (q.flatten ++ r) hh.1 hh.2.1 hh.2.2
    have hp := ih (l ++ a) r
    simp only [List.flatten_cons,List.map_cons,List.sum_cons]
    simp only [List.append_assoc] at hb hp ⊢
    omega

lemma sorted_blocks_eq_of_zero (p q : List (List ℤ))
    (h : List.Forall₂ (fun a b => a.Perm b ∧ a.Pairwise (· ≤ ·)) p q)
    (hz : (q.map (pairs disorder)).sum = 0) : p = q := by
  induction h with
  | nil => rfl
  | @cons a b p q hh ht ih =>
    simp only [List.map_cons,List.sum_cons,Nat.add_eq_zero_iff] at hz
    have hab : a = b := hh.1.eq_of_pairwise' hh.2 ((disorder_zero_iff b).mp hz.1)
    exact congrArg₂ List.cons hab (ih hz.2)

theorem inversion_sorted_blocks_minimum (hN : 0 < N) (p q : List (List ℤ))
    (h : List.Forall₂ (fun a b => a.Perm b ∧ a.Pairwise (· ≤ ·) ∧
      b.Pairwise (fun x y => x % (N : ℤ) ≠ y % (N : ℤ))) p q)
    (l r : List ℤ) :
    inversion (N := N) (l ++ p.flatten ++ r) ≤ inversion (N := N) (l ++ q.flatten ++ r) ∧
    (inversion (N := N) (l ++ q.flatten ++ r) = inversion (N := N) (l ++ p.flatten ++ r) ↔ p = q) := by
  have he := inversion_sorted_blocks hN p q h l r
  refine ⟨by omega,?_⟩
  constructor
  · intro hh
    apply sorted_blocks_eq_of_zero p q
    · exact h.imp (fun _ _ hh => ⟨hh.1,hh.2.1⟩)
    · omega
  · rintro rfl
    rfl
end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}
def slice (p : Fin N → ℤ) (a b : Fin (N+1)) : List ℤ :=
  List.ofFn fun r : Fin (b.val-a.val) => p ⟨a.val+r.val,by have := r.isLt; have := b.isLt; omega⟩
lemma mem_slice (p : Fin N → ℤ) (a b : Fin (N+1)) (x : ℤ) :
    x ∈ slice p a b ↔ ∃ r : Fin N, a.val ≤ r.val ∧ r.val < b.val ∧ p r = x := by
  rw [slice,List.mem_ofFn]
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨⟨a.val+r.val,by have := r.isLt; have := b.isLt; omega⟩,by simp,?_,hr⟩
    have := r.isLt
    dsimp only
    omega
  · rintro ⟨r,ha,hb,hr⟩
    refine ⟨⟨r.val-a.val,by omega⟩,?_⟩
    dsimp only
    have he : (⟨a.val+(r.val-a.val),by omega⟩ : Fin N) = r := Fin.ext (by dsimp only; omega)
    simpa only [he] using hr
lemma slice_nodup (p : Fin N → ℤ) (hp : Function.Injective p) (a b : Fin (N+1)) :
    (slice p a b).Nodup := by
  apply List.nodup_ofFn.mpr
  intro r s he
  have hv := congrArg Fin.val (hp he)
  apply Fin.ext
  dsimp only at hv
  omega
lemma slice_eq_take_drop (p : Fin N → ℤ) (a b : Fin (N+1)) :
    slice p a b = ((List.ofFn p).drop a.val).take (b.val-a.val) := by
  apply List.ext_getElem
  · simp only [slice,List.length_ofFn,List.length_take,List.length_drop]
    have := b.isLt
    omega
  · intro i hi hri
    simp only [slice,List.getElem_ofFn,List.getElem_take,List.getElem_drop]
lemma slice_pairwise (p : Fin N → ℤ) (a b : Fin (N+1)) (R : ℤ → ℤ → Prop)
    (h : ∀ i j : Fin N, a.val ≤ i.val → j.val < b.val → i < j → R (p i) (p j)) :
    (slice p a b).Pairwise R := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  apply h
  · simp
  · have := j.isLt; dsimp only; omega
  · change a.val+i.val < a.val+j.val
    exact Nat.add_lt_add_left hij _
end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
variable (C D : ResidueChamber (K := K) (N := N))
lemma shared_stage_prefix (ht : C.top = D.top) (r : Fin (N+1))
    (hr : C.stage r = D.stage r) (i : Fin N) :
    (C.word.symm i).val < r.val ↔ (D.word.symm i).val < r.val := by
  classical
  have hc := C.stage_degree r i
  have hd := D.stage_degree r i
  simp only [ht,hr] at hc
  by_cases hci : (C.word.symm i).val < r.val <;>
    by_cases hdi : (D.word.symm i).val < r.val <;> simp_all
  omega
lemma same_top_window (ht : C.top = D.top) (r : Fin N) :
    C.window r = D.window (D.word.symm (C.word r)) := by
  simp only [window,Equiv.apply_symm_apply,ht]
lemma window_injective (C : ResidueChamber (K := K) (N := N)) : Function.Injective C.window := by
  intro r s he
  have hN : 0 < N := (r.isLt).trans_le' (Nat.zero_le _)
  have hh := congrArg (· % (N : ℤ)) he
  rw [C.window_mod hN,C.window_mod hN] at hh
  exact C.word.injective (Fin.ext (by exact_mod_cast hh))

theorem window_slice_perm (ht : C.top = D.top) (a b : Fin (N+1))
    (ha : C.stage a = D.stage a) (hb : C.stage b = D.stage b) :
    (AffineWindow.slice C.window a b).Perm (AffineWindow.slice D.window a b) := by
  classical
  apply (List.perm_ext_iff_of_nodup (AffineWindow.slice_nodup _ C.window_injective a b)
    (AffineWindow.slice_nodup _ D.window_injective a b)).mpr
  intro x
  rw [AffineWindow.mem_slice,AffineWindow.mem_slice]
  constructor
  · rintro ⟨r,har,hrb,hrx⟩
    refine ⟨D.word.symm (C.word r),?_,?_,(C.same_top_window D ht r).symm.trans hrx⟩
    · have hh := C.shared_stage_prefix D ht a ha (C.word r)
      simp only [Equiv.symm_apply_apply] at hh
      omega
    · have hh := C.shared_stage_prefix D ht b hb (C.word r)
      simp only [Equiv.symm_apply_apply] at hh
      exact hh.mp hrb
  · rintro ⟨r,har,hrb,hrx⟩
    refine ⟨C.word.symm (D.word r),?_,?_,(D.same_top_window C ht.symm r).symm.trans hrx⟩
    · have hh := D.shared_stage_prefix C ht.symm a ha.symm (D.word r)
      simp only [Equiv.symm_apply_apply] at hh
      omega
    · have hh := D.shared_stage_prefix C ht.symm b hb.symm (D.word r)
      simp only [Equiv.symm_apply_apply] at hh
      exact hh.mp hrb
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.AffineWindow
variable {N L : ℕ}
lemma slice_append (p : Fin N → ℤ) (a b c : Fin (N+1)) (hab : a ≤ b) (hbc : b ≤ c) :
    slice p a b ++ slice p b c = slice p a c := by
  rw [slice_eq_take_drop,slice_eq_take_drop,slice_eq_take_drop]
  have he : c.val-a.val = (b.val-a.val)+(c.val-b.val) := by
    change a.val ≤ b.val at hab
    change b.val ≤ c.val at hbc
    omega
  rw [he,List.take_add,List.drop_drop]
  have hh : a.val+(b.val-a.val) = b.val := Nat.add_sub_of_le hab
  rw [hh]
lemma slice_self (p : Fin N → ℤ) (a : Fin (N+1)) : slice p a a = [] := by simp [slice]
lemma slice_full (p : Fin N → ℤ) : slice p 0 (Fin.last N) = List.ofFn p := by
  simp [slice_eq_take_drop]
def blocks (p : Fin N → ℤ) (c : Fin (L+1) → Fin (N+1)) : List (List ℤ) :=
  List.ofFn fun r : Fin L => slice p (c r.castSucc) (c r.succ)
lemma flatten_blocks (p : Fin N → ℤ) (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c) :
    (blocks p c).flatten = slice p (c 0) (c (Fin.last L)) := by
  induction L with
  | zero => simp [blocks,slice_self]
  | succ L ih =>
    rw [blocks,List.ofFn_succ,List.flatten_cons]
    have hh := ih (fun j => c j.succ) (fun i j hij => hc (Fin.succ_le_succ_iff.mpr hij))
    change (blocks p (fun j => c j.succ)).flatten = _ at hh
    change slice p (c 0) (c (Fin.succ 0)) ++ (blocks p (fun j => c j.succ)).flatten = _
    rw [hh]
    apply slice_append
    · exact hc (show (0 : Fin (L+2)) ≤ (0 : Fin (L+1)).succ from Fin.zero_le _)
    · exact hc (Fin.succ_le_succ_iff.mpr (Fin.zero_le _))
lemma blocks_forall₂ {p q : Fin N → ℤ} (c : Fin (L+1) → Fin (N+1))
    (R : List ℤ → List ℤ → Prop)
    (h : ∀ r : Fin L, R (slice p (c r.castSucc) (c r.succ)) (slice q (c r.castSucc) (c r.succ))) :
    List.Forall₂ R (blocks p c) (blocks q c) := by
  suffices hh : ∀ (n : ℕ) (f g : Fin n → List ℤ), (∀ i, R (f i) (g i)) →
      List.Forall₂ R (List.ofFn f) (List.ofFn g) from hh L _ _ h
  intro n
  induction n with
  | zero => intro f g hh; simp
  | succ n ih =>
    intro f g hh
    rw [List.ofFn_succ,List.ofFn_succ]
    exact List.Forall₂.cons (hh 0) (ih _ _ (fun i => hh i.succ))
end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open AffineWindow
variable {K : Type} [Field K] {N L : ℕ}
variable (C D : ResidueChamber (K := K) (N := N))

theorem fixed_stage_length (hN : 0 < N) (ht : C.top = D.top)
    (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (hstage : ∀ r, C.stage (c r) = D.stage (c r))
    (hsorted : ∀ r : Fin L, (slice C.window (c r.castSucc) (c r.succ)).Pairwise (· ≤ ·)) :
    D.length = C.length + ((blocks D.window c).map (pairs disorder)).sum := by
  have h : List.Forall₂ (fun a b => a.Perm b ∧ a.Pairwise (· ≤ ·) ∧
      b.Pairwise (fun x y => x % (N : ℤ) ≠ y % (N : ℤ))) (blocks C.window c) (blocks D.window c) := by
    apply blocks_forall₂
    intro r
    refine ⟨C.window_slice_perm D ht _ _ (hstage _) (hstage _),hsorted r,?_⟩
    apply slice_pairwise
    intro i j _ _ hij he
    rw [D.window_mod hN,D.window_mod hN] at he
    exact (ne_of_lt hij) (D.word.injective (Fin.ext (by exact_mod_cast he)))
  have he := inversion_sorted_blocks hN _ _ h [] []
  rw [flatten_blocks _ _ hc,flatten_blocks _ _ hc,h0,hl,slice_full,slice_full] at he
  simpa only [length,List.nil_append,List.append_nil] using he

theorem fixed_stage_minimum (hN : 0 < N) (ht : C.top = D.top)
    (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (hstage : ∀ r, C.stage (c r) = D.stage (c r))
    (hsorted : ∀ r : Fin L, (slice C.window (c r.castSucc) (c r.succ)).Pairwise (· ≤ ·)) :
    C.length ≤ D.length := by
  have he := C.fixed_stage_length D hN ht c hc h0 hl hstage hsorted
  omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.AffineWindow
variable {N L : ℕ}
lemma fin_mono_of_steps {A : Type} [Preorder A] {m : ℕ} (f : Fin m → A)
    (h : ∀ i j, i.val+1 = j.val → f i ≤ f j) : Monotone f := by
  cases m with
  | zero => intro i; exact Fin.elim0 i
  | succ m => exact Fin.monotone_iff_le_succ.mpr (fun i => h i.castSucc i.succ rfl)

lemma slices_sorted_of_descents (hN : 0 < N) (p : Fin N → ℤ)
    (c : Fin (L+1) ↪o Fin (N+1))
    (hdes : ∀ r ∈ descents hN p, r.succ ∈ Set.range c) (r : Fin L) :
    (slice p (c r.castSucc) (c r.succ)).Pairwise (· ≤ ·) := by
  classical
  let a := c r.castSucc
  let b := c r.succ
  let f : Fin (b.val-a.val) → ℤ := fun i => p ⟨a.val+i.val,by have := i.isLt; have := b.isLt; omega⟩
  have hm : Monotone f := by
    apply fin_mono_of_steps
    intro i j hij
    dsimp only [f]
    by_contra hn
    let v : Fin N := ⟨a.val+i.val,by have := i.isLt; have := b.isLt; omega⟩
    have hjN : a.val+j.val < N := by have := j.isLt; have := b.isLt; omega
    have hv : v.val+1 < N := by dsimp only [v]; omega
    have hd : v ∈ descents hN p := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [periodicEnd,dite_eq_left (show v.succ.val < N from hv)]
      have he : (⟨v.succ.val,hv⟩ : Fin N) = ⟨a.val+j.val,hjN⟩ := Fin.ext (by dsimp only [v]; simp only [Fin.val_succ]; omega)
      rw [he]
      exact lt_of_not_ge hn
    obtain ⟨t,ht⟩ := hdes v hd
    have hat : c r.castSucc < c t := by
      rw [ht]
      change a.val < a.val+i.val+1
      omega
    have htb : c t < c r.succ := by
      rw [ht]
      change a.val+i.val+1 < b.val
      have := j.isLt
      omega
    have h₁ := c.lt_iff_lt.mp hat
    have h₂ := c.lt_iff_lt.mp htb
    change r.val < t.val at h₁
    change t.val < r.val+1 at h₂
    omega
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact hm hij.le

noncomputable def cutSet (hN : 0 < N) (p : Fin N → ℤ) : Finset (Fin (N+1)) :=
  insert 0 (insert (Fin.last N) ((descents hN p).image Fin.succ))
lemma cuts_enumeration (hN : 0 < N) (p : Fin N → ℤ) :
    ∃ L : ℕ, ∃ c : Fin (L+1) ↪o Fin (N+1),
      c 0 = 0 ∧ c (Fin.last L) = Fin.last N ∧ Set.range c = cutSet hN p := by
  classical
  let S := cutSet hN p
  have h0 : (0 : Fin (N+1)) ∈ S := Finset.mem_insert_self _ _
  have hn : Fin.last N ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨0,h0⟩
  have hcard : S.card = (S.card-1)+1 := by omega
  let c := S.orderEmbOfFin hcard
  have hr : Set.range c = S := Finset.range_orderEmbOfFin S hcard
  obtain ⟨i,hi⟩ : ∃ i, c i = 0 := by exact (hr ▸ h0 : (0 : Fin (N+1)) ∈ Set.range c)
  obtain ⟨j,hj⟩ : ∃ j, c j = Fin.last N := by exact (hr ▸ hn : Fin.last N ∈ Set.range c)
  refine ⟨S.card-1,c,?_,?_,hr⟩
  · apply le_antisymm _ (Fin.zero_le _)
    exact hi ▸ c.monotone (Fin.zero_le i)
  · apply le_antisymm (Fin.le_last _) _
    exact hj ▸ c.monotone (Fin.le_last j)
end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open AffineWindow
variable {K : Type} [Field K] {N : ℕ}
variable (C D : ResidueChamber (K := K) (N := N))

theorem descent_minimum (hN : 0 < N) (ht : C.top = D.top)
    (hstage : ∀ r ∈ descents hN C.window, C.stage r.succ = D.stage r.succ) : C.length ≤ D.length := by
  classical
  obtain ⟨L,c,hc0,hcN,hcrange⟩ := cuts_enumeration hN C.window
  refine C.fixed_stage_minimum D hN ht c c.monotone hc0 hcN ?_ ?_
  · intro r
    have hr : c r ∈ cutSet hN C.window := by
      change c r ∈ (↑(cutSet hN C.window) : Set _)
      rw [← hcrange]
      exact Set.mem_range_self r
    rcases Finset.mem_insert.mp hr with he | hr
    · rw [he,C.initial,D.initial,ht]
    · rcases Finset.mem_insert.mp hr with he | hr
      · rw [he,C.terminal,D.terminal,ht]
      · obtain ⟨s,hs,he⟩ := Finset.mem_image.mp hr
        rw [← he]
        exact hstage s hs
  · apply slices_sorted_of_descents hN C.window c
    intro r hr
    rw [hcrange]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r,hr,rfl⟩))
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
lemma increments_card (C : ResidueChamber (K := K) (N := N)) (r : Fin (N+1)) :
    (incrementSet C.top (C.stage r) C.hasTop (C.hasStage r)).card = r.val := by
  classical
  induction r using Fin.induction with
  | zero => simp only [C.increments,Fin.val_zero,Nat.not_lt_zero,Finset.filter_false,Finset.card_empty]
  | succ r ih => rw [(C.word_spec r).1,Finset.card_insert_of_notMem (C.word_spec r).2,ih]; rfl
lemma stage_index_eq (C D : ResidueChamber (K := K) (N := N)) (ht : C.top = D.top)
    (r s : Fin (N+1)) (he : C.stage r = D.stage s) : r = s := by
  apply Fin.ext
  have hc := C.increments_card r
  have hd := D.increments_card s
  simp only [ht,he] at hc
  exact hc.symm.trans hd
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N : ℕ}
lemma vertex_index_eq (C D : ResidueChamber (K := K) (N := N))
    (hC : PolyBounded C.top) (hD : PolyBounded D.top) (hN : 0 < N)
    (ht : C.top = D.top) (r s : Fin N)
    (he : vertex C hC hN r = vertex D hD hN s) : r = s := by
  exact Fin.castSucc_injective _ (C.stage_index_eq D ht _ _
    (stage_eq_of_vertex_eq C D hC hD hN ht r s he))
lemma shared_vertex_stage (C D : ResidueChamber (K := K) (N := N))
    (hC : PolyBounded C.top) (hD : PolyBounded D.top) (hN : 0 < N)
    (ht : C.top = D.top) (r : Fin N) (hr : vertex C hC hN r ∈ face D hD hN) :
    C.stage r.castSucc = D.stage r.castSucc := by
  obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hr
  have he := vertex_index_eq C D hC hD hN ht r s hs.symm
  subst s
  exact stage_eq_of_vertex_eq C D hC hD hN ht r r hs.symm

noncomputable def descentCore {M : ℕ} (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) : Finset (Vertex K (M+2)) :=
  (AffineWindow.descents (by omega) C.window).image
    (fun r => vertex C hC (by omega) (finRotate (M+2) r))
lemma full_descentCore {M : ℕ} (E : FullChamber K (M+2) (by omega)) :
    descentCore E.polynomialChamber (polyBounded_vertex _) = E.descentCore := by
  unfold descentCore FullChamber.descentCore
  congr 1
  funext r
  exact full_vertex E _

theorem core_minimum_same_top {M : ℕ} (C D : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) (hD : PolyBounded D.top) (ht : C.top = D.top)
    (hcore : descentCore C hC ⊆ face D hD (by omega)) : C.length ≤ D.length := by
  apply C.descent_minimum D (by omega) ht
  intro r hr
  by_cases hlast : r.val = M+1
  · have he : r.succ = Fin.last (M+2) := Fin.ext (by change r.val+1 = M+2; omega)
    rw [he,C.terminal,D.terminal,ht]
  · have hlt : r.val < M+1 := by have := r.isLt; omega
    have hh := hcore (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
    rw [finRotate_of_lt hlt] at hh
    exact shared_vertex_stage C D hC hD (by omega) ht ⟨r.val+1,by omega⟩ hh
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open AffineWindow
variable {K : Type} [Field K] {M : ℕ}
lemma rotate_window_of_lt (C : ResidueChamber (K := K) (N := M+2))
    (r : Fin (M+2)) (hr : r.val < M+1) :
    (C.rotate (by omega)).window r = C.window ⟨r.val+1,by omega⟩ :=
  C.rotate_window_castSucc ⟨r.val,hr⟩
lemma rotate_descent_iff (C : ResidueChamber (K := K) (N := M+2)) (r : Fin (M+2)) :
    r ∈ descents (by omega) (C.rotate (by omega)).window ↔
      finRotate (M+2) r ∈ descents (by omega) C.window := by
  classical
  simp only [descents,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hr : r.val < M+1
  · rw [finRotate_of_lt hr,C.rotate_window_of_lt r hr]
    rw [periodicEnd,dite_eq_left (show r.succ.val < M+2 by change r.val+1 < M+2; omega)]
    by_cases hrr : r.val+1 < M+1
    · rw [C.rotate_window_of_lt _ hrr]
      rw [periodicEnd,dite_eq_left (show (⟨r.val+1,by omega⟩ : Fin (M+2)).succ.val < M+2 by change r.val+1+1 < M+2; omega)]
      rfl
    · have he : (⟨r.succ.val,by change r.val+1 < M+2; omega⟩ : Fin (M+2)) = Fin.last (M+1) :=
        Fin.ext (by change r.val+1 = M+1; omega)
      rw [he,C.rotate_window_last]
      rw [periodicEnd,dite_eq_right (show ¬ (⟨r.val+1,by omega⟩ : Fin (M+2)).succ.val < M+2 by change ¬ r.val+1+1 < M+2; omega)]
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      rfl
  · have he : r = Fin.last (M+1) := Fin.ext (by have := r.isLt; change r.val = M+1; omega)
    subst r
    rw [finRotate_last,C.rotate_window_last,periodicEnd,dite_eq_right (by simp)]
    change (C.rotate (by omega)).window 0 + (↑(M+2) : ℤ) < _ ↔ _
    rw [C.rotate_window_of_lt 0 (by simp)]
    rw [periodicEnd,dite_eq_left (by simp)]
    simp only [Fin.val_zero,Fin.val_succ,zero_add]
    omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow
variable {K : Type} [Field K] {M : ℕ}
lemma scale_descentCore (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) (m : ℕ) :
    descentCore (C.scale m) (hC.powerShift m) = descentCore C hC := by
  classical
  have hd : descents (by omega) (C.scale m).window = descents (by omega) C.window := by
    ext r
    simp only [descents,Finset.mem_filter,Finset.mem_univ,true_and,C.scale_window]
    unfold periodicEnd
    split_ifs <;> rw [C.scale_window] <;> omega
  unfold descentCore
  rw [hd]
  congr 1
  funext r
  exact scale_vertex C hC m (by omega) _
lemma rotate_descentCore (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) :
    descentCore (C.rotate (by omega)) (rotate_bounded C hC _) = descentCore C hC := by
  classical
  ext v
  simp only [descentCore,Finset.mem_image]
  constructor
  · rintro ⟨r,hr,he⟩
    refine ⟨finRotate (M+2) r,(C.rotate_descent_iff r).mp hr,?_⟩
    rw [rotate_vertex] at he
    exact he
  · rintro ⟨r,hr,he⟩
    obtain ⟨s,hs⟩ := (finRotate (M+2)).surjective r
    refine ⟨s,(C.rotate_descent_iff s).mpr (hs ▸ hr),?_⟩
    rw [rotate_vertex,hs]
    exact he
lemma reroot_descentCore (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) (j : ℕ) :
    descentCore (C.reroot (by omega) j) (reroot_bounded C hC _ j) = descentCore C hC := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [C.reroot_succ]
    exact (rotate_descentCore _ (reroot_bounded C hC _ j)).trans ih
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow
variable {K : Type} [Field K] {M : ℕ}
lemma descentCore_subset (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) : descentCore C hC ⊆ face C hC (by omega) := by
  intro v hv
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨finRotate (M+2) r,Finset.mem_univ _,rfl⟩
lemma descentCore_nonempty (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) (hp : 0 < C.length) : (descentCore C hC).Nonempty := by
  apply Finset.Nonempty.image
  apply descents_nonempty
  · intro r s he
    dsimp only at he
    rw [C.window_mod (by omega),C.window_mod (by omega)] at he
    exact C.word.injective (Fin.ext (by exact_mod_cast he))
  · exact hp

theorem core_minimum (C D : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) (hD : PolyBounded D.top)
    (hcore : descentCore C hC ⊆ face D hD (by omega)) : C.length ≤ D.length := by
  classical
  by_cases hz : C.length = 0
  · rw [hz]; exact Nat.zero_le _
  obtain ⟨A,hA⟩ := descentCore_nonempty C hC (by omega)
  obtain ⟨r,_,hr⟩ := Finset.mem_image.mp (descentCore_subset C hC hA)
  obtain ⟨s,_,hs⟩ := Finset.mem_image.mp (hcore hA)
  let R := C.reroot (by omega) r.val
  let S := D.reroot (by omega) s.val
  have hR : PolyBounded R.top := reroot_bounded C hC _ _
  have hS : PolyBounded S.top := reroot_bounded D hD _ _
  have hrt : R.top = C.stage r.castSucc := C.reroot_top _ r.val r.isLt.le
  have hst : S.top = D.stage s.castSucc := D.reroot_top _ s.val s.isLt.le
  have hh : Homothetic (shift K (M+2)) (R.top.map (polynomialEmbedding K (M+2)))
      (S.top.map (polynomialEmbedding K (M+2))) := by
    rw [hrt,hst]
    exact homothetic_trans _ (vertex_homothetic C hC (by omega) r)
      (hr ▸ hs ▸ homothetic_symm _ (vertex_homothetic D hD (by omega) s))
  obtain ⟨u,v,huv⟩ := hh
  have ht : (R.scale u).top = (S.scale v).top := by
    apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+2))
    change (powerShift R.top u).map _ = (powerShift S.top v).map _
    rw [powerShift_map_embedding,powerShift_map_embedding]
    exact huv
  have hc := core_minimum_same_top (R.scale u) (S.scale v) (hR.powerShift u) (hS.powerShift v) ht
    (by
      rw [scale_descentCore R hR u,scale_face S hS v (by omega)]
      change descentCore (C.reroot _ r.val) _ ⊆ face (D.reroot _ s.val) _ _
      rw [reroot_descentCore C hC r.val,reroot_face D hD s.val]
      exact hcore)
  simpa only [ResidueChamber.scale_length,R,S,ResidueChamber.reroot_length] using hc
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.FullChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
theorem core_minimum (C D : FullChamber K (M+2) (by omega))
    (hcore : C.descentCore ⊆ D.face) : C.length ≤ D.length := by
  apply BoundedChamber.core_minimum C.polynomialChamber D.polynomialChamber
    (polyBounded_vertex _) (polyBounded_vertex _)
  rwa [BoundedChamber.full_descentCore,BoundedChamber.full_face]
theorem core_not_previous (C : FullChamber K (M+2) (by omega)) (hp : 0 < C.length) :
    C.descentCore ∉ codistanceStage K (M+2) (by omega) (C.length-1) := by
  rintro ⟨D,hD,hcore⟩
  have hh := C.core_minimum D hcore
  omega

theorem previous_iff_missing_core (C : FullChamber K (M+2) (by omega))
    (hp : 0 < C.length) {s : Finset (Vertex K (M+2))} (hs : s ⊆ C.face) :
    s ∈ codistanceStage K (M+2) (by omega) (C.length-1) ↔ ¬ C.descentCore ⊆ s := by
  constructor
  · intro h hc
    exact C.core_not_previous hp (codistanceStage_downward _ _ _ _ h hc)
  · exact C.face_missing_descent_previous hs
end CoboundaryExpanders.RationalLattices.FullChamber

namespace CoboundaryExpanders.RationalLattices.FullChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
lemma core_eq_of_contains (C D : FullChamber K (M+2) (by omega))
    (hp : 0 < C.length) (hlen : C.length = D.length)
    (hcore : C.descentCore ⊆ D.face) : C.descentCore = D.descentCore := by
  classical
  have hpD : 0 < D.length := hlen ▸ hp
  have hn : C.descentCore ∉ codistanceStage K (M+2) (by omega) (D.length-1) := by
    rw [← hlen]; exact C.core_not_previous hp
  have hDC : D.descentCore ⊆ C.descentCore := by
    by_contra hh
    exact hn (D.face_missing_descent_previous hcore hh)
  apply Finset.Subset.antisymm _ hDC
  by_contra hh
  have hh' := C.face_missing_descent_previous (hDC.trans C.descentCore_subset) hh
  rw [hlen] at hh'
  exact D.core_not_previous hpD hh'
lemma core_eq_of_new_intersection (C D : FullChamber K (M+2) (by omega))
    (hp : 0 < C.length) (hlen : C.length = D.length)
    {s : Finset (Vertex K (M+2))} (hC : s ⊆ C.face) (hD : s ⊆ D.face)
    (hs : s ∉ codistanceStage K (M+2) (by omega) (C.length-1)) :
    C.descentCore = D.descentCore := by
  classical
  have hh : C.descentCore ⊆ s := by
    by_contra hh
    exact hs (C.face_missing_descent_previous hC hh)
  exact C.core_eq_of_contains D hp hlen (hh.trans hD)
end CoboundaryExpanders.RationalLattices.FullChamber

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
def codistanceBlock (m : ℕ) (A : Finset (Vertex K (M+2))) : Set (Finset (Vertex K (M+2))) :=
  {s | ∃ C : FullChamber K (M+2) (by omega), C.length = m+1 ∧ C.descentCore = A ∧ s ⊆ C.face}
lemma codistanceBlock_downward (m : ℕ) (A : Finset (Vertex K (M+2)))
    {s t : Finset (Vertex K (M+2))} (hs : s ∈ codistanceBlock m A) (ht : t ⊆ s) :
    t ∈ codistanceBlock m A := by
  obtain ⟨C,hC,hA,hs⟩ := hs
  exact ⟨C,hC,hA,ht.trans hs⟩
lemma codistanceBlock_old_iff (m : ℕ) (A : Finset (Vertex K (M+2)))
    {s : Finset (Vertex K (M+2))} (hs : s ∈ codistanceBlock m A) :
    s ∈ codistanceStage K (M+2) (by omega) m ↔ ¬ A ⊆ s := by
  obtain ⟨C,hC,rfl,hs⟩ := hs
  have hh := C.previous_iff_missing_core (by omega) hs
  simpa only [hC,Nat.add_sub_cancel] using hh
lemma codistanceBlock_intersection (m : ℕ) (A B : Finset (Vertex K (M+2))) (hne : A ≠ B) :
    codistanceBlock m A ∩ codistanceBlock m B ⊆ codistanceStage K (M+2) (by omega) m := by
  classical
  intro s hs
  by_contra hn
  obtain ⟨C,hC,hA,hsC⟩ := hs.1
  obtain ⟨D,hD,hB,hsD⟩ := hs.2
  apply hne
  rw [← hA,← hB]
  exact C.core_eq_of_new_intersection D (by omega) (hC.trans hD.symm) hsC hsD
    (by simpa only [hC,Nat.add_sub_cancel] using hn)
theorem codistanceStage_successor (m : ℕ) :
    codistanceStage K (M+2) (by omega) (m+1) =
      codistanceStage K (M+2) (by omega) m ∪ ⋃ A, codistanceBlock m A := by
  ext s
  constructor
  · rintro ⟨C,hC,hs⟩
    by_cases he : C.length = m+1
    · exact Or.inr (Set.mem_iUnion.mpr ⟨C.descentCore,C,he,rfl,hs⟩)
    · exact Or.inl ⟨C,by omega,hs⟩
  · rintro (⟨C,hC,hs⟩ | hs)
    · exact ⟨C,by omega,hs⟩
    · obtain ⟨A,C,hC,_,hs⟩ := Set.mem_iUnion.mp hs
      exact ⟨C,by omega,hs⟩

def codistanceLink (m : ℕ) (A : Finset (Vertex K (M+2))) :
    Set (Finset (Vertex K (M+2))) := {s | Disjoint A s ∧ s ∈ codistanceBlock m A}
lemma codistanceBlock_join (m : ℕ) (A s : Finset (Vertex K (M+2))) :
    s ∈ codistanceBlock m A ↔ ∃ u v, u ⊆ A ∧ v ∈ codistanceLink m A ∧ s = u ∪ v := by
  classical
  constructor
  · intro hs
    refine ⟨s ∩ A,s \ A,Finset.inter_subset_right,⟨(by apply Finset.disjoint_left.mpr; intro v hv hv'; exact (Finset.mem_sdiff.mp hv').2 hv),
      codistanceBlock_downward m A hs Finset.sdiff_subset⟩,?_⟩
    ext v
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  · rintro ⟨u,v,hu,⟨_,C,hC,hA,hv⟩,rfl⟩
    refine ⟨C,hC,hA,Finset.union_subset ?_ hv⟩
    exact hu.trans (hA ▸ C.descentCore_subset)
end CoboundaryExpanders.RationalLattices

end

end OAI
