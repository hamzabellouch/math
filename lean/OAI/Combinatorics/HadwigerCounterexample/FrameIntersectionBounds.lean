import OAI.Combinatorics.HadwigerCounterexample.TensorIntersections
import OAI.Combinatorics.HadwigerCounterexample.ConstructionScales

namespace OAI

/-! # Frame Intersection Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap
open scoped BigOperators

/-- Standard embedding padded by zeros. -/
theorem pad_matrix_inj (a b : ℕ) (h : a ≤ b) :
    ∃ M : Mat (Fin b) (Fin a), Function.Injective M.mulVec := by
  let M : Mat (Fin b) (Fin a) := (1:Mat (Fin b) (Fin b)).submatrix _root_.id (Fin.castLE h)
  have hf : Function.Injective (1:Mat (Fin b) (Fin b)).mulVec := by intro i j he; simpa using he
  refine ⟨M,Matrix.mulVec_injective_iff.mpr ?_⟩
  exact (Matrix.mulVec_injective_iff.mp hf).comp (Fin.castLE h) (Fin.castLE_injective h)

theorem bounded_pack {I : Type} [Fintype I] (S : Space (Vec I)) (k : ℕ) :
    ∃ M : Mat I (Fin k), colSp M ≤ S ∧ dim (colSp M) = min (dim S) k := by
  have h (M : Mat (Fin (dim S)) (Fin k)) : colSp (pack S*M) ≤ S := by
    rw [colSp,mulVecLin_mul,LinearMap.range_comp]
    apply le_trans (Submodule.map_mono (show _ ≤ ⊤ from le_top))
    rw [←LinearMap.range_eq_map]
    exact (colSp_pack S).le
  by_cases hs : dim S ≤ k
  · obtain ⟨M,hM⟩ := pad_matrix_inj _ _ hs
    refine ⟨pack S * Mᵀ,h _,?_⟩
    have hg : Function.Surjective Mᵀ.mulVecLin := transpose_surj_iff.mpr hM
    have hh : colSp (pack S * Mᵀ) = S := by
      rw [colSp,mulVecLin_mul,LinearMap.range_comp,
        LinearMap.range_eq_top.mpr hg,← LinearMap.range_eq_map]; exact colSp_pack S
    rw [hh,min_eq_left hs]
  · obtain ⟨M,hM⟩ := pad_matrix_inj _ _ (by omega : k ≤ dim S)
    refine ⟨pack S * M,h _,?_⟩
    have hh := mrk_inj.mp (inj_comp_mat _ _ (pack_inj S) hM)
    rw [colSp_dim,hh,Fintype.card_fin,min_eq_right (by omega)]

variable {p : Shape} {n N : ℕ}

abbrev KCand (p : Shape) (n t : ℕ) := Comp p.g → Mat (JointIdx p n) (Fin t)

def zeroPin {t : ℕ} (f : KCand p n t) : Pin p n N :=
  ⟨fun z => if z.2 then colSp (f z.1) else ⊥,0⟩

theorem largeJoin_pin {t : ℕ} {x : UnitType p n N} (h : t ≤ joins x) :
    ∃ g : KCand p n t,
      (t ≤ planRank (zeroPin (N:=N) g).sp) ∧ (zeroPin g).agree x := by
  classical
  choose M hM hg using (fun i : Comp p.g =>
    bounded_pack (ker (images x (i,true)).mulVecLin) t)
  let d (i : Comp p.g) := dim (ker (images x (i,true)).mulVecLin)
  refine ⟨M, ?_, ?_⟩
  · unfold planRank
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    change t ≤ ∑ i : Comp p.g, (dim (colSp (M i))+dim (⊥ : Submodule F (Dir p n)))
    have hb : dim (⊥ : Submodule F (Dir p n)) = 0 := finrank_bot _ _
    simp_rw [hb,add_zero,hg]
    change t ≤ ∑ i, min (d i) t
    by_cases hh : ∃ i, t ≤ d i
    · obtain ⟨i,h⟩ := hh
      exact (min_eq_right h).symm.le.trans
        (Finset.single_le_sum (fun i _ => Nat.zero_le (min (d i) t)) (Finset.mem_univ _))
    · push Not at hh
      simp_rw [min_eq_left (hh _).le]; exact h
  · rintro ⟨i,_|_⟩ a ha
    · change a ∈ (⊥ : Submodule _ _) at ha
      have he : a = 0 := by simpa using ha
      rw [he,Matrix.mulVec_zero,Matrix.mulVec_zero]
    · have he := hM i (show a ∈ colSp (M i) from (by simpa only [zeroPin,↓reduceIte] using ha))
      change _ = (0:Mat _ _)*ᵥ_
      rw [Matrix.zero_mulVec]
      exact he

theorem num_kcand (p : Shape) (n t : ℕ) :
    num (KCand p n t) = bp (num (Comp p.g) * (2*num (Full p n)) * t) := by
  have heq : Fintype.card (KCand p n t) =
      Fintype.card (Mat (JointIdx p n) (Fin t)) ^ Fintype.card (Comp p.g) :=
    Fintype.card_fun
  unfold num; rw [heq]
  push_cast
  rw [card_space, dim_mat, ← bp_mul_nat]
  have h : Fintype.card (JointIdx p n) = 2*Fintype.card (Full p n) :=
    (Fintype.card_sum ..).trans (two_mul _).symm
  rw [h,Fintype.card_fin]
  push_cast; ring_nf

theorem raw_join_cap (m : Mixer p n) (H : ∀ a : Pin p n N,
    pr (pairW (raw m N) (raw m N)) a.agree ≤ bp (-(1-1/8)*(planRank a.sp)*N)) (t : ℕ) :
    pr (pairW (raw m N) (raw m N)) (fun x => t ≤ joins x) ≤
      bp (num (Comp p.g)*(2*num (Full p n))*t - (1-1/8)*t*N) := by
  classical
  let w := pairW (raw m N) (raw m N)
  have hw (x) : 0 ≤ w x := mul_nonneg (raw_nonneg _ _) (raw_nonneg _ _)
  have hh (c : KCand p n t) :
      pr w (fun x => t ≤ planRank (zeroPin (N:=N) c).sp ∧ (zeroPin c).agree x) ≤
        bp (-(1-1/8)*(t:ℝ)*N) := by
    by_cases h : t ≤ planRank (zeroPin (N:=N) c).sp
    · simp only [h,true_and]
      apply le_trans (H _)
      apply bp_le
      have ht : (t:ℝ) ≤ planRank (zeroPin (N:=N) c).sp := by exact_mod_cast h
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith only [ht]
    · simp only [h,false_and,pr_false]
      exact (bp_pos _).le
  refine (le_trans (pr_mono (w:=w) hw (fun _ => largeJoin_pin)) (pr_exists_le hw _)).trans
    ((Finset.sum_le_sum (fun i _ => hh i)).trans_eq ?_)
  rw [sub_eq_add_neg (num (Comp p.g)*(2*num (Full p n))*t),bp_add,← num_kcand]
  simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,num]
  rw [neg_mul,neg_mul]

open Filter
/-- The stronger join restriction is exponentially likely under the stated joint cap. -/
theorem sparse_usual (p : Shape) (D : ℕ) (hd : 0 < D) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ n : ℕ in atTop, let N := M*n;
      ∀ (m : Mixer p n) (w : Wgt (UnitType p n N)),
        (∀ x, w x ≤ bp ((D:ℝ)*N) * pairW (raw m N) (raw m N) x) →
        pr w (fun x => 2*D < joins x) ≤ bp (-(D:ℝ)/2*N) := by
  have H := raw_ready p (δ:=1/8) (by norm_num)
  let a := num (Comp p.g)*4*D
  have hd' : 0 < (D:ℝ)/4 := by positivity
  have hA := columns_budget p hd' a 0 (by dsimp [a,num]; positivity) (by norm_num)
  filter_upwards [H,hA] with M hM ha
  filter_upwards [hM,eventually_ge_atTop 1] with n hn hn'
  specialize ha n hn'
  rw [add_zero] at ha
  intro N m w h
  let v := (pairW (raw m N) (raw m N))
  have hi := pr_cap (v:=v) h (fun x => 2*D < joins x)
  refine hi.trans ?_
  have hv (x) : 0 ≤ v x := mul_nonneg (raw_nonneg _ _) (raw_nonneg _ _)
  apply le_trans (mul_le_mul_of_nonneg_left (le_trans
    (pr_mono hv (p:=fun x => 2*D<joins x) (q:=fun x => 2*D≤joins x) (fun _ => le_of_lt))
    (raw_join_cap m (hn.2 m).2 (2*D))) (bp_pos _).le)
  rw [←bp_add]
  apply bp_le
  unfold a at ha
  unfold N; push_cast at ha ⊢
  linarith only [ha]

end HadwigerCounterexample

end

end OAI
