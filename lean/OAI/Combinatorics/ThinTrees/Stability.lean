import OAI.Combinatorics.ThinTrees.Expectation

namespace OAI

universe uI uI2 uA uD uI3 uD2

section

namespace StrongThinTree.MSS
noncomputable section
open Finset Polynomial
open scoped Classical ComplexOrder

def Stable {I : Type uI} (p : MvPolynomial I ℂ) : Prop :=
  ∀z : I → ℂ, (∀i, 0 < (z i).im) → MvPolynomial.eval z p ≠ 0

variable {I : Type uI2} [DecidableEq I]

def slice (p : MvPolynomial I ℂ) (z : I → ℂ) (i : I) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun j => if j=i then Polynomial.X else Polynomial.C (z j)) p

lemma slice_eval (p : MvPolynomial I ℂ) (z : I → ℂ) (i : I) (w : ℂ) :
    (slice p z i).eval w = MvPolynomial.eval (Function.update z i w) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slice]
  | add p q hp hq => simpa [slice,MvPolynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | mul_X p j hp =>
    simp only [slice] at hp
    by_cases hji : j=i
    · subst j
      simp [slice,MvPolynomial.eval₂_mul,hp]
    · simp [slice,MvPolynomial.eval₂_mul,hji,hp]

lemma slice_derivative (p : MvPolynomial I ℂ) (z : I → ℂ) (i : I) :
    (slice p z i).derivative = slice (MvPolynomial.pderiv i p) z i := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slice]
  | add p q hp hq =>
    simp only [slice] at hp hq
    simp [slice,MvPolynomial.eval₂_add,hp,hq]
  | mul_X p j hp =>
    simp only [slice] at hp
    rw [MvPolynomial.pderiv_mul]
    by_cases hji : j=i
    · subst j
      simp [slice,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_add,Polynomial.derivative_mul,hp]
    · simp [slice,MvPolynomial.eval₂_mul,Polynomial.derivative_mul,
        MvPolynomial.pderiv_X,hji,hp]

lemma slice_eval_self (p : MvPolynomial I ℂ) (z : I → ℂ) (i : I) :
    (slice p z i).eval (z i) = MvPolynomial.eval z p := by
  simpa using slice_eval p z i (z i)

lemma slice_derivative_eval_self (p : MvPolynomial I ℂ) (z : I → ℂ) (i : I) :
    (slice p z i).derivative.eval (z i) = MvPolynomial.eval z (MvPolynomial.pderiv i p) := by
  rw [slice_derivative,slice_eval_self]

lemma inverse_difference_im_neg {z a : ℂ} (hz : 0 < z.im) (ha : a.im ≤ 0) :
    (1/(z-a)).im < 0 := by
  have hd : 0 < (z-a).im := by simp only [Complex.sub_im]; linarith
  have hd0 : z-a ≠ 0 := fun h => by simpa [h] using hd.ne'
  simp only [one_div,Complex.inv_im]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hd) (Complex.normSq_pos.mpr hd0)

lemma polynomial_log_derivative {p : Polynomial ℂ} {z : ℂ}
    (hz : 0 < z.im) (hp : ∀w : ℂ, 0 < w.im → p.eval w ≠ 0) :
    p.derivative.eval z / p.eval z = 0 ∨ (p.derivative.eval z / p.eval z).im < 0 := by
  have hp0 : p ≠ 0 := fun h => by simpa [h] using hp z hz
  have hr : ∀a ∈ p.roots, a.im ≤ 0 := by
    intro a ha
    by_contra h
    exact hp a (lt_of_not_ge h) ((Polynomial.mem_roots hp0).mp ha)
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero (hp z hz)]
  by_cases hempty : p.roots = 0
  · left
    simp [hempty]
  · right
    have hsum : ∀s : Multiset ℂ, (∀a ∈ s, a.im ≤ 0) → s ≠ 0 →
        ((s.map (fun a => 1/(z-a))).sum).im < 0 := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | @cons a s ih =>
        intro hs _
        have ha := inverse_difference_im_neg hz (hs a (by simp))
        have hsn : ∀b ∈ s, b.im ≤ 0 := fun b hb => hs b (by simp [hb])
        by_cases he : s=0
        · simp only [he,Multiset.map_cons,Multiset.map_zero,Multiset.sum_cons,Multiset.sum_zero,add_zero]
          exact ha
        · have hh := ih hsn he
          simp only [Multiset.map_cons,Multiset.sum_cons,Complex.add_im]
          linarith
    exact hsum _ hr hempty

lemma Stable.sub_pderiv {p : MvPolynomial I ℂ} (hp : Stable p) (i : I) :
    Stable (p-MvPolynomial.pderiv i p) := by
  intro z hz
  have hslice : ∀w : ℂ, 0 < w.im → (slice p z i).eval w ≠ 0 := by
    intro w hw
    rw [slice_eval]
    apply hp
    intro j
    by_cases hji : j=i
    · subst j
      simpa using hw
    · simpa [Function.update_of_ne hji] using hz j
  have hh := polynomial_log_derivative (hz i) hslice
  rw [slice_derivative_eval_self,slice_eval_self] at hh
  intro heq
  have heq' : MvPolynomial.eval z (MvPolynomial.pderiv i p) = MvPolynomial.eval z p := by
    exact (sub_eq_zero.mp (by simpa only [MvPolynomial.eval_sub] using heq)).symm
  rw [heq',div_self (hp z hz)] at hh
  rcases hh with hh | hh
  · exact one_ne_zero hh
  · simp at hh

lemma factor_norm_bound {z a r : ℂ} (hz : 0 < z.im) (hr : r.im ≤ 0) :
    ‖a-r‖ ≤ (1+‖a-z‖/z.im)*‖z-r‖ := by
  have hzr : z.im ≤ ‖z-r‖ := by
    have hh := Complex.abs_im_le_norm (z-r)
    have hh' := le_abs_self (z-r).im
    simp only [Complex.sub_im] at hh hh'
    linarith
  have htriangle : ‖a-r‖ ≤ ‖a-z‖+‖z-r‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a-z) (z-r)
  have hh := mul_le_mul_of_nonneg_left hzr (div_nonneg (norm_nonneg (a-z)) hz.le)
  have he : (‖a-z‖/z.im)*z.im = ‖a-z‖ := div_mul_cancel₀ _ hz.ne'
  nlinarith only [hh,he,htriangle]

lemma stable_eval_norm_bound {p : Polynomial ℂ} {z : ℂ} (hz : 0 < z.im)
    (hp : ∀w : ℂ, 0 < w.im → p.eval w ≠ 0) (a : ℂ) {D : ℕ}
    (hD : p.natDegree ≤ D) :
    ‖p.eval a‖ ≤ ‖p.eval z‖*(1+‖a-z‖/z.im)^D := by
  have hp0 : p ≠ 0 := fun h => by simpa [h] using hp z hz
  have hr : ∀r ∈ p.roots, r.im ≤ 0 := by
    intro r hr
    by_contra hh
    exact hp r (lt_of_not_ge hh) ((Polynomial.mem_roots hp0).mp hr)
  let C := 1+‖a-z‖/z.im
  have hC : 1 ≤ C := le_add_of_nonneg_right (div_nonneg (norm_nonneg _) hz.le)
  have hg : ∀s : Multiset ℂ, (∀r ∈ s, r.im ≤ 0) →
      ‖(s.map (fun r => a-r)).prod‖ ≤ C^s.card*‖(s.map (fun r => z-r)).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons r s ih =>
      intro hrs
      have h1 := factor_norm_bound (a := a) hz (hrs r (by simp))
      have h2 := ih (fun u hu => hrs u (by simp [hu]))
      have hm := mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (zero_le_one.trans hC) (norm_nonneg _))
      simpa only [Multiset.map_cons,Multiset.prod_cons,Multiset.card_cons,norm_mul,pow_succ,
        mul_assoc,mul_left_comm,mul_comm] using hm
  have hroot := hg p.roots hr
  have hdeg : C^p.roots.card ≤ C^D := by
    rw [←(IsAlgClosed.splits p).natDegree_eq_card_roots]
    exact pow_le_pow_right₀ hC hD
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots a,(IsAlgClosed.splits p).eval_eq_prod_roots z]
  simp only [norm_mul]
  have h1 := mul_le_mul_of_nonneg_left hroot (norm_nonneg p.leadingCoeff)
  have h2 := mul_le_mul_of_nonneg_left hdeg
    (mul_nonneg (norm_nonneg p.leadingCoeff) (norm_nonneg ((p.roots.map (fun r => z-r)).prod)))
  nlinarith only [h1,h2]

lemma polynomial_stability_limit {A : Type uA} {L : Filter A} [L.NeBot]
    (f : A → Polynomial ℂ) (p : Polynomial ℂ) {D : ℕ}
    (hD : ∀ᶠa in L, (f a).natDegree ≤ D)
    (hf : ∀ᶠa in L, ∀z : ℂ, 0 < z.im → (f a).eval z ≠ 0)
    (hlim : ∀z : ℂ, Filter.Tendsto (fun a => (f a).eval z) L (nhds (p.eval z)))
    (hp : p ≠ 0) : ∀z : ℂ, 0 < z.im → p.eval z ≠ 0 := by
  intro z hz hzero
  have hvanish : ∀w : ℂ, 0 < w.im → p.eval w = 0 := by
    intro w hw
    have hb : ‖p.eval w‖ ≤ ‖p.eval z‖*(1+‖w-z‖/z.im)^D :=
      le_of_tendsto_of_tendsto (hlim w).norm ((hlim z).norm.mul_const _) (by
        filter_upwards [hD,hf] with a hDa hfa
        exact stable_eval_norm_bound hz hfa w hDa)
    rw [hzero,norm_zero,zero_mul] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  have hinj : Function.Injective (fun k : ℕ => (k:ℂ)+Complex.I) := by
    intro k l h
    have hh := congrArg Complex.re h
    simpa only [Complex.add_re,Complex.natCast_re,Complex.I_re,add_zero,Nat.cast_inj] using hh
  have hinf := Set.infinite_range_of_injective hinj
  have hroots : Set.range (fun k : ℕ => (k:ℂ)+Complex.I) ⊆ {w | p.IsRoot w} := by
    rintro w ⟨k,rfl⟩
    exact hvanish _ (by simp)
  exact hp (p.eq_zero_of_infinite_isRoot (hinf.mono hroots))

lemma slice_degree_bound (p : MvPolynomial I ℂ) :
    ∃D : ℕ, ∀z i, (slice p z i).natDegree ≤ D := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0,fun z i => by simp [slice]⟩
  | add p q hp hq =>
    obtain ⟨P,hP⟩ := hp
    obtain ⟨Q,hQ⟩ := hq
    refine ⟨max P Q,fun z i => ?_⟩
    have he : slice (p+q) z i = slice p z i+slice q z i := by simp [slice,MvPolynomial.eval₂_add]
    rw [he]
    exact (Polynomial.natDegree_add_le _ _).trans (max_le_max (hP z i) (hQ z i))
  | mul_X p j hp =>
    obtain ⟨P,hP⟩ := hp
    refine ⟨P+1,fun z i => ?_⟩
    have he : slice (p*MvPolynomial.X j) z i = slice p z i * (if j=i then Polynomial.X else Polynomial.C (z j)) := by
      simp [slice,MvPolynomial.eval₂_mul]
    rw [he]
    calc
      _ ≤ (slice p z i).natDegree+(if j=i then Polynomial.X else Polynomial.C (z j)).natDegree := Polynomial.natDegree_mul_le
      _ ≤ P+1 := by have hh := hP z i; split_ifs <;> simp only [Polynomial.natDegree_X,Polynomial.natDegree_C] <;> omega

lemma Stable.slice_boundary {p : MvPolynomial I ℂ} (hp : Stable p)
    (z : I → ℂ) (hz : ∀j, 0 ≤ (z j).im) (i : I)
    (h0 : slice p z i ≠ 0) :
    ∀w : ℂ, 0 < w.im → (slice p z i).eval w ≠ 0 := by
  obtain ⟨D,hD⟩ := slice_degree_bound p
  let f : ℝ → Polynomial ℂ := fun t => slice p (fun j => z j+(t:ℂ)*Complex.I) i
  apply polynomial_stability_limit (L := nhdsWithin (0:ℝ) (Set.Ioi 0)) f (slice p z i)
    (D := D) (Filter.Eventually.of_forall (fun t => hD _ _)) _ _ h0
  · filter_upwards [self_mem_nhdsWithin] with t ht
    intro w hw
    rw [slice_eval]
    apply hp
    intro j
    by_cases hji : j=i
    · subst j
      simpa using hw
    · simp only [Function.update_of_ne hji,Complex.add_im,Complex.mul_im,
        Complex.ofReal_re,Complex.I_im,mul_one,Complex.ofReal_im,
        Complex.I_re,mul_zero,add_zero]
      exact add_pos_of_nonneg_of_pos (hz j) ht
  · intro w
    have hc : Continuous (fun t : ℝ =>
        MvPolynomial.eval (Function.update (fun j => z j+(t:ℂ)*Complex.I) i w) p) := by
      apply (MvPolynomial.continuous_eval p).comp
      apply continuous_pi
      intro j
      by_cases hji : j=i
      · subst j
        simpa using (continuous_const : Continuous (fun _ : ℝ => w))
      · simp only [Function.update_of_ne hji]
        fun_prop
    have hh := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa only [f,slice_eval,Complex.ofReal_zero,zero_mul,add_zero] using hh

lemma splits_of_upper_half_plane (p : Polynomial ℝ)
    (hp : ∀w : ℂ, 0 < w.im → (p.map (algebraMap ℝ ℂ)).eval w ≠ 0) : p.Splits := by
  apply Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _)
  intro a ha
  have hroot := Polynomial.isRoot_of_mem_roots ha
  have haeval : Polynomial.aeval a p=0 := by
    simpa only [Polynomial.IsRoot,Polynomial.eval_map,Polynomial.aeval_def] using hroot
  have hle : a.im ≤ 0 := by
    by_contra hh
    exact hp a (lt_of_not_ge hh) hroot
  have hge : 0 ≤ a.im := by
    by_contra hh
    have hconj : (p.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ a)=0 := by
      simp only [Polynomial.eval_map,←Polynomial.aeval_def,Polynomial.aeval_conj,haeval,map_zero]
    exact hp _ (by simpa only [Complex.conj_im] using neg_pos.mpr (lt_of_not_ge hh)) hconj
  refine ⟨a.re,?_⟩
  apply Complex.ext
  · rfl
  · change 0 = a.im
    exact (le_antisymm hle hge).symm

section Determinant
open Matrix
variable {D : Type uD} [Fintype D] [DecidableEq D] [Fintype I]

omit [DecidableEq I] in
lemma stable_matrix_pencil (A : I → Matrix D D ℂ)
    (hA : ∀i, (A i).PosSemidef) (hSum : (∑i, A i).PosDef) (z : I → ℂ)
    (hz : ∀i, 0 < (z i).im) : (∑i, z i • A i).det ≠ 0 := by
  let M := ∑i, z i • A i
  have hker : ∀x : D → ℂ, M*ᵥx=0 → x=0 := by
    intro x hx
    by_contra hx0
    let a : I → ℂ := fun i => star x ⬝ᵥ (A i)*ᵥx
    have ha : ∀i, 0 ≤ a i := fun i => (hA i).dotProduct_mulVec_nonneg x
    have haR : ∀i, 0 ≤ (a i).re := fun i => (Complex.nonneg_iff.mp (ha i)).1
    have haI : ∀i, (a i).im=0 := fun i => (Complex.nonneg_iff.mp (ha i)).2.symm
    have hs : 0 < ∑i, (a i).re := by
      have hh := (Complex.pos_iff.mp (hSum.dotProduct_mulVec_pos hx0)).1
      simpa only [sum_mulVec,dotProduct_sum,Complex.re_sum] using hh
    obtain ⟨j,hj,hjpos⟩ := (sum_pos_iff_of_nonneg (fun i _ => haR i)).mp hs
    have hpos : 0 < ∑i, (z i).im*(a i).re :=
      (sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hz i).le (haR i))).mpr
        ⟨j,mem_univ _,mul_pos (hz j) hjpos⟩
    have hzero : ∑i, z i*a i=0 := by
      have hh := congrArg (fun y => star x ⬝ᵥ y) hx
      simpa only [M,sum_mulVec,smul_mulVec,dotProduct_sum,dotProduct_smul,
        smul_eq_mul,dotProduct_zero] using hh
    have him : (∑i, (z i).im*(a i).re)=0 := by
      have hh := congrArg Complex.im hzero
      simpa only [Complex.im_sum,Complex.mul_im,haI,mul_zero,zero_add,Complex.zero_im] using hh
    linarith only [hpos,him]
  have hinj : Function.Injective M.mulVec := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hker
    rw [mulVec_sub,hxy,sub_self]
  exact isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det M).mp (mulVec_injective_iff_isUnit.mp hinj))

def determinantPencil (A : I → Matrix D D ℂ) : MvPolynomial I ℂ :=
  Matrix.det (fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b))

omit [DecidableEq I] in
lemma determinantPencil_eval (A : I → Matrix D D ℂ) (z : I → ℂ) :
    MvPolynomial.eval z (determinantPencil A) = (∑i, z i • A i).det := by
  let M : Matrix D D (MvPolynomial I ℂ) := fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)
  change (MvPolynomial.eval z) M.det = _
  rw [(MvPolynomial.eval z).map_det M]
  congr 1
  ext a b
  change (MvPolynomial.eval z) (∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)) = _
  simp [Matrix.sum_apply,Matrix.smul_apply]

omit [DecidableEq I] in
lemma determinantPencil_stable (A : I → Matrix D D ℂ)
    (hA : ∀i, (A i).PosSemidef) (hSum : (∑i, A i).PosDef) : Stable (determinantPencil A) := by
  intro z hz
  rw [determinantPencil_eval]
  exact stable_matrix_pencil A hA hSum z hz
end Determinant

end
end StrongThinTree.MSS

namespace StrongThinTree.MSS
noncomputable section
open Finset Polynomial
open scoped Classical ComplexOrder
variable {I : Type uI3} [DecidableEq I]

def differentialProduct (dirs : List I) (p : MvPolynomial I ℂ) : MvPolynomial I ℂ :=
  dirs.foldl (fun q i => q-MvPolynomial.pderiv i q) p

lemma Stable.differentialProduct {p : MvPolynomial I ℂ} (hp : Stable p) (dirs : List I) :
    Stable (differentialProduct dirs p) := by
  induction dirs generalizing p with
  | nil => exact hp
  | cons i dirs ih => exact ih (hp.sub_pderiv i)

open Matrix
variable {D : Type uD2} [Fintype D] [DecidableEq D] [Fintype I]

end
end StrongThinTree.MSS

end

end OAI
