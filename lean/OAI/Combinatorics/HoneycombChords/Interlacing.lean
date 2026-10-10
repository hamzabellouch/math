import OAI.Combinatorics.HoneycombChords.PositiveFlags

namespace OAI

/-!
# Moment pencils and positive root interlacing

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
noncomputable def flagPencil (n : ℕ) (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>∫ p in Set.Ioi (0:ℝ),(p^2-r)*F i (p^2)*G j (p^2)*w p
lemma flagPencil_prefix (n : ℕ) (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ) :
    (flagPencil (n+1) F G w r).submatrix Fin.castSucc Fin.castSucc=flagPencil n F G w r := rfl
lemma flagPencil_transpose (n : ℕ) (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ) :
    (flagPencil n F G w r).transpose=flagPencil n G F w r := by
  ext i j
  apply integral_congr_ae
  filter_upwards [] with p
  ring
lemma flagPencil_pairing {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ)
    (a : Fin n → ℝ) (j : ℕ)
    (hi : ∀ i : Fin n,IntegrableOn (fun p=>(p^2-r)*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    IntegrableOn (fun p=>(p^2-r)*familyCombination F a (p^2)*G j (p^2)*w p) (Set.Ioi 0) ∧
    (∫ p in Set.Ioi (0:ℝ),(p^2-r)*familyCombination F a (p^2)*G j (p^2)*w p)=
      ∑ i,a i*(∫ p in Set.Ioi (0:ℝ),(p^2-r)*F i (p^2)*G j (p^2)*w p) := by
  have he : (fun p=>(p^2-r)*familyCombination F a (p^2)*G j (p^2)*w p)=
      fun p=>∑ i,a i*((p^2-r)*F i (p^2)*G j (p^2)*w p) := by
    funext p
    simp only [familyCombination,mul_sum,sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  constructor
  · exact integrable_finsetSum _ (fun i _=>(hi i).const_mul (a i))
  · rw [integral_finsetSum _ (fun i _=>(hi i).const_mul (a i))]
    simp only [integral_const_mul]
lemma flagPencil_kernel_last_ne {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ)
    (a : Fin (n+1) → ℝ) (ha : a ≠ 0) (hk : a ᵥ* flagPencil (n+1) F G w r=0)
    (hF : PositiveFlag F (n+1)) (hG : PositiveFlag G (n+1))
    (hFc : ∀ i : Fin (n+1),Continuous (F i)) (hGc : ∀ i : Fin (n+1),Continuous (G i))
    (hw : ∀ p,0 < p → 0 < w p)
    (hi : ∀ i j : Fin (n+1),IntegrableOn (fun p=>(p^2-r)*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    a (Fin.last n) ≠ 0 ∧ 0 < r := by
  have hoi (j : Fin (n+1)) := flagPencil_pairing F G w r a j (fun i=>hi i j)
  have ho (j : Fin (n+1)) :
      (∫ p in Set.Ioi (0:ℝ),(p^2-r)*familyCombination F a (p^2)*G j (p^2)*w p)=0 := by
    rw [(hoi j).2]
    exact congrFun hk j
  obtain ⟨Z,hZc,hZ,hr,_⟩ := flag_orthogonal_linear_zeros F G a w r (hF _ le_rfl) hG hFc hGc ha hw
    (fun j=>(hoi j).1) ho
  refine ⟨?_,hr⟩
  intro he
  let b : Fin n → ℝ := fun i=>a i.castSucc
  have hb : b ≠ 0 := by
    intro hz
    apply ha
    ext i
    refine Fin.lastCases ?_ (fun k=>?_) i
    · exact he
    · exact congrFun hz k
  have hab x : familyCombination F a x=familyCombination F b x := by
    simp [familyCombination,Fin.sum_univ_castSucc,he,b]
  have hc := familyCombination_zeros_card_lt F b (hF _ (by omega)) hb Z
    (fun x hx=>⟨((hZ x).mp hx).1,by rw [←hab];exact ((hZ x).mp hx).2⟩)
  omega
lemma flagPencil_monic_left_kernel {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ)
    (hz : (flagPencil (n+1) F G w r).det=0)
    (hF : PositiveFlag F (n+1)) (hG : PositiveFlag G (n+1))
    (hFc : ∀ i : Fin (n+1),Continuous (F i)) (hGc : ∀ i : Fin (n+1),Continuous (G i))
    (hw : ∀ p,0 < p → 0 < w p)
    (hi : ∀ i j : Fin (n+1),IntegrableOn (fun p=>(p^2-r)*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    0 < r ∧ ∃ a : Fin (n+1) → ℝ,a (Fin.last n)=1 ∧ a ᵥ* flagPencil (n+1) F G w r=0 := by
  obtain ⟨a,ha,hk⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz
  obtain ⟨hl,hr⟩ := flagPencil_kernel_last_ne F G w r a ha hk hF hG hFc hGc hw hi
  refine ⟨hr,(a (Fin.last n))⁻¹ • a,?_,?_⟩
  · simp [hl]
  · rw [smul_vecMul,hk,smul_zero]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
/-- Exact signed-border identity with positive factors at every real root.
This proves the Sturm sign needed for the second oblique comparison. -/
theorem flagPencil_sturm {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ)
    (hz : (flagPencil (n+1) F G w r).det=0)
    (hF : PositiveFlag F (n+2)) (hG : PositiveFlag G (n+2))
    (hFc : ∀ i : Fin (n+2),Continuous (F i)) (hGc : ∀ i : Fin (n+2),Continuous (G i))
    (hw : ∀ p,0 < p → 0 < w p)
    (hi : ∀ i j : Fin (n+2),IntegrableOn (fun p=>(p^2-r)*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    0 < r ∧ ∃ L R : ℝ,0 < L ∧ 0 < R ∧
      (flagPencil (n+2) F G w r).det= -(flagPencil n F G w r).det*L*R := by
  have hF' : PositiveFlag F (n+1) := fun k hk=>hF k (by omega)
  have hG' : PositiveFlag G (n+1) := fun k hk=>hG k (by omega)
  obtain ⟨hr,a,ha,hak⟩ := flagPencil_monic_left_kernel F G w r hz hF' hG'
    (fun i=>hFc i.castSucc) (fun j=>hGc j.castSucc) hw (fun i j=>hi i.castSucc j.castSucc)
  have hzt : (flagPencil (n+1) G F w r).det=0 := by
    rw [←flagPencil_transpose,det_transpose,hz]
  have hit (i j : Fin (n+2)) : IntegrableOn (fun p=>(p^2-r)*G i (p^2)*F j (p^2)*w p) (Set.Ioi 0) := by
    have he : (fun p=>(p^2-r)*G i (p^2)*F j (p^2)*w p)=(fun p=>(p^2-r)*F j (p^2)*G i (p^2)*w p) := by
      funext p
      ring
    rw [he]
    exact hi j i
  obtain ⟨_,h,hh,hht⟩ := flagPencil_monic_left_kernel G F w r hzt hG' hF'
    (fun i=>hGc i.castSucc) (fun j=>hFc j.castSucc) hw (fun i j=>hit i.castSucc j.castSucc)
  have hhk : flagPencil (n+1) F G w r *ᵥ h=0 := by
    rw [←flagPencil_transpose,vecMul_transpose] at hht
    exact hht
  let L := ∫ p in Set.Ioi (0:ℝ),(p^2-r)*familyCombination F a (p^2)*G (n+1) (p^2)*w p
  let R := ∫ p in Set.Ioi (0:ℝ),(p^2-r)*familyCombination G h (p^2)*F (n+1) (p^2)*w p
  have hL : 0 < L := by
    apply monic_cross_pairing_pos F G a w r hF' hG (fun i=>hFc i.castSucc) hGc ha hw
    · intro j
      exact (flagPencil_pairing F G w r a j (fun i=>hi i.castSucc j)).1
    · intro j
      rw [(flagPencil_pairing F G w r a j (fun i=>hi i.castSucc j.castSucc)).2]
      exact congrFun hak j
  have hR : 0 < R := by
    apply monic_cross_pairing_pos G F h w r hG' hF (fun i=>hGc i.castSucc) hFc hh hw
    · intro j
      exact (flagPencil_pairing G F w r h j (fun i=>hit i.castSucc j)).1
    · intro j
      rw [(flagPencil_pairing G F w r h j (fun i=>hit i.castSucc j.castSucc)).2]
      exact congrFun hht j
  refine ⟨hr,L,R,hL,hR,?_⟩
  have hDL : ((Fin.lastCases 0 a) ᵥ* flagPencil (n+2) F G w r) (Fin.last (n+1))=L := by
    dsimp [L]
    rw [(flagPencil_pairing F G w r a (n+1) (fun i=>hi i.castSucc (Fin.last (n+1)))).2]
    simp [vecMul,dotProduct,Fin.sum_univ_castSucc,flagPencil]
  have hDR : (flagPencil (n+2) F G w r *ᵥ (Fin.lastCases 0 h)) (Fin.last (n+1))=R := by
    rw [←vecMul_transpose,flagPencil_transpose]
    dsimp [R]
    rw [(flagPencil_pairing G F w r h (n+1) (fun i=>hit i.castSucc (Fin.last (n+1)))).2]
    simp [vecMul,dotProduct,Fin.sum_univ_castSucc,flagPencil]
  have he := det_double_border_at_nullvectors (flagPencil (n+2) F G w r) a h ha hh hak hhk
  rw [hDL,hDR] at he
  exact he
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Polynomial
noncomputable def generalizedCharpoly {n : ℕ} (W X : Matrix (Fin n) (Fin n) ℝ) : ℝ[X] :=
  (W⁻¹*X).charpoly
lemma generalizedCharpoly_monic {n : ℕ} (W X : Matrix (Fin n) (Fin n) ℝ) :
    (generalizedCharpoly W X).Monic := Matrix.charpoly_monic _
lemma generalizedCharpoly_natDegree {n : ℕ} (W X : Matrix (Fin n) (Fin n) ℝ) :
    (generalizedCharpoly W X).natDegree=n := by simp [generalizedCharpoly]
lemma generalizedCharpoly_eval {n : ℕ} (W X : Matrix (Fin n) (Fin n) ℝ)
    (hW : W.det ≠ 0) (r : ℝ) :
    W.det*(generalizedCharpoly W X).eval r = (-1:ℝ)^n*(X-r • W).det := by
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr hW
  have he : W*(Matrix.scalar (Fin n) r-W⁻¹*X)=r • W-X := by
    rw [mul_sub,←Matrix.mul_assoc,Matrix.mul_nonsing_inv W hu,Matrix.one_mul]
    rw [Matrix.scalar_apply,←Matrix.smul_eq_mul_diagonal]
  rw [generalizedCharpoly,Matrix.eval_charpoly,←Matrix.det_mul,he]
  have hn : r • W-X= -(X-r • W) := by abel
  rw [hn,Matrix.det_neg,Fintype.card_fin]
lemma generalizedCharpoly_eval_zero_iff {n : ℕ} (W X : Matrix (Fin n) (Fin n) ℝ)
    (hW : W.det ≠ 0) (r : ℝ) :
    (generalizedCharpoly W X).eval r=0 ↔ (X-r • W).det=0 := by
  have h := generalizedCharpoly_eval W X hW r
  have hs : (-1:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  exact ⟨fun hz=>by rw [hz,mul_zero] at h;exact (mul_eq_zero.mp h.symm).resolve_left hs,
    fun hz=>by rw [hz,mul_zero] at h;exact (mul_eq_zero.mp h).resolve_left hW⟩
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Polynomial
noncomputable def flagGram (n : ℕ) (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  familyGram w (fun i=>F i) (fun j=>G j)
noncomputable def flagCharacteristic (n : ℕ) (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) : ℝ[X] :=
  generalizedCharpoly (flagGram n F G w) (flagPencil n F G w 0)
lemma flagPencil_affine {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin n,IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    flagPencil n F G w r=flagPencil n F G w 0-r • flagGram n F G w := by
  ext i j
  have he : (fun p=>(p^2-r)*F i (p^2)*G j (p^2)*w p)=
      (fun p=>p^2*F i (p^2)*G j (p^2)*w p)-(fun p=>r*(F i (p^2)*G j (p^2)*w p)) := by
    funext p
    simp only [Pi.sub_apply]
    ring
  simp only [flagPencil,flagGram,familyGram,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,sub_zero,he]
  change (∫ p in Set.Ioi 0, (p^2*F i (p^2)*G j (p^2)*w p)-r*(F i (p^2)*G j (p^2)*w p)) = _
  rw [integral_sub (h2 i j) ((hi i j).const_mul r),integral_const_mul]
lemma flagPencil_integrable {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin n,IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    ∀ i j : Fin n,IntegrableOn (fun p=>(p^2-r)*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0) := by
  intro i j
  have he : (fun p=>(p^2-r)*F i (p^2)*G j (p^2)*w p)=
      (fun p=>p^2*F i (p^2)*G j (p^2)*w p)-(fun p=>r*(F i (p^2)*G j (p^2)*w p)) := by
    funext p
    simp only [Pi.sub_apply]
    ring
  rw [he]
  exact (h2 i j).sub ((hi i j).const_mul r)
lemma flagGram_det_pos {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (hF : PositiveFlag F n) (hG : PositiveFlag G n) (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    0 < (flagGram n F G w).det := familyGram_det_pos w _ _ (hF _ le_rfl) (hG _ le_rfl) hw hi
lemma flagPencil_zero_det_pos {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (hF : PositiveFlag F n) (hG : PositiveFlag G n) (hw : ∀ p,0<p → 0<w p)
    (h2 : ∀ i j : Fin n,IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    0 < (flagPencil n F G w 0).det := by
  have he : flagPencil n F G w 0=familyGram (fun p=>p^2*w p) (fun i : Fin n=>F i) (fun j : Fin n=>G j) := by
    ext i j
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  rw [he]
  apply familyGram_det_pos _ _ _ (hF _ le_rfl) (hG _ le_rfl)
  · intro p hp
    exact mul_pos (sq_pos_of_pos hp) (hw p hp)
  · intro i j
    have he' : (fun p=>F i (p^2)*G j (p^2)*(p^2*w p))=(fun p=>p^2*F i (p^2)*G j (p^2)*w p) := by
      funext p
      ring
    rw [he']
    exact h2 i j
lemma flagCharacteristic_eval {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ)
    (hW : (flagGram n F G w).det ≠ 0)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin n,IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    (flagGram n F G w).det*(flagCharacteristic n F G w).eval r=
      (-1:ℝ)^n*(flagPencil n F G w r).det := by
  rw [flagCharacteristic,generalizedCharpoly_eval _ _ hW,←flagPencil_affine F G w r hi h2]
lemma flagCharacteristic_eval_zero_iff {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ)
    (hW : (flagGram n F G w).det ≠ 0)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin n,IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    (flagCharacteristic n F G w).eval r=0 ↔ (flagPencil n F G w r).det=0 := by
  rw [flagCharacteristic,generalizedCharpoly_eval_zero_iff _ _ hW,←flagPencil_affine F G w r hi h2]
lemma flagCharacteristic_zero_sign {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (hF : PositiveFlag F n) (hG : PositiveFlag G n) (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin n,IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    0 < (-1:ℝ)^n*(flagCharacteristic n F G w).eval 0 := by
  have hW:=flagGram_det_pos F G w hF hG hw hi
  have hX:=flagPencil_zero_det_pos F G w hF hG hw h2
  have he:=flagCharacteristic_eval F G w 0 hW.ne' hi h2
  have hs : (-1:ℝ)^n*(-1:ℝ)^n=1 := by rw [←pow_add,show n+n=2*n by omega,pow_mul];norm_num
  have he' : (flagGram n F G w).det*((-1:ℝ)^n*(flagCharacteristic n F G w).eval 0)=
      (flagPencil n F G w 0).det := by
    calc
      _ = (-1:ℝ)^n*((flagGram n F G w).det*(flagCharacteristic n F G w).eval 0) := by ring
      _ = _ := by rw [he,←mul_assoc,hs,one_mul]
  exact pos_of_mul_pos_right (he'.symm ▸ hX) hW.le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset
lemma monic_eq_root_product {n : ℕ} (p : ℝ[X]) (r : Fin n → ℝ)
    (hp : p.Monic) (hd : p.natDegree=n) (hr : Function.Injective r)
    (hz : ∀ i,p.eval (r i)=0) : p=∏ i : Fin n,(X-Polynomial.C (r i)) := by
  apply eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C r univ) hp
  · exact Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hr)
      (fun i=>dvd_iff_isRoot.mpr (hz i))
  · simp [hd]
lemma product_cut_sign {n : ℕ} (r : Fin n → ℝ) (x : ℝ) (k : ℕ) (hk : k≤n)
    (hl : ∀ i : Fin n,i.val<k → r i<x) (hu : ∀ i : Fin n,k ≤ i.val → x<r i) :
    0 < (-1:ℝ)^(n-k)*(∏ i : Fin n,(x-r i)) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    by_cases he : k=n+1
    · subst k
      simp only [Nat.sub_self,pow_zero,one_mul]
      apply mul_pos
      · apply prod_pos
        intro i _
        exact sub_pos.mpr (hl i.castSucc (by omega))
      · exact sub_pos.mpr (hl (Fin.last n) (by simp))
    · have hk' : k≤n := by omega
      have h := ih (fun i=>r i.castSucc) k hk' (fun i h=>hl i.castSucc h) (fun i h=>hu i.castSucc h)
      have ht := hu (Fin.last n) (by simpa using hk')
      have hn : n+1-k=(n-k)+1 := by omega
      rw [hn,pow_succ]
      nlinarith only [mul_neg_of_pos_of_neg h (sub_neg.mpr ht)]
lemma interlacing_product_sign {n : ℕ} (a : Fin n → ℝ) (r : Fin (n+1) → ℝ)
    (hr : StrictMono r) (ha : ∀ i,a i<r i.succ) (hb : ∀ i,r i.castSucc<a i)
    (j : Fin (n+1)) :
    0 < (-1:ℝ)^(n-j.val)*(∏ i : Fin n,(r j-a i)) := by
  apply product_cut_sign a (r j) j.val (by omega)
  · intro i hij
    exact (ha i).trans_le (hr.monotone (show i.succ≤j by exact hij))
  · intro i hij
    exact (hr.monotone (show j ≤ i.castSucc by exact hij)).trans_lt (hb i)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Filter
lemma strictMono_lastCases_real {n : ℕ} (c : Fin n → ℝ) (R : ℝ)
    (hc : StrictMono c) (hR : ∀ i,c i<R) : StrictMono (Fin.lastCases R c) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last => exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
  | cast i =>
    cases j using Fin.lastCases with
    | last => simpa using hR i
    | cast j => simpa only [Fin.lastCases_castSucc] using hc (by simpa using hij)
lemma continuous_root_between (f : ℝ → ℝ) (a b : ℝ) (hc : Continuous f)
    (hab : a<b) (hs : f a*f b<0) : ∃ x,a<x ∧ x<b ∧ f x=0 := by
  rcases mul_neg_iff.mp hs with h|h
  · obtain ⟨x,hx,hz⟩ := intermediate_value_Ioo' hab.le hc.continuousOn (show (0:ℝ) ∈ Set.Ioo (f b) (f a) from ⟨h.2,h.1⟩)
    exact ⟨x,hx.1,hx.2,hz⟩
  · obtain ⟨x,hx,hz⟩ := intermediate_value_Ioo hab.le hc.continuousOn (show (0:ℝ) ∈ Set.Ioo (f a) (f b) from ⟨h.1,h.2⟩)
    exact ⟨x,hx.1,hx.2,hz⟩
lemma root_between_each {n : ℕ} (p : ℝ[X]) (b : Fin (n+1) → ℝ)
    (hb : StrictMono b) (hs : ∀ j : Fin n,p.eval (b j.castSucc)*p.eval (b j.succ)<0) :
    ∃ r : Fin n → ℝ,StrictMono r ∧ (∀ j,b j.castSucc<r j ∧ r j<b j.succ) ∧
      (∀ j,p.eval (r j)=0) := by
  have he (j : Fin n) := continuous_root_between (fun x=>p.eval x) (b j.castSucc) (b j.succ)
    p.continuous (hb (Fin.castSucc_lt_succ (i:=j))) (hs j)
  choose r hr using he
  refine ⟨r,?_,fun j=>⟨(hr j).1,(hr j).2.1⟩,fun j=>(hr j).2.2⟩
  intro i j hij
  exact (hr i).2.1.trans_le (hb.monotone (show i.succ ≤ j.castSucc from hij)) |>.trans (hr j).1
lemma alternating_sign_opposite (a b : ℝ) (k : ℕ)
    (ha : 0 < (-1:ℝ)^(k+1)*a) (hb : 0 < (-1:ℝ)^k*b) : a*b<0 := by
  have hh:=mul_pos ha hb
  have hp : (-1:ℝ)^k*(-1:ℝ)^k=1 := by
    rw [←pow_add,show k+k=2*k by omega,pow_mul]
    norm_num
  rw [pow_succ] at hh
  have he : ((-1:ℝ)^k*(-1)*a)*((-1:ℝ)^k*b)= -(((-1:ℝ)^k*(-1:ℝ)^k)*(a*b)) := by ring
  rw [he,hp,one_mul] at hh
  linarith
/-- A polynomial with the Sturm signs at a positive ordered node vector has a
root in each intervening interval, including the first and last. -/
theorem polynomial_sturm_intervals {n : ℕ} (p : ℝ[X]) (r : Fin n → ℝ)
    (hr : StrictMono r) (hr0 : ∀ i,0<r i)
    (hrootSigns : ∀ j,0 < (-1:ℝ)^(n-j.val)*p.eval (r j))
    (hzero : 0 < (-1:ℝ)^(n+1)*p.eval 0)
    (htop : Tendsto (fun x=>p.eval x) atTop atTop) :
    ∃ s : Fin (n+1) → ℝ,StrictMono s ∧ (∀ i,0<s i) ∧ (∀ i,p.eval (s i)=0) ∧
      (∀ i,s i.castSucc<r i ∧ r i<s i.succ) := by
  let c : Fin (n+1) → ℝ := Fin.cons 0 r
  have hc : StrictMono c := Fin.strictMono_cons.mpr ⟨hr0,hr⟩
  have hcs (j : Fin (n+1)) : 0 < (-1:ℝ)^(n+1-j.val)*p.eval (c j) := by
    refine Fin.cases ?_ (fun i=>?_) j
    · simpa [c] using hzero
    · simpa [c,Nat.succ_sub_succ_eq_sub] using hrootSigns i
  obtain ⟨R,hR0,hR⟩ := ((htop.eventually (eventually_gt_atTop 0)).and
    (eventually_gt_atTop (c (Fin.last n)))).exists
  have hRc (i : Fin (n+1)) : c i<R := (hc.monotone (Fin.le_last i)).trans_lt hR
  let b : Fin (n+2) → ℝ := Fin.lastCases R c
  have hb : StrictMono b := strictMono_lastCases_real c R hc hRc
  have hbs (j : Fin (n+1)) : p.eval (b j.castSucc)*p.eval (b j.succ)<0 := by
    refine Fin.lastCases ?_ (fun i=>?_) j
    · have hh:=hcs (Fin.last n)
      have hh' : p.eval (c (Fin.last n))<0 := by simpa using hh
      simpa [b] using mul_neg_of_neg_of_pos hh' hR0
    · have h1:=hcs i.castSucc
      have h2:=hcs i.succ
      have hn : n+1-i.castSucc.val=(n+1-i.succ.val)+1 := by simp;omega
      rw [hn] at h1
      have he:=alternating_sign_opposite _ _ _ h1 h2
      simpa only [b,←Fin.castSucc_succ,Fin.lastCases_castSucc] using he
  obtain ⟨s,hs,hbounds,hz⟩ := root_between_each p b hb hbs
  refine ⟨s,hs,?_,hz,?_⟩
  · intro i
    have h0 : b 0=0 := by
      change Fin.lastCases R c (Fin.castSucc (0:Fin (n+1)))=(0:ℝ)
      simp only [Fin.lastCases_castSucc,c,Fin.cons_zero]
    have hle : b 0 ≤ b i.castSucc := hb.monotone (Fin.zero_le _)
    rw [h0] at hle
    exact hle.trans_lt (hbounds i).1
  · intro i
    have h1:=(hbounds i.castSucc).2
    have h2:=(hbounds i.succ).1
    exact ⟨by simpa only [b,c,←Fin.castSucc_succ,Fin.lastCases_castSucc,Fin.cons_succ] using h1,by simpa only [b,c,Fin.lastCases_castSucc,Fin.cons_succ] using h2⟩
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Filter
/-- Strict positive interlacing, with the exact characteristic factorization. -/
def PositiveInterlacing (p q : ℝ[X]) (n : ℕ) : Prop :=
  ∃ a : Fin n → ℝ,∃ r : Fin (n+1) → ℝ,StrictMono a ∧ StrictMono r ∧
    (∀ i,0<a i) ∧ (∀ i,0<r i) ∧
    p=∏ i,(X-Polynomial.C (a i)) ∧ q=∏ i,(X-Polynomial.C (r i)) ∧
    (∀ i,r i.castSucc<a i ∧ a i<r i.succ)
lemma monic_polynomial_tendsto {n : ℕ} (p : ℝ[X]) (hp : p.Monic) (hd : p.natDegree=n+1) :
    Tendsto (fun x=>p.eval x) atTop atTop := by
  apply p.tendsto_atTop_of_leadingCoeff_nonneg
  · exact natDegree_pos_iff_degree_pos.mp (by omega)
  · rw [hp.leadingCoeff]
    norm_num
/-- The sign relation for a one-dimensional oblique extension implies real, simple, positive, interlacing roots for every finite prefix. -/
theorem polynomial_sturm_chain {N : ℕ} (p : ℕ → ℝ[X])
    (hm : ∀ k,k ≤ N → (p k).Monic) (hd : ∀ k,k ≤ N → (p k).natDegree=k)
    (hzero : ∀ k,k ≤ N → 0 < (-1:ℝ)^k*(p k).eval 0)
    (hstep : ∀ k,k+2 ≤ N → ∀ x,(p (k+1)).eval x=0 →
      ∃ C : ℝ,0<C ∧ (p (k+2)).eval x= -C*(p k).eval x) :
    ∀ n,n+1 ≤ N → PositiveInterlacing (p n) (p (n+1)) n := by
  intro n
  induction n with
  | zero =>
    intro hn
    let a : Fin 0 → ℝ := Fin.elim0
    have ha : StrictMono a := by intro i;exact Fin.elim0 i
    have ha0 : ∀ i,0<a i := fun i=>Fin.elim0 i
    have hz : ∀ j : Fin 0,0 < (-1:ℝ)^(0-j.val)*(p 1).eval (a j) := fun i=>Fin.elim0 i
    obtain ⟨r,hr,hr0,hrz,hra⟩ := polynomial_sturm_intervals (p 1) a ha ha0 hz (hzero _ hn)
      (monic_polynomial_tendsto (p 1) (hm _ hn) (hd _ hn))
    refine ⟨a,r,ha,hr,ha0,hr0,?_,?_,fun i=>Fin.elim0 i⟩
    · exact monic_eq_root_product (p 0) a (hm _ (by omega)) (hd _ (by omega)) ha.injective (fun i=>Fin.elim0 i)
    · exact monic_eq_root_product (p 1) r (hm _ hn) (hd _ hn) hr.injective hrz
  | succ n ih =>
    intro hn
    obtain ⟨a,r,ha,hr,ha0,hr0,hpa,hpr,hinter⟩ := ih (by omega)
    have hrz (j : Fin (n+1)) : (p (n+1)).eval (r j)=0 := by
      rw [hpr,eval_prod]
      apply prod_eq_zero (mem_univ j)
      simp
    have hsign (j : Fin (n+1)) : 0 < (-1:ℝ)^(n+1-j.val)*(p (n+2)).eval (r j) := by
      have hsmall := interlacing_product_sign a r hr (fun i=>(hinter i).2) (fun i=>(hinter i).1) j
      have hse : (p n).eval (r j)=∏ i,(r j-a i) := by simp only [hpa,eval_prod,eval_sub,eval_X,eval_C]
      rw [←hse] at hsmall
      obtain ⟨C,hC,he⟩ := hstep n (by omega) (r j) (hrz j)
      have hj : n+1-j.val=(n-j.val)+1 := by omega
      rw [hj,pow_succ,he]
      have he' : ((-1:ℝ)^(n-j.val)*(-1))*(-C*(p n).eval (r j))=C*((-1:ℝ)^(n-j.val)*(p n).eval (r j)) := by ring
      rw [he']
      exact mul_pos hC hsmall
    obtain ⟨s,hs,hs0,hsz,hsr⟩ := polynomial_sturm_intervals (p (n+2)) r hr hr0 hsign (hzero _ hn)
      (monic_polynomial_tendsto _ (hm _ hn) (hd _ hn))
    exact ⟨r,s,hr,hs,hr0,hs0,hpr,
      monic_eq_root_product _ s (hm _ hn) (hd _ hn) hs.injective hsz,hsr⟩
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset
lemma positive_fraction_mono {A B x y : ℝ} (hA : 0<A) (hAB : A<B) (hx : 0 ≤ x) (hxy : x ≤ y) :
    (A+x)/(B+x) ≤ (A+y)/(B+y) := by
  apply (div_le_div_iff₀ (by linarith : 0<B+x) (by linarith : 0<B+y)).mpr
  nlinarith only [mul_nonneg (sub_nonneg.mpr hAB.le) (sub_nonneg.mpr hxy)]
lemma interlacing_product_ratio {n : ℕ} (a : Fin n → ℝ) (r : Fin (n+1) → ℝ)
    (ha : ∀ i,0<a i) (hr : ∀ i,0<r i)
    (hi : ∀ i,r i.castSucc<a i ∧ a i<r i.succ)
    {A B : ℝ} (hA : 0<A) (hAB : A<B) :
    (A/B)*(∏ i,(A+a i)/(B+a i)) ≤ ∏ i,(A+r i)/(B+r i) ∧
      (∏ i,(A+r i)/(B+r i)) ≤ ∏ i,(A+a i)/(B+a i) := by
  let f : ℝ → ℝ := fun x=>(A+x)/(B+x)
  have hf (x : ℝ) (hx : 0 ≤ x) : 0<f x := div_pos (by linarith) (by linarith)
  have hf1 (x : ℝ) (hx : 0 ≤ x) : f x ≤ 1 := (div_le_one (by linarith : 0<B+x)).mpr (by linarith)
  constructor
  · have hfirst : A/B ≤ f (r 0) := by
      simpa [f] using positive_fraction_mono hA hAB (le_refl (0:ℝ)) (hr 0).le
    have hprod : (∏ i : Fin n,f (a i)) ≤ ∏ i : Fin n,f (r i.succ) := by
      apply prod_le_prod₀
      · intro i _;exact (hf _ (ha i).le).le
      · intro i _;exact positive_fraction_mono hA hAB (ha i).le (hi i).2.le
    change (A/B)*(∏ i : Fin n,f (a i)) ≤ ∏ i : Fin (n+1),f (r i)
    rw [Fin.prod_univ_succ]
    exact mul_le_mul hfirst hprod (prod_nonneg (fun i _=>(hf _ (ha i).le).le)) (hf _ (hr 0).le).le
  · have hprod : (∏ i : Fin n,f (r i.castSucc)) ≤ ∏ i : Fin n,f (a i) := by
      apply prod_le_prod₀
      · intro i _;exact (hf _ (hr i.castSucc).le).le
      · intro i _;exact positive_fraction_mono hA hAB (hr i.castSucc).le (hi i).1.le
    change (∏ i : Fin (n+1),f (r i)) ≤ ∏ i : Fin n,f (a i)
    rw [Fin.prod_univ_castSucc]
    calc
      _ ≤ (∏ i : Fin n,f (a i))*1 := mul_le_mul hprod (hf1 _ (hr _).le) (hf _ (hr _).le).le
        (prod_nonneg (fun i _=>(hf _ (ha i).le).le))
      _ = _ := mul_one _
lemma polynomial_product_negative_ratio {n : ℕ} (a : Fin n → ℝ) (A B : ℝ) :
    (∏ i : Fin n,(X-Polynomial.C (a i))).eval (-A)/(∏ i : Fin n,(X-Polynomial.C (a i))).eval (-B)=
      ∏ i : Fin n,(A+a i)/(B+a i) := by
  simp only [eval_prod,eval_sub,eval_X,eval_C,←prod_div_distrib]
  apply prod_congr rfl
  intro i _
  rw [show -A-a i= -(A+a i) by ring,show -B-a i= -(B+a i) by ring,neg_div_neg_eq]
theorem positive_interlacing_ratio {n : ℕ} (p q : ℝ[X]) (hi : PositiveInterlacing p q n)
    {A B : ℝ} (hA : 0<A) (hAB : A<B) :
    (A/B)*(p.eval (-A)/p.eval (-B)) ≤ q.eval (-A)/q.eval (-B) ∧
      q.eval (-A)/q.eval (-B) ≤ p.eval (-A)/p.eval (-B) := by
  obtain ⟨a,r,_,_,ha,hr,hp,hq,h⟩ := hi
  rw [hp,hq,polynomial_product_negative_ratio,polynomial_product_negative_ratio]
  exact interlacing_product_ratio a r ha hr h hA hAB
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Polynomial
lemma flagCharacteristic_sturm {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r : ℝ)
    (hz : (flagCharacteristic (n+1) F G w).eval r=0)
    (hF : PositiveFlag F (n+2)) (hG : PositiveFlag G (n+2))
    (hFc : ∀ i : Fin (n+2),Continuous (F i)) (hGc : ∀ i : Fin (n+2),Continuous (G i))
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i j : Fin (n+2),IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin (n+2),IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    ∃ C : ℝ,0<C ∧ (flagCharacteristic (n+2) F G w).eval r=
      -C*(flagCharacteristic n F G w).eval r := by
  have hF' : PositiveFlag F (n+1) := fun k hk=>hF k (by omega)
  have hG' : PositiveFlag G (n+1) := fun k hk=>hG k (by omega)
  have hFn : PositiveFlag F n := fun k hk=>hF k (by omega)
  have hGn : PositiveFlag G n := fun k hk=>hG k (by omega)
  have hW1:=flagGram_det_pos F G w hF' hG' hw (fun i j=>hi i.castSucc j.castSucc)
  have hWn:=flagGram_det_pos F G w hFn hGn hw (fun i j=>hi i.castSucc.castSucc j.castSucc.castSucc)
  have hWb:=flagGram_det_pos F G w hF hG hw hi
  have hzp := (flagCharacteristic_eval_zero_iff F G w r hW1.ne'
    (fun i j=>hi i.castSucc j.castSucc) (fun i j=>h2 i.castSucc j.castSucc)).mp hz
  obtain ⟨_,L,R,hL,hR,hborder⟩ := flagPencil_sturm F G w r hzp hF hG hFc hGc hw (flagPencil_integrable F G w r hi h2)
  have hen:=flagCharacteristic_eval F G w r hWn.ne'
    (fun i j=>hi i.castSucc.castSucc j.castSucc.castSucc) (fun i j=>h2 i.castSucc.castSucc j.castSucc.castSucc)
  have heb:=flagCharacteristic_eval F G w r hWb.ne' hi h2
  have hs : (-1:ℝ)^(n+2)=(-1:ℝ)^n := by rw [pow_add];norm_num
  have he : (flagGram (n+2) F G w).det*(flagCharacteristic (n+2) F G w).eval r=
      -((flagGram n F G w).det*(flagCharacteristic n F G w).eval r)*L*R := by
    rw [heb,hs,hborder,hen]
    ring
  let C := (flagGram n F G w).det*L*R/(flagGram (n+2) F G w).det
  refine ⟨C,div_pos (mul_pos (mul_pos hWn hL) hR) hWb,?_⟩
  apply mul_left_cancel₀ hWb.ne'
  rw [he]
  dsimp [C]
  field_simp
/-- Finite moment pencils of two positive flags have real, strictly positive, interlacing roots. -/
theorem flagCharacteristic_interlaces {N : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (hF : PositiveFlag F N) (hG : PositiveFlag G N)
    (hFc : ∀ i : Fin N,Continuous (F i)) (hGc : ∀ i : Fin N,Continuous (G i))
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i j : Fin N,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin N,IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    ∀ n,n+1 ≤ N → PositiveInterlacing (flagCharacteristic n F G w) (flagCharacteristic (n+1) F G w) n := by
  apply polynomial_sturm_chain (fun n=>flagCharacteristic n F G w)
  · intro k _
    exact generalizedCharpoly_monic _ _
  · intro k _
    exact generalizedCharpoly_natDegree _ _
  · intro k hk
    exact flagCharacteristic_zero_sign F G w (fun j hj=>hF j (hj.trans hk)) (fun j hj=>hG j (hj.trans hk)) hw
      (fun i j=>hi (i.castLE hk) (j.castLE hk)) (fun i j=>h2 (i.castLE hk) (j.castLE hk))
  · intro k hk r hz
    exact flagCharacteristic_sturm F G w r hz (fun j hj=>hF j (hj.trans hk)) (fun j hj=>hG j (hj.trans hk))
      (fun i=>hFc (i.castLE hk)) (fun i=>hGc (i.castLE hk)) hw
      (fun i j=>hi (i.castLE hk) (j.castLE hk)) (fun i j=>h2 (i.castLE hk) (j.castLE hk))
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Polynomial
lemma flagPencil_ratio {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r s : ℝ)
    (hW : (flagGram n F G w).det ≠ 0)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin n,IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    (flagPencil n F G w r).det/(flagPencil n F G w s).det=
      (flagCharacteristic n F G w).eval r/(flagCharacteristic n F G w).eval s := by
  have hr:=flagCharacteristic_eval F G w r hW hi h2
  have hs:=flagCharacteristic_eval F G w s hW hi h2
  have he:=congrArg₂ (fun a b : ℝ=>a/b) hr hs
  simpa only [mul_div_mul_left _ _ hW,mul_div_mul_left _ _ (pow_ne_zero n (by norm_num : (-1:ℝ)≠0))] using he.symm
/-- A one-dimensional determinant comparison for oblique chains with positive Chebyshev extensions. -/
theorem flagPencil_one_step {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (hF : PositiveFlag F (n+1)) (hG : PositiveFlag G (n+1))
    (hFc : ∀ i : Fin (n+1),Continuous (F i)) (hGc : ∀ i : Fin (n+1),Continuous (G i))
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i j : Fin (n+1),IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin (n+1),IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    {A B : ℝ} (hA : 0<A) (hAB : A<B) :
    (A/B)*((flagPencil n F G w (-A)).det/(flagPencil n F G w (-B)).det) ≤
      (flagPencil (n+1) F G w (-A)).det/(flagPencil (n+1) F G w (-B)).det ∧
    (flagPencil (n+1) F G w (-A)).det/(flagPencil (n+1) F G w (-B)).det ≤
      (flagPencil n F G w (-A)).det/(flagPencil n F G w (-B)).det := by
  have hW:=flagGram_det_pos F G w hF hG hw hi
  have hWn:=flagGram_det_pos F G w (fun k hk=>hF k (by omega))
    (fun k hk=>hG k (by omega)) hw (fun i j : Fin n=>hi i.castSucc j.castSucc)
  rw [flagPencil_ratio F G w _ _ hW.ne' hi h2,
    flagPencil_ratio F G w _ _ hWn.ne' (fun i j=>hi i.castSucc j.castSucc) (fun i j=>h2 i.castSucc j.castSucc)]
  exact positive_interlacing_ratio _ _ (flagCharacteristic_interlaces F G w hF hG hFc hGc hw hi h2 n le_rfl) hA hAB
theorem flagPencil_two_steps {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (hF : PositiveFlag F (n+2)) (hG : PositiveFlag G (n+2))
    (hFc : ∀ i : Fin (n+2),Continuous (F i)) (hGc : ∀ i : Fin (n+2),Continuous (G i))
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i j : Fin (n+2),IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin (n+2),IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    {A B : ℝ} (hA : 0<A) (hAB : A<B) :
    (A/B)^2*((flagPencil n F G w (-A)).det/(flagPencil n F G w (-B)).det) ≤
      (flagPencil (n+2) F G w (-A)).det/(flagPencil (n+2) F G w (-B)).det ∧
    (flagPencil (n+2) F G w (-A)).det/(flagPencil (n+2) F G w (-B)).det ≤
      (flagPencil n F G w (-A)).det/(flagPencil n F G w (-B)).det := by
  have h1:=flagPencil_one_step (n:=n) F G w (fun k hk=>hF k (by omega)) (fun k hk=>hG k (by omega))
    (fun i=>hFc i.castSucc) (fun i=>hGc i.castSucc) hw (fun i j=>hi i.castSucc j.castSucc)
    (fun i j=>h2 i.castSucc j.castSucc) hA hAB
  have h2':=flagPencil_one_step (n:=n+1) F G w hF hG hFc hGc hw hi h2 hA hAB
  refine ⟨?_,h2'.2.trans h1.2⟩
  calc
    _ = (A/B)*((A/B)*((flagPencil n F G w (-A)).det/(flagPencil n F G w (-B)).det)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left h1.1 (div_nonneg hA.le (hA.trans hAB).le)).trans h2'.1
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
/-- For the actual second oblique chain, the bases are reordered relative to
the sorted complete jets. The orientation is immaterial for a pencil ratio. -/
def NonvanishingFlag (F : ℕ → ℝ → ℝ) (N : ℕ) : Prop :=
  ∀ k,k ≤ N → ∀ x : Fin k → ℝ,StrictMono x → (∀ i,0<x i) →
    (evaluationMatrix (fun i : Fin k=>F i) x).det ≠ 0
noncomputable def flagAnchor (F : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  (evaluationMatrix (fun i : Fin n=>F i) (fun i : Fin n=>(i.val:ℝ)+1)).det
noncomputable def flagOrientation (F : ℕ → ℝ → ℝ) (i : ℕ) : ℝ := flagAnchor F i/flagAnchor F (i+1)
noncomputable def orientedFlag (F : ℕ → ℝ → ℝ) (i : ℕ) (x : ℝ) : ℝ := flagOrientation F i*F i x
lemma flagAnchor_ne_zero {N : ℕ} (F : ℕ → ℝ → ℝ) (hF : NonvanishingFlag F N) (k : ℕ) (hk : k ≤ N) :
    flagAnchor F k ≠ 0 := by
  apply hF k hk
  · intro i j hij
    have h : (i.val:ℝ)<j.val := by exact_mod_cast hij
    dsimp
    linarith
  · intro i;positivity
lemma evaluation_det_same_sign {n : ℕ} (F : Fin n → ℝ → ℝ)
    (hF : ∀ x : Fin n → ℝ,StrictMono x → (∀ i,0<x i) → (evaluationMatrix F x).det ≠ 0)
    (hc : ∀ i,Continuous (F i)) (x y : Fin n → ℝ)
    (hx : StrictMono x) (hy : StrictMono y) (hx0 : ∀ i,0<x i) (hy0 : ∀ i,0<y i) :
    0<(evaluationMatrix F x).det*(evaluationMatrix F y).det := by
  let v : ℝ → Fin n → ℝ := fun t i=>(1-t)*x i+t*y i
  let f : ℝ → ℝ := fun t=>(evaluationMatrix F (v t)).det
  have hc' : Continuous f := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (hc i).comp ((continuous_const.sub continuous_id).mul continuous_const |>.add (continuous_id.mul continuous_const))
  have hv t (ht : t∈Set.Icc (0:ℝ) 1) : StrictMono (v t) ∧ ∀ i,0<v t i := by
    constructor
    · intro i j hij
      dsimp [v]
      by_cases ht0 : t=0
      · simp [ht0,hx hij]
      · have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
        exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (hx hij).le (by linarith [ht.2]))
          (mul_lt_mul_of_pos_left (hy hij) htp)
    · intro i
      dsimp [v]
      by_cases ht0 : t=0
      · simpa [ht0] using hx0 i
      · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.2]) (hx0 i).le)
          (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (hy0 i))
  have hn t (ht : t∈Set.Icc (0:ℝ) 1) : f t≠0 := hF (v t) (hv t ht).1 (hv t ht).2
  have hs : f 0<0 ↔ f 1<0 := by
    constructor <;> intro hneg <;> by_contra hh
    · obtain ⟨t,ht,he⟩ := isPreconnected_Icc.intermediate_value (by simp : (0:ℝ)∈Set.Icc 0 1)
        (by simp : (1:ℝ)∈Set.Icc 0 1) hc'.continuousOn ⟨hneg.le,le_of_not_gt hh⟩
      exact hn t ht he
    · obtain ⟨t,ht,he⟩ := isPreconnected_Icc.intermediate_value (by simp : (1:ℝ)∈Set.Icc 0 1)
        (by simp : (0:ℝ)∈Set.Icc 0 1) hc'.continuousOn ⟨hneg.le,le_of_not_gt hh⟩
      exact hn t ht he
  have hp : 0<f 0*f 1 := by
    rcases lt_or_gt_of_ne (hn 0 (by simp)) with h|h
    · exact mul_pos_of_neg_of_neg h (hs.mp h)
    · have h1 : 0<f 1 := lt_of_le_of_ne (le_of_not_gt (fun hn=>not_lt_of_gt h (hs.mpr hn))) (Ne.symm (hn 1 (by simp)))
      exact mul_pos h h1
  simpa [f,v] using hp
lemma flagOrientation_product {N : ℕ} (F : ℕ → ℝ → ℝ) (hF : NonvanishingFlag F N) :
    ∀ n,n ≤ N → (∏ i : Fin n,flagOrientation F i)=1/flagAnchor F n := by
  intro n
  induction n with
  | zero => intro _;simp [flagAnchor]
  | succ n ih =>
    intro hn
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih (by omega)]
    dsimp [flagOrientation]
    field_simp [flagAnchor_ne_zero F hF n (by omega),flagAnchor_ne_zero F hF (n+1) hn]
lemma orientedFlag_positive {N : ℕ} (F : ℕ → ℝ → ℝ) (hF : NonvanishingFlag F N)
    (hc : ∀ i : Fin N,Continuous (F i)) : PositiveFlag (orientedFlag F) N := by
  intro n hn x hx hx0
  have hy : StrictMono (fun i : Fin n=>(i.val:ℝ)+1) := by
    intro i j hij
    have h : (i.val:ℝ)<j.val := by exact_mod_cast hij
    dsimp
    linarith
  have hp:=evaluation_det_same_sign (fun i : Fin n=>F i) (hF n hn) (fun i=>hc (i.castLE hn)) x
    (fun i : Fin n=>(i.val:ℝ)+1) hx hy hx0 (fun i=>by positivity)
  change 0 < (Matrix.of (fun i j : Fin n=>flagOrientation F i*F i (x j))).det
  have hd := Matrix.det_mul_column (fun i : Fin n=>flagOrientation F i) (evaluationMatrix (fun i : Fin n=>F i) x)
  simp only [evaluationMatrix] at hd
  rw [hd,flagOrientation_product F hF n hn]
  change 0<(1/flagAnchor F n)*(evaluationMatrix (fun i : Fin n=>F i) x).det
  rw [one_div,mul_comm,←div_eq_mul_inv]
  exact (div_pos_iff).mpr (by
    rcases mul_pos_iff.mp hp with h|h
    · exact Or.inl h
    · exact Or.inr h)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Equiv Finset
/-- Move one selected row to the end, preserving the order of the rest. -/
def moveLast (n : ℕ) (p : Fin (n+1)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' (Fin.last n)).trans (finSuccEquiv' p).symm
lemma moveLast_castSucc (n : ℕ) (p : Fin (n+1)) (i : Fin n) :
    moveLast n p i.castSucc=p.succAbove i := by
  simp [moveLast,finSuccEquiv'_last_apply_castSucc]
lemma moveLast_last (n : ℕ) (p : Fin (n+1)) : moveLast n p (Fin.last n)=p := by simp [moveLast]
def liftLastPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' (Fin.last n)).trans ((Equiv.optionCongr σ).trans (finSuccEquiv' (Fin.last n)).symm)
lemma liftLastPerm_castSucc {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    liftLastPerm σ i.castSucc=(σ i).castSucc := by
  simp [liftLastPerm,finSuccEquiv'_last_apply_castSucc]
lemma liftLastPerm_last {n : ℕ} (σ : Equiv.Perm (Fin n)) : liftLastPerm σ (Fin.last n)=Fin.last n := by
  simp [liftLastPerm]
def liftFirstPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' 0).trans ((Equiv.optionCongr σ).trans (finSuccEquiv' 0).symm)
lemma liftFirstPerm_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) : liftFirstPerm σ 0=0 := by simp [liftFirstPerm]
lemma liftFirstPerm_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    liftFirstPerm σ i.succ=(σ i).succ := by
  simp [liftFirstPerm,finSuccEquiv'_above (Fin.zero_le i.castSucc)]
lemma evaluation_perm_det_ne_zero {n : ℕ} (F : Fin n → ℝ → ℝ) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (h : (evaluationMatrix F x).det ≠ 0) : (evaluationMatrix (fun i=>F (σ i)) x).det ≠ 0 := by
  have he : evaluationMatrix (fun i=>F (σ i)) x=(evaluationMatrix F x).submatrix σ id := by ext;rfl
  rw [he,Matrix.det_permute]
  exact mul_ne_zero (by exact_mod_cast (Perm.sign σ).ne_zero) h
lemma constant_row_subtraction_det {n : ℕ} (H : Fin (n+1) → ℝ → ℝ) (hH : ∀ x,H 0 x=1) (x : Fin (n+1) → ℝ) :
    (evaluationMatrix (Fin.cons (fun _=>1) (fun i y=>H i.succ y-H i.succ 0)) x).det=(evaluationMatrix H x).det := by
  let c : Fin (n+1) → ℝ := Fin.cons 0 (fun i=> -H i.succ 0)
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c])
  intro i j
  refine Fin.cases ?_ (fun i=>?_) i
  · simp [evaluationMatrix,c,hH]
  · simp [evaluationMatrix,c,hH,sub_eq_add_neg]
lemma cons_zeroJet_det {n : ℕ} (b : ℕ → ℝ) (hb : b 0=0) (x : Fin (n+1) → ℝ) :
    (evaluationMatrix (Fin.cons (fun _=>1) (fun i : Fin n=>zeroJet b i)) x).det=(jetEvaluation b x).det := by
  exact constant_row_subtraction_det (fun i : Fin (n+1)=>cosineKernelJet (nodalOrder b i) 0 (b i))
    (jet_first_constant b hb) x
lemma prepend_permuted_det_ne_zero {n : ℕ} (u : Fin n → ℝ → ℝ) (a : ℝ → ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin (n+1) → ℝ) (h : (evaluationMatrix (Fin.cons a u) x).det ≠ 0) :
    (evaluationMatrix (Fin.cons a (fun i=>u (σ i))) x).det ≠ 0 := by
  have he : Fin.cons a (fun i=>u (σ i))=(fun i=>(Fin.cons a u : Fin (n+1) → ℝ → ℝ) (liftFirstPerm σ i)) := by
    funext i
    refine Fin.cases ?_ (fun i=>?_) i
    · simp [liftFirstPerm_zero]
    · simp [liftFirstPerm_succ]
  rw [he]
  exact evaluation_perm_det_ne_zero _ _ _ h
lemma append_permuted_det_ne_zero {n : ℕ} (u : Fin n → ℝ → ℝ) (a : ℝ → ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin (n+1) → ℝ) (h : (evaluationMatrix (Fin.lastCases a u) x).det ≠ 0) :
    (evaluationMatrix (Fin.lastCases a (fun i=>u (σ i))) x).det ≠ 0 := by
  have he : Fin.lastCases a (fun i=>u (σ i))=(fun i=>(Fin.lastCases a u : Fin (n+1) → ℝ → ℝ) (liftLastPerm σ i)) := by
    funext i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simp [liftLastPerm_last]
    · simp [liftLastPerm_castSucc]
  rw [he]
  exact evaluation_perm_det_ne_zero _ _ _ h
lemma constant_to_last_det_ne_zero {n : ℕ} (u : Fin n → ℝ → ℝ) (a : ℝ → ℝ)
    (x : Fin (n+1) → ℝ) (h : (evaluationMatrix (Fin.cons a u) x).det ≠ 0) :
    (evaluationMatrix (Fin.lastCases a u) x).det ≠ 0 := by
  have he : Fin.lastCases a u=(fun i=>(Fin.cons a u : Fin (n+1) → ℝ → ℝ) (moveLast n 0 i)) := by
    funext i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simp [moveLast_last]
    · simp [moveLast_castSucc]
  rw [he]
  exact evaluation_perm_det_ne_zero _ _ _ h
lemma cons_lastCases_swap {n : ℕ} (u : Fin n → ℝ → ℝ) (a b : ℝ → ℝ) :
    (Fin.cons a (Fin.lastCases b u) : Fin (n+2) → ℝ → ℝ)=Fin.lastCases b (Fin.cons a u) := by
  funext i
  refine Fin.cases ?_ (fun i=>?_) i
  · change a=(Fin.lastCases b (Fin.cons a u) : Fin (n+2) → ℝ → ℝ) (0 : Fin (n+1)).castSucc
    simp only [Fin.lastCases_castSucc,Fin.cons_zero]
  · refine Fin.lastCases ?_ (fun i=>?_) i
    · simp only [Fin.cons_succ,Fin.lastCases_last]
      change b=(Fin.lastCases b (Fin.cons a u) : Fin (n+2) → ℝ → ℝ) (Fin.last (n+1))
      simp only [Fin.lastCases_last]
    · simp only [Fin.cons_succ,Fin.lastCases_castSucc]
      rw [←Fin.castSucc_succ]
      simp only [Fin.lastCases_castSucc,Fin.cons_succ]
lemma constant_to_penultimate_det_ne_zero {n : ℕ} (u : Fin n → ℝ → ℝ) (a b : ℝ → ℝ)
    (x : Fin (n+2) → ℝ) (h : (evaluationMatrix (Fin.cons a (Fin.lastCases b u)) x).det ≠ 0) :
    (evaluationMatrix (Fin.lastCases b (Fin.lastCases a u)) x).det ≠ 0 := by
  rw [cons_lastCases_swap] at h
  have he : Fin.lastCases a u=(fun i=>(Fin.cons a u : Fin (n+1) → ℝ → ℝ) (moveLast n 0 i)) := by
    funext i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simp [moveLast_last]
    · simp [moveLast_castSucc]
  rw [he]
  exact append_permuted_det_ne_zero _ _ _ _ h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv
lemma extendedKnot_before (N k : ℕ) (hk : k<2*N+1) :
    extendedKnotLabels N k=interiorKnotLabels N (angle/2) k := by simp [extendedKnotLabels,hk]
lemma extendedKnot_order_before (N k : ℕ) (hk : k<2*N+1) :
    nodalOrder (extendedKnotLabels N) k=nodalOrder (interiorKnotLabels N (angle/2)) k := by
  unfold nodalOrder
  congr 1
  apply filter_congr
  intro j hj
  rw [extendedKnot_before N k hk,extendedKnot_before N j ((mem_range.mp hj).trans hk)]
lemma zero_extended_before (N j : ℕ) (hj : j+1<2*N+1) :
    zeroJet (extendedKnotLabels N) j=zeroJet (interiorKnotLabels N (angle/2)) j := by
  funext x
  simp [zeroJet,extendedKnot_before N (j+1) hj,extendedKnot_order_before N (j+1) hj]
lemma extendedKnot_monotone (N : ℕ) : Monotone (extendedKnotLabels N) := by
  have hhalf : 0<angle/2 := half_pos strip_angle_pos
  have hhalfL : angle/2<angle := by linarith [strip_angle_pos]
  intro i j hij
  unfold extendedKnotLabels
  split_ifs with hi hj
  · exact interiorKnot_monotone N hhalf hhalfL hij
  · have h:=interiorKnot_le N i hhalf hhalfL
    nlinarith [strip_angle_pos]
  · omega
  · rfl
lemma extendedKnot_nonneg (N k : ℕ) : 0 ≤ extendedKnotLabels N k := by
  unfold extendedKnotLabels
  split_ifs
  · exact interiorKnot_nonneg N k _
  · positivity
lemma extendedKnot_bound (N k : ℕ) : extendedKnotLabels N k ≤ (3*angle/2)^2 := by
  unfold extendedKnotLabels
  split_ifs
  · have h:=interiorKnot_le N k (half_pos strip_angle_pos) (by linarith [strip_angle_pos])
    nlinarith [strip_angle_pos]
  · rfl
lemma extendedKnot_first (N : ℕ) (hN : 0<N) : extendedKnotLabels N 0=0 := by simp [extendedKnotLabels,interiorKnot_first N hN]
def zeroInsertion {m N : ℕ} (hm : m+1=2*N) : Fin (m+1) := ⟨N-1,by omega⟩
lemma zero_insertion_reorder {m N : ℕ} (hm : m+1=2*N) (hN : 0<N) {s : ℝ} (hs : 0<s) (hsL : s<angle) :
    (fun i : Fin (m+1)=>zeroJet (interiorKnotLabels N s) (moveLast m (zeroInsertion hm) i))=
    Fin.lastCases (zeroJet (interiorKnotLabels N s) (N-1)) (fun i : Fin m=>zeroJet (twoKnotLabels N) i) := by
  funext i x
  refine Fin.lastCases ?_ (fun i=>?_) i
  · simp [moveLast_last,zeroInsertion]
  · rw [moveLast_castSucc]
    simp only [Fin.lastCases_castSucc]
    by_cases hi : i.val<N-1
    · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc<zeroInsertion hm from hi)]
      exact zero_interior_row_before N i.val hs hsL (by omega) x
    · rw [Fin.succAbove_of_le_castSucc _ _ (show zeroInsertion hm ≤ i.castSucc from le_of_not_gt hi)]
      simpa only [Fin.val_succ,Nat.add_sub_cancel] using zero_interior_row_after N (i.val+1) hN hs hsL (by omega) x
lemma zero_interior_appended_det_ne_zero {m N : ℕ} (hm : m+1=2*N) (hN : 0<N) {s : ℝ} (hs : 0<s) (hsL : s<angle)
    (x : Fin (m+1) → ℝ) (hx : StrictMono x) (hx0 : ∀ i,0<x i) :
    (evaluationMatrix (Fin.lastCases (zeroJet (interiorKnotLabels N s) (N-1))
      (fun i : Fin m=>zeroJet (twoKnotLabels N) i)) x).det ≠ 0 := by
  rw [←zero_insertion_reorder hm hN hs hsL]
  apply evaluation_perm_det_ne_zero (fun i : Fin (m+1)=>zeroJet (interiorKnotLabels N s) i) (moveLast m (zeroInsertion hm)) x
  exact (zeroJet_positiveEvaluation (interiorKnotLabels N s)
    (fun i j hij=>interiorKnot_monotone N hs hsL hij) (fun i=>interiorKnot_nonneg N i s)
    (interiorKnot_first N hN s) x hx hx0).ne'
lemma zero_extended_split {m N : ℕ} (hm : m+1=2*N) :
    (fun i : Fin (m+2)=>zeroJet (extendedKnotLabels N) i)=
    Fin.lastCases (zeroJet (extendedKnotLabels N) (m+1)) (fun i : Fin (m+1)=>zeroJet (interiorKnotLabels N (angle/2)) i) := by
  funext i
  refine Fin.lastCases ?_ (fun i=>?_) i
  · simp
  · simp only [Fin.lastCases_castSucc,Fin.val_castSucc]
    exact zero_extended_before N i (by omega)
lemma secondLeft_top_det_ne_zero {m N : ℕ} (hm : m+1=2*N) (hN : 0<N)
    (x : Fin (m+2) → ℝ) (hx : StrictMono x) (hx0 : ∀ i,0<x i) :
    (evaluationMatrix (Fin.lastCases (zeroJet (extendedKnotLabels N) (m+1))
      (Fin.lastCases (zeroJet (interiorKnotLabels N (angle/2)) (N-1))
      (fun i : Fin m=>zeroJet (twoKnotLabels N) i))) x).det ≠ 0 := by
  have hs : 0<angle/2 := half_pos strip_angle_pos
  have hsL : angle/2<angle := by linarith [strip_angle_pos]
  rw [←zero_insertion_reorder hm hN hs hsL]
  apply append_permuted_det_ne_zero (fun i : Fin (m+1)=>zeroJet (interiorKnotLabels N (angle/2)) i)
    (zeroJet (extendedKnotLabels N) (m+1)) (moveLast m (zeroInsertion hm)) x
  rw [←zero_extended_split hm]
  exact (zeroJet_positiveEvaluation (extendedKnotLabels N)
    (fun i j hij=>extendedKnot_monotone N hij) (fun i=>extendedKnot_nonneg N i)
    (extendedKnot_first N hN) x hx hx0).ne'
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
lemma scalar_familyPencil_det {n : ℕ} (F G : ℕ → ℝ → ℝ) (a b : ℕ → ℝ) (w : ℝ → ℝ) (r : ℝ) :
    (flagPencil n (fun i x=>a i*F i x) (fun i x=>b i*G i x) w r).det=
    (∏ i : Fin n,a i)*(∏ j : Fin n,b j)*(flagPencil n F G w r).det := by
  have he : flagPencil n (fun i x=>a i*F i x) (fun i x=>b i*G i x) w r=
    Matrix.of (fun i j : Fin n=>a i*(b j*flagPencil n F G w r i j)) := by
    ext i j
    dsimp [flagPencil]
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  have hd := Matrix.det_mul_column (fun i : Fin n=>a i) (Matrix.of (fun i j : Fin n=>b j*flagPencil n F G w r i j))
  simp only [Matrix.of_apply] at hd
  rw [he,hd,Matrix.det_mul_row,mul_assoc]
lemma orientedFlagPencil_ratio {N n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (r s : ℝ)
    (hF : NonvanishingFlag F N) (hG : NonvanishingFlag G N) (hn : n ≤ N) :
    (flagPencil n (orientedFlag F) (orientedFlag G) w r).det/
      (flagPencil n (orientedFlag F) (orientedFlag G) w s).det=
    (flagPencil n F G w r).det/(flagPencil n F G w s).det := by
  unfold orientedFlag
  rw [scalar_familyPencil_det,scalar_familyPencil_det]
  apply mul_div_mul_left
  exact mul_ne_zero (by rw [flagOrientation_product F hF n hn];exact one_div_ne_zero (flagAnchor_ne_zero F hF n hn))
    (by rw [flagOrientation_product G hG n hn];exact one_div_ne_zero (flagAnchor_ne_zero G hG n hn))
lemma orientedFlag_integrable {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    ∀ i j : Fin n,IntegrableOn (fun p=>orientedFlag F i (p^2)*orientedFlag G j (p^2)*w p) (Set.Ioi 0) := by
  intro i j
  have he : (fun p=>orientedFlag F i (p^2)*orientedFlag G j (p^2)*w p)=
    fun p=>(flagOrientation F i*flagOrientation G j)*(F i (p^2)*G j (p^2)*w p) := by
    funext p;dsimp [orientedFlag];ring
  rw [he]
  exact (hi i j).const_mul _
/-- A two-step determinant comparison for Chebyshev families. -/
theorem unorientedPencil_two_steps {n : ℕ} (F G : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (hF : NonvanishingFlag F (n+2)) (hG : NonvanishingFlag G (n+2))
    (hFc : ∀ i : Fin (n+2),Continuous (F i)) (hGc : ∀ i : Fin (n+2),Continuous (G i))
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i j : Fin (n+2),IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin (n+2),IntegrableOn (fun p=>p^2*F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    {A B : ℝ} (hA : 0<A) (hAB : A<B) :
    (A/B)^2*((flagPencil n F G w (-A)).det/(flagPencil n F G w (-B)).det) ≤
      (flagPencil (n+2) F G w (-A)).det/(flagPencil (n+2) F G w (-B)).det ∧
    (flagPencil (n+2) F G w (-A)).det/(flagPencil (n+2) F G w (-B)).det ≤
      (flagPencil n F G w (-A)).det/(flagPencil n F G w (-B)).det := by
  have h2' : ∀ i j : Fin (n+2),IntegrableOn (fun p=>p^2*orientedFlag F i (p^2)*orientedFlag G j (p^2)*w p) (Set.Ioi 0) := by
    intro i j
    have he : (fun p=>p^2*orientedFlag F i (p^2)*orientedFlag G j (p^2)*w p)=
      fun p=>(flagOrientation F i*flagOrientation G j)*(p^2*F i (p^2)*G j (p^2)*w p) := by
      funext p;dsimp [orientedFlag];ring
    rw [he]
    exact (h2 i j).const_mul _
  have h:=flagPencil_two_steps (orientedFlag F) (orientedFlag G) w
    (orientedFlag_positive F hF hFc) (orientedFlag_positive G hG hGc)
    (fun i=>(hFc i).const_mul _) (fun i=>(hGc i).const_mul _) hw
    (orientedFlag_integrable F G w hi) h2' hA hAB
  rw [orientedFlagPencil_ratio F G w _ _ hF hG le_rfl,
    orientedFlagPencil_ratio F G w _ _ hF hG (by omega)] at h
  exact h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv
lemma secondRight_middle_det_ne_zero {m N : ℕ} (hN : 0<N)
    (x : Fin (m+1) → ℝ) (hx : StrictMono x) (hx0 : ∀ i,0<x i) :
    (evaluationMatrix (Fin.lastCases (fun _=>1) (fun i : Fin m=>zeroJet (twoKnotLabels N) i)) x).det ≠ 0 := by
  apply constant_to_last_det_ne_zero
  rw [cons_zeroJet_det _ (twoKnot_first N hN)]
  exact (jetEvaluation_det_pos (twoKnotLabels N) x (fun i j hij=>twoKnot_monotone N hij) hx
    (fun i=>twoKnot_nonneg N i) (fun i=>(hx0 i).le)).ne'
lemma secondRight_top_det_ne_zero {m N : ℕ} (hm : m+1=2*N) (hN : 0<N) {t : ℝ} (ht : 0<t) (htL : t<angle)
    (x : Fin (m+2) → ℝ) (hx : StrictMono x) (hx0 : ∀ i,0<x i) :
    (evaluationMatrix (Fin.lastCases (zeroJet (interiorKnotLabels N t) (N-1))
      (Fin.lastCases (fun _=>1) (fun i : Fin m=>zeroJet (twoKnotLabels N) i))) x).det ≠ 0 := by
  apply constant_to_penultimate_det_ne_zero
  rw [←zero_insertion_reorder hm hN ht htL]
  apply prepend_permuted_det_ne_zero (fun i : Fin (m+1)=>zeroJet (interiorKnotLabels N t) i)
    (fun _=>1) (moveLast m (zeroInsertion hm)) x
  rw [cons_zeroJet_det _ (interiorKnot_first N hN t)]
  exact (jetEvaluation_det_pos (interiorKnotLabels N t) x (fun i j hij=>interiorKnot_monotone N ht htL hij) hx
    (fun i=>interiorKnot_nonneg N i t) (fun i=>(hx0 i).le)).ne'
noncomputable def appendTwo (F : ℕ → ℝ → ℝ) (m : ℕ) (a b : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  if k < m then F k x else if k=m then a x else b x
lemma appendTwo_prefix {m n : ℕ} (F : ℕ → ℝ → ℝ) (a b : ℝ → ℝ) (hn : n ≤ m) :
    (fun i : Fin n=>appendTwo F m a b i)=(fun i : Fin n=>F i) := by
  funext i x
  simp [appendTwo,show i.val < m from i.isLt.trans_le hn]
lemma appendTwo_middle (m : ℕ) (F : ℕ → ℝ → ℝ) (a b : ℝ → ℝ) :
    (fun i : Fin (m+1)=>appendTwo F m a b i)=Fin.lastCases a (fun i : Fin m=>F i) := by
  funext i x
  refine Fin.lastCases ?_ (fun i=>?_) i
  · simp [appendTwo]
  · simp [appendTwo,i.isLt]
lemma appendTwo_top (m : ℕ) (F : ℕ → ℝ → ℝ) (a b : ℝ → ℝ) :
    (fun i : Fin (m+2)=>appendTwo F m a b i)=Fin.lastCases b (Fin.lastCases a (fun i : Fin m=>F i)) := by
  funext i x
  refine Fin.lastCases ?_ (fun i=>?_) i
  · simp [appendTwo]
  · simpa only [Fin.val_castSucc,Fin.lastCases_castSucc] using congrFun (congrFun (appendTwo_middle m F a b) i) x
noncomputable def secondLeftFlag (m N : ℕ) : ℕ → ℝ → ℝ :=
  appendTwo (zeroJet (twoKnotLabels N)) m (zeroJet (interiorKnotLabels N (angle/2)) (N-1))
    (zeroJet (extendedKnotLabels N) (m+1))
noncomputable def secondRightFlag (m N : ℕ) (t : ℝ) : ℕ → ℝ → ℝ :=
  appendTwo (zeroJet (twoKnotLabels N)) m (fun _=>1) (zeroJet (interiorKnotLabels N t) (N-1))
lemma zero_twoKnot_nonvanishing (N : ℕ) (hN : 0<N) (m : ℕ) : NonvanishingFlag (zeroJet (twoKnotLabels N)) m := by
  intro n _ x hx hx0
  exact (zeroJet_positiveEvaluation (twoKnotLabels N) (fun i j hij=>twoKnot_monotone N hij)
    (fun i=>twoKnot_nonneg N i) (twoKnot_first N hN) x hx hx0).ne'
lemma secondLeft_nonvanishing {m N : ℕ} (hm : m+1=2*N) (hN : 0<N) :
    NonvanishingFlag (secondLeftFlag m N) (m+2) := by
  intro n hn x hx hx0
  by_cases hnm : n ≤ m
  · change (evaluationMatrix (fun i : Fin n=>appendTwo _ m _ _ i) x).det ≠ 0
    rw [appendTwo_prefix _ _ _ hnm]
    exact zero_twoKnot_nonvanishing N hN m n hnm x hx hx0
  · have hc : n=m+1 ∨ n=m+2 := by omega
    rcases hc with rfl|rfl
    · change (evaluationMatrix (fun i : Fin (m+1)=>appendTwo _ m _ _ i) x).det ≠ 0
      rw [appendTwo_middle]
      exact zero_interior_appended_det_ne_zero hm hN (half_pos strip_angle_pos) (by linarith [strip_angle_pos]) x hx hx0
    · change (evaluationMatrix (fun i : Fin (m+2)=>appendTwo _ m _ _ i) x).det ≠ 0
      rw [appendTwo_top]
      exact secondLeft_top_det_ne_zero hm hN x hx hx0
lemma secondRight_nonvanishing {m N : ℕ} (hm : m+1=2*N) (hN : 0<N) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    NonvanishingFlag (secondRightFlag m N t) (m+2) := by
  intro n hn x hx hx0
  by_cases hnm : n ≤ m
  · change (evaluationMatrix (fun i : Fin n=>appendTwo _ m _ _ i) x).det ≠ 0
    rw [appendTwo_prefix _ _ _ hnm]
    exact zero_twoKnot_nonvanishing N hN m n hnm x hx hx0
  · have hc : n=m+1 ∨ n=m+2 := by omega
    rcases hc with rfl|rfl
    · change (evaluationMatrix (fun i : Fin (m+1)=>appendTwo _ m _ _ i) x).det ≠ 0
      rw [appendTwo_middle]
      exact secondRight_middle_det_ne_zero hN x hx hx0
    · change (evaluationMatrix (fun i : Fin (m+2)=>appendTwo _ m _ _ i) x).det ≠ 0
      rw [appendTwo_top]
      exact secondRight_top_det_ne_zero hm hN ht htL x hx hx0
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
noncomputable def stripKernelSpan (B : ℝ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ {f | ∃ b : ℝ,∃ r : ℕ,0 ≤ b ∧ b ≤ B ∧ f=cosineKernelJet r 0 b}
lemma kernel_mem_stripSpan {B b : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) (r : ℕ) :
    cosineKernelJet r 0 b ∈ stripKernelSpan B := Submodule.subset_span ⟨b,r,hb,hbB,rfl⟩
lemma one_mem_stripSpan {B : ℝ} (hB : 0 ≤ B) : (fun _ : ℝ=>1) ∈ stripKernelSpan B := by
  have he : cosineKernelJet 0 0 0=(fun _ : ℝ=>1) := by
    funext x
    simpa [nodalOrder] using jet_first_constant (fun _ : ℕ=>0) rfl x
  rw [←he]
  exact kernel_mem_stripSpan le_rfl hB 0
lemma zeroJet_mem_stripSpan {B : ℝ} (b : ℕ → ℝ) (j : ℕ) (hB : 0 ≤ B)
    (hb : 0 ≤ b (j+1)) (hbB : b (j+1) ≤ B) : zeroJet b j ∈ stripKernelSpan B := by
  have h0 := (stripKernelSpan B).smul_mem (cosineKernelJet (nodalOrder b (j+1)) 0 (b (j+1)) 0) (one_mem_stripSpan hB)
  have h:= (stripKernelSpan B).sub_mem (kernel_mem_stripSpan hb hbB (nodalOrder b (j+1))) h0
  have he : zeroJet b j = cosineKernelJet (nodalOrder b (j+1)) 0 (b (j+1)) -
      cosineKernelJet (nodalOrder b (j+1)) 0 (b (j+1)) 0 • (fun _ : ℝ=>1) := by
    funext x
    simp [zeroJet]
  rw [he]
  exact h
lemma stripSpan_continuous {B : ℝ} {f : ℝ → ℝ} (hf : f ∈ stripKernelSpan B) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨b,r,_,_,rfl⟩ := hf;exact (cosineKernelJet_contDiff_right r 0 b 0).continuous
  | zero => exact continuous_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c
lemma stripSpan_pair_integrable {z : ℝ} (hz : 0<z) (k : ℕ) {f g : ℝ → ℝ}
    (hf : f ∈ stripKernelSpan ((3*angle/2)^2)) (hg : g ∈ stripKernelSpan (angle^2)) :
    IntegrableOn (fun p=>p^k*f (p^2)*g (p^2)*poleAdjustedDensity z p) (Set.Ioi 0) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b,r,hb,hbB,rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨c,s,hc,hcB,rfl⟩ := hg
      exact pole_adjusted_pair_moment_integrable hb hc hbB hcB hz r s k
    | zero => simp
    | add g h _ _ hg hh =>
      apply (hg.add hh).congr
      filter_upwards with p
      simp only [Pi.add_apply]
      ring
    | smul a g _ hg =>
      have he : (fun p=>p^k*cosineKernelJet r 0 b (p^2)*(a • g) (p^2)*poleAdjustedDensity z p)=
        fun p=>a*(p^k*cosineKernelJet r 0 b (p^2)*g (p^2)*poleAdjustedDensity z p) := by
        funext p;simp only [Pi.smul_apply,smul_eq_mul];ring
      rw [he]
      exact hg.const_mul a
  | zero => simp
  | add f h _ _ hf hh =>
    apply (hf.add hh).congr
    filter_upwards with p
    simp only [Pi.add_apply]
    ring
  | smul a f _ hf =>
    have he : (fun p=>p^k*(a • f) (p^2)*g (p^2)*poleAdjustedDensity z p)=
      fun p=>a*(p^k*f (p^2)*g (p^2)*poleAdjustedDensity z p) := by
      funext p;simp only [Pi.smul_apply,smul_eq_mul];ring
    rw [he]
    exact hf.const_mul a
lemma secondLeft_mem (m N j : ℕ) : secondLeftFlag m N j ∈ stripKernelSpan ((3*angle/2)^2) := by
  unfold secondLeftFlag appendTwo
  split_ifs
  · apply zeroJet_mem_stripSpan _ _ (sq_nonneg _) (twoKnot_nonneg N _)
    have h:=twoKnot_le N (j+1)
    nlinarith [strip_angle_pos]
  · apply zeroJet_mem_stripSpan _ _ (sq_nonneg _) (interiorKnot_nonneg N _ _)
    have h:=interiorKnot_le N (N-1+1) (half_pos strip_angle_pos) (by linarith [strip_angle_pos])
    nlinarith [strip_angle_pos]
  · exact zeroJet_mem_stripSpan _ _ (sq_nonneg _) (extendedKnot_nonneg N _) (extendedKnot_bound N _)
lemma secondRight_mem (m N j : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    secondRightFlag m N t j ∈ stripKernelSpan (angle^2) := by
  unfold secondRightFlag appendTwo
  split_ifs
  · exact zeroJet_mem_stripSpan _ _ (sq_nonneg _) (twoKnot_nonneg N _) (twoKnot_le N _)
  · exact one_mem_stripSpan (sq_nonneg _)
  · exact zeroJet_mem_stripSpan _ _ (sq_nonneg _) (interiorKnot_nonneg N _ _) (interiorKnot_le N _ ht htL)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv MeasureTheory
noncomputable def permutationFactor {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℝ := ((Perm.sign σ:ℤ):ℝ)
lemma permutationFactor_ne_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) : permutationFactor σ ≠ 0 := by
  unfold permutationFactor
  exact_mod_cast (Perm.sign σ).ne_zero
lemma evaluation_perm_factor {n : ℕ} (F : Fin n → ℝ → ℝ) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    (evaluationMatrix (fun i=>F (σ i)) x).det=permutationFactor σ*(evaluationMatrix F x).det := by
  have he : evaluationMatrix (fun i=>F (σ i)) x=(evaluationMatrix F x).submatrix σ id := by ext;rfl
  rw [he,Matrix.det_permute]
  rfl
lemma evaluation_append_perm_factor {n : ℕ} (u : Fin n → ℝ → ℝ) (a : ℝ → ℝ) (σ : Equiv.Perm (Fin n)) (x : Fin (n+1) → ℝ) :
    (evaluationMatrix (Fin.lastCases a (fun i=>u (σ i))) x).det=
      permutationFactor (liftLastPerm σ)*(evaluationMatrix (Fin.lastCases a u) x).det := by
  have he : Fin.lastCases a (fun i=>u (σ i))=(fun i=>(Fin.lastCases a u : Fin (n+1) → ℝ → ℝ) (liftLastPerm σ i)) := by
    funext i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simp [liftLastPerm_last]
    · simp [liftLastPerm_castSucc]
  rw [he,evaluation_perm_factor]
lemma evaluation_prepend_perm_factor {n : ℕ} (u : Fin n → ℝ → ℝ) (a : ℝ → ℝ) (σ : Equiv.Perm (Fin n)) (x : Fin (n+1) → ℝ) :
    (evaluationMatrix (Fin.cons a (fun i=>u (σ i))) x).det=
      permutationFactor (liftFirstPerm σ)*(evaluationMatrix (Fin.cons a u) x).det := by
  have he : Fin.cons a (fun i=>u (σ i))=(fun i=>(Fin.cons a u : Fin (n+1) → ℝ → ℝ) (liftFirstPerm σ i)) := by
    funext i
    refine Fin.cases ?_ (fun i=>?_) i
    · simp [liftFirstPerm_zero]
    · simp [liftFirstPerm_succ]
  rw [he,evaluation_perm_factor]
lemma constant_to_penultimate_factor {n : ℕ} (u : Fin n → ℝ → ℝ) (a b : ℝ → ℝ) (x : Fin (n+2) → ℝ) :
    (evaluationMatrix (Fin.lastCases b (Fin.lastCases a u)) x).det=
      permutationFactor (liftLastPerm (moveLast n 0))*(evaluationMatrix (Fin.cons a (Fin.lastCases b u)) x).det := by
  rw [cons_lastCases_swap]
  have he : Fin.lastCases a u=(fun i=>(Fin.cons a u : Fin (n+1) → ℝ → ℝ) (moveLast n 0 i)) := by
    funext i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simp [moveLast_last]
    · simp [moveLast_castSucc]
  rw [he,evaluation_append_perm_factor]
lemma familyGram_evaluation_factors {n : ℕ} (F G F' G' : Fin n → ℝ → ℝ) (w : ℝ → ℝ) (a b : ℝ)
    (hF : ∀ x,(evaluationMatrix F' x).det=a*(evaluationMatrix F x).det)
    (hG : ∀ x,(evaluationMatrix G' x).det=b*(evaluationMatrix G x).det)
    (hi : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hi' : ∀ i j,IntegrableOn (fun p=>F' i (p^2)*G' j (p^2)*w p) (Set.Ioi 0)) :
    (familyGram w F' G').det=(a*b)*(familyGram w F G).det := by
  have h:= (family_gram_andreief w F G hi).2
  have h':= (family_gram_andreief w F' G' hi').2
  have he : familyPointDensity w F' G'=(fun p=>(a*b)*familyPointDensity w F G p) := by
    funext p
    dsimp [familyPointDensity]
    rw [hF,hG]
    ring
  rw [he,integral_const_mul,h] at h'
  have hc : (Fintype.card (Perm (Fin n)):ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hc
  rw [←h']
  ring
lemma stripSpan_pair_pencil_integrable {z : ℝ} (hz : 0<z) (r : ℝ) {f g : ℝ → ℝ}
    (hf : f ∈ stripKernelSpan ((3*angle/2)^2)) (hg : g ∈ stripKernelSpan (angle^2)) :
    IntegrableOn (fun p=>f (p^2)*g (p^2)*((p^2-r)*poleAdjustedDensity z p)) (Set.Ioi 0) := by
  have h0 := stripSpan_pair_integrable hz 0 hf hg
  have h2 := stripSpan_pair_integrable hz 2 hf hg
  apply (h2.sub (h0.const_mul r)).congr
  filter_upwards with p
  simp only [Pi.sub_apply,pow_zero,one_mul]
  ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv MeasureTheory
noncomputable def secondLeftFactor {m N : ℕ} (hm : m+1=2*N) : ℝ :=
  permutationFactor (liftLastPerm (moveLast m (zeroInsertion hm)))
noncomputable def secondRightFactor {m N : ℕ} (hm : m+1=2*N) : ℝ :=
  permutationFactor (liftLastPerm (moveLast m 0))*permutationFactor (liftFirstPerm (moveLast m (zeroInsertion hm)))
lemma secondLeftFactor_ne_zero {m N : ℕ} (hm : m+1=2*N) : secondLeftFactor hm ≠ 0 :=
  permutationFactor_ne_zero _
lemma secondRightFactor_ne_zero {m N : ℕ} (hm : m+1=2*N) : secondRightFactor hm ≠ 0 :=
  mul_ne_zero (permutationFactor_ne_zero _) (permutationFactor_ne_zero _)
lemma secondLeft_evaluation_factor {m N : ℕ} (hm : m+1=2*N) (hN : 0<N) (x : Fin (m+2) → ℝ) :
    (evaluationMatrix (fun i : Fin (m+2)=>secondLeftFlag m N i) x).det=
    secondLeftFactor hm*(evaluationMatrix (fun i : Fin (m+2)=>zeroJet (extendedKnotLabels N) i) x).det := by
  unfold secondLeftFlag
  rw [appendTwo_top,←zero_insertion_reorder hm hN (half_pos strip_angle_pos) (by linarith [strip_angle_pos]),
    evaluation_append_perm_factor (fun i : Fin (m+1)=>zeroJet (interiorKnotLabels N (angle/2)) i)
      (zeroJet (extendedKnotLabels N) (m+1)) (moveLast m (zeroInsertion hm)),←zero_extended_split hm]
  rfl
lemma secondRight_evaluation_factor {m N : ℕ} (hm : m+1=2*N) (hN : 0<N) {t : ℝ} (ht : 0<t) (htL : t<angle)
    (x : Fin (m+2) → ℝ) :
    (evaluationMatrix (fun i : Fin (m+2)=>secondRightFlag m N t i) x).det=
    secondRightFactor hm*(evaluationMatrix (fun i : Fin (m+2)=>cosineKernelJet
      (nodalOrder (interiorKnotLabels N t) i) 0 (interiorKnotLabels N t i)) x).det := by
  unfold secondRightFlag
  rw [appendTwo_top,constant_to_penultimate_factor,
    ←zero_insertion_reorder hm hN ht htL,
    evaluation_prepend_perm_factor (fun i : Fin (m+1)=>zeroJet (interiorKnotLabels N t) i)
      (fun _=>1) (moveLast m (zeroInsertion hm)),
    cons_zeroJet_det _ (interiorKnot_first N hN t)]
  simp only [secondRightFactor,mul_assoc]
  rfl
lemma extendedZero_mem (N j : ℕ) : zeroJet (extendedKnotLabels N) j ∈ stripKernelSpan ((3*angle/2)^2) :=
  zeroJet_mem_stripSpan _ _ (sq_nonneg _) (extendedKnot_nonneg N _) (extendedKnot_bound N _)
lemma interiorRaw_mem (N j : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    cosineKernelJet (nodalOrder (interiorKnotLabels N t) j) 0 (interiorKnotLabels N t j) ∈ stripKernelSpan (angle^2) :=
  kernel_mem_stripSpan (interiorKnot_nonneg N j t) (interiorKnot_le N j ht htL) _
lemma secondChain_pencil_factor {m N : ℕ} (hm : m+1=2*N) (hN : 0<N) {t z : ℝ} (ht : 0<t) (htL : t<angle)
    (hz : 0<z) (r : ℝ) :
    (flagPencil (m+2) (secondLeftFlag m N) (secondRightFlag m N t) (poleAdjustedDensity z) r).det=
    (secondLeftFactor hm*secondRightFactor hm)*
    (mixedZeroJetPencil (n:=m+2) (poleAdjustedDensity z) (extendedKnotLabels N) (interiorKnotLabels N t) r).det := by
  have h := familyGram_evaluation_factors
    (fun i : Fin (m+2)=>zeroJet (extendedKnotLabels N) i)
    (fun i : Fin (m+2)=>cosineKernelJet (nodalOrder (interiorKnotLabels N t) i) 0 (interiorKnotLabels N t i))
    (fun i : Fin (m+2)=>secondLeftFlag m N i) (fun i : Fin (m+2)=>secondRightFlag m N t i)
    (fun p=>(p^2-r)*poleAdjustedDensity z p) (secondLeftFactor hm) (secondRightFactor hm)
    (secondLeft_evaluation_factor hm hN) (secondRight_evaluation_factor hm hN ht htL)
    (fun i j=>stripSpan_pair_pencil_integrable hz r (extendedZero_mem N i) (interiorRaw_mem N j ht htL))
    (fun i j=>stripSpan_pair_pencil_integrable hz r (secondLeft_mem m N i) (secondRight_mem m N j ht htL))
  have h1 : familyGram (fun p=>(p^2-r)*poleAdjustedDensity z p)
      (fun i : Fin (m+2)=>secondLeftFlag m N i) (fun i : Fin (m+2)=>secondRightFlag m N t i)=
      flagPencil (m+2) (secondLeftFlag m N) (secondRightFlag m N t) (poleAdjustedDensity z) r := by
    ext i j
    apply integral_congr_ae
    filter_upwards with p
    ring
  have h2 : familyGram (fun p=>(p^2-r)*poleAdjustedDensity z p)
      (fun i : Fin (m+2)=>zeroJet (extendedKnotLabels N) i)
      (fun i : Fin (m+2)=>cosineKernelJet (nodalOrder (interiorKnotLabels N t) i) 0 (interiorKnotLabels N t i))=
      mixedZeroJetPencil (n:=m+2) (poleAdjustedDensity z) (extendedKnotLabels N) (interiorKnotLabels N t) r := by
    ext i j
    apply integral_congr_ae
    filter_upwards with p
    ring
  rwa [h1,h2] at h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory
lemma secondChain_bottom_pencil (m N : ℕ) (t r : ℝ) (w : ℝ → ℝ) :
    flagPencil m (secondLeftFlag m N) (secondRightFlag m N t) w r=
    zeroJetPencil (n:=m) w (twoKnotLabels N) (twoKnotLabels N) r := by
  ext i j
  dsimp [flagPencil,zeroJetPencil,secondLeftFlag,secondRightFlag]
  simp only [appendTwo,i.isLt,j.isLt,ite_true]
lemma secondChain_pencil_ratio {m N : ℕ} (hm : m+1=2*N) (hN : 0<N) {t z : ℝ} (ht : 0<t) (htL : t<angle)
    (hz : 0<z) (r s : ℝ) :
    (flagPencil (m+2) (secondLeftFlag m N) (secondRightFlag m N t) (poleAdjustedDensity z) r).det/
    (flagPencil (m+2) (secondLeftFlag m N) (secondRightFlag m N t) (poleAdjustedDensity z) s).det=
    (mixedZeroJetPencil (n:=m+2) (poleAdjustedDensity z) (extendedKnotLabels N) (interiorKnotLabels N t) r).det/
    (mixedZeroJetPencil (n:=m+2) (poleAdjustedDensity z) (extendedKnotLabels N) (interiorKnotLabels N t) s).det := by
  rw [secondChain_pencil_factor hm hN ht htL hz,secondChain_pencil_factor hm hN ht htL hz]
  exact mul_div_mul_left _ _ (mul_ne_zero (secondLeftFactor_ne_zero hm) (secondRightFactor_ne_zero hm))
lemma secondOblique_comparison_aux {m N : ℕ} (hm : m+1=2*N) (hN : 0<N) {t y z : ℝ}
    (ht : 0<t) (htL : t<angle) (hy : 0<y) (hyz : y<z) :
    let S := (zeroJetPencil (n:=m) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) (-(y^2))).det/
      (zeroJetPencil (n:=m) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) (-(z^2))).det
    let Q := (mixedZeroJetPencil (n:=m+2) (poleAdjustedDensity z) (extendedKnotLabels N) (interiorKnotLabels N t) (-(y^2))).det/
      (mixedZeroJetPencil (n:=m+2) (poleAdjustedDensity z) (extendedKnotLabels N) (interiorKnotLabels N t) (-(z^2))).det
    (y^2/z^2)^2*S ≤ Q ∧ Q ≤ S := by
  have hz : 0<z := hy.trans hyz
  have hi (i j : Fin (m+2)) : IntegrableOn
      (fun p=>secondLeftFlag m N i (p^2)*secondRightFlag m N t j (p^2)*poleAdjustedDensity z p) (Set.Ioi 0) := by
    simpa only [pow_zero,one_mul] using stripSpan_pair_integrable hz 0 (secondLeft_mem m N i) (secondRight_mem m N j ht htL)
  have h := unorientedPencil_two_steps (secondLeftFlag m N) (secondRightFlag m N t) (poleAdjustedDensity z)
    (secondLeft_nonvanishing hm hN) (secondRight_nonvanishing hm hN ht htL)
    (fun i=>stripSpan_continuous (secondLeft_mem m N i)) (fun i=>stripSpan_continuous (secondRight_mem m N i ht htL))
    (fun _ hp=>poleAdjustedDensity_pos hz hp) hi
    (fun i j=>stripSpan_pair_integrable hz 2 (secondLeft_mem m N i) (secondRight_mem m N j ht htL))
    (sq_pos_of_pos hy) (by nlinarith : y^2<z^2)
  rw [secondChain_pencil_ratio hm hN ht htL hz,secondChain_bottom_pencil,secondChain_bottom_pencil] at h
  exact h
/-- The second oblique characteristic comparison follows from complete jet positivity and finite moments. -/
theorem secondObliqueCharacteristicComparison : SecondObliqueCharacteristicComparison := by
  intro N hN t ht htL y z hy hyz
  have hm : (2*N-1)+1=2*N := by omega
  have hn : (2*N-1)+2=2*N+1 := by omega
  have h := secondOblique_comparison_aux hm hN ht htL hy hyz
  dsimp only at h ⊢
  rw [hn] at h
  exact h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
