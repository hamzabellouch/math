import OAI.Combinatorics.HoneycombChords.SparseInterpolation

namespace OAI

/-! Physical pole factors and positive mixtures of interpolation kernels.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section

namespace CriticalHoneycomb.FiniteFunctional
open Finset

lemma physicalPole_strictMono : StrictMono physicalPole := by
  intro m n hmn
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (m:ℝ) < n := by exact_mod_cast hmn
  unfold physicalPole
  nlinarith

noncomputable def poleTailRatio (u : ℝ) (n : ℕ) : ℝ :=
  (physicalPole n-u)/(physicalPole n-physicalPole 0)

lemma poleTailRatio_ge_one {u : ℝ} (hu : u ≤ 4) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ poleTailRatio u n := by
  have hd : 0 < physicalPole n-physicalPole 0 := sub_pos.mpr (physicalPole_strictMono (by omega))
  apply (le_div_iff₀ hd).mpr
  have h0 : (4:ℝ) < physicalPole 0 := by norm_num [physicalPole]
  linarith

lemma poleTailRatio_le {u : ℝ} (hu : 0 ≤ u) {n : ℕ} (hn : 1 ≤ n) :
    poleTailRatio u n ≤ ((n:ℝ)+1)^2/((n:ℝ)*((n:ℝ)+2)) := by
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hd : 0 < physicalPole n-physicalPole 0 := sub_pos.mpr (physicalPole_strictMono (by omega))
  calc
    poleTailRatio u n ≤ physicalPole n/(physicalPole n-physicalPole 0) := by
      exact div_le_div_of_nonneg_right (sub_le_self _ hu) hd.le
    _ = 1+1/(4*(n:ℝ)*((n:ℝ)+1)) := by
      apply (div_eq_iff hd.ne').mpr
      unfold physicalPole
      push_cast
      field_simp
      ring
    _ ≤ 1+1/((n:ℝ)*((n:ℝ)+2)) := by
      apply add_le_add (le_refl 1)
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ = ((n:ℝ)+1)^2/((n:ℝ)*((n:ℝ)+2)) := by
      field_simp
      ring

lemma poleTailProduct_le {u : ℝ} (hu : 0 ≤ u) (hu4 : u ≤ 4) (m : ℕ) :
    (∏ j ∈ range m,poleTailRatio u (j+1)) ≤ 2*((m:ℝ)+1)/((m:ℝ)+2) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [prod_range_succ]
    have hpos : 0 ≤ poleTailRatio u (m+1) := le_trans zero_le_one (poleTailRatio_ge_one hu4 (by omega))
    have hh := mul_le_mul ih (poleTailRatio_le hu (by omega : 1 ≤ m+1)) hpos (by positivity)
    apply hh.trans_eq
    push_cast
    field_simp
    ring

lemma poleTailProduct_uniform {u : ℝ} (hu : 0 ≤ u) (hu4 : u ≤ 4) (m : ℕ) :
    (∏ j ∈ range m,poleTailRatio u (j+1)) ≤ 2 := by
  apply (poleTailProduct_le hu hu4 m).trans
  apply (div_le_iff₀ (by positivity)).mpr
  linarith [Nat.cast_nonneg (α:=ℝ) m]

lemma poleTailSubset_uniform {u : ℝ} (hu : 0 ≤ u) (hu4 : u ≤ 4)
    (s : Finset ℕ) (m : ℕ) (hs : ∀ j ∈ s,j < m) :
    (∏ j ∈ s,poleTailRatio u (j+1)) ≤ 2 := by
  have hsub : s ⊆ range m := fun j hj => mem_range.mpr (hs j hj)
  apply (prod_le_prod_of_subset_of_one_le₀ hsub
    (fun j _ => le_trans zero_le_one (poleTailRatio_ge_one hu4 (by omega)))
    (fun j _ _ => poleTailRatio_ge_one hu4 (by omega))).trans
  exact poleTailProduct_uniform hu hu4 m

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset
namespace ReciprocalExpr

noncomputable def rangeProduct (f : ℕ → ReciprocalExpr) : ℕ → ReciprocalExpr
  | 0 => const 1
  | n+1 => mulExpr (rangeProduct f n) (f n)

lemma rangeProduct_eval (f : ℕ → ReciprocalExpr) (n : ℕ) (x : ℝ) :
    (rangeProduct f n).eval x = ∏ i ∈ range n,(f i).eval x := by
  induction n with
  | zero => simp [rangeProduct,eval]
  | succ n ih => simp [rangeProduct,mulExpr_eval,prod_range_succ,ih]
lemma rangeProduct_poles {f : ℕ → ReciprocalExpr} {L : ℝ} (n : ℕ)
    (h : ∀ i < n,(f i).PolesAbove L) : (rangeProduct f n).PolesAbove L := by
  induction n with
  | zero => trivial
  | succ n ih => exact mulExpr_poles (ih (fun i hi => h i (by omega))) (h n (by omega))
lemma rangeProduct_coeff {f : ℕ → ReciprocalExpr} (n : ℕ)
    (h : ∀ i < n,(f i).CoeffNonneg) : (rangeProduct f n).CoeffNonneg := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mulExpr_coeff (ih (fun i hi => h i (by omega))) (h n (by omega))

noncomputable def tripleWeight (a b c : ℝ) : ℝ := c*(b-a)/(b*(c-a))
noncomputable def tripleFactor (a b c : ℝ) : ReciprocalExpr :=
  add (scale (tripleWeight a b c) (normalizedPole a))
    (scale (1-tripleWeight a b c) (normalizedPole c))

lemma tripleWeight_pos {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    0 < tripleWeight a b c := by
  exact div_pos (mul_pos (by linarith) (sub_pos.mpr hab))
    (mul_pos (by linarith) (sub_pos.mpr (hab.trans hbc)))
lemma tripleWeight_lt_one {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    tripleWeight a b c < 1 := by
  unfold tripleWeight
  apply (div_lt_one (mul_pos (by linarith) (by linarith))).mpr
  nlinarith
lemma tripleFactor_coeff {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    (tripleFactor a b c).CoeffNonneg :=
  ⟨⟨(tripleWeight_pos ha hab hbc).le,normalizedPole_coeff ha.le⟩,
   ⟨(sub_pos.mpr (tripleWeight_lt_one ha hab hbc)).le,normalizedPole_coeff (by linarith)⟩⟩
lemma tripleFactor_poles {a b c L : ℝ} (hL : L < a) (hac : a < c) :
    (tripleFactor a b c).PolesAbove L :=
  ⟨normalizedPole_poles hL,normalizedPole_poles (hL.trans hac)⟩
lemma tripleFactor_eval {a b c x : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hax : a+x ≠ 0) (hcx : c+x ≠ 0) :
    (tripleFactor a b c).eval x = (1+x/b)*(a/(a+x))*(c/(c+x)) := by
  simp only [tripleFactor,eval,normalizedPole_eval,tripleWeight]
  have hb : b ≠ 0 := ne_of_gt (ha.trans hab)
  have hca : c-a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hab.trans hbc))
  field_simp
  ring
lemma normalizedPole_zero {a : ℝ} (ha : 0 < a) :
    (normalizedPole a).eval 0=1 := by rw [normalizedPole_eval,add_zero,div_self ha.ne']
lemma tripleFactor_zero {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    (tripleFactor a b c).eval 0=1 := by
  simp only [tripleFactor,eval,normalizedPole_zero ha,normalizedPole_zero (ha.trans (hab.trans hbc))]
  ring

end ReciprocalExpr

noncomputable def shiftedPole (u : ℝ) (n : ℕ) := physicalPole n-u
lemma shiftedPole_pos {u : ℝ} (hu : u ≤ 4) (n : ℕ) : 0 < shiftedPole u n := by
  unfold shiftedPole
  linarith [physicalPole_ge n]
lemma shiftedPole_strictMono (u : ℝ) : StrictMono (shiftedPole u) :=
  fun _ _ h => sub_lt_sub_right (physicalPole_strictMono h) u

noncomputable def physicalPairExpr (u : ℝ) (n : ℕ) : ReciprocalExpr :=
  ReciprocalExpr.mulExpr (ReciprocalExpr.normalizedPole (shiftedPole u (3*n)))
    (ReciprocalExpr.normalizedPole (shiftedPole u (3*n+2)))
noncomputable def physicalTripleExpr (u : ℝ) (n : ℕ) : ReciprocalExpr :=
  ReciprocalExpr.tripleFactor (shiftedPole u (3*n)) (shiftedPole u (3*n+1)) (shiftedPole u (3*n+2))

lemma physicalTripleExpr_poles {u : ℝ} (n : ℕ) :
    (physicalTripleExpr u (n+1)).PolesAbove (shiftedPole u 0) := by
  apply ReciprocalExpr.tripleFactor_poles
  · exact shiftedPole_strictMono u (by omega)
  · exact shiftedPole_strictMono u (by omega)
lemma physicalTripleExpr_coeff {u : ℝ} (hu : u ≤ 4) (n : ℕ) :
    (physicalTripleExpr u n).CoeffNonneg :=
  ReciprocalExpr.tripleFactor_coeff (shiftedPole_pos hu _)
    (shiftedPole_strictMono u (by omega)) (shiftedPole_strictMono u (by omega))
lemma physicalTripleExpr_zero {u : ℝ} (hu : u ≤ 4) (n : ℕ) :
    (physicalTripleExpr u n).eval 0=1 :=
  ReciprocalExpr.tripleFactor_zero (shiftedPole_pos hu _)
    (shiftedPole_strictMono u (by omega)) (shiftedPole_strictMono u (by omega))

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset

lemma slowPole_eval {u : ℝ} (n : ℕ) :
    (ReciprocalExpr.normalizedPole (shiftedPole u n)).eval (-shiftedPole u 0)=poleTailRatio u n := by
  rw [ReciprocalExpr.normalizedPole_eval]
  simp only [shiftedPole,poleTailRatio]
  congr 1
  ring

lemma tripleFactor_le_pair {a b c x : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hx : -a < x) (hx0 : x ≤ 0) :
    (ReciprocalExpr.tripleFactor a b c).eval x ≤ (a/(a+x))*(c/(c+x)) := by
  rw [ReciprocalExpr.tripleFactor_eval ha hab hbc (by linarith) (by linarith)]
  have hp : 0 ≤ (a/(a+x))*(c/(c+x)) := mul_nonneg (div_nonneg ha.le (by linarith)) (div_nonneg (by linarith) (by linarith))
  have h : 1+x/b ≤ 1 := by apply add_le_of_nonpos_right;exact div_nonpos_of_nonpos_of_nonneg hx0 (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right h hp]

lemma tailScalar_majorant {u : ℝ} (hu4 : u ≤ 4) (f : ℕ → ℝ)
    (hf : ∀ j,0 ≤ f j) (hbound : ∀ j,f j ≤ poleTailRatio u (3*j+3)*poleTailRatio u (3*j+5)) (m : ℕ) :
    poleTailRatio u 2*(∏ j ∈ range m,f j) ≤ ∏ j ∈ range (3*m+2),poleTailRatio u (j+1) := by
  have hR (j : ℕ) : 1 ≤ poleTailRatio u (j+1) := poleTailRatio_ge_one hu4 (by omega)
  induction m with
  | zero =>
    simp only [mul_zero,zero_add,prod_range_zero,mul_one]
    norm_num [prod_range_succ,prod_range_zero]
    nlinarith [hR 0,hR 1]
  | succ m ih =>
    rw [prod_range_succ,mul_left_comm] -- put old product together below
    have hh := mul_le_mul ih (hbound m) (hf m)
      (prod_nonneg (fun j hj=>le_trans zero_le_one (hR j)))
    have hmid : 1 ≤ poleTailRatio u (3*m+4) := by simpa using hR (3*m+3)
    have hr1 : 0 ≤ poleTailRatio u (3*m+3) := by exact le_trans zero_le_one (poleTailRatio_ge_one hu4 (by omega))
    have hr2 : 0 ≤ poleTailRatio u (3*m+5) := by exact le_trans zero_le_one (poleTailRatio_ge_one hu4 (by omega))
    have hp : 0 ≤ ∏ j ∈ range (3*m+2),poleTailRatio u (j+1) := prod_nonneg (fun j hj=>le_trans zero_le_one (hR j))
    have ht := mul_le_mul_of_nonneg_left hmid (mul_nonneg hp (mul_nonneg hr1 hr2))
    rw [show 3*(m+1)+2=(3*m+2)+1+1+1 by omega,prod_range_succ,prod_range_succ,prod_range_succ]
    simpa only [Nat.add_assoc] using (show
      (∏ j ∈ range m,f j)*(poleTailRatio u 2*f m) ≤
      (((∏ j ∈ range (3*m+2),poleTailRatio u (j+1))*poleTailRatio u (3*m+3))*poleTailRatio u (3*m+4))*poleTailRatio u (3*m+5) by
        nlinarith [hh,ht])

lemma tailScalar_uniform {u : ℝ} (hu : 0 ≤ u) (hu4 : u ≤ 4) (f : ℕ → ℝ)
    (hf : ∀ j,0 ≤ f j) (hbound : ∀ j,f j ≤ poleTailRatio u (3*j+3)*poleTailRatio u (3*j+5)) (m : ℕ) :
    poleTailRatio u 2*(∏ j ∈ range m,f j) ≤ 2 :=
  (tailScalar_majorant hu4 f hf hbound m).trans (poleTailProduct_uniform hu hu4 (3*m+2))

noncomputable def physicalPairTail (u : ℝ) (m : ℕ) : ReciprocalExpr :=
  ReciprocalExpr.rangeProduct (fun j=>physicalPairExpr u (j+1)) m
noncomputable def physicalTripleTail (u : ℝ) (m : ℕ) : ReciprocalExpr :=
  ReciprocalExpr.rangeProduct (fun j=>physicalTripleExpr u (j+1)) m

lemma physicalPairExpr_poles (u : ℝ) (n : ℕ) :
    (physicalPairExpr u (n+1)).PolesAbove (shiftedPole u 0) := by
  apply ReciprocalExpr.mulExpr_poles
  · exact ReciprocalExpr.normalizedPole_poles (shiftedPole_strictMono u (by omega))
  · exact ReciprocalExpr.normalizedPole_poles (shiftedPole_strictMono u (by omega))
lemma physicalPairExpr_coeff {u : ℝ} (hu4 : u ≤ 4) (n : ℕ) :
    (physicalPairExpr u n).CoeffNonneg := ReciprocalExpr.mulExpr_coeff
      (ReciprocalExpr.normalizedPole_coeff (shiftedPole_pos hu4 _).le)
      (ReciprocalExpr.normalizedPole_coeff (shiftedPole_pos hu4 _).le)
lemma physicalPairExpr_zero {u : ℝ} (hu4 : u ≤ 4) (n : ℕ) :
    (physicalPairExpr u n).eval 0=1 := by
  rw [physicalPairExpr,ReciprocalExpr.mulExpr_eval,ReciprocalExpr.normalizedPole_zero (shiftedPole_pos hu4 _),
    ReciprocalExpr.normalizedPole_zero (shiftedPole_pos hu4 _),mul_one]
lemma physicalPairTail_poles (u : ℝ) (m : ℕ) : (physicalPairTail u m).PolesAbove (shiftedPole u 0) :=
  ReciprocalExpr.rangeProduct_poles m (fun j _=>physicalPairExpr_poles u j)
lemma physicalTripleTail_poles (u : ℝ) (m : ℕ) : (physicalTripleTail u m).PolesAbove (shiftedPole u 0) :=
  ReciprocalExpr.rangeProduct_poles m (fun j _=>physicalTripleExpr_poles j)
lemma physicalPairTail_coeff {u : ℝ} (hu4 : u ≤ 4) (m : ℕ) : (physicalPairTail u m).CoeffNonneg :=
  ReciprocalExpr.rangeProduct_coeff m (fun _ _=>physicalPairExpr_coeff hu4 _)
lemma physicalTripleTail_coeff {u : ℝ} (hu4 : u ≤ 4) (m : ℕ) : (physicalTripleTail u m).CoeffNonneg :=
  ReciprocalExpr.rangeProduct_coeff m (fun _ _=>physicalTripleExpr_coeff hu4 _)
lemma physicalPairTail_zero {u : ℝ} (hu4 : u ≤ 4) (m : ℕ) : (physicalPairTail u m).eval 0=1 := by
  simp [physicalPairTail,ReciprocalExpr.rangeProduct_eval,physicalPairExpr_zero hu4]
lemma physicalTripleTail_zero {u : ℝ} (hu4 : u ≤ 4) (m : ℕ) : (physicalTripleTail u m).eval 0=1 := by
  simp [physicalTripleTail,ReciprocalExpr.rangeProduct_eval,physicalTripleExpr_zero hu4]

lemma physicalPairTail_uniform {u : ℝ} (hu : 0 ≤ u) (hu4 : u ≤ 4) (m : ℕ) :
    poleTailRatio u 2*(physicalPairTail u m).eval (-shiftedPole u 0) ≤ 2 := by
  unfold physicalPairTail
  rw [ReciprocalExpr.rangeProduct_eval]
  apply tailScalar_uniform hu hu4
  · intro j
    exact ReciprocalExpr.eval_nonneg (physicalPairExpr_poles u j) (physicalPairExpr_coeff hu4 _) le_rfl
  · intro j
    simp only [physicalPairExpr,ReciprocalExpr.mulExpr_eval,slowPole_eval]
    rw [show 3*(j+1)+2=3*j+5 by omega,show 3*(j+1)=3*j+3 by omega]

lemma physicalTripleTail_uniform {u : ℝ} (hu : 0 ≤ u) (hu4 : u ≤ 4) (m : ℕ) :
    poleTailRatio u 2*(physicalTripleTail u m).eval (-shiftedPole u 0) ≤ 2 := by
  unfold physicalTripleTail
  rw [ReciprocalExpr.rangeProduct_eval]
  apply tailScalar_uniform hu hu4
  · intro j
    exact ReciprocalExpr.eval_nonneg (physicalTripleExpr_poles j) (physicalTripleExpr_coeff hu4 _) le_rfl
  · intro j
    have h := tripleFactor_le_pair (shiftedPole_pos hu4 (3*(j+1)))
      (shiftedPole_strictMono u (by omega : 3*(j+1)<3*(j+1)+1))
      (shiftedPole_strictMono u (by omega : 3*(j+1)+1<3*(j+1)+2))
      (neg_lt_neg (shiftedPole_strictMono u (by omega : 0<3*(j+1))))
      (neg_nonpos.mpr (shiftedPole_pos hu4 0).le)
    change (physicalTripleExpr u (j+1)).eval (-shiftedPole u 0) ≤ _ at h
    have h1 := slowPole_eval (u:=u) (3*(j+1))
    have h2 := slowPole_eval (u:=u) (3*(j+1)+2)
    rw [ReciprocalExpr.normalizedPole_eval] at h1 h2
    rw [h1,h2,show 3*(j+1)+2=3*j+5 by omega,show 3*(j+1)=3*j+3 by omega] at h
    exact h

lemma physical_first_weight_half {u : ℝ} (hu : 0 ≤ u) (hu4 : u ≤ 4) :
    (1/2:ℝ) ≤ ReciprocalExpr.tripleWeight (shiftedPole u 0) (shiftedPole u 1) (shiftedPole u 2) := by
  unfold ReciprocalExpr.tripleWeight shiftedPole physicalPole
  norm_num
  apply (le_div_iff₀ (by nlinarith : 0 < (64-u)*(512/3))).mpr
  nlinarith

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset

noncomputable def originPowerData {n : ℕ} (v : ℕ → ℝ) (g : ℝ → ℝ)
    (k : ℕ) (j : Fin (n+1)) : ℝ := if k=0 then g (v j) else (v j)^k
noncomputable def coefficientMinor {n : ℕ} (C : Fin (n+1) → ℕ → ℝ)
    (e : Fin (n+1) → ℕ) : ℝ := Matrix.det (fun i j => C j (e i))

lemma increasing_zero_sparse {n : ℕ} {d : Fin (n+1) → ℕ}
    (hd : StrictMono d) (h0 : d 0=0) :
    ∃ e : Fin n → ℕ,StrictMono e ∧ d=sparseExponent e := by
  let e : Fin n → ℕ := fun i=>d i.succ-1
  have hp (i : Fin n) : 0<d i.succ := by
    rw [←h0]
    exact hd (Fin.succ_pos i)
  refine ⟨e,?_,?_⟩
  · intro i j hij
    have h := hd (Fin.succ_lt_succ_iff.mpr hij)
    have hi := hp i
    dsimp [e]
    omega
  · funext i
    refine Fin.cases ?_ (fun i=>?_) i
    · simpa [sparseExponent] using h0
    · simp only [sparseExponent,Fin.cons_succ,e]
      have hi := hp i
      omega

lemma originPowerData_sparse {n : ℕ} (v : ℕ → ℝ) (g : ℝ → ℝ) (e : Fin n → ℕ) :
    (fun i j : Fin (n+1)=>originPowerData v g (sparseExponent e i) j)=
      Fin.cases (fun j=>g (v j)) (fun i j=>(v j)^(e i+1)) := by
  ext i j
  refine Fin.cases ?_ (fun i=>?_) i <;> simp [originPowerData,sparseExponent]

lemma originPowerData_sparse_det {n : ℕ} (v : ℕ → ℝ) (g : ℝ → ℝ) (e : Fin n → ℕ)
    (hv : ∀ i : Fin (n+1),0<v i) (hord : StrictMono (fun i : Fin (n+1)=>v i))
    (he : StrictMono e) :
    Matrix.det (fun i j : Fin (n+1)=>originPowerData v g (sparseExponent e i) j)=
      (sparseMatrix v e).det*sparseEval v e g := by
  rw [originPowerData_sparse]
  unfold sparseEval
  rw [sparseWeight_eval]
  field_simp [(sparseMatrix_det_pos hv hord he).ne']

lemma coefficient_power_pair_permute {n : ℕ} (C : Fin (n+1) → ℕ → ℝ)
    (v : ℕ → ℝ) (g : ℝ → ℝ) (d : Fin (n+1) → ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    coefficientMinor C (d∘σ)*Matrix.det (fun i j=>originPowerData v g ((d∘σ) i) j)=
      coefficientMinor C d*Matrix.det (fun i j=>originPowerData v g (d i) j) := by
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun i j=>C j (d i)
  let B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun i j=>originPowerData v g (d i) j
  change (A.submatrix σ id).det*(B.submatrix σ id).det=A.det*B.det
  rw [Matrix.det_permute,Matrix.det_permute]
  have hs : (((Equiv.Perm.sign σ:ℤ):ℝ))^2=1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h|h <;> simp [h]
  calc
    _=(((Equiv.Perm.sign σ:ℤ):ℝ))^2*(A.det*B.det) := by ring
    _=A.det*B.det := by rw [hs,one_mul]


lemma positive_mixture_finite_bounds {n m q : ℕ}
    (C : Fin (n+1) → ℕ → ℝ) (v : ℕ → ℝ) (g : ℝ → ℝ)
    (hv : ∀ i : Fin (n+1),0<v i) (hord : StrictMono (fun i : Fin (n+1)=>v i))
    (hc : ∀ d : Fin (n+1) → ℕ,StrictMono d → 0≤coefficientMinor C d)
    (hz : ∀ d : Fin (n+1) → ℕ,StrictMono d →
      (∃ k,k≤q ∧ ∀ i,d i≠k) → coefficientMinor C d=0)
    {L U : ℝ}
    (hbound : ∀ e : Fin n → ℕ,StrictMono e →
      (∀ k,1≤k → k≤q → ∃ i,e i+1=k) → L ≤ sparseEval v e g ∧ sparseEval v e g ≤ U) :
    let A : Matrix (Fin (n+1)) (Fin m) ℝ := fun i k=>C i k
    let B : Matrix (Fin m) (Fin (n+1)) ℝ := fun k j=>(v j)^k.val
    let D : Matrix (Fin m) (Fin (n+1)) ℝ := fun k j=>originPowerData v g k j
    L*(A*B).det≤(A*D).det ∧ (A*D).det≤U*(A*B).det := by
  classical
  dsimp only
  let A : Matrix (Fin (n+1)) (Fin m) ℝ := fun i k=>C i k
  let B : Matrix (Fin m) (Fin (n+1)) ℝ := fun k j=>(v j)^k.val
  let D : Matrix (Fin m) (Fin (n+1)) ℝ := fun k j=>originPowerData v g k j
  have hminor (f : Fin (n+1) → Fin m) : (A.submatrix id f).det=coefficientMinor C (fun i=>(f i).val) := by
    rw [←Matrix.det_transpose]
    rfl
  have hterm (e : Fin (n+1) → ℕ) :
      L*(coefficientMinor C e*Matrix.det (fun i j=>originPowerData v (fun _=>1) (e i) j))≤
        coefficientMinor C e*Matrix.det (fun i j=>originPowerData v g (e i) j) ∧
      coefficientMinor C e*Matrix.det (fun i j=>originPowerData v g (e i) j)≤
        U*(coefficientMinor C e*Matrix.det (fun i j=>originPowerData v (fun _=>1) (e i) j)) := by
    by_cases hi : Function.Injective e
    · obtain ⟨d,σ,hd,rfl⟩ := sorted_injective_exponents hi
      rw [coefficient_power_pair_permute,coefficient_power_pair_permute]
      by_cases hz' : ∃ k,k≤q ∧ ∀ i,d i≠k
      · rw [hz d hd hz']
        simp
      · push Not at hz'
        obtain ⟨i,hi⟩ := hz' 0 (Nat.zero_le q)
        have h0 : d 0=0 := by
          have hle := hd.monotone (Fin.zero_le i)
          omega
        obtain ⟨f,hf,rfl⟩ := increasing_zero_sparse hd h0
        have hq : ∀ k,1≤k → k≤q → ∃ i,f i+1=k := by
          intro k hk hkq
          obtain ⟨i,hi⟩ := hz' k hkq
          refine Fin.cases ?_ (fun j=>?_) i hi
          · simp [sparseExponent] at *
            omega
          · intro hi
            exact ⟨j,by simpa [sparseExponent] using hi⟩
        rw [originPowerData_sparse_det v _ f hv hord hf,originPowerData_sparse_det v _ f hv hord hf]
        have hs : sparseEval v f (fun _=>1)=1 := by
          simpa [sparseEval] using sparseWeight_sum hv hord hf
        rw [hs,mul_one]
        have hm := mul_nonneg (hc _ hd) (sparseMatrix_det_pos hv hord hf).le
        have hb := hbound f hf hq
        constructor <;> nlinarith only [mul_nonneg hm (sub_nonneg.mpr hb.1),mul_nonneg hm (sub_nonneg.mpr hb.2)]
    · have hh : coefficientMinor C e=0 := by
        obtain ⟨i,j,heq,hij⟩ := Function.not_injective_iff.mp hi
        apply Matrix.det_zero_of_row_eq hij
        funext k

        rw [heq]
      rw [hh]
      simp
  have hb (f : Fin (n+1) → Fin m) :
      L*((A.submatrix id f).det*(B.submatrix f id).det)≤
        (A.submatrix id f).det*(D.submatrix f id).det ∧
      (A.submatrix id f).det*(D.submatrix f id).det≤
        U*((A.submatrix id f).det*(B.submatrix f id).det) := by
    have h := hterm (fun i=>(f i).val)
    rw [hminor]
    have he : B.submatrix f id = (fun i j=>originPowerData v (fun _=>1) ((f i).val) j) := by
      ext i j
      change (v j)^(f i).val = if (f i).val=0 then 1 else (v j)^(f i).val
      split_ifs with h <;> simp [h]
    rw [he]
    exact h
  have hL := sum_le_sum (fun f (_ : f∈univ)=> (hb f).1)
  have hU := sum_le_sum (fun f (_ : f∈univ)=> (hb f).2)
  rw [←mul_sum,det_rectangular_binet,det_rectangular_binet] at hL hU
  have hp : (0:ℝ)<Fintype.card (Equiv.Perm (Fin (n+1))) := by exact_mod_cast Fintype.card_pos
  constructor
  · exact (mul_le_mul_iff_right₀ hp).mp (by nlinarith only [hL])
  · exact (mul_le_mul_iff_right₀ hp).mp (by nlinarith only [hU])

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
lemma cosineKernelJet_square_cosh (m p : ℝ) :
    cosineKernelJet 0 0 (m^2) (p^2)=Real.cosh (m*p) := by
  rw [cosineKernelJet_zero_zero_cosh (sq_nonneg _) (sq_nonneg _),Real.sqrt_sq_eq_abs,Real.sqrt_sq_eq_abs,
    ←abs_mul,Real.cosh_abs]
lemma cosineKernelJet_first_square (m p : ℝ) :
    2*m*cosineKernelJet 1 0 (m^2) (p^2)=p*Real.sinh (m*p) := by
  have h:= (cosineKernelJet_hasDerivAt_left 0 0 (m^2) (p^2)).comp m ((hasDerivAt_id m).pow 2)
  have he : (fun b=>cosineKernelJet 0 0 (b^2) (p^2))=(fun b=>Real.cosh (b*p)) := funext (fun b=>cosineKernelJet_square_cosh b p)
  have h' : HasDerivAt (fun b=>cosineKernelJet 0 0 (b^2) (p^2))
      (((0+1:ℝ)*cosineKernelJet (0+1) 0 (m^2) (p^2))*(2*m)) m := by convert! h using 1 ; simp only [id_eq,pow_one,Nat.cast_ofNat,mul_one,Nat.cast_zero,zero_add,show 2-1=1 by omega]
  rw [he] at h'
  have hc : HasDerivAt (fun b=>Real.cosh (b*p)) (Real.sinh (m*p)*p) m := by
    convert! ((Real.hasDerivAt_cosh (m*p)).comp m ((hasDerivAt_id m).mul_const p)) using 1 ; simp only [one_mul]
  have hd:=h'.unique hc
  simp only [zero_add,one_mul] at hd
  nlinarith only [hd]
lemma cosineKernelJet_ode_zero {b : ℝ} (hb : 0<b) (p : ℝ) :
    p^2*cosineKernelJet 0 0 b (p^2)=8*b*cosineKernelJet 2 0 b (p^2)+2*cosineKernelJet 1 0 b (p^2) := by
  let m := Real.sqrt b
  have hm : m^2=b := Real.sq_sqrt hb.le
  have hJ := (cosineKernelJet_hasDerivAt_left 1 0 (m^2) (p^2)).comp m ((hasDerivAt_id m).pow 2)
  have h : HasDerivAt (fun s=>2*s*cosineKernelJet 1 0 (s^2) (p^2))
      (2*cosineKernelJet 1 0 (m^2) (p^2)+8*m^2*cosineKernelJet 2 0 (m^2) (p^2)) m := by
    convert! (((hasDerivAt_id m).const_mul 2).mul hJ) using 1 ; simp only [Function.comp_def,Pi.pow_apply,id_eq,pow_one,Nat.cast_ofNat,mul_one,show 2-1=1 by omega] ; ring
  have he : (fun s=>2*s*cosineKernelJet 1 0 (s^2) (p^2))=(fun s=>p*Real.sinh (s*p)) :=
    funext (fun s=>cosineKernelJet_first_square s p)
  rw [he] at h
  have hs : HasDerivAt (fun s=>p*Real.sinh (s*p)) (p*(Real.cosh (m*p)*p)) m := by
    convert! (((Real.hasDerivAt_sinh (m*p)).comp m ((hasDerivAt_id m).mul_const p)).const_mul p) using 1 ; simp only [one_mul]
  have hd:=h.unique hs
  rw [←cosineKernelJet_square_cosh m p,hm] at hd
  nlinarith only [hd]
lemma cosineKernelJet_ode (r : ℕ) {b : ℝ} (hb : 0<b) (p : ℝ) :
    p^2*cosineKernelJet r 0 b (p^2)=
      4*b*((r:ℝ)+1)*((r:ℝ)+2)*cosineKernelJet (r+2) 0 b (p^2)+
      2*((r:ℝ)+1)*(2*(r:ℝ)+1)*cosineKernelJet (r+1) 0 b (p^2) := by
  induction r generalizing b with
  | zero =>
    norm_num
    nlinarith only [cosineKernelJet_ode_zero hb p]
  | succ r ih =>
    have hL := (cosineKernelJet_hasDerivAt_left r 0 b (p^2)).const_mul (p^2)
    have hR := ((((hasDerivAt_id b).const_mul 4).mul_const ((r:ℝ)+1)).mul_const ((r:ℝ)+2)).mul
      (cosineKernelJet_hasDerivAt_left (r+2) 0 b (p^2)) |>.add
      ((cosineKernelJet_hasDerivAt_left (r+1) 0 b (p^2)).const_mul (2*((r:ℝ)+1)*(2*(r:ℝ)+1)))
    have hev : (fun s=>p^2*cosineKernelJet r 0 s (p^2)) =ᶠ[𝓝 b]
        (fun s=>4*s*((r:ℝ)+1)*((r:ℝ)+2)*cosineKernelJet (r+2) 0 s (p^2)+
          (2*((r:ℝ)+1)*(2*(r:ℝ)+1))*cosineKernelJet (r+1) 0 s (p^2)) := by
      filter_upwards [eventually_gt_nhds hb] with s hs
      exact ih hs
    have hd := (hL.congr_of_eventuallyEq hev.symm).unique hR
    simp only [id_eq,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,show r+1+1=r+2 by omega,show r+2+1=r+1+2 by omega] at hd ⊢
    have hn : (r:ℝ)+1≠0 := by positivity
    apply (mul_left_cancel₀ hn)
    linear_combination hd
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
